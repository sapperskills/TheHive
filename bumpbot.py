#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Pump.fun swing booster with house-profit buybacks + CRASH-SAFE STATE + SOL↔USDC swings:

 - Drip buys with burst/dip states
 - Swing sells gated by profit & volume
 - House skim on realized profits -> TWAP buybacks
   · NEW: Optional per-burner self-buybacks (from the same burner) on SOL↔USDC swing profits
 - OPTIONAL native SOL swing engine (SOL<->USDC via Jupiter)
   · Rotates SOL→USDC on weakness, USDC→SOL on strength
   · Skims realized SOL profit (configurable sink: main wallet or self-buybacks)
 - Optional park/lock target (transfer stub; true LP lock not included)
 - Dynamic burners on SOL deposits
 - Persistent wallet list (wallets_list.json) with atomic writes + backup
 - Reconnects, rate-limit backoff, metrics
 - RPC failover (hard-coded) + Pump 429 backoff + daily SOL budget
 - Anti-snipe window + volatility brake + drawdown-reactive buybacks
 - ATA auto-create + safe balance reads (generic and token-specific)
 - Single persistent WS socket (subscribe/unsubscribe without reconnects)
 - Crash-safe state.json with periodic checkpoints + on-boot recovery
"""

import asyncio
import aiohttp
import base58
import base64
import json
import os
import random
import random as _rand
import signal
import sys
import time
import traceback
import websockets
import tempfile
from math import isfinite
from pathlib import Path

from typing import Dict, Tuple, Optional
from collections import deque

from solders.keypair import Keypair
from solders.pubkey import Pubkey
from solders.transaction import VersionedTransaction
from solders.system_program import TransferParams, transfer
from solders.instruction import Instruction, AccountMeta

from solana.rpc.async_api import AsyncClient
from solana.rpc.types import TxOpts
from solana.exceptions import SolanaRpcException

# try legacy tx (for funding burners / ATA creates)
try:
    from solana.transaction import Transaction as LegacyTransaction
except Exception:
    from solders.transaction import Transaction as LegacyTransaction  # fallback

from prometheus_client import start_http_server, Counter, Gauge, Histogram

# ─── Metrics ───────────────────────────────────────────────────────────────
BUY_COUNTER    = Counter('booster_buys_total',             'Total buy trades')
SELL_COUNTER   = Counter('booster_sells_total',            'Total sell trades')
FAIL_COUNTER   = Counter('booster_trade_failures',         'Total failed trades')
RPC429_COUNTER = Counter('booster_rpc_429_errors',         'RPC errors (429/timeouts/etc)')
BANKROLL_GAUGE = Gauge('booster_current_bankroll',         'Latest SOL bankroll')
PEAK_GAUGE     = Gauge('booster_peak_bankroll',            'All-time high bankroll')
LOSS_STREAK    = Gauge('booster_loss_streak',              'Consecutive losing trades')
CUM_BUYS       = Gauge('booster_cumulative_buys',          'SOL bought since boost threshold')
LOOP_TIME      = Histogram('booster_loop_duration_seconds','Time per loop iteration')
HOUSE_BANK     = Gauge('booster_house_bank_sol',           'Pending house SOL for buybacks')
PRICE_GAUGE    = Gauge('booster_token_price',              'Latest price (SOL)')
VOL_GAUGE      = Gauge('booster_volume_ema',               'Volume EMA (SOL)')
SPENT_TODAY    = Gauge('booster_spent_today_sol',          'SOL spent today by the bot')
RPC_INDEX_GAUGE= Gauge('booster_current_rpc_index',        'Current RPC index in pool')

# ─── Load config.json ───────────────────────────────────────────────────────
CFG = "config.json"
if not os.path.exists(CFG):
    sys.exit("❌ config.json missing")
cfg = json.load(open(CFG))

# Required
TOKEN_MINT          = cfg["TOKEN_MINT"]
WS_URI              = cfg.get("WS_URI", "wss://pumpportal.fun/api/data")
MAIN_SECRET         = cfg["MAIN_SECRET"]

# Funding & trade settings
INITIAL_BANKROLL_SOL = cfg.get("INITIAL_BANKROLL_SOL", 1.0)
SLIPPAGE_BPS        = int(cfg.get("SLIPPAGE_BPS", 30))
PRIORITY_FEE        = float(cfg.get("PRIORITY_FEE", 0.0005))
PCT_MIN             = float(cfg.get("PCT_MIN", 1.0))     # % of SOL balance per drip buy
PCT_MAX             = float(cfg.get("PCT_MAX", 2.5))

DRIP_MIN_SEC        = int(cfg.get("DRIP_MIN_SEC", 20))
DRIP_MAX_SEC        = int(cfg.get("DRIP_MAX_SEC", 40))
BURST_PROB          = float(cfg.get("BURST_PROB", 0.01))
BURST_DURATION_MIN  = int(cfg.get("BURST_DURATION_MIN", 45))
BURST_DURATION_MAX  = int(cfg.get("BURST_DURATION_MAX", 120))
BURST_DRIP_MIN_SEC  = int(cfg.get("BURST_DRIP_MIN_SEC", 5))
BURST_DRIP_MAX_SEC  = int(cfg.get("BURST_DRIP_MAX_SEC", 15))
DIP_DURATION_MIN    = int(cfg.get("DIP_DURATION_MIN", 120))
DIP_DURATION_MAX    = int(cfg.get("DIP_DURATION_MAX", 300))

BOOST_THRESHOLD_SOL = float(cfg.get("BOOST_THRESHOLD_SOL", 3.0))
BOOST_MULTIPLIER    = float(cfg.get("BOOST_MULTIPLIER", 1.25))
STOP_LOSS_PCT       = float(cfg.get("STOP_LOSS_PCT", 0.003))
CONSEC_LOSS_LIMIT   = int(cfg.get("CONSECUTIVE_LOSS_LIMIT", 3))
COOLDOWN_PERIOD_SEC = int(cfg.get("COOLDOWN_PERIOD_SEC", 1800))
MAX_RUNTIME_SEC     = int(cfg.get("MAX_RUNTIME_SEC", 43200))

SWING_PROFIT_TARGET = float(cfg.get("SWING_PROFIT_TARGET", 0.05))
VOLUME_EMA_ALPHA    = float(cfg.get("VOLUME_EMA_ALPHA", 0.1))
VOLUME_MULT         = float(cfg.get("VOLUME_MULT", 2.0))

DONATION_INTERVAL   = int(cfg.get("DONATION_CHECK_INTERVAL", 5))
DONATION_THRESHOLD_SOL = float(cfg.get("DONATION_THRESHOLD_SOL", 0.1))

# NEW: house-profit & market-hold controls
HOUSE_PROFIT_PCT     = float(cfg.get("HOUSE_PROFIT_PCT", 0.35))     # 35% of realized profit skimmed
HOUSE_MIN_BUY_SOL    = float(cfg.get("HOUSE_MIN_BUY_SOL", 0.05))    # threshold to trigger buybacks
HOUSE_TWAP_CHUNKS    = int(cfg.get("HOUSE_TWAP_CHUNKS", 3))
HOUSE_TWAP_DELAY_SEC = int(cfg.get("HOUSE_TWAP_DELAY_SEC", 15))

# NEW: choose where swing profit skims are spent
# - True  => burner self-buys its own token directly (per-burner TWAP)
# - False => send skim to main wallet (centralized TWAP from main)
BURNER_SELF_BUYBACKS = bool(cfg.get("BURNER_SELF_BUYBACKS", True))

MAX_SHELL_FRAC_FIX   = 1.0  # no-op (placeholder for future guards)

MAX_SELL_FRAC        = float(cfg.get("MAX_SELL_FRAC", 0.15))        # sell <= 15% of inventory per event
MAX_VOL_SELL_FRAC    = float(cfg.get("MAX_VOL_SELL_FRAC", 0.20))    # sell <= 20% of rolling vol
MIN_HOLD_RATIO       = float(cfg.get("MIN_HOLD_RATIO", 0.60))       # keep >=60% of lifetime acquired

# Optional park/lock wallet (just a separate wallet to hold house tokens)
LOCK_DEST            = cfg.get("LOCK_DEST")                  # base58 pubkey or None
LOCK_MODE            = cfg.get("LOCK_MODE", "hold")          # "hold" or "transfer" (transfer stub)
LOCK_PCT             = float(cfg.get("LOCK_PCT", 1.0))       # fraction of house buys to park

# Daily budget & buy caps
DAILY_SOL_BUDGET     = float(cfg.get("DAILY_SOL_BUDGET", 0.8))
MIN_BUY_SOL          = float(cfg.get("MIN_BUY_SOL", 0.0005))
MAX_BUY_SOL          = float(cfg.get("MAX_BUY_SOL", 0.02))

# Anti-snipe & volatility/drawdown controls
ANTI_SNIPE_SECS           = int(cfg.get("ANTI_SNIPE_SECS", 600))   # 10 min after start
TIGHT_SLIPPAGE_BPS        = int(cfg.get("TIGHT_SLIPPAGE_BPS", 20)) # tighter early slippage

VOL_BRAKE_PCT             = float(cfg.get("VOL_BRAKE_PCT", 0.08))  # 8% move in window pauses sells
VOL_BRAKE_LOOKBACK_SEC    = int(cfg.get("VOL_BRAKE_LOOKBACK_SEC", 60))
VOL_BRAKE_COOLDOWN_SEC    = int(cfg.get("VOL_BRAKE_COOLDOWN_SEC", 120))

DRAWDOWN_THRESH_1         = float(cfg.get("DRAWDOWN_THRESH_1", 0.10)) # 10% off peak
DRAWDOWN_THRESH_2         = float(cfg.get("DRAWDOWN_THRESH_2", 0.20)) # 20% off peak
DRAWDOWN_CHUNKS_MULT_1    = float(cfg.get("DRAWDOWN_CHUNKS_MULT_1", 2.0))
DRAWDOWN_CHUNKS_MULT_2    = float(cfg.get("DRAWDOWN_CHUNKS_MULT_2", 4.0))
DRAWDOWN_DELAY_MIN_SEC    = int(cfg.get("DRAWDOWN_DELAY_MIN_SEC", 5))

# Infra
LAMPORTS_PER_SOL    = 10**9
TX_FEE_BUFFER       = 5_000
TX_FEE_APPROX       = 5_000
WALLETS_LOG         = cfg.get("WALLETS_LOG", "wallets_list.json")
PUMP_API_URL        = cfg.get("PUMP_API_URL", "https://pumpportal.fun/api/trade-local")
MAX_PARALLEL_RPC    = int(cfg.get("MAX_PARALLEL_RPC", 4))
RETRY_BACKOFF       = tuple(cfg.get("RETRY_BACKOFF", [1,6]))
BAL_CHECK_SEC       = int(cfg.get("BAL_CHECK_SEC", 60))
BALANCE_TTL_SEC     = int(cfg.get("BALANCE_TTL_SEC", 5))  # cache TTL for get_balance

# Crash-safe state
STATE_FILE        = cfg.get("STATE_FILE", "state.json")
CHECKPOINT_SEC    = int(cfg.get("CHECKPOINT_SEC", 15))
RECOVER_ON_BOOT   = bool(cfg.get("RECOVER_TOKENS_ON_BOOT", True))

# ── SOL↔USDC swing config (Jupiter) ────────────────────────────────────────
ENABLE_SOL_SWINGS      = bool(cfg.get("ENABLE_SOL_SWINGS", False))
SWING_ON_MAIN          = bool(cfg.get("SWING_ON_MAIN", True))
SWING_ON_BURNERS       = bool(cfg.get("SWING_ON_BURNERS", False))

SOL_SWING_DROP_PCT     = float(cfg.get("SOL_SWING_DROP_PCT", 0.02))   # rotate SOL→USDC if price drops ≥2% from pivot
SOL_SWING_RISE_PCT     = float(cfg.get("SOL_SWING_RISE_PCT", 0.02))   # rotate USDC→SOL if price rises ≥2% from pivot
SOL_SWING_MIN_INTERVAL = int(cfg.get("SOL_SWING_MIN_INTERVAL_SEC", 60))
SOL_SWING_MIN_SKIM_SOL = float(cfg.get("SOL_SWING_MIN_SKIM_SOL", 0.003))
SOL_SWING_ALLOC_FRAC   = float(cfg.get("SOL_SWING_ALLOC_FRAC", 1.00))

JUP_QUOTE_URL          = cfg.get("JUP_QUOTE_URL", "https://quote-api.jup.ag/v6/quote")
JUP_SWAP_URL           = cfg.get("JUP_SWAP_URL",  "https://quote-api.jup.ag/v6/swap")

USDC_MINT_STR          = cfg.get("SWING_USDC_MINT", "EPjFWdd5AufqSSqeM2qN1xzybapC8G4wEGGkZwyTDt1v")
SOL_MINT_STR           = cfg.get("SOL_MINT", "So11111111111111111111111111111111111111112")

# Built-in Jupiter rate-limit/backoff defaults so config.json needn't change
JUP_MAX_QPS            = float(cfg.get("JUP_MAX_QPS", 3.0))   # steady quotes/sec
JUP_BURST              = int(cfg.get("JUP_BURST", 3))         # short burst capacity
JUP_PRICE_TTL_SEC      = float(cfg.get("JUP_PRICE_TTL_SEC", 8.0))  # price cache TTL
JUP_429_COOLDOWN_SEC   = float(cfg.get("JUP_429_COOLDOWN_SEC", 25.0))
JUP_MAX_RETRIES        = int(cfg.get("JUP_MAX_RETRIES", 5))
JUP_USER_AGENT         = cfg.get("JUP_USER_AGENT", "GuardianXBoost/1.0 (+github.com/guardianx)")

# ─── HARD-CODED RPC POOL (primary + backup only) ───────────────────────────
PRIMARY_RPC   = "https://mainnet.helius-rpc.com/?api-key=1ed247f5-6cee-42ba-90d5-2fb2e2ec5925"
SECONDARY_RPC = "https://solana-mainnet.core.chainstack.com/f98a200a3ddab23bd133db2a2fd14e07"
RPC_POOL = [PRIMARY_RPC, SECONDARY_RPC]

rpc_sema: asyncio.Semaphore | None = None
MINT_PUB: Pubkey = Pubkey.from_string(TOKEN_MINT)

# Program IDs
TOKEN_PROGRAM_ID              = Pubkey.from_string("TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA")
ASSOCIATED_TOKEN_PROGRAM_ID   = Pubkey.from_string("ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL")
SYS_PROGRAM_ID                = Pubkey.from_string("11111111111111111111111111111111")
RENT_SYSVAR_ID                = Pubkey.from_string("SysvarRent111111111111111111111111111111111")

# Swing mint Pubkeys
USDC_MINT = Pubkey.from_string(USDC_MINT_STR)
SOL_MINT  = Pubkey.from_string(SOL_MINT_STR)

# ─── Helpers for crash-safe IO ─────────────────────────────────────────────
def _write_text_atomic(path: str, data: str):
    p = Path(path)
    tmp = p.with_suffix(p.suffix + ".tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(data)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, p)

def _atomic_update_wallets_log(new_wallet_bytes: bytes):
    """
    Append a new keypair (as list of ints) to wallets_list.json atomically,
    and create/refresh a .bak for extra safety.
    """
    current = []
    try:
        raw = Path(WALLETS_LOG).read_text().strip()
        current = json.loads(raw) if raw else []
        if not isinstance(current, list):
            current = []
    except FileNotFoundError:
        current = []
    except Exception:
        # if corrupt, try backup
        try:
            raw = Path(WALLETS_LOG + ".bak").read_text().strip()
            current = json.loads(raw) if raw else []
        except Exception:
            current = []

    current.append(list(new_wallet_bytes))
    data = json.dumps(current, indent=2)
    _write_text_atomic(WALLETS_LOG, data)
    _write_text_atomic(WALLETS_LOG + ".bak", data)

# ─── Minimal trace ─────────────────────────────────────────────────────────
def log_trace(e: Exception):
    traceback.print_exc()

# ─── Simple async token-bucket limiter for Jupiter ─────────────────────────
class TokenBucket:
    """
    capacity: max tokens; refill_rate: tokens per second
    acquire(): waits until ≥1 token available, then consumes 1
    """
    def __init__(self, capacity: int, refill_rate: float):
        self.capacity = int(max(1, capacity))
        self.tokens = float(self.capacity)
        self.refill_rate = float(max(0.1, refill_rate))
        self.last = time.monotonic()
        self._lock = asyncio.Lock()

    async def acquire(self):
        async with self._lock:
            now = time.monotonic()
            delta = now - self.last
            self.last = now
            self.tokens = min(self.capacity, self.tokens + delta * self.refill_rate)
            if self.tokens < 1.0:
                need = 1.0 - self.tokens
                wait = need / self.refill_rate
                await asyncio.sleep(max(0.0, wait))
                self.tokens = 0.0
                return
            self.tokens -= 1.0

# ─── State manager ─────────────────────────────────────────────────────────
class StateManager:
    """Crash-safe JSON snapshot of key runtime fields."""
    def __init__(self, bot: "Booster", path: str):
        self.bot = bot
        self.path = path
        self._dirty = False

    def mark_dirty(self):
        self._dirty = True

    def snapshot(self) -> dict:
        return {
            "version": 1,
            "token_mint": TOKEN_MINT,
            "created_at": int(time.time()),
            "avg_buy_price": self.bot.avg_buy_price,
            "lifetime_acquired": self.bot.lifetime_acquired,
            "total_tokens": self.bot.total_tokens,
            "house_bank_sol": self.bot.house_bank_sol,
            "peak_price_seen": self.bot.peak_price_seen,
            "peak_bankroll": self.bot.peak_bankroll,
            "spent_today": self.bot.spent_today,
            "day_of_year": self.bot.day_of_year,
        }

    def apply(self, data: dict):
        if not data or data.get("token_mint") != TOKEN_MINT:
            return
        self.bot.avg_buy_price      = float(data.get("avg_buy_price", 0.0))
        self.bot.lifetime_acquired  = float(data.get("lifetime_acquired", 0.0))
        self.bot.total_tokens       = float(data.get("total_tokens", 0.0))
        self.bot.house_bank_sol     = float(data.get("house_bank_sol", 0.0))
        self.bot.peak_price_seen    = data.get("peak_price_seen", None)
        self.bot.peak_bankroll      = data.get("peak_bankroll", None)
        self.bot.spent_today        = float(data.get("spent_today", 0.0))
        self.bot.day_of_year        = int(data.get("day_of_year", time.gmtime().tm_yday))
        HOUSE_BANK.set(self.bot.house_bank_sol)
        SPENT_TODAY.set(self.bot.spent_today)
        if self.bot.peak_bankroll is not None:
            PEAK_GAUGE.set(self.bot.peak_bankroll)

    async def load(self):
        try:
            with open(self.path, "r", encoding="utf-8") as f:
                data = json.load(f)
            self.apply(data)
            print(f"💾 Loaded state from {self.path}")
        except FileNotFoundError:
            print(f"ℹ️ No prior state file at {self.path} (fresh start).")
        except Exception as e:
            print(f"⚠️ Failed to load {self.path}: {e}")

    async def save_now(self):
        try:
            snap = self.snapshot()
            _write_text_atomic(self.path, json.dumps(snap, indent=2))
            self._dirty = False
        except Exception as e:
            print(f"⚠️ Failed to write {self.path}: {e}")

    async def checkpoint_loop(self):
        while self.bot.running:
            try:
                if self._dirty:
                    await self.save_now()
            except Exception as e:
                print(f"⚠️ checkpoint error: {e}")
            await asyncio.sleep(CHECKPOINT_SEC)

# ─── Single persistent WS manager (subscribe/unsubscribe without reconnects) ─
class PumpWS:
    def __init__(self, uri: str):
        self.uri = uri
        self.ws: Optional[websockets.WebSocketClientProtocol] = None
        self.subs: set[str] = set()
        self.queue: asyncio.Queue[str] = asyncio.Queue(maxsize=2000)
        self._task: Optional[asyncio.Task] = None
        self._send_lock = asyncio.Lock()
        self._running = True   # now indented correctly
        self._backoff = 1.0

    async def start(self):
        if self._task:
            return
        self._task = asyncio.create_task(self._runner(), name="pump_ws_runner")

    async def stop(self):
        self._running = False
        try:
            if self.ws:
                await self.ws.close()
        except Exception:
            pass
        if self._task:
            self._task.cancel()

    async def subscribe(self, key: str):
        self.subs.add(key)
        await self._send({"method": "subscribeTokenTrade", "keys": [key]})

    async def unsubscribe(self, key: str):
        if key in self.subs:
            await self._send({"method": "unsubscribeTokenTrade", "keys": [key]})
            self.subs.discard(key)

    async def _send(self, obj: dict):
        async with self._send_lock:
            if self.ws is None:
                return
            try:
                await self.ws.send(json.dumps(obj))
            except Exception as e:
                print(f"⚠️ WS send error: {e}")

    async def _runner(self):
        import random as _r
        while self._running:
            try:
                async with websockets.connect(
                    self.uri,
                    ping_interval=30,
                    ping_timeout=20,
                    max_queue=2000,
                    close_timeout=5,
                ) as ws:
                    self.ws = ws
                    if self.subs:
                        await self._send({"method": "subscribeTokenTrade", "keys": list(self.subs)})
                    self._backoff = 1.0
                    async for raw in ws:
                        try:
                            self.queue.put_nowait(raw)
                        except asyncio.QueueFull:
                            pass
            except (websockets.ConnectionClosedOK, websockets.ConnectionClosedError) as e:
                print(f"⚠️ WS closed: {e}.")
            except Exception as e:
                print(f"⚠️ WS error: {e}.")
            finally:
                self.ws = None
                if not self._running:
                    break
                jitter = _r.uniform(0, 0.5)
                wait = min(self._backoff, 15.0) + jitter
                print(f"⏳ WS reconnect in {wait:.1f}s… (single persistent socket)")
                await asyncio.sleep(wait)
                self._backoff = min(self._backoff * 2.0, 15.0)

class Booster:
    def __init__(self):
        self.main_kp       = self._load_kp()
        self._rpc_idx      = 0
        self.rpc           = AsyncClient(RPC_POOL[self._rpc_idx])
        self._rpc_lock     = asyncio.Lock()
        self.ws_mgr: Optional[PumpWS] = None
        self.session: Optional[aiohttp.ClientSession] = None
        global rpc_sema
        rpc_sema           = asyncio.Semaphore(MAX_PARALLEL_RPC)

        # persistent burners (hardened)
        try:
            raw = open(WALLETS_LOG).read().strip()
            data = json.loads(raw) if raw else []
        except (FileNotFoundError, json.JSONDecodeError):
            data = []
        _write_text_atomic(WALLETS_LOG, json.dumps(data, indent=2))
        _write_text_atomic(WALLETS_LOG + ".bak", json.dumps(data, indent=2))

        self.burners       = [Keypair.from_bytes(bytes(arr)) for arr in data]
        self.dynamic_tasks: list[asyncio.Task] = []
        self.running       = True

        # state
        self.in_burst       = False
        self.in_dip         = False
        self.state_ends     = 0.0
        self.peak_bankroll  = None
        self.loss_streak    = 0
        self.start_time     = time.time()

        # price/volume
        self.current_price: Optional[float] = None
        self.avg_volume: float = 0.0

        # inventory accounting (global)
        self.total_tokens: float = 0.0
        self.avg_buy_price: float = 0.0  # SOL per token (weighted)
        self.lifetime_acquired: float = 0.0  # tokens acquired since start

        # per-burner token balances (uiAmount cache)
        self.token_cache: Dict[str, float] = {}

        # house bank (SOL skim waiting to buy back)
        self.house_bank_sol: float = 0.0
        self.last_main_bal: int = 0

        # budget tracking
        self.spent_today: float = 0.0
        self.day_of_year: int   = time.gmtime().tm_yday
        SPENT_TODAY.set(0.0)
        RPC_INDEX_GAUGE.set(self._rpc_idx)

        # anti-snipe & volatility
        self.start_wall_time     = time.time()
        self.vol_brake_until     = 0.0
        self.price_window        = deque()     # (ts, price) points
        self.peak_price_seen     = None

        # NEW: cached balances
        self._bal_cache: Dict[str, Tuple[int, float]] = {}  # pubkey_str -> (lamports, ts)

        # crash-safe state manager
        self.state = StateManager(self, STATE_FILE)

        # —— Jupiter rate limit + price cache ——
        self.jup_rl = TokenBucket(capacity=JUP_BURST, refill_rate=JUP_MAX_QPS)
        self._last_px: Optional[float] = None
        self._last_px_ts: float = 0.0
        self._jup_cooldown_until: float = 0.0
        self._jup_429s_row: int = 0

    def _load_kp(self) -> Keypair:
        arr = json.loads(MAIN_SECRET)
        if not isinstance(arr, list) or len(arr) not in (64, 32):
            raise SystemExit("❌ MAIN_SECRET must be a JSON array of 64 or 32 bytes.")
        b = bytes(arr)
        try:
            return Keypair.from_bytes(b)
        except Exception as e:
            raise SystemExit(f"❌ MAIN_SECRET invalid: {e}")

    # ─── Anti-snipe / vol helpers ──────────────────────────────────────────
    def _in_antisnipe(self) -> bool:
        return (time.time() - self.start_wall_time) < ANTI_SNIPE_SECS

    def _vol_brake_active(self) -> bool:
        return time.time() < self.vol_brake_until

    def _slippage_bps(self) -> int:
        return TIGHT_SLIPPAGE_BPS if self._in_antisnipe() else SLIPPAGE_BPS

    # ─── RPC lifecycle helpers ─────────────────────────────────────────────
    async def _reinit_rpc(self):
        async with self._rpc_lock:
            try:
                if self.rpc is not None:
                    await self.rpc.close()
            except Exception:
                pass
            self.rpc = AsyncClient(RPC_POOL[self._rpc_idx])

    async def _switch_rpc(self):
        self._rpc_idx = (self._rpc_idx + 1) % len(RPC_POOL)
        await self._reinit_rpc()
        print(f"↪️  RPC failover → {RPC_POOL[self._rpc_idx]}")
        RPC_INDEX_GAUGE.set(self._rpc_idx)

    async def _rpc_call(self, method_name: str, *args, **kwargs):
        attempts = len(RPC_POOL) * 2  # loop pool twice
        backoff  = 1
        for _ in range(attempts):
            client = self.rpc
            if client is None:
                await self._reinit_rpc()
                client = self.rpc
            method = getattr(client, method_name)
            try:
                async with rpc_sema:
                    return await method(*args, **kwargs)

            except RuntimeError as e:
                if "client has been closed" in str(e).lower():
                    await self._reinit_rpc()
                    continue
                raise

            except Exception as e:
                msg = f"{type(e).__name__}: {e}"
                is_provider_err = (
                    isinstance(e, SolanaRpcException)
                    or "Too Many Requests" in msg or "429" in msg
                    or "Forbidden" in msg or "403" in msg
                    or "Timeout" in msg or "timed out" in msg
                    or "503" in msg or "HTTPStatusError" in msg
                )
                if is_provider_err:
                    RPC429_COUNTER.inc()
                    await self._switch_rpc()
                    await asyncio.sleep(backoff)
                    backoff = min(backoff * 2, 8)
                    continue
                raise

        print("⏳ All RPC endpoints cycled; sleeping 10s then one last attempt…")
        await asyncio.sleep(10)
        client = self.rpc
        if client is None:
            await self._reinit_rpc()
            client = self.rpc
        async with rpc_sema:
            return await getattr(client, method_name)(*args, **kwargs)

    # ---- Balance cache -----------------------------------------------------
    async def get_balance_cached(self, pubkey: Pubkey):
        """Return an object with .value like solana-py GetBalanceResp, using a short TTL cache."""
        now = time.time()
        key = str(pubkey)
        rec = self._bal_cache.get(key)
        if rec and (now - rec[1]) < BALANCE_TTL_SEC:
            class _Resp:
                def __init__(self, v): self.value = v
            return _Resp(rec[0])
        resp = await self._rpc_call("get_balance", pubkey)
        self._bal_cache[key] = (resp.value, now)
        return resp

    # ---- ATA helpers (token-specific & generic) ----------------------------
    def _ata_for(self, owner: Pubkey, mint: Pubkey) -> Pubkey:
        ata, _bump = Pubkey.find_program_address(
            [bytes(owner), bytes(TOKEN_PROGRAM_ID), bytes(mint)],
            ASSOCIATED_TOKEN_PROGRAM_ID
        )
        return ata

    async def ensure_ata(self, owner: Pubkey, payer_kp: Keypair) -> Pubkey:
        """Ensure ATA for your TARGET TOKEN mint only (MINT_PUB)."""
        ata = self._ata_for(owner, MINT_PUB)
        try:
            info = await self._rpc_call("get_account_info", ata)
            if hasattr(info, "value") and info.value is not None:
                return ata
        except Exception:
            pass

        accs = [
            AccountMeta(pubkey=payer_kp.pubkey(), is_signer=True,  is_writable=True),
            AccountMeta(pubkey=ata,               is_signer=False, is_writable=True),
            AccountMeta(pubkey=owner,             is_signer=False, is_writable=False),
            AccountMeta(pubkey=MINT_PUB,          is_signer=False, is_writable=False),
            AccountMeta(pubkey=SYS_PROGRAM_ID,    is_signer=False, is_writable=False),
            AccountMeta(pubkey=TOKEN_PROGRAM_ID,  is_signer=False, is_writable=False),
            AccountMeta(pubkey=RENT_SYSVAR_ID,    is_signer=False, is_writable=False),
        ]
        ix = Instruction(ASSOCIATED_TOKEN_PROGRAM_ID, b"", accs)
        tx = LegacyTransaction().add(ix)
        await self._rpc_call("send_transaction", tx, payer_kp,
                             opts=TxOpts(skip_preflight=True, skip_confirmation=True))
        return ata

    async def get_spl_ui_balance(self, owner: Pubkey) -> Tuple[float, int]:
        """Balance reader for your TARGET TOKEN (MINT_PUB)."""
        ata = self._ata_for(owner, MINT_PUB)
        try:
            res = await self._rpc_call("get_token_account_balance", ata)
        except Exception:
            return 0.0, 9
        if not hasattr(res, "value"):
            return 0.0, 9

        v = res.value
        ui = None
        dec = None
        for k in ("ui_amount", "ui_amount_string", "uiAmount", "uiAmountString"):
            if hasattr(v, k):
                val = getattr(v, k)
                try:
                    ui = float(val) if not isinstance(val, (int, float)) else float(val)
                except Exception:
                    pass
                break
        if hasattr(v, "decimals"):
            try:
                dec = int(getattr(v, "decimals"))
            except Exception:
                pass

        if ui is None and isinstance(v, dict):
            for k in ("uiAmount", "uiAmountString", "ui_amount", "ui_amount_string"):
                if k in v:
                    try:
                        ui = float(v[k])
                    except Exception:
                        pass
                    break
            if "decimals" in v and dec is None:
                try:
                    dec = int(v["decimals"])
                except Exception:
                    pass

        return (ui if ui is not None else 0.0), (dec if dec is not None else 9)

    # ---- Generic for any SPL mint (used for USDC) --------------------------
    def _ata_for_mint(self, owner: Pubkey, mint: Pubkey) -> Pubkey:
        ata, _ = Pubkey.find_program_address(
            [bytes(owner), bytes(TOKEN_PROGRAM_ID), bytes(mint)],
            ASSOCIATED_TOKEN_PROGRAM_ID
        )
        return ata

    async def ensure_ata_for_mint(self, owner: Pubkey, payer_kp: Keypair, mint: Pubkey) -> Pubkey:
        ata = self._ata_for_mint(owner, mint)
        try:
            info = await self._rpc_call("get_account_info", ata)
            if hasattr(info, "value") and info.value is not None:
                return ata
        except Exception:
            pass
        accs = [
            AccountMeta(pubkey=payer_kp.pubkey(), is_signer=True,  is_writable=True),
            AccountMeta(pubkey=ata,               is_signer=False, is_writable=True),
            AccountMeta(pubkey=owner,             is_signer=False, is_writable=False),
            AccountMeta(pubkey=mint,              is_signer=False, is_writable=False),
            AccountMeta(pubkey=SYS_PROGRAM_ID,    is_signer=False, is_writable=False),
            AccountMeta(pubkey=TOKEN_PROGRAM_ID,  is_signer=False, is_writable=False),
            AccountMeta(pubkey=RENT_SYSVAR_ID,    is_signer=False, is_writable=False),
        ]
        ix = Instruction(ASSOCIATED_TOKEN_PROGRAM_ID, b"", accs)
        tx = LegacyTransaction().add(ix)
        await self._rpc_call("send_transaction", tx, payer_kp,
                             opts=TxOpts(skip_preflight=True, skip_confirmation=True))
        return ata

    async def get_spl_ui_balance_for_mint(self, owner: Pubkey, mint: Pubkey) -> tuple[float,int]:
        ata = self._ata_for_mint(owner, mint)
        try:
            res = await self._rpc_call("get_token_account_balance", ata)
        except Exception:
            return 0.0, 6
        v = getattr(res, "value", None)
        if not v:
            return 0.0, 6
        try:
            dec = int(getattr(v, "decimals", 6))
        except Exception:
            dec = 6
        ui = None
        for k in ("ui_amount", "ui_amount_string", "uiAmount", "uiAmountString"):
            if hasattr(v, k):
                try:
                    ui = float(getattr(v, k)); break
                except Exception:
                    pass
        if ui is None and isinstance(v, dict):
            for k in ("uiAmount", "uiAmountString", "ui_amount", "ui_amount_string"):
                if k in v:
                    try: ui = float(v[k]); break
                    except Exception: pass
        return (ui if isinstance(ui,(int,float)) else 0.0), dec

    # ─── HTTP with backoff (Pump.fun) ──────────────────────────────────────
    async def _post_json(self, url: str, json_payload, max_backoff=20):
        back = 1
        while True:
            try:
                async with self.session.post(url, json=json_payload) as r:
                    if r.status in (429, 503):
                        print(f"⏳ {url} {r.status} → backoff {back}s")
                        await asyncio.sleep(back)
                        back = min(back * 2, max_backoff)
                        continue
                    r.raise_for_status()
                    return await r.json()
            except aiohttp.ClientError as e:
                print(f"⚠️ HTTP error {url}: {e} → backoff {back}s")
                await asyncio.sleep(back)
                back = min(back * 2, max_backoff)

    # ─── Trade & accounting (Pump.fun token) ───────────────────────────────
    async def _send_signed_bytes(self, kp: Keypair, tx_bytes: bytes):
        # Only send to RPC; no Jito submission.
        await self._rpc_call("send_raw_transaction", tx_bytes, opts=TxOpts(skip_preflight=True))

    async def _trade(self, kp: Keypair, side: str, amount_sol: float) -> bool:
        payload = {
            "publicKey": str(kp.pubkey()),
            "action": side,                    # "buy" or "sell"
            "mint": TOKEN_MINT,
            "amount": amount_sol,
            "denominatedInSol": "true",
            "slippage": self._slippage_bps()/100,
            "priorityFee": PRIORITY_FEE,
            "pool": "auto"
        }
        try:
            enc = await self._post_json(PUMP_API_URL, [payload])
            raw    = base58.b58decode(enc[0])
            signed = VersionedTransaction.from_bytes(raw)
            signed = VersionedTransaction(signed.message, [kp])
            txb    = bytes(signed)
            await self._send_signed_bytes(kp, txb)
            if side == "buy":
                BUY_COUNTER.inc()
            else:
                SELL_COUNTER.inc()
            return True
        except Exception as e:
            FAIL_COUNTER.inc()
            print(f"✖ {side} failed → {e}")
            log_trace(e)
            return False

    async def _post_buy(self, owner: Keypair, sol_spent: float):
        pub = str(owner.pubkey())
        before = self.token_cache.get(pub, 0.0)
        await asyncio.sleep(2.0)
        now_ui, _ = await self.get_spl_ui_balance(owner.pubkey())
        self.token_cache[pub] = now_ui
        delta = max(0.0, now_ui - before)
        if delta > 0:
            eff_px = sol_spent / delta
            new_total = self.total_tokens + delta
            if new_total > 0:
                self.avg_buy_price = (self.avg_buy_price * self.total_tokens + eff_px * delta) / new_total
            self.total_tokens = new_total
            self.lifetime_acquired += delta
            self.state.mark_dirty()

    async def _post_sell(self, owner: Keypair, sol_received: float) -> float:
        pub = str(owner.pubkey())
        before = self.token_cache.get(pub, 0.0)
        await asyncio.sleep(2.0)
        now_ui, _ = await self.get_spl_ui_balance(owner.pubkey())
        self.token_cache[pub] = now_ui
        sold_tokens = max(0.0, before - now_ui)
        if sold_tokens > 0 and self.avg_buy_price > 0:
            est_cost = sold_tokens * self.avg_buy_price
            profit   = max(0.0, sol_received - est_cost)
            skim     = profit * HOUSE_PROFIT_PCT
            self.total_tokens = max(0.0, self.total_tokens - sold_tokens)
            self.state.mark_dirty()
            return skim
        return 0.0

    # ─── House buybacks (TWAP from main wallet) ────────────────────────────
    async def maybe_house_buybacks(self):
        if self.house_bank_sol < HOUSE_MIN_BUY_SOL:
            return
        chunks = max(1, int(HOUSE_TWAP_CHUNKS))
        delay  = HOUSE_TWAP_DELAY_SEC

        try:
            p   = float(self.current_price) if self.current_price is not None else None
            peak= float(self.peak_price_seen) if self.peak_price_seen is not None else None
        except Exception:
            p, peak = None, None

        dd = 0.0
        if p and peak and peak > 0:
            dd = max(0.0, (peak - p) / peak)

        if p and self.avg_buy_price and p < self.avg_buy_price:
            chunks = max(chunks, int(HOUSE_TWAP_CHUNKS * DRAWDOWN_CHUNKS_MULT_1))
            delay  = max(DRAWDOWN_DELAY_MIN_SEC, delay)

        if dd >= DRAWDOWN_THRESH_2:
            chunks = max(chunks, int(HOUSE_TWAP_CHUNKS * DRAWDOWN_CHUNKS_MULT_2))
            delay  = max(DRAWDOWN_DELAY_MIN_SEC, delay // 2 if delay > 1 else 1)
        elif dd >= DRAWDOWN_THRESH_1:
            chunks = max(chunks, int(HOUSE_TWAP_CHUNKS * DRAWDOWN_CHUNKS_MULT_1))
            delay  = max(DRAWDOWN_DELAY_MIN_SEC, delay)

        per = self.house_bank_sol / float(chunks)
        print(f"🏠 House buybacks: {self.house_bank_sol:.6f} SOL → {chunks} chunks of {per:.6f} SOL (dd={dd:.1%}, delay={delay}s)")
        for _ in range(chunks):
            ok = await self._trade(self.main_kp, "buy", per)
            if ok:
                await self._post_buy(self.main_kp, per)
                if LOCK_DEST and LOCK_MODE == "transfer" and LOCK_PCT > 0:
                    print("ℹ️ LOCK_MODE=transfer configured; SPL transfer not wired in this file.")
            await asyncio.sleep(delay)

        self.house_bank_sol = 0.0
        HOUSE_BANK.set(0.0)
        self.state.mark_dirty()

    # ─── Budget helpers ────────────────────────────────────────────────────
    def _rollover_budget_if_new_day(self):
        today = time.gmtime().tm_yday
        if today != self.day_of_year:
            self.day_of_year = today
            self.spent_today = 0.0
            SPENT_TODAY.set(0.0)
            self.state.mark_dirty()

    async def buy_with_budget(self, kp: Keypair, sol_amt: float):
        self._rollover_budget_if_new_day()
        sol_amt = max(sol_amt, 0.0)
        if sol_amt < MIN_BUY_SOL:
            return False
        sol_amt = min(sol_amt, MAX_BUY_SOL)
        if self.spent_today + sol_amt > DAILY_SOL_BUDGET:
            return False
        ok = await self._trade(kp, "buy", sol_amt)
        if ok:
            self.spent_today += sol_amt
            SPENT_TODAY.set(self.spent_today)
            await self._post_buy(kp, sol_amt)
            self.state.mark_dirty()
        return ok

    # ─── Donation monitor: spawn new burners on deposits ───────────────────
    async def monitor_donations(self):
        resp = await self.get_balance_cached(self.main_kp.pubkey())
        self.last_main_bal = resp.value
        print(f"🔄 donations: initial main balance {self.last_main_bal/ LAMPORTS_PER_SOL:.6f} SOL")

        while self.running:
            resp = await self.get_balance_cached(self.main_kp.pubkey())
            bal  = resp.value
            donated_lam = bal - self.last_main_bal
            if donated_lam <= TX_FEE_BUFFER:
                await asyncio.sleep(DONATION_INTERVAL)
                continue

            donated_sol = donated_lam / LAMPORTS_PER_SOL
            if donated_sol < DONATION_THRESHOLD_SOL:
                await asyncio.sleep(DONATION_INTERVAL)
                continue

            # Calculate num_new based on donated / threshold
            num_new = int(donated_sol / DONATION_THRESHOLD_SOL)
            if num_new == 0:
                await asyncio.sleep(DONATION_INTERVAL)
                continue

            # Estimate total fees
            total_fees_estimate = num_new * TX_FEE_APPROX
            available_for_fund = donated_lam - total_fees_estimate
            if available_for_fund < num_new * int(DONATION_THRESHOLD_SOL * LAMPORTS_PER_SOL):
                num_new = max(1, available_for_fund // int(DONATION_THRESHOLD_SOL * LAMPORTS_PER_SOL))

            per_burner_lam = available_for_fund // num_new
            print(f"➕ donations: detected {donated_sol:.6f} SOL → {num_new} new burner(s) each with ~{per_burner_lam / LAMPORTS_PER_SOL:.6f} SOL")

            for i in range(num_new):
                try:
                    kp = Keypair()
                    # persist atomically
                    _atomic_update_wallets_log(bytes(kp))
                    # fund
                    amt = per_burner_lam
                    tx  = LegacyTransaction().add(
                        transfer(TransferParams(
                            from_pubkey=self.main_kp.pubkey(),
                            to_pubkey=kp.pubkey(),
                            lamports=amt)))
                    await self._rpc_call("send_transaction", tx, self.main_kp,
                                         opts=TxOpts(skip_preflight=False, skip_confirmation=False))  # Wait for confirmation

                    # ensure the burner has an ATA for this mint (payer = main wallet)
                    await self.ensure_ata(kp.pubkey(), self.main_kp)

                    # warm token cache
                    ui,_ = await self.get_spl_ui_balance(kp.pubkey())
                    self.token_cache[str(kp.pubkey())] = ui
                    # spawn
                    self.burners.append(kp)
                    task = asyncio.create_task(self.loop(kp))
                    self.dynamic_tasks.append(task)
                    print(f"➕ New burner {kp.pubkey()} created & started.")
                    await asyncio.sleep(1.0)  # Wait a bit for confirmation and next balance check
                except Exception as e:
                    print(f"✖ Failed to create burner: {e}")
                    log_trace(e)
                    continue

            # Reset last_main_bal to actual current balance after funding transfers
            await asyncio.sleep(2.0)  # Extra wait to ensure all txs confirmed
            resp = await self.get_balance_cached(self.main_kp.pubkey())
            self.last_main_bal = resp.value
            print(f"🔄 donations: reset main balance to {self.last_main_bal / LAMPORTS_PER_SOL:.6f} SOL after funding")
            self.state.mark_dirty()
            await asyncio.sleep(DONATION_INTERVAL)

    # ─── Core per-burner loop (Pump.fun token accumulation) ────────────────
    async def loop(self, kp: Keypair):
        pub = str(kp.pubkey())
        ui,_ = await self.get_spl_ui_balance(kp.pubkey())
        self.token_cache[pub] = ui

        while self.running:
            if time.time() - self.start_time > MAX_RUNTIME_SEC:
                print("⏸ cooldown…")
                await asyncio.sleep(COOLDOWN_PERIOD_SEC)
                self.start_time = time.time()

            with LOOP_TIME.time():
                self._update_state()

                resp = await self.get_balance_cached(kp.pubkey())
                sol_bal = resp.value / LAMPORTS_PER_SOL
                BANKROLL_GAUGE.set(sol_bal)
                if self.peak_bankroll is None or sol_bal > self.peak_bankroll:
                    self.peak_bankroll = sol_bal
                    PEAK_GAUGE.set(sol_bal)
                    self.state.mark_dirty()

                if self.in_burst:
                    sleep_lo, sleep_hi = BURST_DRIP_MIN_SEC, BURST_DRIP_MAX_SEC
                elif self.in_dip:
                    sleep_lo, sleep_hi = max(DRIP_MIN_SEC*1.5, DRIP_MIN_SEC), DRIP_MAX_SEC*1.6
                else:
                    sleep_lo, sleep_hi = DRIP_MIN_SEC, DRIP_MAX_SEC

                pct = random.uniform(PCT_MIN, PCT_MAX) / 100.0
                if self._in_antisnipe():
                    pct *= 0.6
                buy_sol = max(0.0, sol_bal * pct)
                if buy_sol >= MIN_BUY_SOL:
                    await self.buy_with_budget(kp, buy_sol)

                tokens_ui = self.token_cache.get(pub, 0.0)
                inv_value = (tokens_ui * self.current_price) if (self.current_price and tokens_ui) else 0.0
                vol_cap   = self.avg_volume * MAX_VOL_SELL_FRAC
                keep_min  = self.lifetime_acquired * MIN_HOLD_RATIO
                sell_ok   = (
                    self.current_price is not None and
                    self.avg_buy_price > 0 and
                    self.current_price >= self.avg_buy_price * (1.0 + SWING_PROFIT_TARGET) and
                    tokens_ui > 0.0 and
                    self.total_tokens > 0.0 and
                    not self._in_antisnipe() and
                    not self._vol_brake_active()
                )
                if sell_ok:
                    wanted_sol = inv_value * MAX_SELL_FRAC
                    wanted_sol = min(wanted_sol, vol_cap if vol_cap > 0 else wanted_sol)
                    if tokens_ui - (wanted_sol / max(1e-12, self.current_price)) < keep_min:
                        allowed_tokens = max(0.0, tokens_ui - keep_min)
                        wanted_sol = min(wanted_sol, allowed_tokens * self.current_price)

                    if wanted_sol >= 0.001:
                        ok = await self._trade(kp, "sell", wanted_sol)
                        if ok:
                            skim = await self._post_sell(kp, wanted_sol)
                            if skim > 0:
                                self.house_bank_sol += skim
                                HOUSE_BANK.set(self.house_bank_sol)
                                self.state.mark_dirty()

                await self.maybe_house_buybacks()

            await asyncio.sleep(random.uniform(sleep_lo, sleep_hi))

    # ─── WS consumer (reads from single PumpWS queue) ───────────────────────
    async def price_consumer(self):
        while self.running:
            raw = await self.ws_mgr.queue.get()
            try:
                data = json.loads(raw)
            except Exception:
                continue

            p = (
                data.get("price")
                or data.get("p")
                or (data.get("data", {}).get("price") if isinstance(data.get("data"), dict) else None)
            )
            v = (
                data.get("sol_amount")
                or data.get("amount")
                or data.get("v")
                or (data.get("data", {}).get("amount") if isinstance(data.get("data"), dict) else None)
            )
            if p is not None:
                try:
                    p = float(p)
                    self.current_price = p
                    PRICE_GAUGE.set(p)
                    if self.peak_price_seen is None or p > self.peak_price_seen:
                        self.peak_price_seen = p
                        self.state.mark_dirty()
                    nowt = time.time()
                    self.price_window.append((nowt, p))
                    cutoff = nowt - VOL_BRAKE_LOOKBACK_SEC
                    while self.price_window and self.price_window[0][0] < cutoff:
                        self.price_window.popleft()
                    if len(self.price_window) >= 2:
                        first = self.price_window[0][1]
                        last  = self.price_window[-1][1]
                        if first > 0:
                            move = abs(last - first) / first
                            if move >= VOL_BRAKE_PCT:
                                self.vol_brake_until = nowt + VOL_BRAKE_COOLDOWN_SEC
                                print(f"🧯 Volatility brake: {move:.1%} over {VOL_BRAKE_LOOKBACK_SEC}s → pause sells for {VOL_BRAKE_COOLDOWN_SEC}s")
                except Exception:
                    pass
            if v is not None:
                try:
                    v = float(v)
                    self.avg_volume = (1 - VOLUME_EMA_ALPHA) * self.avg_volume + VOLUME_EMA_ALPHA * v
                    VOL_GAUGE.set(self.avg_volume)
                except Exception:
                    pass

    # ─── State machine for burst/dip ───────────────────────────────────────
    def _update_state(self):
        now = asyncio.get_running_loop().time()
        if now >= self.state_ends:
            if self.in_burst:
                self.in_burst   = False
                self.in_dip     = True
                self.state_ends = now + random.uniform(DIP_DURATION_MIN, DIP_DURATION_MAX)
            elif self.in_dip:
                self.in_dip = False
                self.state_ends = now + random.uniform(DRIP_MIN_SEC, DRIP_MAX_SEC)
            else:
                if random.random() < BURST_PROB:
                    self.in_burst   = True
                    self.state_ends = now + random.uniform(BURST_DURATION_MIN, BURST_DURATION_MAX)
                else:
                    self.state_ends = now + random.uniform(DRIP_MIN_SEC, DRIP_MAX_SEC)

    # ─── Jupiter quote/swap + SOL swing engine (throttled) ─────────────────
    async def jup_quote(self, in_mint: str, out_mint: str, amount_base_units: int, slippage_bps: int | None = None):
        # Global cooldown after repeated 429s
        now = time.time()
        if now < self._jup_cooldown_until:
            raise aiohttp.ClientResponseError(None, (), status=429, message="global-cooldown")

        params = {
            "inputMint": in_mint,
            "outputMint": out_mint,
            "amount": str(int(amount_base_units)),
            "onlyDirectRoutes": "false",
            "asLegacyTransaction": "false",
            "slippageBps": str(int(slippage_bps if slippage_bps is not None else self._slippage_bps()))
        }

        base = 0.35
        for attempt in range(JUP_MAX_RETRIES):
            await self.jup_rl.acquire()
            try:
                timeout = aiohttp.ClientTimeout(total=10)
                async with self.session.get(JUP_QUOTE_URL, params=params, timeout=timeout) as r:
                    if r.status == 429:
                        self._jup_429s_row += 1
                        retry_after = r.headers.get("Retry-After")
                        if retry_after:
                            try:
                                ra = float(retry_after)
                            except:
                                ra = 1.5
                        else:
                            ra = min(5.0, base * (2 ** attempt)) * (1.0 + _rand.random()*0.5)
                        if self._jup_429s_row >= 3:
                            self._jup_cooldown_until = time.time() + JUP_429_COOLDOWN_SEC
                            self._jup_429s_row = 0
                        await asyncio.sleep(ra)
                        continue

                    r.raise_for_status()
                    self._jup_429s_row = 0
                    return await r.json()

            except (aiohttp.ClientError, asyncio.TimeoutError):
                await asyncio.sleep(min(3.0, base * (2 ** attempt)) * (1.0 + _rand.random()*0.5))

        raise RuntimeError("Jupiter quote failed after retries")

    async def jup_swap(self, kp: Keypair, quote_resp: dict) -> bool:
        payload = {
            "userPublicKey": str(kp.pubkey()),
            "wrapAndUnwrapSol": True,
            "useTokenLedger": False,
            "quoteResponse": quote_resp,
            "asLegacyTransaction": False
        }
        async with self.session.post(JUP_SWAP_URL, json=payload) as r:
            r.raise_for_status()
            data = await r.json()
        tx_b64 = data.get("swapTransaction")
        if not tx_b64:
            raise RuntimeError(f"Jupiter swap error: {data}")
        raw = base64.b64decode(tx_b64)
        tx  = VersionedTransaction.from_bytes(raw)
        signed = VersionedTransaction(tx.message, [kp])
        await self._send_signed_bytes(kp, bytes(signed))
        return True

    async def get_sol_usdc_price(self, poll_amount_sol: float = 1.0) -> float | None:
        """
        Cached price of SOL in USDC ui units. Uses TTL to avoid hammering Jupiter.
        """
        now = time.time()
        if self._last_px is not None and (now - self._last_px_ts) < JUP_PRICE_TTL_SEC:
            return self._last_px

        lamports = int(max(1, poll_amount_sol * LAMPORTS_PER_SOL))
        try:
            q = await self.jup_quote(SOL_MINT_STR, USDC_MINT_STR, lamports)
            out_amt = float(q.get("outAmount", 0)) / (10**6)  # USDC 6 decimals
            px = out_amt / (lamports / LAMPORTS_PER_SOL)
            if px > 0 and isfinite(px):
                self._last_px, self._last_px_ts = px, now
                return px
        except Exception as e:
            if self._last_px is not None:
                return self._last_px
            print(f"⚠️ SOL price quote failed (no cache): {e}")
        return None

    async def _transfer_sol(self, from_kp: Keypair, to_pub: Pubkey, lamports: int) -> bool:
        try:
            if lamports <= TX_FEE_BUFFER:
                return False
            tx = LegacyTransaction().add(
                transfer(TransferParams(
                    from_pubkey=from_kp.pubkey(),
                    to_pubkey=to_pub,
                    lamports=lamports
                ))
            )
            await self._rpc_call("send_transaction", tx, from_kp,
                                 opts=TxOpts(skip_preflight=True, skip_confirmation=True))
            return True
        except Exception as e:
            print(f"✖ transfer failed: {e}")
            return False

    async def sol_swing_loop(self, kp: Keypair):
        """
        Simple pivot-based rotation:
          • Hold SOL by default.
          • If price falls ≥ DROP_PCT from pivot → rotate SOL→USDC.
          • If price rises ≥ RISE_PCT from pivot → rotate USDC→SOL.
        On USDC→SOL rotations that increase SOL qty, skim HOUSE_PROFIT_PCT:
          • If BURNER_SELF_BUYBACKS = True  → TWAP buybacks from this burner
          • Else                            → transfer skim SOL to main (centralized TWAP)
        """
        pub = str(kp.pubkey())
        last_side = "SOL"   # "SOL" or "USDC"
        last_pivot_px = None
        last_rotation_ts = 0.0

        # Ensure USDC ATA exists
        try:
            await self.ensure_ata_for_mint(kp.pubkey(), self.main_kp, USDC_MINT)
        except Exception as e:
            print(f"⚠️ ensure USDC ATA for {pub} failed: {e}")

        # Track SOL units after each rotation for PnL
        resp = await self.get_balance_cached(kp.pubkey())
        last_sol_units = resp.value / LAMPORTS_PER_SOL

        while self.running and ENABLE_SOL_SWINGS:
            # cadence gate for rotations
            now = time.time()
            if now - last_rotation_ts < SOL_SWING_MIN_INTERVAL:
                await asyncio.sleep(0.5)
                continue

            # TTL-cached price to avoid hammering quotes
            px = await self.get_sol_usdc_price(1.0)
            if px is None:
                await asyncio.sleep(2.0)
                continue

            if last_pivot_px is None:
                last_pivot_px = px

            # current balances
            sol_lamports = (await self.get_balance_cached(kp.pubkey())).value
            sol_ui       = sol_lamports / LAMPORTS_PER_SOL
            usdc_ui, _   = await self.get_spl_ui_balance_for_mint(kp.pubkey(), USDC_MINT)

            if last_side == "SOL":
                drop = (last_pivot_px - px) / last_pivot_px if last_pivot_px > 0 else 0.0
                if drop >= SOL_SWING_DROP_PCT:
                    amt_ui = max(0.0, sol_ui * SOL_SWING_ALLOC_FRAC - (TX_FEE_BUFFER / LAMPORTS_PER_SOL))
                    if amt_ui >= 0.001:
                        try:
                            q = await self.jup_quote(SOL_MINT_STR, USDC_MINT_STR, int(amt_ui * LAMPORTS_PER_SOL), self._slippage_bps())
                            ok = await self.jup_swap(kp, q)
                        except Exception as e:
                            print(f"✖ SOL→USDC swap failed: {e}")
                            ok = False
                        if ok:
                            last_side = "USDC"
                            last_pivot_px = px
                            last_rotation_ts = time.time()
                            sol_lamports = (await self.get_balance_cached(kp.pubkey())).value
                            last_sol_units = sol_lamports / LAMPORTS_PER_SOL
                            print(f"🔄 {pub[:6]}… SOL→USDC @ {px:.2f}")
            else:
                rise = (px - last_pivot_px) / last_pivot_px if last_pivot_px > 0 else 0.0
                if rise >= SOL_SWING_RISE_PCT and usdc_ui > 0:
                    try:
                        q = await self.jup_quote(USDC_MINT_STR, SOL_MINT_STR, int(usdc_ui * (10**6)), self._slippage_bps())
                        ok = await self.jup_swap(kp, q)
                    except Exception as e:
                        print(f"✖ USDC→SOL swap failed: {e}")
                        ok = False
                    if ok:
                        last_side = "SOL"
                        last_rotation_ts = time.time()
                        new_sol = (await self.get_balance_cached(kp.pubkey())).value / LAMPORTS_PER_SOL
                        profit_sol = max(0.0, new_sol - last_sol_units)
                        last_sol_units = new_sol
                        last_pivot_px = px
                        print(f"🔄 {pub[:6]}… USDC→SOL @ {px:.2f} (ΔSOL ≈ {profit_sol:.6f})")

                        if profit_sol > 0:
                            skim = profit_sol * HOUSE_PROFIT_PCT
                            if skim >= SOL_SWING_MIN_SKIM_SOL:
                                if BURNER_SELF_BUYBACKS:
                                    # Per-burner TWAP buybacks executed directly from this burner
                                    chunks = max(1, int(HOUSE_TWAP_CHUNKS))
                                    per = skim / float(chunks)
                                    print(f"🧯 Burner self-buybacks: {skim:.6f} SOL → {chunks} chunks of {per:.6f} SOL")
                                    for _ in range(chunks):
                                        ok2 = await self._trade(kp, "buy", per)
                                        if ok2:
                                            await self._post_buy(kp, per)
                                        await asyncio.sleep(HOUSE_TWAP_DELAY_SEC)
                                else:
                                    # Centralized path: send skim to main and let house TWAP later
                                    lam = int(skim * LAMPORTS_PER_SOL)
                                    sent = await self._transfer_sol(kp, self.main_kp.pubkey(), lam)
                                    if sent:
                                        self.house_bank_sol += skim
                                        HOUSE_BANK.set(self.house_bank_sol)
                                        self.state.mark_dirty()
                                        print(f"🏠 Skimmed {skim:.6f} SOL to main for buybacks.")

                        # If centralized, try house buybacks now; self-buybacks already executed above
                        if not BURNER_SELF_BUYBACKS:
                            await self.maybe_house_buybacks()

            await asyncio.sleep(2.0)

    # ─── Run ───────────────────────────────────────────────────────────────
    async def run(self):
        self.session = aiohttp.ClientSession(
            headers={"User-Agent": JUP_USER_AGENT}
        )

        # Load persisted state (if any)
        await self.state.load()

        # main wallet SOL
        resp = await self.get_balance_cached(self.main_kp.pubkey())
        print(f"🔑 Main wallet SOL: {resp.value / LAMPORTS_PER_SOL:.6f}")

        # Ensure main wallet ATA exists (TARGET TOKEN)
        await self.ensure_ata(self.main_kp.pubkey(), self.main_kp)

        # Ensure USDC ATA for main (and optionally burners) for swing engine
        if ENABLE_SOL_SWINGS:
            try:
                await self.ensure_ata_for_mint(self.main_kp.pubkey(), self.main_kp, USDC_MINT)
            except Exception as e:
                print(f"⚠️ ensure USDC ATA for main failed: {e}")
            if SWING_ON_BURNERS:
                for kp in self.burners:
                    try:
                        await self.ensure_ata_for_mint(kp.pubkey(), self.main_kp, USDC_MINT)
                    except Exception as e:
                        print(f"⚠️ ensure USDC ATA for burner {kp.pubkey()} failed: {e}")

        # warm main token cache
        ui,_ = await self.get_spl_ui_balance(self.main_kp.pubkey())
        self.token_cache[str(self.main_kp.pubkey())] = ui

        # Reconcile live balances for all holders (main + burners)
        pubs = [self.main_kp.pubkey()] + [kp.pubkey() for kp in self.burners]
        live_total = 0.0
        for p in pubs:
            u,_ = await self.get_spl_ui_balance(p)
            self.token_cache[str(p)] = u
            live_total += u
        if RECOVER_ON_BOOT:
            self.total_tokens = live_total  # use live on-chain sum

        # Ensure daily budget respects day change since last run
        self._rollover_budget_if_new_day()

        # Single persistent WS socket for token price/volume
        self.ws_mgr = PumpWS(WS_URI)
        await self.ws_mgr.start()
        await self.ws_mgr.subscribe(TOKEN_MINT)

        tasks = [asyncio.create_task(self.price_consumer(), name="price_consumer")]
        for kp in self.burners:
            tasks.append(asyncio.create_task(self.loop(kp)))
        tasks.append(asyncio.create_task(self.monitor_donations()))
        tasks.append(asyncio.create_task(self.state.checkpoint_loop(), name="checkpoint"))

        # NEW: start SOL swing loops
        if ENABLE_SOL_SWINGS:
            if SWING_ON_MAIN:
                tasks.append(asyncio.create_task(self.sol_swing_loop(self.main_kp), name="sol_swing_main"))
            if SWING_ON_BURNERS:
                for i, kp in enumerate(self.burners):
                    tasks.append(asyncio.create_task(self.sol_swing_loop(kp), name=f"sol_swing_burner_{i}"))

        print("> Booster with crash-safe state + SOL↔USDC swing engine running…")
        try:
            await asyncio.gather(*tasks)
        finally:
            self.running = False
            for t in tasks + self.dynamic_tasks:
                t.cancel()
            try:
                await self.ws_mgr.stop()
            except Exception:
                pass
            # Force final checkpoint
            try:
                await self.state.save_now()
            except Exception:
                pass
            try:
                await self.session.close()
            except Exception:
                pass
            try:
                await self.rpc.close()
            except Exception:
                pass

def main():
    start_http_server(8000)
    print("📊 Metrics at http://localhost:8000/metrics (localhost only)")
    bot = Booster()
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    try:
        loop.add_signal_handler(signal.SIGINT,  setattr, bot, "running", False)
        loop.add_signal_handler(signal.SIGTERM, setattr, bot, "running", False)
    except NotImplementedError:
        pass
    loop.run_until_complete(bot.run())
    loop.close()

if __name__ == "__main__":
    main()