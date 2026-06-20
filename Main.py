#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Telegram Guarantee Bot (ESCROW) - Безопасная версия
TON + USDT. Комиссия только на депозиты (2% сверху).
ПОЛНАЯ ВЕРСИЯ — Только русский — Асинхронная архитектура.
"""

import asyncio
import atexit
import hashlib
import hmac
import json
import logging
import logging.handlers
import os
import re
import signal
import sqlite3
import sys
import tempfile
import time
import uuid
from datetime import datetime, timedelta
from typing import Optional, Tuple, Dict, List, Any
from contextlib import asynccontextmanager

from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import Application, CommandHandler, MessageHandler, filters, CallbackQueryHandler, ContextTypes
from telegram.request import HTTPXRequest
from telegram.error import Conflict, BadRequest, Forbidden

# TON
try:
    from pytoniq import LiteBalancer, WalletV4R2
    from pytoniq_core import Address, begin_cell
    HAS_PYTONIQ = True
except ImportError:
    HAS_PYTONIQ = False
    LiteBalancer = None
    WalletV4R2 = None
    Address = None
    begin_cell = None

try:
    import aiohttp
    HAS_AIOHTTP = True
except ImportError:
    HAS_AIOHTTP = False

try:
    import filelock
    HAS_FILELOCK = True
except ImportError:
    HAS_FILELOCK = False
    filelock = None

try:
    from dotenv import load_dotenv
    load_dotenv()
except:
    pass

# ========== ПЕРЕМЕННЫЕ ОКРУЖЕНИЯ ==========
BOT_TOKEN = os.getenv("BOT_TOKEN")
BOT_USERNAME = os.getenv("BOT_USERNAME")
ADMIN_IDS_RAW = os.getenv("ADMIN_IDS")
ADMIN_IDS = {int(x.strip()) for x in ADMIN_IDS_RAW.split(",") if x.strip()} if ADMIN_IDS_RAW else set()
SUPPORT_USERNAME = os.getenv("SUPPORT_USERNAME", "").lstrip("@")
TON_DEPOSIT_ADDRESS = os.getenv("TON_DEPOSIT_ADDRESS")
TON_API_KEY = os.getenv("TON_API_KEY")
BOT_WALLET_MNEMONIC = os.getenv("BOT_WALLET_MNEMONIC")
TON_NETWORK = os.getenv("TON_NETWORK", "mainnet").lower()
TON_MAINNET = TON_NETWORK == "mainnet"
DEPOSIT_COMMISSION_PERCENT = int(os.getenv("DEPOSIT_COMMISSION", "2"))
SECRET_KEY = os.getenv("SECRET_KEY", hashlib.sha256(os.urandom(32)).hexdigest())
USDT_JETTON_MASTER = os.getenv("USDT_JETTON_ADDRESS", "EQCxE6mUtQJKFnGfaROTKOt1lZbDiiX1kCixRv7Nw2Id_sDs")

# ========== ПУТИ ==========
PROJECT_DIR = os.path.dirname(os.path.abspath(__file__))
LOGS_DIR = os.path.join(PROJECT_DIR, "logs")
os.makedirs(LOGS_DIR, exist_ok=True)
DB_PATH = os.path.join(LOGS_DIR, "bot_data.db")
LOCK_FILE = os.path.join(LOGS_DIR, "bot.lock")

# ========== КОНСТАНТЫ ==========
NANO_TON = 1_000_000_000
USDT_DECIMALS = 6

MIN_DEAL_TON = 0.5
MAX_DEAL_TON = 1_000_000.0
MIN_DEAL_USDT = 0.5
MAX_DEAL_USDT = 1_000_000.0

MIN_DEPOSIT_TON = 0.5
MIN_DEPOSIT_USDT = 0.5

MIN_WITHDRAW_TON = 0.5
MIN_WITHDRAW_USDT = 0.5

DEAL_TIMEOUT_MIN = 1440
DEAL_DISPUTE_AUTO_TIMEOUT_HOURS = 48
DEAL_SELLER_SENT_TIMEOUT_HOURS = 48
DEAL_TIMEOUT_CHECK_INTERVAL_SEC = 60

PAYOUT_JETTON_GAS_TON = 0.05
PAYOUT_TON_GAS_RESERVE = 0.2
DAILY_WITHDRAW_CAP_TON = 1000.0
DAILY_WITHDRAW_CAP_USDT = 5000.0

TON_POLL_INTERVAL_SEC = 15
TON_POLL_LIMIT = 20

PRICE_CACHE_TTL_SEC = 300
RETRY_DELAYS = [0, 5, 15, 45, 120, 300]

# ========== ГЛОБАЛЬНОЕ СОСТОЯНИЕ ==========
user_data: Dict[int, dict] = {}
deals: Dict[str, dict] = {}
_LAST_LT = 0
_LAST_LT_LOADED = False
_LT_LOCK = asyncio.Lock()
_shutdown_flag = False
_bot_start_time = datetime.now()
_session: Optional[aiohttp.ClientSession] = None

# Блокировки для атомарных операций
_balance_locks: Dict[int, asyncio.Lock] = {}
_deal_locks: Dict[str, asyncio.Lock] = {}
_withdraw_locks: Dict[int, asyncio.Lock] = {}
_db_semaphore = asyncio.Semaphore(1)

# ========== ЛОГИРОВАНИЕ ==========
class SensitiveDataFilter(logging.Filter):
    def filter(self, record):
        msg = record.getMessage()
        sensitive = [BOT_WALLET_MNEMONIC, BOT_TOKEN, TON_API_KEY, SECRET_KEY]
        for s in sensitive:
            if s and s in msg:
                record.msg = msg.replace(s, "***СКРЫТО***")
                record.args = ()
        return True

log_handler = logging.handlers.TimedRotatingFileHandler(
    os.path.join(LOGS_DIR, "bot.log"),
    when="midnight", interval=1, backupCount=30, encoding="utf-8"
)
log_handler.setFormatter(logging.Formatter('%(asctime)s - %(levelname)s - %(message)s'))
log_handler.addFilter(SensitiveDataFilter())

stream_handler = logging.StreamHandler()
stream_handler.setFormatter(logging.Formatter('%(asctime)s - %(levelname)s - %(message)s'))
stream_handler.addFilter(SensitiveDataFilter())

logging.basicConfig(level=logging.INFO, handlers=[log_handler, stream_handler])
logger = logging.getLogger(__name__)

payment_logger = logging.getLogger("payments")
payment_handler = logging.handlers.RotatingFileHandler(
    os.path.join(LOGS_DIR, "payments.log"),
    maxBytes=10_000_000, backupCount=10, encoding="utf-8"
)
payment_handler.setFormatter(logging.Formatter('%(asctime)s - %(message)s'))
payment_logger.addHandler(payment_handler)
payment_logger.setLevel(logging.INFO)

# ========== БЛОКИРОВКА ОДНОГО ЭКЗЕМПЛЯРА ==========
_lock_file_handle = None

def acquire_lock():
    global _lock_file_handle
    try:
        os.makedirs(LOGS_DIR, exist_ok=True)
        if sys.platform == "win32":
            import msvcrt
            fd = os.open(LOCK_FILE, os.O_CREAT | os.O_RDWR)
            try:
                msvcrt.locking(fd, msvcrt.LK_NBLCK, 1)
                _lock_file_handle = fd
                return True
            except:
                os.close(fd)
                return False
        else:
            import fcntl
            fd = os.open(LOCK_FILE, os.O_CREAT | os.O_RDWR)
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                _lock_file_handle = fd
                return True
            except:
                os.close(fd)
                return False
    except:
        return False

def release_lock():
    global _lock_file_handle
    try:
        if _lock_file_handle is not None:
            if sys.platform == "win32":
                import msvcrt
                msvcrt.locking(_lock_file_handle, msvcrt.LK_UNLCK, 1)
            else:
                import fcntl
                fcntl.flock(_lock_file_handle, fcntl.LOCK_UN)
            os.close(_lock_file_handle)
            _lock_file_handle = None
        if os.path.isfile(LOCK_FILE):
            os.remove(LOCK_FILE)
    except:
        pass

# ========== БАЗА ДАННЫХ С ТРАНЗАКЦИЯМИ ==========
@asynccontextmanager
async def db_transaction():
    """Асинхронный контекст для транзакций с повторными попытками при блокировке"""
    async with _db_semaphore:
        conn = None
        for attempt in range(5):
            try:
                conn = sqlite3.connect(DB_PATH, timeout=30, check_same_thread=False)
                conn.execute("PRAGMA busy_timeout=5000")
                conn.execute("PRAGMA foreign_keys=ON")
                conn.execute("PRAGMA journal_mode=WAL")
                conn.execute("PRAGMA synchronous=NORMAL")
                conn.execute("BEGIN IMMEDIATE")
                yield conn
                conn.commit()
                return
            except sqlite3.OperationalError as e:
                if conn:
                    try:
                        conn.rollback()
                    except:
                        pass
                if "locked" in str(e).lower() and attempt < 4:
                    await asyncio.sleep(0.05 * (2 ** attempt))
                    continue
                raise
            except Exception:
                if conn:
                    try:
                        conn.rollback()
                    except:
                        pass
                raise
            finally:
                if conn:
                    try:
                        conn.close()
                    except:
                        pass

def db_connect():
    conn = sqlite3.connect(DB_PATH, timeout=30, check_same_thread=False)
    conn.execute("PRAGMA busy_timeout=30000")
    conn.execute("PRAGMA foreign_keys=ON")
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=NORMAL")
    return conn

def init_db():
    with db_connect() as conn:
        conn.executescript('''
            CREATE TABLE IF NOT EXISTS users (
                user_id INTEGER PRIMARY KEY,
                ton_address TEXT,
                balance_currencies TEXT DEFAULT '{}',
                successful_deals INTEGER DEFAULT 0,
                lang TEXT DEFAULT 'ru',
                likes INTEGER DEFAULT 0,
                dislikes INTEGER DEFAULT 0,
                registered_at INTEGER,
                total_volume_usd REAL DEFAULT 0
            );
            
            CREATE TABLE IF NOT EXISTS deals (
                deal_id TEXT PRIMARY KEY,
                amount REAL,
                description TEXT,
                seller_id INTEGER,
                buyer_id INTEGER,
                status TEXT,
                currency TEXT,
                created_at TEXT,
                escrow_collected INTEGER DEFAULT 0,
                seller_voted INTEGER DEFAULT 0,
                buyer_voted INTEGER DEFAULT 0,
                join_notification_sent INTEGER DEFAULT 0,
                completed_at INTEGER,
                version INTEGER DEFAULT 1
            );
            
            CREATE TABLE IF NOT EXISTS deposits (
                tx_hash TEXT PRIMARY KEY,
                user_id INTEGER,
                currency TEXT,
                amount REAL,
                commission REAL DEFAULT 0,
                net_amount REAL DEFAULT 0,
                created_at INTEGER,
                status TEXT DEFAULT 'completed',
                processed_at INTEGER
            );
            
            CREATE TABLE IF NOT EXISTS pending_transactions (
                tx_hash TEXT PRIMARY KEY,
                user_id INTEGER,
                currency TEXT,
                amount REAL,
                created_at INTEGER,
                status TEXT DEFAULT 'pending'
            );
            
            CREATE TABLE IF NOT EXISTS withdrawals (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                currency TEXT,
                amount REAL,
                address TEXT,
                status TEXT DEFAULT 'pending',
                created_at INTEGER,
                processed_at INTEGER,
                tx_hash TEXT,
                error TEXT,
                broadcast_at INTEGER,
                retry_count INTEGER DEFAULT 0,
                idempotency_key TEXT UNIQUE
            );
            
            CREATE TABLE IF NOT EXISTS bot_settings (
                key TEXT PRIMARY KEY,
                value TEXT
            );
            
            CREATE TABLE IF NOT EXISTS workers (
                user_id INTEGER PRIMARY KEY
            );
            
            CREATE TABLE IF NOT EXISTS balance_audit (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                currency TEXT,
                amount REAL,
                operation TEXT,
                reference TEXT,
                created_at INTEGER,
                balance_after REAL
            );
            
            CREATE INDEX IF NOT EXISTS idx_deals_seller ON deals(seller_id);
            CREATE INDEX IF NOT EXISTS idx_deals_buyer ON deals(buyer_id);
            CREATE INDEX IF NOT EXISTS idx_deals_status ON deals(status);
            CREATE INDEX IF NOT EXISTS idx_withdrawals_user ON withdrawals(user_id);
            CREATE INDEX IF NOT EXISTS idx_withdrawals_status ON withdrawals(status);
            CREATE INDEX IF NOT EXISTS idx_withdrawals_pending ON withdrawals(user_id, status, created_at);
            CREATE INDEX IF NOT EXISTS idx_withdrawals_idem ON withdrawals(idempotency_key);
            CREATE INDEX IF NOT EXISTS idx_deposits_user ON deposits(user_id);
            CREATE INDEX IF NOT EXISTS idx_pending_user ON pending_transactions(user_id, status);
            CREATE INDEX IF NOT EXISTS idx_audit_user ON balance_audit(user_id, created_at);
            CREATE INDEX IF NOT EXISTS idx_audit_ref ON balance_audit(reference);
        ''')
        
        # Миграции
        migrations = [
            "ALTER TABLE withdrawals ADD COLUMN idempotency_key TEXT",
            "ALTER TABLE deals ADD COLUMN version INTEGER DEFAULT 1",
            "ALTER TABLE deposits ADD COLUMN processed_at INTEGER",
        ]
        for m in migrations:
            try:
                conn.execute(m)
            except sqlite3.OperationalError:
                pass
    
    logger.info("База данных инициализирована")

def load_data():
    global user_data, deals
    user_data.clear()
    deals.clear()
    
    with db_connect() as conn:
        cur = conn.execute("SELECT user_id, ton_address, balance_currencies, successful_deals, lang, likes, dislikes, registered_at, total_volume_usd FROM users")
        for row in cur.fetchall():
            uid, addr, bc_json, cnt, lang, likes, dislikes, reg, volume = row
            try:
                bc = json.loads(bc_json) if bc_json else {}
            except:
                bc = {"TON": 0.0, "USDT": 0.0}
            user_data[uid] = {
                "ton_address": addr or "",
                "balance_currencies": bc,
                "successful_deals": cnt or 0,
                "lang": "ru",
                "likes": likes or 0,
                "dislikes": dislikes or 0,
                "registered_at": reg or int(time.time()),
                "total_volume_usd": volume or 0.0
            }
        
        cur = conn.execute("SELECT deal_id, amount, description, seller_id, buyer_id, status, currency, created_at, escrow_collected, seller_voted, buyer_voted, join_notification_sent, completed_at FROM deals")
        for row in cur.fetchall():
            did, amt, desc, seller, buyer, status, cur, created, escrow, sv, bv, join_sent, completed_at = row
            deals[did] = {
                "amount": amt, "description": desc,
                "seller_id": seller, "buyer_id": buyer,
                "status": status, "currency": cur,
                "created_at": created,
                "escrow_collected": bool(escrow),
                "seller_voted": bool(sv),
                "buyer_voted": bool(bv),
                "join_notification_sent": bool(join_sent),
                "completed_at": completed_at
            }
    
    logger.info(f"Загружено {len(user_data)} пользователей, {len(deals)} сделок")

def save_user(uid: int):
    u = user_data.get(uid, {})
    with db_connect() as conn:
        conn.execute(
            "INSERT OR REPLACE INTO users (user_id, ton_address, balance_currencies, successful_deals, lang, likes, dislikes, registered_at, total_volume_usd) VALUES (?,?,?,?,?,?,?,?,?)",
            (uid, u.get("ton_address", ""), json.dumps(u.get("balance_currencies", {})), u.get("successful_deals", 0), "ru", u.get("likes", 0), u.get("dislikes", 0), u.get("registered_at", int(time.time())), u.get("total_volume_usd", 0.0))
        )

def save_deal(did: str):
    d = deals.get(did, {})
    with db_connect() as conn:
        conn.execute(
            "INSERT OR REPLACE INTO deals (deal_id, amount, description, seller_id, buyer_id, status, currency, created_at, escrow_collected, seller_voted, buyer_voted, join_notification_sent, completed_at) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?)",
            (did, d.get("amount"), d.get("description"), d.get("seller_id"), d.get("buyer_id"), d.get("status"), d.get("currency"), d.get("created_at"), 1 if d.get("escrow_collected") else 0, 1 if d.get("seller_voted") else 0, 1 if d.get("buyer_voted") else 0, 1 if d.get("join_notification_sent") else 0, d.get("completed_at"))
        )

# ========== АУДИТ БАЛАНСА ==========
def audit_balance(uid: int, currency: str, amount: float, operation: str, reference: str, balance_after: float):
    try:
        with db_connect() as conn:
            conn.execute(
                "INSERT INTO balance_audit (user_id, currency, amount, operation, reference, created_at, balance_after) VALUES (?,?,?,?,?,?,?)",
                (uid, currency, amount, operation, reference, int(time.time()), balance_after)
            )
    except Exception as e:
        logger.error(f"Ошибка аудита баланса: {e}")

# ========== АТОМАРНЫЕ ОПЕРАЦИИ БАЛАНСА ==========
def ensure_user(uid: int):
    if uid not in user_data:
        user_data[uid] = {
            "ton_address": "",
            "balance_currencies": {"TON": 0.0, "USDT": 0.0},
            "successful_deals": 0, "lang": "ru",
            "likes": 0, "dislikes": 0,
            "registered_at": int(time.time()),
            "total_volume_usd": 0.0
        }
        save_user(uid)

def get_balance(uid: int, currency: str) -> float:
    ensure_user(uid)
    return float(user_data[uid].get("balance_currencies", {}).get(currency, 0.0))

def add_balance(uid: int, currency: str, amount: float, operation: str = "deposit", reference: str = "") -> bool:
    if amount <= 0:
        return False
    ensure_user(uid)
    cur = user_data[uid].setdefault("balance_currencies", {})
    old = cur.get(currency, 0.0)
    new = old + amount
    cur[currency] = new
    save_user(uid)
    audit_balance(uid, currency, amount, operation, reference or f"add_{int(time.time())}", new)
    return True

def sub_balance(uid: int, currency: str, amount: float, operation: str = "withdraw", reference: str = "") -> bool:
    if amount <= 0:
        return False
    ensure_user(uid)
    cur = user_data[uid].get("balance_currencies", {})
    bal = cur.get(currency, 0.0)
    if bal < amount - 1e-9:
        return False
    new = bal - amount
    user_data[uid]["balance_currencies"][currency] = new
    save_user(uid)
    audit_balance(uid, currency, -amount, operation, reference or f"sub_{int(time.time())}", new)
    return True

def get_ton_address(uid: int) -> str:
    ensure_user(uid)
    return user_data[uid].get("ton_address", "")

def set_ton_address(uid: int, addr: str):
    ensure_user(uid)
    user_data[uid]["ton_address"] = addr
    save_user(uid)

def add_successful_deal(uid: int):
    ensure_user(uid)
    user_data[uid]["successful_deals"] = user_data[uid].get("successful_deals", 0) + 1
    save_user(uid)

def add_rating(uid: int, is_like: bool):
    ensure_user(uid)
    if is_like:
        user_data[uid]["likes"] = user_data[uid].get("likes", 0) + 1
    else:
        user_data[uid]["dislikes"] = user_data[uid].get("dislikes", 0) + 1
    save_user(uid)

def is_worker(uid: int) -> bool:
    try:
        with db_connect() as conn:
            return conn.execute("SELECT 1 FROM workers WHERE user_id = ?", (uid,)).fetchone() is not None
    except:
        return False

# ========== ДЕПОЗИТЫ С ЗАЩИТОЙ ОТ ПОВТОРОВ ==========
def deposit_exists(tx_hash: str) -> bool:
    with db_connect() as conn:
        return conn.execute("SELECT 1 FROM deposits WHERE tx_hash = ?", (tx_hash,)).fetchone() is not None

def calculate_deposit_amount(desired_amount: float) -> Tuple[float, float]:
    commission = desired_amount * DEPOSIT_COMMISSION_PERCENT / 100
    return desired_amount + commission, commission

async def record_deposit_safe(tx_hash: str, uid: int, currency: str, send_amount: float, commission: float, net_amount: float) -> bool:
    """Запись депозита с транзакционной защитой от двойного зачисления"""
    async with _balance_locks.setdefault(uid, asyncio.Lock()):
        try:
            async with db_transaction() as conn:
                # Проверка идемпотентности
                if conn.execute("SELECT 1 FROM deposits WHERE tx_hash = ?", (tx_hash,)).fetchone():
                    logger.warning(f"Депозит уже существует: {tx_hash}")
                    return False
                
                # Запись депозита
                conn.execute(
                    "INSERT INTO deposits (tx_hash, user_id, currency, amount, commission, net_amount, created_at, status, processed_at) VALUES (?,?,?,?,?,?,?,?,?)",
                    (tx_hash, uid, currency, send_amount, commission, net_amount, int(time.time()), "completed", int(time.time()))
                )
                
                # Обновление баланса
                ensure_user(uid)
                cur = user_data[uid].setdefault("balance_currencies", {})
                old_balance = cur.get(currency, 0.0)
                new_balance = old_balance + net_amount
                cur[currency] = new_balance
                
                conn.execute(
                    "UPDATE users SET balance_currencies = ? WHERE user_id = ?",
                    (json.dumps(cur), uid)
                )
                
                conn.execute(
                    "INSERT INTO balance_audit (user_id, currency, amount, operation, reference, created_at, balance_after) VALUES (?,?,?,?,?,?,?)",
                    (uid, currency, net_amount, "deposit", tx_hash, int(time.time()), new_balance)
                )
            
            payment_logger.info(f"DEPOSIT|{tx_hash}|{uid}|{currency}|{send_amount}|{commission}|{net_amount}")
            logger.info(f"✅ Депозит: +{net_amount} {currency} пользователю {uid}")
            return True
        except Exception as e:
            logger.error(f"Ошибка записи депозита: {e}")
            return False

def check_deposit_by_user(uid: int, currency: str) -> Tuple[bool, float, str]:
    try:
        with db_connect() as conn:
            cur = conn.execute(
                "SELECT COALESCE(SUM(net_amount), 0) FROM deposits WHERE user_id=? AND currency=? AND created_at > ?",
                (uid, currency, int(time.time()) - 604800)
            )
            total = float(cur.fetchone()[0] or 0)
            if total > 0:
                cur2 = conn.execute(
                    "SELECT tx_hash FROM deposits WHERE user_id=? AND currency=? AND created_at > ? ORDER BY created_at DESC LIMIT 1",
                    (uid, currency, int(time.time()) - 604800)
                )
                last_tx = cur2.fetchone()
                return True, total, last_tx[0] if last_tx else ""
        return False, 0.0, ""
    except Exception as e:
        logger.error(f"Ошибка проверки депозита: {e}")
        return False, 0.0, ""

# ========== ВЫВОД СРЕДСТВ С ИДЕМПОТЕНТНОСТЬЮ ==========
def validate_ton_address(address: str) -> bool:
    if not address:
        return False
    try:
        if HAS_PYTONIQ:
            return Address(address).is_valid
        return bool(re.match(r'^[EU]Q[A-Za-z0-9_\-]{46}$', address))
    except:
        return False

def create_withdrawal(uid: int, currency: str, amount: float, address: str) -> int:
    """Создаёт вывод с проверками и идемпотентным ключом"""
    if address == TON_DEPOSIT_ADDRESS:
        raise ValueError("cannot_withdraw_to_deposit")
    if not validate_ton_address(address):
        raise ValueError("invalid_address")
    
    min_amt = MIN_WITHDRAW_TON if currency == "TON" else MIN_WITHDRAW_USDT
    if amount < min_amt - 1e-9:
        raise ValueError(f"min_amount_{min_amt}")
    
    # Идемпотентный ключ
    idem_key = hashlib.sha256(f"{uid}:{currency}:{amount}:{address}:{int(time.time() / 60)}".encode()).hexdigest()[:32]
    
    async def _create():
        async with _withdraw_locks.setdefault(uid, asyncio.Lock()):
            async with db_transaction() as conn:
                # Проверка существующей заявки
                cur = conn.execute("SELECT id, status FROM withdrawals WHERE idempotency_key = ?", (idem_key,))
                row = cur.fetchone()
                if row:
                    if row[1] == "pending":
                        raise ValueError("recent_pending")
                    return row[0]
                
                # Проверка недавних заявок
                if conn.execute(
                    "SELECT 1 FROM withdrawals WHERE user_id=? AND status='pending' AND created_at > ?",
                    (uid, int(time.time()) - 60)
                ).fetchone():
                    raise ValueError("recent_pending")
                
                # Суточный лимит
                cap = DAILY_WITHDRAW_CAP_TON if currency == "TON" else DAILY_WITHDRAW_CAP_USDT
                if cap > 0:
                    cur = conn.execute(
                        "SELECT COALESCE(SUM(amount), 0) FROM withdrawals WHERE user_id=? AND currency=? AND status IN ('pending','sent') AND created_at > ?",
                        (uid, currency, int(time.time()) - 86400)
                    )
                    if float(cur.fetchone()[0] or 0) + amount > cap + 1e-9:
                        raise ValueError("daily_cap_exceeded")
                
                # Проверка баланса
                ensure_user(uid)
                bal = user_data[uid].get("balance_currencies", {}).get(currency, 0.0)
                if bal < amount - 1e-9:
                    raise ValueError("insufficient_funds")
                
                new_balance = bal - amount
                user_data[uid]["balance_currencies"][currency] = new_balance
                
                conn.execute(
                    "UPDATE users SET balance_currencies = ? WHERE user_id = ?",
                    (json.dumps(user_data[uid]["balance_currencies"]), uid)
                )
                
                conn.execute(
                    "INSERT INTO balance_audit (user_id, currency, amount, operation, reference, created_at, balance_after) VALUES (?,?,?,?,?,?,?)",
                    (uid, currency, -amount, "withdraw_create", f"wd_{idem_key[:8]}", int(time.time()), new_balance)
                )
                
                cur = conn.execute(
                    "INSERT INTO withdrawals (user_id, currency, amount, address, status, created_at, idempotency_key) VALUES (?,?,?,?,?,?,?)",
                    (uid, currency, amount, address, "pending", int(time.time()), idem_key)
                )
                wid = cur.lastrowid
                
                payment_logger.info(f"WITHDRAWAL_CREATE|{wid}|{uid}|{currency}|{amount}|{address}")
                logger.info(f"Заявка на вывод #{wid}: {amount} {currency}")
                return wid
    
    loop = asyncio.get_event_loop()
    if loop.is_running():
        future = asyncio.run_coroutine_threadsafe(_create(), loop)
        return future.result(timeout=10)
    else:
        return asyncio.run(_create())

def mark_withdrawal_sent(wid: int, tx_hash: str):
    async def _mark():
        async with db_transaction() as conn:
            conn.execute(
                "UPDATE withdrawals SET status='sent', processed_at=?, tx_hash=? WHERE id=? AND status='pending'",
                (int(time.time()), tx_hash, wid)
            )
        payment_logger.info(f"WITHDRAWAL_SENT|{wid}|{tx_hash}")
    
    loop = asyncio.get_event_loop()
    if loop.is_running():
        asyncio.run_coroutine_threadsafe(_mark(), loop)
    else:
        asyncio.run(_mark())

def mark_withdrawal_error(wid: int, error: str, refund: bool = True):
    async def _mark():
        async with db_transaction() as conn:
            cur = conn.execute("SELECT user_id, currency, amount, status FROM withdrawals WHERE id=?", (wid,))
            row = cur.fetchone()
            if not row or row[3] != "pending":
                return
            
            user_id, currency, amount, _ = row
            
            conn.execute(
                "UPDATE withdrawals SET status='failed', error=?, processed_at=? WHERE id=?",
                (error[:500], int(time.time()), wid)
            )
            
            if refund:
                async with _balance_locks.setdefault(user_id, asyncio.Lock()):
                    ensure_user(user_id)
                    cur_bal = user_data[user_id].setdefault("balance_currencies", {})
                    old = cur_bal.get(currency, 0.0)
                    new = old + amount
                    cur_bal[currency] = new
                    
                    conn.execute(
                        "UPDATE users SET balance_currencies = ? WHERE user_id = ?",
                        (json.dumps(cur_bal), user_id)
                    )
                    
                    conn.execute(
                        "INSERT INTO balance_audit (user_id, currency, amount, operation, reference, created_at, balance_after) VALUES (?,?,?,?,?,?,?)",
                        (user_id, currency, amount, "withdraw_refund", f"wd_failed_{wid}", int(time.time()), new)
                    )
                
                payment_logger.info(f"WITHDRAWAL_REFUND|{wid}|{user_id}|{currency}|{amount}")
    
    loop = asyncio.get_event_loop()
    if loop.is_running():
        asyncio.run_coroutine_threadsafe(_mark(), loop)
    else:
        asyncio.run(_mark())

def get_pending_withdrawals() -> List[tuple]:
    with db_connect() as conn:
        return conn.execute(
            "SELECT id, user_id, currency, amount, address FROM withdrawals WHERE status='pending' AND (broadcast_at IS NULL OR broadcast_at < ?)",
            (int(time.time()) - 300,)
        ).fetchall()

def recover_stuck_withdrawals() -> List[tuple]:
    with db_connect() as conn:
        return conn.execute(
            "SELECT id, user_id, currency, amount, address FROM withdrawals WHERE status='pending' AND broadcast_at IS NOT NULL AND broadcast_at < ?",
            (int(time.time()) - 3600,)
        ).fetchall()

# ========== АТОМАРНЫЕ ОПЕРАЦИИ СДЕЛОК ==========
async def atomic_deal_status_change(deal_id: str, expected_status: str, new_status: str) -> bool:
    """Меняет статус сделки атомарно с проверкой текущего статуса"""
    async with _deal_locks.setdefault(deal_id, asyncio.Lock()):
        async with db_transaction() as conn:
            cur = conn.execute(
                "SELECT status, version FROM deals WHERE deal_id = ?",
                (deal_id,)
            )
            row = cur.fetchone()
            if not row:
                return False
            
            current, ver = row
            if current != expected_status:
                logger.warning(f"Сделка {deal_id}: ожидался {expected_status}, текущий {current}")
                return False
            
            conn.execute(
                "UPDATE deals SET status = ?, version = ? WHERE deal_id = ? AND version = ?",
                (new_status, ver + 1, deal_id, ver)
            )
            
            if conn.total_changes == 0:
                return False
            
            if deal_id in deals:
                deals[deal_id]["status"] = new_status
        
        return True

# ========== ЦЕНЫ ==========
_price_cache = {"ts": 0.0, "ton_usd": 2.0}
_last_price_warning = 0

def _fetch_prices_sync():
    global _last_price_warning
    try:
        import urllib.request
        req = urllib.request.Request(
            "https://api.coingecko.com/api/v3/simple/price?ids=the-open-network&vs_currencies=usd",
            headers={"User-Agent": "ForSale/1.0"}
        )
        with urllib.request.urlopen(req, timeout=10) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        ton = float((data.get("the-open-network") or {}).get("usd") or 0.0)
        if ton > 0:
            _price_cache["ton_usd"] = ton
            _price_cache["ts"] = time.time()
            return True
    except Exception as e:
        now = time.time()
        if now - _last_price_warning > 600:
            logger.warning(f"Ошибка цены: {e}, кэш: {_price_cache['ton_usd']}")
            _last_price_warning = now
    return False

def ton_usd() -> float:
    if time.time() - _price_cache["ts"] > PRICE_CACHE_TTL_SEC:
        _fetch_prices_sync()
    return _price_cache["ton_usd"] if _price_cache["ton_usd"] > 0 else 2.0

def to_usd(amount: float, currency: str) -> float:
    return amount * ton_usd() if currency == "TON" else amount

def format_amount(value: float, currency: str) -> str:
    if currency == "USDT":
        return f"{value:.2f}".rstrip("0").rstrip(".") or "0"
    return f"{value:.4f}".rstrip("0").rstrip(".") or "0"

# ========== ТЕКСТЫ (ТОЛЬКО РУССКИЙ, PREMIUM ЭМОДЗИ) ==========
TEXTS = {
    "start": "<tg-emoji emoji-id=\"5118454879039259395\">🤖</tg-emoji> <b>Гарант-бот</b>\n\n<tg-emoji emoji-id=\"5104960787579929462\">💎</tg-emoji> <b>Комиссия при пополнении:</b> {deposit_comm}% (добавляется сверху)\n\n<tg-emoji emoji-id=\"5085022089103016925\">🛟</tg-emoji> <b>Поддержка:</b> @{support}\n\n<tg-emoji emoji-id=\"5134122666331996794\">🛡️</tg-emoji> <b>Ваши средства под защитой</b>",
    
    "menu": "<tg-emoji emoji-id=\"5118454879039259395\">🤖</tg-emoji> <b>Меню</b>",
    
    "create_deal": "<tg-emoji emoji-id=\"5118454879039259395\">🤖</tg-emoji> <b>Создать сделку</b>\n\n<tg-emoji emoji-id=\"5116113383128564448\">🔗</tg-emoji> Выберите валюту:",
    
    "choose_currency": "<tg-emoji emoji-id=\"5118454879039259395\">🤖</tg-emoji> <b>Создать сделку</b>\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> Выберите валюту:",
    
    "enter_amount": "<tg-emoji emoji-id=\"5172834782823842584\">💎</tg-emoji> <b>Сумма</b>\n\n<tg-emoji emoji-id=\"5116275208906343429\">❗️</tg-emoji> <b>Мин:</b> {min_limit} {currency}\n<tg-emoji emoji-id=\"5116275208906343429\">❗️</tg-emoji> <b>Макс:</b> {max_limit} {currency}\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> Введите сумму:",
    
    "enter_desc": "<tg-emoji emoji-id=\"4918327330239152795\">📝</tg-emoji> <b>Описание</b>\n\n<tg-emoji emoji-id=\"4915853119839011973\">📦</tg-emoji> Опишите товар\n<tg-emoji emoji-id=\"4916036072560919511\">✅</tg-emoji> Пример: iPhone 13 Pro, 256GB, отличное состояние",
    
    "deal_created": "<tg-emoji emoji-id=\"4916036072560919511\">✅</tg-emoji> <b>Сделка создана</b>\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> {amount} {currency}\n<tg-emoji emoji-id=\"5134472688986756318\">📦</tg-emoji> {desc}\n\n<tg-emoji emoji-id=\"5116113383128564448\">🔗</tg-emoji> <b>Ссылка:</b>\nhttps://t.me/{bot_username}?start={deal_id}",
    
    "deal_info": "<tg-emoji emoji-id=\"5104960787579929462\">💎</tg-emoji> <b>Детали сделки</b>\n\n<tg-emoji emoji-id=\"4904848288345228262\">👤</tg-emoji> <b>Продавец:</b> @{seller}\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> <b>Сумма:</b> {amount} {currency}\n<tg-emoji emoji-id=\"4915853119839011973\">📦</tg-emoji> <b>Товар:</b> {desc}\n\n<tg-emoji emoji-id=\"4911656069207426158\">💸</tg-emoji> Оплата с баланса",
    
    "insufficient": "<tg-emoji emoji-id=\"5121063440311386962\">❌</tg-emoji> <b>Не хватает средств</b>\n\n<tg-emoji emoji-id=\"5118686540985271080\">💰</tg-emoji> <b>Баланс:</b> {balance} {currency}",
    
    "insufficient_for_deal": "<tg-emoji emoji-id=\"5121063440311386962\">❌</tg-emoji> <b>Недостаточно средств</b>\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> <b>Нужно:</b> {needed} {currency}\n<tg-emoji emoji-id=\"5118686540985271080\">💰</tg-emoji> <b>Баланс:</b> {balance} {currency}",
    
    "payment_ok": "<tg-emoji emoji-id=\"5123163417326126159\">✅</tg-emoji> <b>Оплата подтверждена</b>\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> Ожидайте товар",
    
    "seller_payment": "<tg-emoji emoji-id=\"4915853119839011973\">📦</tg-emoji> <b>Оплата получена</b>\n\n<tg-emoji emoji-id=\"4904848288345228262\">👤</tg-emoji> <b>Покупатель:</b> @{buyer}\n<tg-emoji emoji-id=\"4915853119839011973\">📦</tg-emoji> <b>Товар:</b> {desc}\n\n<tg-emoji emoji-id=\"5116113383128564448\">🔗</tg-emoji> Передайте товар",
    
    "seller_sent": "<tg-emoji emoji-id=\"5123163417326126159\">✅</tg-emoji> <b>Товар передан</b>\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> Ожидаем подтверждения",
    
    "buyer_notify": "<tg-emoji emoji-id=\"5085022089103016925\">🛟</tg-emoji> <b>Товар передан</b>\n\n<tg-emoji emoji-id=\"4911656069207426158\">💸</tg-emoji> Проверьте и подтвердите",
    
    "deal_completed": "<tg-emoji emoji-id=\"5116309444090661129\">🏁</tg-emoji> <b>Сделка завершена</b>\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> Продавцу зачислено {amount} {currency}",
    
    "deal_completed_buyer": "<tg-emoji emoji-id=\"5116309444090661129\">🏁</tg-emoji> <b>Сделка завершена</b>\n\n<tg-emoji emoji-id=\"5116163917713769254\">⭐</tg-emoji> Спасибо за использование",
    
    "deal_completed_seller": "<tg-emoji emoji-id=\"5116309444090661129\">🏁</tg-emoji> <b>Сделка завершена</b>\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> Вам зачислено {amount} {currency}",
    
    "deal_paid_buyer": "<tg-emoji emoji-id=\"5123163417326126159\">✅</tg-emoji> <b>Оплата подтверждена</b>\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> Ожидайте товар",
    
    "deal_paid_seller": "<tg-emoji emoji-id=\"5123163417326126159\">✅</tg-emoji> <b>Сделка #{deal_id} оплачена</b>\n\n<tg-emoji emoji-id=\"5116113383128564448\">🔗</tg-emoji> Передайте товар",
    
    "deal_shipped_seller": "<tg-emoji emoji-id=\"5116113383128564448\">🔗</tg-emoji> <b>Товар передан</b>\n\n<tg-emoji emoji-id=\"4916036072560919511\">✅</tg-emoji> Ожидаем подтверждения",
    
    "deal_shipped_buyer": "<tg-emoji emoji-id=\"5085022089103016925\">🛟</tg-emoji> <b>Товар передан</b>\n\n<tg-emoji emoji-id=\"4916036072560919511\">✅</tg-emoji> Подтвердите получение",
    
    "rate_seller": "<tg-emoji emoji-id=\"5116163917713769254\">⭐</tg-emoji> <b>Оцените продавца</b>",
    
    "rate_buyer": "<tg-emoji emoji-id=\"5116163917713769254\">⭐</tg-emoji> <b>Оцените покупателя</b>",
    
    "deal_cancelled": "<tg-emoji emoji-id=\"5121063440311386962\">❌</tg-emoji> <b>Сделка отменена</b>\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> Средства возвращены",
    
    "wallet": "<tg-emoji emoji-id=\"5116093437300442328\">💎</tg-emoji> <b>Кошелёк</b>\n\n<tg-emoji emoji-id=\"4902715076873553054\">🔹</tg-emoji> <b>TON:</b> {ton}\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> <b>USDT:</b> {usdt}",
    
    "view_address": "<tg-emoji emoji-id=\"4916086774649848789\">🔗</tg-emoji> <b>Ваш адрес для вывода</b>\n\n<code>{address}</code>\n\n<tg-emoji emoji-id=\"4916036072560919511\">✅</tg-emoji> Используйте этот адрес для вывода средств",
    
    "deposit_prompt": "<tg-emoji emoji-id=\"5116395218882528029\">📥</tg-emoji> <b>Пополнение баланса</b>\n\nВведите сумму, которую хотите получить на баланс:",
    
    "deposit_calculated": "<tg-emoji emoji-id=\"5116395218882528029\">📥</tg-emoji> <b>Пополнение {currency}</b>\n\n<tg-emoji emoji-id=\"4916036072560919511\">✅</tg-emoji> <b>Зачислится на баланс:</b> {desired} {currency}\n<tg-emoji emoji-id=\"5104960787579929462\">💎</tg-emoji> <b>Комиссия ({deposit_comm}%):</b> {commission} {currency}\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> <b>Итого к отправке:</b> {send} {currency}\n\n<tg-emoji emoji-id=\"5116113383128564448\">🔗</tg-emoji> <b>Адрес для отправки:</b>\n<code>{address}</code>\n\n<tg-emoji emoji-id=\"5116275208906343429\">❗️</tg-emoji> <b>ОБЯЗАТЕЛЬНО укажите комментарий:</b>\n<code>user_{user_id}</code>\n\n<tg-emoji emoji-id=\"5118686540985271080\">⏳</tg-emoji> После отправки нажмите «Проверить оплату»",
    
    "checking_payment": "<tg-emoji emoji-id=\"5118686540985271080\">⏳</tg-emoji> <b>Проверяем транзакцию...</b>\n\nПожалуйста, подождите. Это может занять до 1 минуты.",
    
    "check_deposit": "<tg-emoji emoji-id=\"5116395218882528029\">📥</tg-emoji> <b>Проверка оплаты</b>\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> <b>Валюта:</b> {currency}\n\n<tg-emoji emoji-id=\"5118686540985271080\">⏳</tg-emoji> Проверяем транзакции...",
    
    "check_deposit_found": "<tg-emoji emoji-id=\"4916036072560919511\">✅</tg-emoji> <b>Транзакция найдена!</b>\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> <b>Зачислено:</b> +{amount} {currency}\n<tg-emoji emoji-id=\"5116113383128564448\">🔗</tg-emoji> <b>Хэш:</b> <code>{tx_hash}</code>\n\n<tg-emoji emoji-id=\"5116445341150872576\">💎</tg-emoji> Средства зачислены на баланс",
    
    "check_deposit_not_found": "<tg-emoji emoji-id=\"5121063440311386962\">❌</tg-emoji> <b>Транзакций не найдено</b>\n\n<tg-emoji emoji-id=\"5116275208906343429\">❗️</tg-emoji> Убедитесь, что:\n1️⃣ Отправили {currency} на правильный адрес\n2️⃣ Указали комментарий <code>user_{user_id}</code>\n3️⃣ Сумма соответствует рассчитанной\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> Транзакции зачисляются в течение 1-2 минут\n\n<tg-emoji emoji-id=\"5118686540985271080\">⏳</tg-emoji> Попробуйте ещё раз через минуту",
    
    "deposit_auto_notification": "<tg-emoji emoji-id=\"4916036072560919511\">✅</tg-emoji> <b>Депозит зачислен!</b>\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> <b>Отправлено:</b> {amount} {currency}\n<tg-emoji emoji-id=\"5104960787579929462\">💎</tg-emoji> <b>Комиссия ({deposit_comm}%):</b> {commission} {currency}\n<tg-emoji emoji-id=\"4916036072560919511\">✅</tg-emoji> <b>Зачислено:</b> {net} {currency}",
    
    "withdraw": "<tg-emoji emoji-id=\"4904500559203009298\">💸</tg-emoji> <b>Вывод средств</b>\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> Выберите валюту:",
    
    "enter_withdraw_amount": "<tg-emoji emoji-id=\"4904500559203009298\">💸</tg-emoji> <b>Вывод</b>\n\n<tg-emoji emoji-id=\"5118686540985271080\">💰</tg-emoji> <b>Баланс:</b> {balance} {currency}\n<tg-emoji emoji-id=\"5116275208906343429\">❗️</tg-emoji> <b>Мин:</b> {min_amount} {currency}\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> Введите сумму:",
    
    "withdraw_addr": "<tg-emoji emoji-id=\"5116395218882528029\">📥</tg-emoji> <b>Адрес получателя</b>\n\n<tg-emoji emoji-id=\"5116113383128564448\">🔗</tg-emoji> Введите TON-адрес:",
    
    "withdraw_submitted": "<tg-emoji emoji-id=\"5116395218882528029\">📥</tg-emoji> <b>Заявка принята</b>\n\n<tg-emoji emoji-id=\"4904500559203009298\">💸</tg-emoji> {amount} {currency} → {address}\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> Обработка...",
    
    "withdraw_choose_currency": "<tg-emoji emoji-id=\"4904500559203009298\">💸</tg-emoji> <b>Вывод средств</b>\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> Выберите валюту:",
    
    "profile": "<tg-emoji emoji-id=\"4904848288345228262\">👤</tg-emoji> <b>Профиль</b>\n\n<tg-emoji emoji-id=\"5084613633418199991\">🆔</tg-emoji> <b>ID:</b> {user_id}\n<tg-emoji emoji-id=\"5123163417326126159\">✅</tg-emoji> <b>Сделок:</b> {deals}\n<tg-emoji emoji-id=\"4915896438879159184\">⭐</tg-emoji> <b>Рейтинг:</b> +{likes}/-{dislikes}\n\n<tg-emoji emoji-id=\"4902715076873553054\">🔹</tg-emoji> <b>TON:</b> {ton}\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> <b>USDT:</b> {usdt}",
    
    "set_address": "<tg-emoji emoji-id=\"4916086774649848789\">🔗</tg-emoji> <b>Привязка адреса</b>\n\n<tg-emoji emoji-id=\"5116113383128564448\">🔗</tg-emoji> Отправьте TON-адрес (EQ или UQ):",
    
    "addr_saved": "<tg-emoji emoji-id=\"5123163417326126159\">✅</tg-emoji> <b>Адрес сохранён</b>\n<code>{addr}</code>",
    
    "link_wallet_required": "<tg-emoji emoji-id=\"5121063440311386962\">❌</tg-emoji> <b>Сначала привяжите адрес</b>\n\n<tg-emoji emoji-id=\"4916086774649848789\">🔗</tg-emoji> Сейчас я перенаправлю вас в меню привязки адреса.",
    
    "my_deals": "<tg-emoji emoji-id=\"5118686540985271080\">💰</tg-emoji> <b>Мои сделки</b>",
    
    "no_deals": "<tg-emoji emoji-id=\"5118686540985271080\">📭</tg-emoji> <b>Нет сделок</b>",
    
    "deal_status_active": "<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> Активна",
    "deal_status_confirmed": "<tg-emoji emoji-id=\"5123163417326126159\">✅</tg-emoji> Оплачена",
    "deal_status_seller_sent": "<tg-emoji emoji-id=\"5116113383128564448\">🔗</tg-emoji> Товар передан",
    "deal_status_completed": "<tg-emoji emoji-id=\"5116309444090661129\">🏁</tg-emoji> Завершена",
    "deal_status_cancelled": "<tg-emoji emoji-id=\"5121063440311386962\">❌</tg-emoji> Отменена",
    "deal_status_disputed": "<tg-emoji emoji-id=\"5085022089103016925\">⚠️</tg-emoji> Спор",
    
    "error_network": "<tg-emoji emoji-id=\"4906943755644306322\">🌐</tg-emoji> <b>Ошибка сети</b>",
    
    "withdraw_no_addr": "<tg-emoji emoji-id=\"5121063440311386962\">❌</tg-emoji> <b>Сначала привяжите адрес</b>",
    
    "deposit_disabled": "<tg-emoji emoji-id=\"5121063440311386962\">⚠️</tg-emoji> <b>Пополнение недоступно</b>",
    
    "unknown": "<tg-emoji emoji-id=\"4906943755644306322\">❓</tg-emoji> <b>Неизвестная команда</b>",
    
    "confirm_cancel": "<tg-emoji emoji-id=\"5121063440311386962\">⚠️</tg-emoji> <b>Подтверждение отмены</b>\n\nВы уверены, что хотите отменить сделку?\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> Средства будут возвращены покупателю.",
    
    "checking_retry": "<tg-emoji emoji-id=\"5118686540985271080\">⏳</tg-emoji> <b>Проверяем транзакцию...</b>\n\nПопытка {attempt}/10. Транзакция ещё не найдена, ждём 5 секунд...",
    
    "state_reset": "<tg-emoji emoji-id=\"4916036072560919511\">✅</tg-emoji> <b>Состояние сброшено</b>\n\nМожете начать заново",
    
    "status_ok": "<tg-emoji emoji-id=\"4916036072560919511\">✅</tg-emoji> <b>Бот работает</b>\n\n<tg-emoji emoji-id=\"5118686540985271080\">🕐</tg-emoji> <b>Аптайм:</b> {uptime}\n<tg-emoji emoji-id=\"5118686540985271080\">📋</tg-emoji> <b>Сделок:</b> {deals}\n<tg-emoji emoji-id=\"5118686540985271080\">💰</tg-emoji> <b>Пользователей:</b> {users}\n<tg-emoji emoji-id=\"5116648080787112958\">⏳</tg-emoji> <b>Последний LT:</b> {last_lt}",
    
    "dispute_opened": "<tg-emoji emoji-id=\"5121063440311386962\">⚠️</tg-emoji> <b>Спор открыт</b>\n\n<tg-emoji emoji-id=\"5116113383128564448\">🔗</tg-emoji> Сделка {deal_id} заблокирована",
    "dispute_opened_self": "<tg-emoji emoji-id=\"5121063440311386962\">⚠️</tg-emoji> <b>Спор открыт</b>\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> Администратор разберётся",
    "dispute_opened_other": "<tg-emoji emoji-id=\"5121063440311386962\">⚠️</tg-emoji> <b>Открыт спор</b>\n\n<tg-emoji emoji-id=\"5116113383128564448\">🔗</tg-emoji> Сделка #{deal_id} на рассмотрении",
    "dispute_already": "<tg-emoji emoji-id=\"5121063440311386962\">❌</tg-emoji> <b>Спор уже открыт</b>",
    "dispute_cannot": "<tg-emoji emoji-id=\"5121063440311386962\">❌</tg-emoji> <b>Нельзя открыть спор</b>",
    "dispute_resolved_seller": "<tg-emoji emoji-id=\"5116309444090661129\">⚖️</tg-emoji> <b>Спор решён в пользу продавца</b>\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> Средства переведены",
    "dispute_resolved_buyer": "<tg-emoji emoji-id=\"5116309444090661129\">⚖️</tg-emoji> <b>Спор решён в пользу покупателя</b>\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> Средства возвращены",
    
    "buyer_joined": "<tg-emoji emoji-id=\"4904848288345228262\">👤</tg-emoji> <b>Покупатель присоединился</b>\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> Ожидайте оплату",
    
    "faq_text": "<tg-emoji emoji-id=\"4906943755644306322\">❓</tg-emoji> <b>FAQ</b>\n\n1️⃣ <b>Пополнение:</b> введите сумму, бот покажет адрес и комментарий\n2️⃣ <b>Вывод:</b> 5-15 минут\n3️⃣ <b>Комиссия:</b> {deposit_comm}% при пополнении (добавляется сверху)\n4️⃣ <b>Спор:</b> откройте спор, админ разберётся\n5️⃣ <b>Адрес:</b> привяжите в кошельке перед выводом",
    
    "admin_panel": "<tg-emoji emoji-id=\"5118454879039259395\">🔧</tg-emoji> <b>Админ-панель</b>",
    "admin_stats": "📊 Статистика",
    "admin_balance": "💰 Баланс",
    "admin_wallet": "🏦 Кошелёк",
    "admin_withdrawals": "📤 Выводы",
    "admin_disputes": "⚠️ Споры",
    "admin_back": "⬅️ Назад",
    
    "admin_stats_message": "<tg-emoji emoji-id=\"5118686540985271080\">📊</tg-emoji> <b>Статистика</b>\n\n<tg-emoji emoji-id=\"4904848288345228262\">👥</tg-emoji> <b>Пользователей:</b> {users}\n<tg-emoji emoji-id=\"5118686540985271080\">📋</tg-emoji> <b>Сделок:</b> {deals}\n<tg-emoji emoji-id=\"5123163417326126159\">✅</tg-emoji> <b>Завершено:</b> {completed}\n<tg-emoji emoji-id=\"5121063440311386962\">❌</tg-emoji> <b>Отменено:</b> {cancelled}\n<tg-emoji emoji-id=\"5116648080787112958\">⏳</tg-emoji> <b>Активно:</b> {active}\n<tg-emoji emoji-id=\"5085022089103016925\">⚠️</tg-emoji> <b>Споры:</b> {disputed}\n\n<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> <b>Объём:</b> {volume}$\n\n<tg-emoji emoji-id=\"5118686540985271080\">🕐</tg-emoji> <b>Аптайм:</b> {uptime}",
    
    "admin_balance_ask": "<tg-emoji emoji-id=\"5116648080787112958\">💰</tg-emoji> <b>Изменение баланса</b>\n\n<tg-emoji emoji-id=\"5116113383128564448\">🔗</tg-emoji> Введите: <code>user_id сумма TON|USDT</code>",
    "admin_balance_success": "<tg-emoji emoji-id=\"4916036072560919511\">✅</tg-emoji> <b>Баланс изменён</b>\n<code>{uid}</code>\n{currency}: <code>{amount}</code>",
    "admin_wallet_info": "<tg-emoji emoji-id=\"5116093437300442328\">🏦</tg-emoji> <b>Кошелёк бота</b>\n\n<tg-emoji emoji-id=\"5116113383128564448\">🔗</tg-emoji> <b>Адрес:</b>\n<code>{address}</code>\n\n<tg-emoji emoji-id=\"5118686540985271080\">💰</tg-emoji> <b>Баланс:</b> TON {ton}, USDT {usdt}",
    "admin_withdrawals_list": "<tg-emoji emoji-id=\"4904500559203009298\">📤</tg-emoji> <b>Заявки на вывод</b>\n\n{wds}",
    "admin_withdrawal_item": "<tg-emoji emoji-id=\"5116113383128564448\">🔗</tg-emoji> #{id} | {amount} {currency}\n<tg-emoji emoji-id=\"4904848288345228262\">👤</tg-emoji> Пользователь: {user_id}\n<tg-emoji emoji-id=\"5116113383128564448\">🔗</tg-emoji> {address}\n<tg-emoji emoji-id=\"5118686540985271080\">📅</tg-emoji> {created}",
    "admin_withdrawal_none": "<tg-emoji emoji-id=\"5118686540985271080\">📭</tg-emoji> <b>Нет заявок</b>",
    "admin_disputes_list": "<tg-emoji emoji-id=\"5085022089103016925\">⚠️</tg-emoji> <b>Споры</b>\n\n{disputes}",
    "admin_dispute_item": "<tg-emoji emoji-id=\"5116113383128564448\">🔗</tg-emoji> #{deal_id} | {amount} {currency}\n<tg-emoji emoji-id=\"4904848288345228262\">👤</tg-emoji> Продавец: {seller}\n<tg-emoji emoji-id=\"4904848288345228262\">👤</tg-emoji> Покупатель: {buyer}",
    "admin_dispute_none": "<tg-emoji emoji-id=\"5118686540985271080\">📭</tg-emoji> <b>Нет споров</b>",
    "admin_only": "<tg-emoji emoji-id=\"5121063440311386962\">⛔</tg-emoji> <b>Только для админов</b>",
    
    # Кнопки
    "back": "⬅️ Назад",
    "menu_btn": "🏠 Меню",
    "create_deal_btn": "🤝 Создать сделку",
    "profile_btn": "👤 Профиль",
    "wallet_btn": "💎 Кошелёк",
    "deals_btn": "📋 Сделки",
    "address_btn": "🔗 Адрес",
    "deposit_btn": "📥 Пополнить",
    "withdraw_btn": "💸 Вывести",
    "check_payment_btn": "🔍 Проверить оплату",
    "faq_btn": "❓ FAQ",
    "ton_btn": "TON",
    "usdt_btn": "USDT",
    "pay_btn": "💳 Оплатить",
    "confirm_sent_btn": "📤 Товар передан",
    "confirm_received_btn": "✅ Получил",
    "cancel_btn": "❌ Отменить",
    "liked_btn": "👍 Хорошо",
    "disliked_btn": "👎 Плохо",
    "open_dispute_btn": "⚠️ Открыть спор",
    "reset_btn": "🔄 Сброс",
    "change_address_btn": "✏️ Изменить адрес",
}

def get_text(key: str, **kwargs) -> str:
    text = TEXTS.get(key, key)
    try:
        return text.format(**kwargs)
    except:
        return text

def get_deal_status_text(status: str) -> str:
    status_map = {
        "active": "deal_status_active",
        "confirmed": "deal_status_confirmed",
        "seller_sent": "deal_status_seller_sent",
        "completed": "deal_status_completed",
        "cancelled": "deal_status_cancelled",
        "disputed": "deal_status_disputed",
        "paid": "deal_status_confirmed",
        "shipped": "deal_status_seller_sent",
    }
    return get_text(status_map.get(status, "deal_status_active"))

# ========== КЛАВИАТУРЫ ==========
def main_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(get_text("create_deal_btn"), callback_data="create_deal")],
        [InlineKeyboardButton(get_text("profile_btn"), callback_data="profile"),
         InlineKeyboardButton(get_text("wallet_btn"), callback_data="wallet")],
        [InlineKeyboardButton(get_text("faq_btn"), callback_data="faq")],
    ])

def profile_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(get_text("deals_btn"), callback_data="my_deals")],
        [InlineKeyboardButton(get_text("back"), callback_data="menu")],
    ])

def wallet_menu(uid: int) -> InlineKeyboardMarkup:
    addr = get_ton_address(uid)
    addr_text = f"🔗 {addr[:6]}...{addr[-6:]}" if addr else "❌ Не привязан"
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(addr_text, callback_data="view_address")],
        [InlineKeyboardButton(get_text("deposit_btn"), callback_data="deposit"),
         InlineKeyboardButton(get_text("withdraw_btn"), callback_data="withdraw")],
        [InlineKeyboardButton(get_text("check_payment_btn"), callback_data="check_payment")],
        [InlineKeyboardButton(get_text("back"), callback_data="menu")],
    ])

def view_address_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(get_text("change_address_btn"), callback_data="set_address")],
        [InlineKeyboardButton(get_text("back"), callback_data="wallet")],
    ])

def deposit_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("TON", callback_data="deposit_TON"),
         InlineKeyboardButton("USDT", callback_data="deposit_USDT")],
        [InlineKeyboardButton(get_text("back"), callback_data="wallet")],
    ])

def currency_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("TON", callback_data="set_deal_curr_TON"),
         InlineKeyboardButton("USDT", callback_data="set_deal_curr_USDT")],
        [InlineKeyboardButton(get_text("back"), callback_data="menu")],
    ])

def withdraw_currency_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("TON", callback_data="withdraw_curr_TON"),
         InlineKeyboardButton("USDT", callback_data="withdraw_curr_USDT")],
        [InlineKeyboardButton(get_text("back"), callback_data="wallet")],
    ])

def currency_select(action: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("TON", callback_data=f"{action}_TON"),
         InlineKeyboardButton("USDT", callback_data=f"{action}_USDT")],
        [InlineKeyboardButton(get_text("back"), callback_data="wallet")],
    ])

def back_button(callback: str = "menu") -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton(get_text("back"), callback_data=callback)]])

def deal_buttons(deal_id: str, status: str, role: str) -> InlineKeyboardMarkup:
    buttons = []
    if status == "confirmed" and role == "seller":
        buttons.append([InlineKeyboardButton(get_text("confirm_sent_btn"), callback_data=f"confirm_sent_{deal_id}")])
    elif status == "seller_sent" and role == "buyer":
        buttons.append([InlineKeyboardButton(get_text("confirm_received_btn"), callback_data=f"confirm_received_{deal_id}")])
    if status in ["active", "confirmed", "seller_sent"] and role in ["seller", "buyer"]:
        buttons.append([InlineKeyboardButton(get_text("cancel_btn"), callback_data=f"cancel_deal_{deal_id}")])
    if status not in ["completed", "cancelled", "disputed"] and role in ["seller", "buyer"]:
        buttons.append([InlineKeyboardButton(get_text("open_dispute_btn"), callback_data=f"open_dispute_{deal_id}")])
    buttons.append([InlineKeyboardButton(get_text("back"), callback_data="my_deals")])
    return InlineKeyboardMarkup(buttons)

def rating_buttons(deal_id: str, target_role: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(get_text("liked_btn"), callback_data=f"rate_{deal_id}_{target_role}_up"),
         InlineKeyboardButton(get_text("disliked_btn"), callback_data=f"rate_{deal_id}_{target_role}_down")],
        [InlineKeyboardButton(get_text("menu_btn"), callback_data="menu")],
    ])

def admin_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(get_text("admin_stats"), callback_data="admin_stats"),
         InlineKeyboardButton(get_text("admin_wallet"), callback_data="admin_wallet")],
        [InlineKeyboardButton(get_text("admin_balance"), callback_data="admin_balance"),
         InlineKeyboardButton(get_text("admin_withdrawals"), callback_data="admin_withdrawals")],
        [InlineKeyboardButton(get_text("admin_disputes"), callback_data="admin_disputes")],
        [InlineKeyboardButton(get_text("back"), callback_data="menu")],
    ])

def cancel_confirmation_buttons(deal_id: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ Да, отменить", callback_data=f"confirm_cancel_{deal_id}"),
         InlineKeyboardButton("❌ Нет", callback_data=f"view_deal_{deal_id}")],
    ])

# ========== ХЕЛПЕРЫ ==========
async def get_telegram_username(context, uid: int) -> str:
    try:
        chat = await context.bot.get_chat(uid)
        if chat.username:
            return chat.username
        return f"{chat.first_name or ''} {chat.last_name or ''}".strip() or f"user{uid}"
    except:
        return f"user{uid}"

def is_admin(uid: int) -> bool:
    return uid in ADMIN_IDS

def is_deal_participant(deal: dict, uid: int) -> bool:
    return uid == deal.get("seller_id") or uid == deal.get("buyer_id")

def get_deal_role(deal: dict, uid: int) -> Optional[str]:
    if uid == deal.get("seller_id"):
        return "seller"
    elif uid == deal.get("buyer_id"):
        return "buyer"
    return None

def resolve_deal_id(short_id: str) -> Optional[str]:
    if not short_id:
        return None
    short_id = short_id.strip().lstrip("#").lower()
    if short_id in deals:
        return short_id
    if len(short_id) >= 6:
        matches = [did for did in deals if did.startswith(short_id)]
        if len(matches) == 1:
            return matches[0]
    return None

def get_uptime() -> str:
    delta = datetime.now() - _bot_start_time
    days, seconds = delta.days, delta.seconds
    hours, remainder = divmod(seconds, 3600)
    minutes, secs = divmod(remainder, 60)
    if days > 0:
        return f"{days}д {hours}ч"
    elif hours > 0:
        return f"{hours}ч {minutes}м"
    elif minutes > 0:
        return f"{minutes}м {secs}с"
    return f"{secs}с"

async def safe_edit(query, text: str, markup=None):
    try:
        await query.edit_message_text(text, parse_mode="HTML", reply_markup=markup)
    except BadRequest as e:
        if "not modified" not in str(e).lower():
            raise

def get_raw_deposit_address() -> str:
    if not TON_DEPOSIT_ADDRESS:
        return ""
    return TON_DEPOSIT_ADDRESS.replace("0:", "").strip()

# ========== TON API ==========
async def get_session() -> aiohttp.ClientSession:
    global _session
    if _session is None or _session.closed:
        _session = aiohttp.ClientSession()
    return _session

async def async_fetch_actions(start_lt: int = 0) -> List[dict]:
    if not TON_DEPOSIT_ADDRESS or not TON_API_KEY:
        return []
    
    raw_addr = get_raw_deposit_address()
    if not raw_addr:
        return []
    
    params = {
        "account": raw_addr,
        "action_type": "ton_transfer",
        "sort": "asc",
        "limit": str(TON_POLL_LIMIT),
    }
    if start_lt > 0:
        params["start_lt"] = str(start_lt)
    
    try:
        session = await get_session()
        headers = {"X-API-Key": TON_API_KEY, "Accept": "application/json"}
        async with session.get(
            "https://toncenter.com/api/v3/actions",
            params=params, headers=headers,
            timeout=aiohttp.ClientTimeout(total=20)
        ) as resp:
            if resp.status == 200:
                data = await resp.json()
                return data.get("actions", [])
            logger.error(f"HTTP ошибка API: {resp.status}")
            return []
    except Exception as e:
        logger.error(f"Ошибка запроса к API: {e}")
        return []

async def async_fetch_last_actions(limit: int = 5) -> List[dict]:
    if not TON_DEPOSIT_ADDRESS or not TON_API_KEY:
        return []
    
    raw_addr = get_raw_deposit_address()
    if not raw_addr:
        return []
    
    try:
        session = await get_session()
        headers = {"X-API-Key": TON_API_KEY, "Accept": "application/json"}
        async with session.get(
            "https://toncenter.com/api/v3/actions",
            params={"account": raw_addr, "action_type": "ton_transfer", "sort": "desc", "limit": str(limit)},
            headers=headers,
            timeout=aiohttp.ClientTimeout(total=20)
        ) as resp:
            if resp.status == 200:
                return (await resp.json()).get("actions", [])
            return []
    except Exception as e:
        logger.error(f"Ошибка fetch_last_actions: {e}")
        return []

def extract_ton_transfer(action: dict) -> Optional[Tuple[str, int, float, float, float]]:
    try:
        if not action.get("success", True):
            return None
        
        details = action.get("details", {})
        destination = details.get("destination", "")
        source = details.get("source", "")
        our_raw = get_raw_deposit_address()
        
        if destination != our_raw or source == our_raw:
            return None
        
        value_nano = int(details.get("value", "0")) if isinstance(details.get("value"), str) else details.get("value", 0)
        if value_nano <= 0:
            return None
        
        send_amount = value_nano / NANO_TON
        if send_amount < MIN_DEPOSIT_TON:
            return None
        
        comment = details.get("comment", "")
        if not comment:
            return None
        
        match = re.search(r"user[_\-\s]?(\d+)", str(comment), re.IGNORECASE)
        if not match:
            return None
        
        user_id = int(match.group(1))
        tx_hash = (action.get("transactions") or [""])[0]
        if not tx_hash:
            return None
        
        net_amount = send_amount / (1 + DEPOSIT_COMMISSION_PERCENT / 100)
        commission = send_amount - net_amount
        
        return tx_hash, user_id, send_amount, commission, net_amount
    except Exception as e:
        logger.error(f"Ошибка извлечения перевода: {e}")
        return None

# ========== МОНИТОР ДЕПОЗИТОВ ==========
async def process_new_actions(application):
    global _LAST_LT, _LAST_LT_LOADED
    
    async with _LT_LOCK:
        if not _LAST_LT_LOADED:
            with db_connect() as conn:
                cur = conn.execute("SELECT value FROM bot_settings WHERE key = 'ton_monitor_last_lt'")
                row = cur.fetchone()
                if row and row[0]:
                    _LAST_LT = int(row[0])
                else:
                    actions = await async_fetch_last_actions(1)
                    if actions:
                        lt = actions[0].get("end_lt") or actions[0].get("start_lt") or 0
                        if lt:
                            _LAST_LT = int(lt)
                            with db_connect() as conn:
                                conn.execute("INSERT OR REPLACE INTO bot_settings (key, value) VALUES (?, ?)", ("ton_monitor_last_lt", str(_LAST_LT)))
            _LAST_LT_LOADED = True
        
        actions = await async_fetch_actions(start_lt=_LAST_LT if _LAST_LT > 0 else 0)
        max_lt = _LAST_LT
        
        for action in actions:
            lt = action.get("end_lt") or action.get("start_lt") or 0
            if lt:
                try:
                    lt_int = int(lt)
                    if lt_int > max_lt:
                        max_lt = lt_int
                except:
                    pass
            
            if action.get("type") == "ton_transfer":
                parsed = extract_ton_transfer(action)
                if parsed:
                    tx_hash, user_id, send_amount, commission, net_amount = parsed
                    if not deposit_exists(tx_hash):
                        success = await record_deposit_safe(tx_hash, user_id, "TON", send_amount, commission, net_amount)
                        if success and application:
                            text = get_text("deposit_auto_notification",
                                amount=format_amount(send_amount, "TON"),
                                currency="TON",
                                commission=format_amount(commission, "TON"),
                                net=format_amount(net_amount, "TON"),
                                deposit_comm=DEPOSIT_COMMISSION_PERCENT)
                            try:
                                await application.bot.send_message(user_id, text, parse_mode="HTML")
                            except:
                                pass
        
        if max_lt > _LAST_LT:
            _LAST_LT = max_lt
            with db_connect() as conn:
                conn.execute("INSERT OR REPLACE INTO bot_settings (key, value) VALUES (?, ?)", ("ton_monitor_last_lt", str(_LAST_LT)))

async def deposit_monitor_task(application):
    global _shutdown_flag
    while not _shutdown_flag:
        try:
            await process_new_actions(application)
        except Exception as e:
            logger.warning(f"Ошибка монитора депозитов: {e}")
        await asyncio.sleep(TON_POLL_INTERVAL_SEC)

# ========== ПРОВЕРКА ПРОСРОЧЕННЫХ СДЕЛОК ==========
def _parse_deal_created(created_str: Optional[str]) -> Optional[float]:
    if not created_str:
        return None
    for fmt in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H:%M", "%d.%m.%Y %H:%M"):
        try:
            return datetime.strptime(created_str, fmt).timestamp()
        except:
            continue
    return None

async def _cancel_expired_deals(application):
    timeout_sec = DEAL_TIMEOUT_MIN * 60
    cutoff_active = time.time() - timeout_sec
    cutoff_shipped = time.time() - (DEAL_SELLER_SENT_TIMEOUT_HOURS * 3600)
    
    for did, deal in list(deals.items()):
        status = deal.get("status", "")
        created_ts = _parse_deal_created(deal.get("created_at"))
        if not created_ts:
            continue
        
        if status == "active" and created_ts <= cutoff_active:
            if await atomic_deal_status_change(did, "active", "cancelled"):
                if deal.get("escrow_collected") and deal.get("buyer_id"):
                    add_balance(deal["buyer_id"], deal["currency"], deal["amount"], "refund_expired", f"deal_{did}")
                for pid in [deal.get("seller_id"), deal.get("buyer_id")]:
                    if pid:
                        try:
                            await application.bot.send_message(pid, get_text("deal_cancelled"), parse_mode="HTML")
                        except:
                            pass
        
        elif status == "seller_sent" and created_ts <= cutoff_shipped:
            if await atomic_deal_status_change(did, "seller_sent", "completed"):
                if deal.get("escrow_collected") and deal.get("seller_id"):
                    add_balance(deal["seller_id"], deal["currency"], deal["amount"], "auto_complete", f"deal_{did}")
                    add_successful_deal(deal["seller_id"])
                for pid in [deal.get("seller_id"), deal.get("buyer_id")]:
                    if pid:
                        try:
                            await application.bot.send_message(pid, get_text("deal_completed", amount=format_amount(deal["amount"], deal["currency"]), currency=deal["currency"]), parse_mode="HTML")
                        except:
                            pass

async def _auto_open_disputes(application):
    hours = DEAL_DISPUTE_AUTO_TIMEOUT_HOURS
    if hours <= 0:
        return
    cutoff = time.time() - (hours * 3600)
    
    for did, deal in list(deals.items()):
        if deal.get("status") not in ["confirmed", "seller_sent"]:
            continue
        created_ts = _parse_deal_created(deal.get("created_at"))
        if created_ts and created_ts <= cutoff:
            if await atomic_deal_status_change(did, deal["status"], "disputed"):
                for pid in [deal.get("seller_id"), deal.get("buyer_id")]:
                    if pid:
                        try:
                            await application.bot.send_message(pid, get_text("dispute_opened", deal_id=did[:8]), parse_mode="HTML")
                        except:
                            pass
                for aid in ADMIN_IDS:
                    try:
                        await application.bot.send_message(aid, f"⚠️ Авто-спор по сделке {did[:8]}", parse_mode="HTML")
                    except:
                        pass

async def expiry_watcher_task(application):
    global _shutdown_flag
    while not _shutdown_flag:
        try:
            await _cancel_expired_deals(application)
            await _auto_open_disputes(application)
        except Exception as e:
            logger.warning(f"Ошибка проверки просрочек: {e}")
        await asyncio.sleep(DEAL_TIMEOUT_CHECK_INTERVAL_SEC)

# ========== ВЫПЛАТЫ ЧЕРЕЗ TON ==========
def _get_mnemonic_words() -> List[str]:
    raw = (BOT_WALLET_MNEMONIC or "").strip()
    if not raw:
        return []
    words = raw.split()
    if len(words) not in [12, 24]:
        logger.error(f"Неверная длина мнемоники: {len(words)} (нужно 12 или 24)")
    return words

def _wallet_lock_path() -> str:
    mnemo = "".join(_get_mnemonic_words())
    h = hashlib.sha256(mnemo.encode()).hexdigest()[:16] if mnemo else "default"
    return os.path.join(tempfile.gettempdir(), f"forsale_hot_wallet_{h}.lock")

def _build_text_comment(memo: str):
    b = begin_cell()
    b.store_uint(0, 32)
    b.store_snake_string(memo)
    return b.end_cell()

def _build_jetton_transfer_body(dest_address: str, jetton_amount: int, memo: str = ""):
    b = begin_cell()
    b.store_uint(0x0f8a7ea5, 32)
    b.store_uint(0, 64)
    b.store_coins(jetton_amount)
    b.store_address(Address(dest_address))
    b.store_address(Address(dest_address))
    b.store_bit(0)
    b.store_coins(1)
    if memo:
        fb = begin_cell()
        fb.store_uint(0, 32)
        fb.store_snake_string(memo)
        b.store_bit(1)
        b.store_ref(fb.end_cell())
    else:
        b.store_bit(0)
    return b.end_cell()

async def _open_provider():
    prov = LiteBalancer.from_mainnet_config(trust_level=2)
    await prov.start_up()
    return prov

async def _open_wallet(provider):
    mnemonics = _get_mnemonic_words()
    if len(mnemonics) not in [12, 24]:
        raise ValueError(f"Неверная длина мнемоники: {len(mnemonics)}")
    if not mnemonics:
        raise ValueError("Мнемоника не задана")
    return await WalletV4R2.from_mnemonic(provider, mnemonics)

async def _get_usdt_wallet_address(provider, owner_address: str) -> Optional[str]:
    try:
        result = await provider.run_get_method(
            address=USDT_JETTON_MASTER,
            method="get_wallet_address",
            stack=[begin_cell().store_address(Address(owner_address)).end_cell().begin_parse()]
        )
        return result[0].load_address().to_str()
    except Exception as e:
        logger.warning(f"Ошибка получения USDT адреса: {e}")
        return None

async def _wait_for_outgoing(memo_marker: str, timeout: int = 90, jetton: bool = False) -> Optional[str]:
    deadline = asyncio.get_event_loop().time() + timeout
    provider = None
    try:
        provider = await _open_provider()
        wallet = await _open_wallet(provider)
        addr = wallet.address.to_str()
        while asyncio.get_event_loop().time() < deadline:
            try:
                txs = await provider.get_transactions(address=addr, count=20)
                for tx in txs:
                    for msg in (tx.out_msgs or []):
                        comment = ""
                        try:
                            if msg.body:
                                s = msg.body.begin_parse()
                                if s.remaining_bits >= 32:
                                    op = s.load_uint(32)
                                    if op == 0:
                                        comment = s.load_snake_string()
                                    elif op == 0x0f8a7ea5 and jetton:
                                        s.load_uint(64); s.load_coins()
                                        s.load_address(); s.load_address()
                                        if s.load_bit(): s.load_ref()
                                        s.load_coins()
                                        if s.load_bit():
                                            fb = s.load_ref().begin_parse()
                                            if fb.remaining_bits >= 32 and fb.load_uint(32) == 0:
                                                comment = fb.load_snake_string()
                        except:
                            pass
                        if memo_marker in comment:
                            return tx.cell.hash.hex()
            except Exception as e:
                logger.debug(f"Ошибка ожидания исходящей: {e}")
            await asyncio.sleep(3)
    finally:
        if provider:
            try:
                await provider.close_all()
            except:
                pass
    return None

async def send_ton(destination: str, amount_ton: float, memo: str = "") -> Tuple[bool, Optional[str], Optional[str]]:
    if not HAS_PYTONIQ:
        return False, None, "pytoniq не установлен"
    
    mnemonics = _get_mnemonic_words()
    if not mnemonics or len(mnemonics) not in [12, 24]:
        return False, None, "Мнемоника не задана или неверна"
    
    unique_id = uuid.uuid4().hex[:8]
    full_memo = f"{memo} | id:{unique_id}" if memo else f"id:{unique_id}"
    amount_nano = int(amount_ton * 1e9)
    
    lock_path = _wallet_lock_path()
    if HAS_FILELOCK:
        flock = filelock.FileLock(lock_path, timeout=120)
        try:
            await asyncio.to_thread(flock.acquire, timeout=120)
        except:
            return False, None, "Ошибка блокировки кошелька"
    else:
        import threading
        lock = threading.Lock()
        await asyncio.to_thread(lock.acquire)
    
    try:
        for attempt, delay in enumerate(RETRY_DELAYS, 1):
            if delay > 0:
                await asyncio.sleep(delay)
            provider = None
            try:
                provider = await _open_provider()
                wallet = await _open_wallet(provider)
                balance = await wallet.get_balance()
                if balance < amount_nano + int(PAYOUT_TON_GAS_RESERVE * 1e9):
                    return False, None, f"Недостаточно TON: {balance/1e9:.4f}"
                await wallet.transfer(destination=destination, amount=amount_nano, body=_build_text_comment(full_memo))
                tx_hash = await _wait_for_outgoing(f"id:{unique_id}", timeout=90, jetton=False)
                if tx_hash:
                    return True, tx_hash, None
                return True, None, "Отправлено, хэш не подтверждён"
            except Exception as e:
                logger.warning(f"Попытка {attempt} не удалась: {e}")
                if attempt == len(RETRY_DELAYS):
                    return False, None, str(e)
            finally:
                if provider:
                    try:
                        await provider.close_all()
                    except:
                        pass
    finally:
        if HAS_FILELOCK:
            try:
                flock.release()
            except:
                pass
        else:
            lock.release()
    
    return False, None, "Все попытки не удались"

async def send_usdt(destination: str, amount_usdt: float, memo: str = "") -> Tuple[bool, Optional[str], Optional[str]]:
    if not HAS_PYTONIQ:
        return False, None, "pytoniq не установлен"
    
    mnemonics = _get_mnemonic_words()
    if not mnemonics or len(mnemonics) not in [12, 24]:
        return False, None, "Мнемоника не задана или неверна"
    
    unique_id = uuid.uuid4().hex[:8]
    full_memo = f"{memo} | id:{unique_id}" if memo else f"id:{unique_id}"
    amount_raw = int(amount_usdt * 10**6)
    attach_ton_nano = int(PAYOUT_JETTON_GAS_TON * 1e9)
    
    lock_path = _wallet_lock_path()
    if HAS_FILELOCK:
        flock = filelock.FileLock(lock_path, timeout=120)
        try:
            await asyncio.to_thread(flock.acquire, timeout=120)
        except:
            return False, None, "Ошибка блокировки кошелька"
    else:
        import threading
        lock = threading.Lock()
        await asyncio.to_thread(lock.acquire)
    
    try:
        for attempt, delay in enumerate(RETRY_DELAYS, 1):
            if delay > 0:
                await asyncio.sleep(delay)
            provider = None
            try:
                provider = await _open_provider()
                wallet = await _open_wallet(provider)
                owner_addr = wallet.address.to_str()
                jetton_wallet = await _get_usdt_wallet_address(provider, owner_addr)
                if not jetton_wallet:
                    return False, None, "Не удалось определить USDT кошелёк"
                result = await provider.run_get_method(address=jetton_wallet, method="get_wallet_data", stack=[])
                usdt_balance = int(result[0]) / 10**6
                if usdt_balance < amount_usdt - 1e-6:
                    return False, None, f"Недостаточно USDT: {usdt_balance:.2f}"
                ton_balance = await wallet.get_balance()
                if ton_balance < attach_ton_nano + int(PAYOUT_TON_GAS_RESERVE * 1e9):
                    return False, None, f"Недостаточно TON для газа: {ton_balance/1e9:.4f}"
                body = _build_jetton_transfer_body(destination, amount_raw, full_memo)
                await wallet.transfer(destination=jetton_wallet, amount=attach_ton_nano, body=body)
                tx_hash = await _wait_for_outgoing(f"id:{unique_id}", timeout=90, jetton=True)
                if tx_hash:
                    return True, tx_hash, None
                return True, None, "Отправлено, хэш не подтверждён"
            except Exception as e:
                logger.warning(f"Попытка {attempt} не удалась: {e}")
                if attempt == len(RETRY_DELAYS):
                    return False, None, str(e)
            finally:
                if provider:
                    try:
                        await provider.close_all()
                    except:
                        pass
    finally:
        if HAS_FILELOCK:
            try:
                flock.release()
            except:
                pass
        else:
            lock.release()
    
    return False, None, "Все попытки не удались"

async def _do_auto_payout(application, wid: int, uid: int, currency: str, amount: float, address: str):
    try:
        async with db_transaction() as conn:
            cur = conn.execute("SELECT status FROM withdrawals WHERE id=? AND status='pending'", (wid,))
            if not cur.fetchone():
                logger.warning(f"Вывод #{wid} не в статусе pending, пропускаем")
                return
        
        if currency == "TON":
            ok, tx_hash, err = await send_ton(address, amount, f"вывод #{wid}")
        else:
            ok, tx_hash, err = await send_usdt(address, amount, f"вывод #{wid}")
        
        if ok:
            mark_withdrawal_sent(wid, tx_hash or "broadcasted")
            try:
                await application.bot.send_message(
                    uid,
                    f"✅ Вывод #{wid} отправлен!\n{format_amount(amount, currency)} {currency} → {address[:20]}...",
                    parse_mode="HTML"
                )
            except:
                pass
            logger.info(f"Автовывод #{wid}: {amount} {currency}")
            payment_logger.info(f"AUTO_PAYOUT|{wid}|{uid}|{currency}|{amount}|{address}|{tx_hash}")
        else:
            mark_withdrawal_error(wid, err or "Неизвестная ошибка", refund=True)
            logger.warning(f"Автовывод #{wid} не удался: {err}")
            try:
                await application.bot.send_message(
                    uid,
                    f"❌ Вывод #{wid} не удался: {err[:200]}\nСредства возвращены на баланс.",
                    parse_mode="HTML"
                )
            except:
                pass
            for aid in ADMIN_IDS:
                try:
                    await application.bot.send_message(
                        aid,
                        f"⚠️ Автовывод #{wid} не удался: {amount} {currency}\nПользователь: {uid}\nОшибка: {err[:200]}",
                        parse_mode="HTML"
                    )
                except:
                    pass
    except Exception as e:
        logger.error(f"Исключение в автовыводе #{wid}: {e}")
        mark_withdrawal_error(wid, str(e)[:200], refund=True)

async def recover_stuck_withdrawals_task(application):
    for wid, uid, currency, amount, address in recover_stuck_withdrawals():
        logger.info(f"Восстановление зависшего вывода #{wid}")
        asyncio.create_task(_do_auto_payout(application, wid, uid, currency, amount, address))

# ========== ПРОВЕРКА ОПЛАТЫ С ПОВТОРАМИ ==========
async def check_payment_with_retry(update: Update, context: ContextTypes.DEFAULT_TYPE, uid: int, currency: str):
    msg = await update.message.reply_text(get_text("checking_payment"), parse_mode="HTML")
    
    for attempt in range(1, 11):
        found, total, tx_hash = check_deposit_by_user(uid, currency)
        
        if found:
            await msg.edit_text(
                get_text("check_deposit_found", amount=format_amount(total, currency), currency=currency, tx_hash=tx_hash[:16]),
                parse_mode="HTML",
                reply_markup=back_button("wallet")
            )
            return True
        
        if attempt < 10:
            await msg.edit_text(get_text("checking_retry", attempt=attempt), parse_mode="HTML")
            await asyncio.sleep(5)
    
    await msg.edit_text(
        get_text("check_deposit_not_found", currency=currency, user_id=uid),
        parse_mode="HTML",
        reply_markup=back_button("wallet")
    )
    return False

# ========== ОБРАБОТЧИК CALLBACK ==========
async def button_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    uid = update.effective_user.id
    data = query.data
    ensure_user(uid)
    
    if data == "menu":
        context.user_data.clear()
        await safe_edit(query, get_text("start", deposit_comm=DEPOSIT_COMMISSION_PERCENT, support=SUPPORT_USERNAME), main_menu())
    
    elif data == "profile":
        ton_bal = get_balance(uid, "TON")
        usdt_bal = get_balance(uid, "USDT")
        await safe_edit(query, get_text("profile",
            user_id=uid,
            deals=user_data[uid].get("successful_deals", 0),
            likes=user_data[uid].get("likes", 0),
            dislikes=user_data[uid].get("dislikes", 0),
            ton=format_amount(ton_bal, "TON"),
            usdt=format_amount(usdt_bal, "USDT")), profile_menu())
    
    elif data == "wallet":
        ton_bal = get_balance(uid, "TON")
        usdt_bal = get_balance(uid, "USDT")
        await safe_edit(query, get_text("wallet", ton=format_amount(ton_bal, "TON"), usdt=format_amount(usdt_bal, "USDT")), wallet_menu(uid))
    
    elif data == "view_address":
        addr = get_ton_address(uid)
        if addr:
            await safe_edit(query, get_text("view_address", address=addr), view_address_menu())
        else:
            context.user_data["state"] = "awaiting_address"
            await safe_edit(query, get_text("link_wallet_required"), back_button("wallet"))
    
    elif data == "set_address":
        context.user_data["state"] = "awaiting_address"
        await safe_edit(query, get_text("set_address"), back_button("wallet"))
    
    elif data == "create_deal":
        await safe_edit(query, get_text("choose_currency"), currency_menu())
    
    elif data == "deposit":
        if not TON_DEPOSIT_ADDRESS:
            await safe_edit(query, get_text("deposit_disabled"), back_button("wallet"))
            return
        await safe_edit(query, get_text("deposit_prompt"), deposit_menu())
    
    elif data == "deposit_TON":
        context.user_data["deposit_currency"] = "TON"
        context.user_data["state"] = "awaiting_deposit_amount"
        await safe_edit(query, "💰 <b>Пополнение TON</b>\n\nВведите сумму, которую хотите получить на баланс (мин. 0.5 TON):", back_button("deposit"))
    
    elif data == "deposit_USDT":
        context.user_data["deposit_currency"] = "USDT"
        context.user_data["state"] = "awaiting_deposit_amount"
        await safe_edit(query, "💰 <b>Пополнение USDT</b>\n\nВведите сумму, которую хотите получить на баланс (мин. 0.5 USDT):", back_button("deposit"))
    
    elif data == "withdraw":
        addr = get_ton_address(uid)
        if not addr:
            context.user_data["state"] = "awaiting_address"
            await safe_edit(query, get_text("link_wallet_required"), back_button("wallet"))
            return
        await safe_edit(query, get_text("withdraw_choose_currency"), withdraw_currency_menu())
    
    elif data.startswith("withdraw_curr_"):
        curr = data.split("_")[-1].upper()
        addr = get_ton_address(uid)
        if not addr:
            context.user_data["state"] = "awaiting_address"
            await safe_edit(query, get_text("link_wallet_required"), back_button("wallet"))
            return
        context.user_data["withdraw_currency"] = curr
        context.user_data["state"] = "awaiting_withdraw_amount"
        balances = {"TON": get_balance(uid, "TON"), "USDT": get_balance(uid, "USDT")}
        min_amt = MIN_WITHDRAW_TON if curr == "TON" else MIN_WITHDRAW_USDT
        await safe_edit(query, get_text("enter_withdraw_amount", balance=format_amount(balances[curr], curr), min_amount=min_amt, currency=curr), back_button("withdraw"))
    
    elif data == "check_payment":
        await safe_edit(query, get_text("check_deposit", currency="TON"), currency_select("check"))
    
    elif data.startswith("check_"):
        currency = data.split("_")[1].upper()
        found, total, tx_hash = check_deposit_by_user(uid, currency)
        if found:
            await safe_edit(query, get_text("check_deposit_found", amount=format_amount(total, currency), currency=currency, tx_hash=tx_hash[:16]), back_button("wallet"))
        else:
            await safe_edit(query, get_text("check_deposit", currency=currency))
            asyncio.create_task(check_payment_with_retry(update, context, uid, currency))
    
    elif data == "faq":
        await safe_edit(query, get_text("faq_text", deposit_comm=DEPOSIT_COMMISSION_PERCENT), back_button("menu"))
    
    elif data.startswith("set_deal_curr_"):
        curr = data.split("_")[-1].upper()
        context.user_data["deal_currency"] = curr
        context.user_data["state"] = "awaiting_amount"
        min_l = MIN_DEAL_TON if curr == "TON" else MIN_DEAL_USDT
        max_l = MAX_DEAL_TON if curr == "TON" else MAX_DEAL_USDT
        await safe_edit(query, get_text("enter_amount", min_limit=min_l, max_limit=max_l, currency=curr), back_button("create_deal"))
    
    elif data == "my_deals":
        user_deals = [(did, d) for did, d in deals.items() if is_deal_participant(d, uid)]
        user_deals.sort(key=lambda x: x[1].get("created_at", ""), reverse=True)
        if not user_deals:
            await safe_edit(query, get_text("no_deals"), back_button("profile"))
            return
        text = get_text("my_deals") + "\n\n"
        kb = []
        for i, (did, d) in enumerate(user_deals[:10], 1):
            st = get_deal_status_text(d.get("status", "active"))
            text += f"{i}. {format_amount(d['amount'], d['currency'])} {d['currency']} | {st}\n"
            kb.append([InlineKeyboardButton(f"#{did[:8]}", callback_data=f"view_deal_{did}")])
        kb.append([InlineKeyboardButton(get_text("back"), callback_data="profile")])
        await safe_edit(query, text, InlineKeyboardMarkup(kb))
    
    elif data.startswith("view_deal_"):
        did = data[10:]
        deal = deals.get(did)
        if not deal:
            await query.answer("Сделка не найдена", show_alert=True)
            return
        role = get_deal_role(deal, uid)
        if not role:
            await query.answer("Вы не участник", show_alert=True)
            return
        seller_name = await get_telegram_username(context, deal["seller_id"])
        text = f"📄 <b>Сделка #{did[:8]}</b>\n\n👤 Продавец: @{seller_name}\n💰 {format_amount(deal['amount'], deal['currency'])} {deal['currency']}\n📦 {deal['description'][:100]}\n📊 Статус: {get_deal_status_text(deal['status'])}"
        await safe_edit(query, text, deal_buttons(did, deal["status"], role))
    
    elif data.startswith("pay_"):
        deal_id = data[4:]
        deal = deals.get(deal_id)
        if not deal or deal.get("status") != "active" or deal.get("buyer_id") or uid == deal.get("seller_id"):
            await query.answer("Недоступно", show_alert=True)
            return
        
        currency = deal["currency"]
        amount = deal["amount"]
        if get_balance(uid, currency) < amount - 1e-9:
            await safe_edit(query, get_text("insufficient_for_deal",
                needed=format_amount(amount, currency),
                balance=format_amount(get_balance(uid, currency), currency),
                currency=currency), back_button("menu"))
            return
        
        async with _deal_locks.setdefault(deal_id, asyncio.Lock()):
            deal = deals.get(deal_id)
            if not deal or deal.get("status") != "active" or deal.get("buyer_id"):
                await query.answer("Статус изменился", show_alert=True)
                return
            
            if not sub_balance(uid, currency, amount, "deal_payment", f"deal_{deal_id}"):
                await query.answer("Недостаточно средств", show_alert=True)
                return
            
            deal["buyer_id"] = uid
            deal["status"] = "confirmed"
            deal["escrow_collected"] = True
            save_deal(deal_id)
            
            await safe_edit(query, get_text("deal_paid_buyer"), back_button("menu"))
            
            seller_id = deal["seller_id"]
            seller_kb = InlineKeyboardMarkup([
                [InlineKeyboardButton(get_text("confirm_sent_btn"), callback_data=f"confirm_sent_{deal_id}")],
                [InlineKeyboardButton(get_text("cancel_btn"), callback_data=f"cancel_deal_{deal_id}")],
                [InlineKeyboardButton(get_text("open_dispute_btn"), callback_data=f"open_dispute_{deal_id}")],
            ])
            await context.bot.send_message(seller_id, get_text("deal_paid_seller", deal_id=deal_id[:8]), parse_mode="HTML", reply_markup=seller_kb)
            
            user_data[seller_id]["total_volume_usd"] = user_data[seller_id].get("total_volume_usd", 0) + to_usd(amount, currency)
            save_user(seller_id)
    
    elif data.startswith("confirm_sent_"):
        deal_id = data[13:]
        deal = deals.get(deal_id)
        if not deal or deal.get("status") != "confirmed" or uid != deal.get("seller_id"):
            await query.answer("Недоступно", show_alert=True)
            return
        
        async with _deal_locks.setdefault(deal_id, asyncio.Lock()):
            deal = deals.get(deal_id)
            if not deal or deal.get("status") != "confirmed":
                await query.answer("Статус изменился", show_alert=True)
                return
            
            if not await atomic_deal_status_change(deal_id, "confirmed", "seller_sent"):
                await query.answer("Статус изменился", show_alert=True)
                return
            
            await safe_edit(query, get_text("seller_sent"), back_button("menu"))
            
            buyer_id = deal["buyer_id"]
            if buyer_id:
                buyer_kb = InlineKeyboardMarkup([
                    [InlineKeyboardButton(get_text("confirm_received_btn"), callback_data=f"confirm_received_{deal_id}")],
                    [InlineKeyboardButton(get_text("cancel_btn"), callback_data=f"cancel_deal_{deal_id}")],
                    [InlineKeyboardButton(get_text("open_dispute_btn"), callback_data=f"open_dispute_{deal_id}")],
                ])
                await context.bot.send_message(buyer_id, get_text("buyer_notify"), parse_mode="HTML", reply_markup=buyer_kb)
    
    elif data.startswith("confirm_received_"):
        deal_id = data[18:]
        deal = deals.get(deal_id)
        if not deal or deal.get("status") != "seller_sent" or uid != deal.get("buyer_id") or not deal.get("buyer_id"):
            await query.answer("Недоступно", show_alert=True)
            return
        
        async with _deal_locks.setdefault(deal_id, asyncio.Lock()):
            deal = deals.get(deal_id)
            if not deal or deal.get("status") != "seller_sent":
                await query.answer("Статус изменился", show_alert=True)
                return
            
            if not await atomic_deal_status_change(deal_id, "seller_sent", "completed"):
                await query.answer("Статус изменился", show_alert=True)
                return
            
            if deal.get("escrow_collected") and deal.get("seller_id"):
                add_balance(deal["seller_id"], deal["currency"], deal["amount"], "deal_complete", f"deal_{deal_id}")
                add_successful_deal(deal["seller_id"])
            
            await safe_edit(query, get_text("deal_completed_buyer"), rating_buttons(deal_id, "seller"))
            await context.bot.send_message(
                deal["seller_id"],
                get_text("deal_completed_seller", amount=format_amount(deal["amount"], deal["currency"]), currency=deal["currency"]),
                parse_mode="HTML",
                reply_markup=rating_buttons(deal_id, "buyer")
            )
    
    elif data.startswith("cancel_deal_"):
        deal_id = data[12:]
        deal = deals.get(deal_id)
        if not deal or not is_deal_participant(deal, uid) or deal.get("status") in ["completed", "cancelled", "disputed", "seller_sent"]:
            await query.answer("Недоступно", show_alert=True)
            return
        await safe_edit(query, get_text("confirm_cancel"), cancel_confirmation_buttons(deal_id))
    
    elif data.startswith("confirm_cancel_"):
        deal_id = data[14:]
        deal = deals.get(deal_id)
        if not deal or not is_deal_participant(deal, uid) or deal.get("status") in ["completed", "cancelled", "disputed"]:
            await query.answer("Недоступно", show_alert=True)
            return
        
        async with _deal_locks.setdefault(deal_id, asyncio.Lock()):
            deal = deals.get(deal_id)
            if not deal or deal.get("status") in ["completed", "cancelled", "disputed"]:
                return
            
            if not await atomic_deal_status_change(deal_id, deal["status"], "cancelled"):
                await query.answer("Статус изменился", show_alert=True)
                return
            
            if deal.get("escrow_collected") and deal.get("buyer_id"):
                add_balance(deal["buyer_id"], deal["currency"], deal["amount"], "deal_cancel", f"deal_{deal_id}")
            
            await safe_edit(query, get_text("deal_cancelled"), back_button("menu"))
            
            other_id = deal["seller_id"] if uid == deal.get("buyer_id") else deal.get("buyer_id")
            if other_id:
                try:
                    await context.bot.send_message(other_id, get_text("deal_cancelled"), parse_mode="HTML")
                except:
                    pass
    
    elif data.startswith("open_dispute_"):
        deal_id = data[13:]
        deal = deals.get(deal_id)
        if not deal or not is_deal_participant(deal, uid) or deal.get("status") not in ["confirmed", "seller_sent"]:
            await query.answer("Недоступно", show_alert=True)
            return
        
        async with _deal_locks.setdefault(deal_id, asyncio.Lock()):
            deal = deals.get(deal_id)
            if deal.get("status") == "disputed":
                await query.answer(get_text("dispute_already"), show_alert=True)
                return
            if not deal or deal.get("status") not in ["confirmed", "seller_sent"]:
                await query.answer("Статус изменился", show_alert=True)
                return
            
            if not await atomic_deal_status_change(deal_id, deal["status"], "disputed"):
                await query.answer("Статус изменился", show_alert=True)
                return
            
            await safe_edit(query, get_text("dispute_opened_self"), back_button("menu"))
            
            other_id = deal["seller_id"] if uid == deal.get("buyer_id") else deal.get("buyer_id")
            if other_id:
                try:
                    await context.bot.send_message(other_id, get_text("dispute_opened_other", deal_id=deal_id[:8]), parse_mode="HTML")
                except:
                    pass
            
            for aid in ADMIN_IDS:
                try:
                    await context.bot.send_message(aid,
                        f"⚠️ <b>Открыт спор</b>\nСделка: #{deal_id[:8]}\nСумма: {deal['amount']} {deal['currency']}\nУчастники: {deal['seller_id']} / {deal['buyer_id']}",
                        parse_mode="HTML")
                except:
                    pass
    
    elif data.startswith("rate_"):
        parts = data.split("_")
        if len(parts) >= 4:
            deal_id, target_role, rating = parts[1], parts[2], parts[3]
            deal = deals.get(deal_id)
            if deal and deal.get("status") == "completed":
                voted_key = f"{target_role}_voted"
                if not deal.get(voted_key):
                    target_id = deal["seller_id"] if target_role == "buyer" else deal["buyer_id"]
                    if target_id:
                        add_rating(target_id, rating == "up")
                        deal[voted_key] = True
                        save_deal(deal_id)
            await safe_edit(query, "⭐ Спасибо за оценку!", main_menu())
    
    # Админ-панель
    elif data == "admin_panel" and is_admin(uid):
        await safe_edit(query, "🔧 <b>Админ-панель</b>", admin_menu())
    
    elif data == "admin_stats" and is_admin(uid):
        total_users = len(user_data)
        total_deals = len(deals)
        completed = sum(1 for d in deals.values() if d.get("status") == "completed")
        cancelled = sum(1 for d in deals.values() if d.get("status") == "cancelled")
        disputed = sum(1 for d in deals.values() if d.get("status") == "disputed")
        active = sum(1 for d in deals.values() if d.get("status") in ["active", "confirmed", "seller_sent"])
        total_volume = sum(u.get("total_volume_usd", 0) for u in user_data.values())
        await safe_edit(query, get_text("admin_stats_message",
            users=total_users, deals=total_deals, completed=completed,
            cancelled=cancelled, disputed=disputed, active=active,
            volume=f"{total_volume:.2f}", uptime=get_uptime()), back_button("admin_panel"))
    
    elif data == "admin_wallet" and is_admin(uid):
        await safe_edit(query, get_text("admin_wallet_info", address=TON_DEPOSIT_ADDRESS or "не задан", ton="?", usdt="?"), back_button("admin_panel"))
    
    elif data == "admin_balance" and is_admin(uid):
        context.user_data["admin_state"] = "awaiting_balance_change"
        await safe_edit(query, get_text("admin_balance_ask"), back_button("admin_panel"))
    
    elif data == "admin_withdrawals" and is_admin(uid):
        wds = get_pending_withdrawals()
        if not wds:
            await safe_edit(query, get_text("admin_withdrawal_none"), back_button("admin_panel"))
            return
        wds_text = ""
        for wid, w_uid, currency, amount, address in wds[:20]:
            wds_text += get_text("admin_withdrawal_item",
                id=wid, amount=format_amount(amount, currency), currency=currency,
                user_id=w_uid, address=address[:20] + "...",
                created=datetime.fromtimestamp(int(time.time())).strftime("%d.%m %H:%M")) + "\n\n"
        text = get_text("admin_withdrawals_list", wds=wds_text)
        kb = [[InlineKeyboardButton("✅ Отправлено", callback_data=f"admin_wd_sent_{wid}"),
               InlineKeyboardButton("❌ Отклонить", callback_data=f"admin_wd_reject_{wid}")]
              for wid, _, _, _, _ in wds[:5]]
        kb.append([InlineKeyboardButton(get_text("back"), callback_data="admin_panel")])
        await safe_edit(query, text, InlineKeyboardMarkup(kb))
    
    elif data.startswith("admin_wd_sent_") and is_admin(uid):
        wid = int(data.split("_")[3])
        with db_connect() as conn:
            conn.execute("UPDATE withdrawals SET status='sent', processed_at=? WHERE id=?", (int(time.time()), wid))
        await query.answer(f"Вывод #{wid} помечен как отправленный")
        await button_callback(update, context)
    
    elif data.startswith("admin_wd_reject_") and is_admin(uid):
        wid = int(data.split("_")[3])
        with db_connect() as conn:
            cur = conn.execute("SELECT user_id, currency, amount FROM withdrawals WHERE id=? AND status='pending'", (wid,))
            row = cur.fetchone()
            if row:
                add_balance(row[0], row[1], row[2], "admin_reject", f"wd_{wid}")
                conn.execute("UPDATE withdrawals SET status='rejected', processed_at=? WHERE id=?", (int(time.time()), wid))
        await query.answer(f"Вывод #{wid} отклонён")
        await button_callback(update, context)
    
    elif data == "admin_disputes" and is_admin(uid):
        disputed = [(did, d) for did, d in deals.items() if d.get("status") == "disputed"]
        if not disputed:
            await safe_edit(query, get_text("admin_dispute_none"), back_button("admin_panel"))
            return
        text = get_text("admin_disputes_list", disputes="") + "\n"
        kb = []
        for did, d in disputed[:10]:
            text += get_text("admin_dispute_item", deal_id=did[:8], amount=format_amount(d["amount"], d["currency"]), currency=d["currency"], seller=d["seller_id"], buyer=d["buyer_id"]) + "\n"
            kb.append([InlineKeyboardButton(f"#{did[:8]}", callback_data=f"admin_resolve_{did}")])
        kb.append([InlineKeyboardButton(get_text("back"), callback_data="admin_panel")])
        await safe_edit(query, text, InlineKeyboardMarkup(kb))
    
    elif data.startswith("admin_resolve_") and is_admin(uid):
        deal_id = data[14:]
        deal = deals.get(deal_id)
        if not deal or deal.get("status") != "disputed":
            await query.answer("Спор уже разрешён", show_alert=True)
            return
        kb = InlineKeyboardMarkup([
            [InlineKeyboardButton("⚖️ Продавцу", callback_data=f"admin_resolve_seller_{deal_id}"),
             InlineKeyboardButton("⚖️ Покупателю", callback_data=f"admin_resolve_buyer_{deal_id}")],
            [InlineKeyboardButton(get_text("back"), callback_data="admin_disputes")],
        ])
        await safe_edit(query, f"⚖️ Разрешение спора #{deal_id[:8]}\n\nВыберите сторону:", kb)
    
    elif data.startswith("admin_resolve_seller_") and is_admin(uid):
        deal_id = data[21:]
        deal = deals.get(deal_id)
        if not deal or deal.get("status") != "disputed":
            await query.answer("Спор уже разрешён", show_alert=True)
            return
        
        async with _deal_locks.setdefault(deal_id, asyncio.Lock()):
            if not await atomic_deal_status_change(deal_id, "disputed", "completed"):
                await query.answer("Статус изменился", show_alert=True)
                return
            
            if deal.get("escrow_collected") and deal.get("seller_id"):
                add_balance(deal["seller_id"], deal["currency"], deal["amount"], "dispute_seller", f"deal_{deal_id}")
                add_successful_deal(deal["seller_id"])
            
            await context.bot.send_message(deal["seller_id"], get_text("dispute_resolved_seller"), parse_mode="HTML")
            if deal.get("buyer_id"):
                await context.bot.send_message(deal["buyer_id"], get_text("dispute_resolved_seller"), parse_mode="HTML")
            
            await safe_edit(query, "✅ Спор решён в пользу продавца", back_button("admin_panel"))
    
    elif data.startswith("admin_resolve_buyer_") and is_admin(uid):
        deal_id = data[20:]
        deal = deals.get(deal_id)
        if not deal or deal.get("status") != "disputed":
            await query.answer("Спор уже разрешён", show_alert=True)
            return
        
        async with _deal_locks.setdefault(deal_id, asyncio.Lock()):
            if not await atomic_deal_status_change(deal_id, "disputed", "cancelled"):
                await query.answer("Статус изменился", show_alert=True)
                return
            
            if deal.get("escrow_collected") and deal.get("buyer_id"):
                add_balance(deal["buyer_id"], deal["currency"], deal["amount"], "dispute_buyer", f"deal_{deal_id}")
            
            await context.bot.send_message(deal["seller_id"], get_text("dispute_resolved_buyer"), parse_mode="HTML")
            if deal.get("buyer_id"):
                await context.bot.send_message(deal["buyer_id"], get_text("dispute_resolved_buyer"), parse_mode="HTML")
            
            await safe_edit(query, "✅ Спор решён в пользу покупателя", back_button("admin_panel"))
    
    elif data == "withdraw_back":
        await safe_edit(query, get_text("withdraw_choose_currency"), withdraw_currency_menu())
    
    else:
        await query.answer("❓ Неизвестная команда", show_alert=True)

# ========== ОБРАБОТЧИК ТЕКСТА ==========
async def text_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    if not user:
        return
    uid = user.id
    text = update.message.text.strip()
    ensure_user(uid)
    
    # Админ: изменение баланса
    admin_state = context.user_data.get("admin_state")
    if admin_state == "awaiting_balance_change" and is_admin(uid):
        parts = text.split()
        if len(parts) >= 3:
            try:
                target_uid = int(parts[0])
                amount = float(parts[1].replace(",", "."))
                currency = parts[2].upper()
                if currency not in ["TON", "USDT"]:
                    await update.message.reply_text("❌ Валюта должна быть TON или USDT", parse_mode="HTML")
                    return
                if amount <= 0:
                    await update.message.reply_text("❌ Сумма должна быть положительной", parse_mode="HTML")
                    return
                add_balance(target_uid, currency, amount, "admin_manual", f"admin_{uid}")
                await update.message.reply_text(get_text("admin_balance_success", uid=target_uid, currency=currency, amount=format_amount(amount, currency)), parse_mode="HTML")
            except ValueError:
                await update.message.reply_text("❌ Неверный формат", parse_mode="HTML")
        else:
            await update.message.reply_text("❌ Формат: user_id сумма TON|USDT", parse_mode="HTML")
        context.user_data.pop("admin_state", None)
        return
    
    state = context.user_data.get("state")
    
    # Сумма депозита
    if state == "awaiting_deposit_amount":
        try:
            desired = float(text.replace(",", "."))
            currency = context.user_data.get("deposit_currency", "TON")
            min_amt = MIN_DEPOSIT_TON if currency == "TON" else MIN_DEPOSIT_USDT
            
            if desired < min_amt:
                await update.message.reply_text(f"❌ Минимальная сумма: {min_amt} {currency}", parse_mode="HTML")
                return
            
            send_amount, commission = calculate_deposit_amount(desired)
            
            context.user_data.pop("state", None)
            context.user_data.pop("deposit_currency", None)
            
            text_msg = get_text("deposit_calculated",
                currency=currency,
                desired=format_amount(desired, currency),
                commission=format_amount(commission, currency),
                send=format_amount(send_amount, currency),
                deposit_comm=DEPOSIT_COMMISSION_PERCENT,
                address=TON_DEPOSIT_ADDRESS,
                user_id=uid)
            
            kb = InlineKeyboardMarkup([
                [InlineKeyboardButton(get_text("check_payment_btn"), callback_data="check_payment")],
                [InlineKeyboardButton(get_text("back"), callback_data="wallet")],
            ])
            
            await update.message.reply_text(text_msg, parse_mode="HTML", reply_markup=kb)
        except ValueError:
            await update.message.reply_text("❌ Введите число", parse_mode="HTML")
        return
    
    # Сумма сделки
    if state == "awaiting_amount":
        try:
            amount = float(text.replace(",", "."))
            if amount <= 0:
                await update.message.reply_text("❌ Сумма должна быть положительной", parse_mode="HTML")
                return
            currency = context.user_data.get("deal_currency", "TON")
            min_amt = MIN_DEAL_TON if currency == "TON" else MIN_DEAL_USDT
            max_amt = MAX_DEAL_TON if currency == "TON" else MAX_DEAL_USDT
            if amount < min_amt or amount > max_amt:
                await update.message.reply_text(f"❌ Сумма от {min_amt} до {max_amt} {currency}", parse_mode="HTML")
                return
            context.user_data["deal_amount"] = amount
            context.user_data["state"] = "awaiting_description"
            await update.message.reply_text(get_text("enter_desc"), parse_mode="HTML")
        except ValueError:
            await update.message.reply_text("❌ Введите число", parse_mode="HTML")
        return
    
    # Описание сделки
    if state == "awaiting_description":
        desc = text[:200]
        currency = context.user_data.get("deal_currency", "TON")
        amount = context.user_data.get("deal_amount", 0)
        deal_id = uuid.uuid4().hex[:16]
        deals[deal_id] = {
            "amount": amount, "description": desc, "seller_id": uid, "buyer_id": None,
            "status": "active", "currency": currency,
            "created_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "escrow_collected": False, "seller_voted": False, "buyer_voted": False,
            "join_notification_sent": False, "completed_at": None
        }
        save_deal(deal_id)
        context.user_data.pop("state", None)
        context.user_data.pop("deal_amount", None)
        context.user_data.pop("deal_currency", None)
        await update.message.reply_text(
            get_text("deal_created", amount=format_amount(amount, currency), currency=currency, desc=desc[:50], bot_username=BOT_USERNAME, deal_id=deal_id),
            parse_mode="HTML", disable_web_page_preview=True,
            reply_markup=back_button("menu")
        )
        return
    
    # Адрес
    if state == "awaiting_address":
        addr = text.strip()
        if HAS_PYTONIQ:
            try:
                if not Address(addr).is_valid:
                    await update.message.reply_text("❌ Неверный TON-адрес. Должен начинаться с EQ или UQ", parse_mode="HTML")
                    return
            except:
                await update.message.reply_text("❌ Неверный TON-адрес", parse_mode="HTML")
                return
        else:
            if not (addr.startswith(("EQ", "UQ")) and len(addr) >= 46):
                await update.message.reply_text("❌ Неверный TON-адрес. Должен начинаться с EQ или UQ", parse_mode="HTML")
                return
        
        set_ton_address(uid, addr)
        context.user_data["state"] = None
        await update.message.reply_text(get_text("addr_saved", addr=addr), parse_mode="HTML", reply_markup=wallet_menu(uid))
        return
    
    # Сумма вывода
    if state == "awaiting_withdraw_amount":
        currency = context.user_data.get("withdraw_currency", "TON")
        min_amt = MIN_WITHDRAW_TON if currency == "TON" else MIN_WITHDRAW_USDT
        try:
            amount = float(text.replace(",", "."))
            if amount <= 0:
                await update.message.reply_text("❌ Сумма должна быть положительной", parse_mode="HTML")
                return
            if amount < min_amt:
                await update.message.reply_text(f"❌ Минимальная сумма: {min_amt} {currency}", parse_mode="HTML")
                return
            if get_balance(uid, currency) < amount - 1e-9:
                await update.message.reply_text(f"❌ Недостаточно средств. Баланс: {format_amount(get_balance(uid, currency), currency)} {currency}", parse_mode="HTML")
                return
            
            cap = DAILY_WITHDRAW_CAP_TON if currency == "TON" else DAILY_WITHDRAW_CAP_USDT
            if cap > 0:
                with db_connect() as conn:
                    cur = conn.execute(
                        "SELECT COALESCE(SUM(amount), 0) FROM withdrawals WHERE user_id=? AND currency=? AND status IN ('pending','sent') AND created_at > ?",
                        (uid, currency, int(time.time()) - 86400))
                    if float(cur.fetchone()[0] or 0) + amount > cap + 1e-9:
                        await update.message.reply_text(f"❌ Суточный лимит: {cap} {currency}", parse_mode="HTML")
                        return
            
            context.user_data["withdraw_amount"] = amount
            context.user_data["state"] = "awaiting_withdraw_address"
            await update.message.reply_text(get_text("withdraw_addr"), parse_mode="HTML")
        except ValueError:
            await update.message.reply_text("❌ Введите число", parse_mode="HTML")
        return
    
    # Адрес вывода
    if state == "awaiting_withdraw_address":
        addr = text.strip()
        if HAS_PYTONIQ:
            try:
                if not Address(addr).is_valid:
                    await update.message.reply_text("❌ Неверный TON-адрес", parse_mode="HTML")
                    return
            except:
                await update.message.reply_text("❌ Неверный TON-адрес", parse_mode="HTML")
                return
        elif not (addr.startswith(("EQ", "UQ")) and len(addr) >= 46):
            await update.message.reply_text("❌ Неверный TON-адрес", parse_mode="HTML")
            return
        
        if addr == TON_DEPOSIT_ADDRESS or addr.replace("UQ", "EQ") == TON_DEPOSIT_ADDRESS:
            await update.message.reply_text("❌ Нельзя выводить на адрес пополнения", parse_mode="HTML")
            return
        
        currency = context.user_data.get("withdraw_currency", "TON")
        amount = context.user_data.get("withdraw_amount", 0)
        try:
            wid = create_withdrawal(uid, currency, amount, addr)
            context.user_data.pop("state", None)
            context.user_data.pop("withdraw_amount", None)
            context.user_data.pop("withdraw_currency", None)
            await update.message.reply_text(
                get_text("withdraw_submitted", amount=format_amount(amount, currency), currency=currency, address=addr[:20] + "..."),
                parse_mode="HTML", reply_markup=back_button("wallet"))
            if HAS_PYTONIQ and BOT_WALLET_MNEMONIC:
                asyncio.create_task(_do_auto_payout(update.application, wid, uid, currency, amount, addr))
        except ValueError as e:
            err_msg = str(e)
            if err_msg == "recent_pending":
                await update.message.reply_text("⏳ У вас уже есть активная заявка на вывод", parse_mode="HTML")
            elif err_msg == "daily_cap_exceeded":
                cap = DAILY_WITHDRAW_CAP_TON if currency == "TON" else DAILY_WITHDRAW_CAP_USDT
                await update.message.reply_text(f"❌ Превышен суточный лимит: {cap} {currency}", parse_mode="HTML")
            else:
                await update.message.reply_text(f"❌ Ошибка: {err_msg}", parse_mode="HTML")
        return
    
    await update.message.reply_text(get_text("unknown"), parse_mode="HTML")

# ========== КОМАНДЫ ==========
async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    if not user:
        return
    uid = user.id
    ensure_user(uid)
    args = context.args
    if args:
        deal_id = resolve_deal_id(args[0])
        if deal_id and deal_id in deals:
            deal = deals[deal_id]
            if deal.get("status") == "active" and deal.get("buyer_id") is None and uid != deal.get("seller_id"):
                seller_name = await get_telegram_username(context, deal["seller_id"])
                text = get_text("deal_info",
                    seller=seller_name,
                    amount=format_amount(deal["amount"], deal["currency"]),
                    currency=deal["currency"],
                    desc=deal["description"][:100])
                kb = InlineKeyboardMarkup([
                    [InlineKeyboardButton(get_text("pay_btn"), callback_data=f"pay_{deal_id}")],
                    [InlineKeyboardButton(get_text("back"), callback_data="menu")],
                ])
                await update.message.reply_text(text, parse_mode="HTML", reply_markup=kb)
                return
    await update.message.reply_text(
        get_text("start", deposit_comm=DEPOSIT_COMMISSION_PERCENT, support=SUPPORT_USERNAME),
        parse_mode="HTML", reply_markup=main_menu())

async def cmd_admin(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text(get_text("admin_only"), parse_mode="HTML")
        return
    await update.message.reply_text("🔧 <b>Админ-панель</b>", parse_mode="HTML", reply_markup=admin_menu())

async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    if is_admin(uid):
        await update.message.reply_text(
            "👑 <b>Админ-команды:</b>\n\n/admin — панель\n/force_deposit user_id сумма TON|USDT — ручное зачисление\n/status — статус бота",
            parse_mode="HTML")
    else:
        await update.message.reply_text(
            f"🤖 <b>Как пользоваться:</b>\n\n1️⃣ Создать сделку\n2️⃣ Кошелёк — пополнение/вывод\n3️⃣ Профиль — статистика\n\n💎 Комиссия при пополнении: {DEPOSIT_COMMISSION_PERCENT}% (сверху)\n🛟 Поддержка: @{SUPPORT_USERNAME}",
            parse_mode="HTML")

async def cmd_deals(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_worker(update.effective_user.id):
        return
    args = context.args
    if not args:
        await update.message.reply_text("/deals <количество>", parse_mode="HTML")
        return
    try:
        count = int(args[0])
        if count < 0:
            await update.message.reply_text("❌ Не может быть отрицательным", parse_mode="HTML")
            return
        ensure_user(update.effective_user.id)
        user_data[update.effective_user.id]["successful_deals"] = count
        save_user(update.effective_user.id)
        await update.message.reply_text(f"✅ Количество сделок: {count}", parse_mode="HTML")
    except ValueError:
        await update.message.reply_text("❌ Введите число", parse_mode="HTML")

async def cmd_money(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_worker(update.effective_user.id):
        return
    args = context.args
    if not args:
        await update.message.reply_text("/money <сумма USD>", parse_mode="HTML")
        return
    try:
        amount = float(args[0].replace(",", "."))
        if amount < 0:
            await update.message.reply_text("❌ Не может быть отрицательной", parse_mode="HTML")
            return
        ensure_user(update.effective_user.id)
        user_data[update.effective_user.id]["total_volume_usd"] = amount
        save_user(update.effective_user.id)
        await update.message.reply_text(f"✅ Объём: {amount:.2f}$", parse_mode="HTML")
    except ValueError:
        await update.message.reply_text("❌ Введите число", parse_mode="HTML")

async def cmd_reset(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data.clear()
    await update.message.reply_text(get_text("state_reset"), parse_mode="HTML", reply_markup=main_menu())

async def cmd_status(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    async with _LT_LOCK:
        last_lt = _LAST_LT
    await update.message.reply_text(
        get_text("status_ok", uptime=get_uptime(), deals=len(deals), users=len(user_data), last_lt=last_lt),
        parse_mode="HTML")

async def cmd_faq(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(get_text("faq_text", deposit_comm=DEPOSIT_COMMISSION_PERCENT), parse_mode="HTML")

async def cmd_force_deposit(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("⛔ Только для админов")
        return
    
    args = context.args
    if len(args) < 3:
        await update.message.reply_text("Использование: /force_deposit <user_id> <сумма_отправки> <TON|USDT>")
        return
    
    try:
        user_id = int(args[0])
        send_amount = float(args[1].replace(",", "."))
        currency = args[2].upper()
        
        if currency not in ["TON", "USDT"]:
            await update.message.reply_text("Валюта должна быть TON или USDT")
            return
        
        net_amount = send_amount / (1 + DEPOSIT_COMMISSION_PERCENT / 100)
        commission = send_amount - net_amount
        
        add_balance(user_id, currency, net_amount, "force_deposit", f"admin_{update.effective_user.id}")
        
        tx_hash = f"manual_{int(time.time())}_{user_id}"
        with db_connect() as conn:
            conn.execute(
                "INSERT INTO deposits (tx_hash, user_id, currency, amount, commission, net_amount, created_at, status, processed_at) VALUES (?,?,?,?,?,?,?,?,?)",
                (tx_hash, user_id, currency, send_amount, commission, net_amount, int(time.time()), "completed", int(time.time())))
        
        await update.message.reply_text(
            f"✅ Ручное зачисление\n\n💰 Отправлено: {send_amount} {currency}\n💎 Комиссия ({DEPOSIT_COMMISSION_PERCENT}%): {commission:.4f} {currency}\n✅ Зачислено: {net_amount:.4f} {currency}\n\n👤 Пользователь: {user_id}",
            parse_mode="HTML")
        logger.info(f"Админ {update.effective_user.id} зачислил {send_amount} {currency} → {user_id}")
    except Exception as e:
        await update.message.reply_text(f"Ошибка: {e}")

async def error_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if isinstance(context.error, Conflict):
        logger.warning("Конфликт: другой экземпляр бота запущен")
        return
    logger.error(f"Ошибка: {context.error}", exc_info=context.error)
    for aid in ADMIN_IDS:
        try:
            await context.bot.send_message(aid, f"⚠️ Ошибка: {str(context.error)[:200]}", parse_mode="HTML")
        except:
            pass

# ========== MAIN ==========
def signal_handler(signum, frame):
    global _shutdown_flag
    _shutdown_flag = True
    logger.info("Получен сигнал завершения")

async def async_main():
    global _shutdown_flag, _session
    
    if not BOT_TOKEN:
        print("ОШИБКА: BOT_TOKEN не задан")
        sys.exit(1)
    
    if TON_DEPOSIT_ADDRESS and not validate_ton_address(TON_DEPOSIT_ADDRESS):
        logger.warning(f"Неверный TON_DEPOSIT_ADDRESS: {TON_DEPOSIT_ADDRESS}")
    
    init_db()
    load_data()
    
    _session = aiohttp.ClientSession()
    
    request = HTTPXRequest(connect_timeout=30, read_timeout=30)
    application = Application.builder().token(BOT_TOKEN).request(request).concurrent_updates(50).build()
    
    application.add_handler(CommandHandler("start", cmd_start))
    application.add_handler(CommandHandler("admin", cmd_admin))
    application.add_handler(CommandHandler("help", cmd_help))
    application.add_handler(CommandHandler("deals", cmd_deals))
    application.add_handler(CommandHandler("money", cmd_money))
    application.add_handler(CommandHandler("reset", cmd_reset))
    application.add_handler(CommandHandler("status", cmd_status))
    application.add_handler(CommandHandler("faq", cmd_faq))
    application.add_handler(CommandHandler("force_deposit", cmd_force_deposit))
    application.add_handler(CallbackQueryHandler(button_callback))
    application.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, text_handler))
    application.add_error_handler(error_handler)
    
    asyncio.create_task(deposit_monitor_task(application))
    asyncio.create_task(expiry_watcher_task(application))
    
    if HAS_PYTONIQ and BOT_WALLET_MNEMONIC:
        await recover_stuck_withdrawals_task(application)
    
    logger.info(f"Бот запущен. Комиссия при пополнении: {DEPOSIT_COMMISSION_PERCENT}% (сверху)")
    
    try:
        await application.initialize()
        await application.start()
        await application.updater.start_polling()
        
        while not _shutdown_flag:
            await asyncio.sleep(1)
    finally:
        await application.updater.stop()
        await application.stop()
        await application.shutdown()
        
        if _session and not _session.closed:
            await _session.close()
        
        release_lock()
        logger.info("Бот остановлен")

def main():
    if not acquire_lock():
        print("Другой экземпляр бота уже запущен. Выход.")
        sys.exit(1)
    atexit.register(release_lock)
    
    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)
    
    try:
        asyncio.run(async_main())
    except KeyboardInterrupt:
        logger.info("Бот остановлен пользователем")
    finally:
        release_lock()

if __name__ == "__main__":
    main()
