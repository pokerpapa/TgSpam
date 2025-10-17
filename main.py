import os
import json
import re
import time
import random
import asyncio
import threading
from telethon.sessions import StringSession
import requests
import openpyxl
import logging
import heapq  # очередь с приоритетом
from collections import defaultdict, deque
from typing import List, Dict, Optional, Set
from bs4 import BeautifulSoup

# MTProto транспорты + ошибка "InvalidBuffer"
from telethon.network.connection import ConnectionTcpAbridged, ConnectionTcpObfuscated
from telethon.errors.common import InvalidBufferError
from telethon.errors import FloodWaitError
from telethon.tl.types import Channel as TlChannel, Chat as TlChat
from telethon import TelegramClient, functions, events
from telethon.errors import (
    ChatWriteForbiddenError,
    FloodWaitError,
    RPCError
)
#  импорты для детектирования банов/деактивации/разлогина
from telethon.errors.rpcerrorlist import (
    UserDeactivatedError,
    UserDeactivatedBanError,
    AuthKeyUnregisteredError,
    SlowModeWaitError,
    UserBannedInChannelError,
    UsernameNotOccupiedError,
    UsernameInvalidError,
    ChannelPrivateError,
    ChatGuestSendForbiddenError,  # NEW
    PeerIdInvalidError,           # NEW
)




import aiohttp  # для HTTP-запросов к Mistral API
import socks  # PySocks, нужен для прокси
# --- Restrictions / quarantine (anti-abuse safe backoff) ---
RESTRICT_DEFAULT_HOURS = int(os.environ.get("RESTRICT_DEFAULT_HOURS", 72))

def _now() -> float:
    return time.time()
def set_campaign_paused(session_name: str, paused: bool) -> dict:
    ctx = get_account_context(session_name)
    ctx["campaign_paused"] = bool(paused)
    try:
        save_account_state(session_name)
    except Exception:
        pass
    return {"name": session_name, "campaign_paused": ctx["campaign_paused"]}

def mark_restricted(session_name: str, hours: int = None, reason: str = "") -> float:
    """
    Пометить аккаунт как 'restricted' на H часов (по умолчанию 72ч) и сохранить в state.
    """
    hours = hours or RESTRICT_DEFAULT_HOURS
    until = _now() + max(1, int(hours * 3600))
    ctx = accounts.get(session_name) or {}
    ctx["restricted_until"] = until
    try:
        save_account_state(session_name)
    except Exception:
        pass
    logging.warning(f"[restrict] account={session_name} until={int(until)} reason={reason or '-'}")
    return until
def _apply_account_floodwait(session_name: str, seconds: int):
    """
    Глобальный бэкофф для аккаунта: замораживаем отправку комментариев и join'ов.
    """
    sec = max(1, int(seconds))
    ctx = accounts.get(session_name) or {}
    now = time.time()
    ctx["next_send_at"] = max(float(ctx.get("next_send_at") or 0), now + sec)
    ctx["next_join_at"] = max(float(ctx.get("next_join_at") or 0), now + sec)

def is_restricted(session_name: str) -> bool:
    ctx = accounts.get(session_name) or {}
    return float(ctx.get("restricted_until") or 0.0) > _now()

global_found_channels = []


# ПАРАМЕТРЫ ТРОТТЛИНГА
# ────────────────────────────────────────────────────────────────────────────────
COMMENT_COOLDOWN_SECONDS = int(os.environ.get("COMMENT_COOLDOWN_SECONDS", 120))
POST_DELAY_SECONDS       = int(os.environ.get("POST_DELAY_SECONDS", 30))

# ── Аватарки / троттлинг профиля ───────────────────────────────────────────────
AVATAR_POOL_DIR = os.environ.get("AVATAR_POOL_DIR", "avatars_pool")
AVATAR_CACHE_DIR = os.environ.get("AVATAR_CACHE_DIR", "avatars_cache")
PROFILE_UPDATE_INTERVAL_SECONDS = int(os.environ.get("PROFILE_UPDATE_INTERVAL_SECONDS", 300))  # пауза между сменами фото
PROFILE_UPDATE_DAILY_LIMIT = int(os.environ.get("PROFILE_UPDATE_DAILY_LIMIT", 2))              # безопасно: до 2/сутки


# ✚ Подписки (join) — интервалы и лимиты
JOIN_INTERVAL_SECONDS = int(os.environ.get("JOIN_INTERVAL_SECONDS", 45))   # базовая пауза между join'ами
JOIN_JITTER_MIN       = float(os.environ.get("JOIN_JITTER_MIN", 0.2))      # джиттер к паузе
JOIN_JITTER_MAX       = float(os.environ.get("JOIN_JITTER_MAX", 1.5))
JOIN_DAILY_LIMIT      = int(os.environ.get("JOIN_DAILY_LIMIT", 40))        # дневной лимит join'ов на аккаунт
              # базовая задержка перед комментом нового поста

# Доп. рассинхрон (джиттер) — можно переопределить в config.json
DESYNC_MIN_SECONDS = int(os.environ.get("DESYNC_MIN_SECONDS", 5))
DESYNC_MAX_SECONDS = int(os.environ.get("DESYNC_MAX_SECONDS", 60))

# История для анти-дубля (сколько последних текстов помнить на дискуссию)
DEDUP_HISTORY_SIZE = int(os.environ.get("DEDUP_HISTORY_SIZE", 5))

# Вероятность лёгкой опечатки (персоны)
DEFAULT_TYPO_PROB = float(os.environ.get("DEFAULT_TYPO_PROB", 0.05))

BIO_MAX_LEN = int(os.environ.get("BIO_MAX_LEN", 140))
# --- Антиспам в супергруппах ---
GROUP_REPLY_PROB = float(os.environ.get("GROUP_REPLY_PROB", 0.2))        # вероятность ответа на входящее сообщение (0..1)
GROUP_MIN_GAP_SECONDS = int(os.environ.get("GROUP_MIN_GAP_SECONDS", 600))# минимум 10 минут между нашими сообщениями в одном чате
GROUP_MAX_PER_HOUR = int(os.environ.get("GROUP_MAX_PER_HOUR", 6))        # не более N ответов в час на чат

# ────────────────────────────────────────────────────────────────────────────────
# ЛОГГЕРЫ
# ────────────────────────────────────────────────────────────────────────────────
def _setup_file_logger(name, filename):
    logger = logging.getLogger(name)
    logger.setLevel(logging.INFO)
    if not any(
        isinstance(h, logging.FileHandler) and getattr(h, "baseFilename", "").endswith(filename)
        for h in logger.handlers
    ):
        fh = logging.FileHandler(filename, encoding='utf-8')
        fh.setLevel(logging.INFO)
        fh.setFormatter(logging.Formatter(
            '%(asctime)s | %(levelname)s | %(message)s',
            datefmt='%Y-%m-%d %H:%M:%S'
        ))
        logger.addHandler(fh)
    # Ключ: пусть сообщения уходят наверх (в корневой StreamHandler → консоль)
    logger.propagate = True
    return logger

leave_logger   = _setup_file_logger("leaves",       "leaves.log")
comment_logger = _setup_file_logger("comments",     "comments.log")
captcha_logger = _setup_file_logger("captcha",      "captcha.log")
chat_logger    = _setup_file_logger("chat_replies", "chat_replies.log")
proxy_logger   = _setup_file_logger("proxy",        "proxy.log")


def refresh_sessions(scan_dir: Optional[str] = None, auto_assign_missing_proxy: bool = True):
    """
    Пересканировать папку sessions/, создать контексты для новых .session,
    подтянуть сохранённое состояние, назначить персоны.
    Возвращает словарь: {"added":[...], "removed":[...]}
    """
    scan_dir = scan_dir or SESSION_DIR

    os.makedirs(scan_dir, exist_ok=True)
    existing = set(available_sessions)
    found_in_fs = set()

    for fname in os.listdir(scan_dir):
        if fname.endswith(".session"):
            found_in_fs.add(fname[:-8])

    # добавленные / удалённые
    added = sorted(found_in_fs - existing)
    removed = sorted(existing - found_in_fs)

    # убрать удалённые
    if removed:
        for name in removed:
            try:
                available_sessions.remove(name)
            except ValueError:
                pass
            # по желанию можно чистить контекст:
            accounts.pop(name, None)

    # подготовить новые
    for name in added:
        if name not in available_sessions:
            available_sessions.append(name)

        # назначим прокси из пула, если нигде не задан
        if auto_assign_missing_proxy and not resolve_proxy_string_for(name):
            try:
                auto_assign_proxy(name, force=False)
            except Exception:
                pass

        # инициализируем контекст
        ctx = get_account_context(name)

        # восстановим состояние, если было
        try:
            st_all = load_state()  # читаем state свежо
            st = st_all.get(name) if isinstance(st_all, dict) else None
        except Exception:
            st = None

        if st:
            ctx["joined_channels"] = set(st.get("joined_channels", []))
            ctx["joined_names"]    = st.get("joined_names", {})
            ctx["monitored_info"]  = {int(k): v for k, v in st.get("monitored_info", {}).items()}
            ctx["restricted_until"] = float(st.get("restricted_until", 0.0))
            ctx["campaign_paused"] = bool(st.get("campaign_paused", False))  # NEW

        ctx["comment_cooldown"] = COMMENT_COOLDOWN_SECONDS

        # назначим персону
        persona_name = assign_persona(name, PERSONAS, _accounts_map)
        persona_data = dict(PERSONAS.get(persona_name or "", {}))
        if "typo_prob" not in persona_data:
            persona_data["typo_prob"] = DEFAULT_TYPO_PROB
        ctx["persona"]      = persona_data
        ctx["persona_name"] = persona_name
        logging.info(f"[sessions] added {name}, persona={persona_name}")

    return {"added": added, "removed": removed}


def log_proxy(account, event, proxy=None, details=""):
    hp = proxy or "-"
    proxy_logger.info(f"{time.strftime('%Y-%m-%d %H:%M:%S')} | ACCOUNT={account} | EVENT={event} | PROXY={hp} | DETAILS={details}")

# ────────────────────────────────────────────────────────────────────────────────
# ХЕЛПЕРЫ ЛОГОВ КОММЕНТОВ
# ────────────────────────────────────────────────────────────────────────────────
def _ts(ts: float) -> str:
    return time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(ts))

def _log_comment(account: str, event: str, **fields):
    order = ["TASK", "CHAT_ID", "DISC_ID", "REPLY_TO", "MSG_ID", "LINK",
             "READY_AT", "ETA_SEC", "WAITED_SEC", "QUEUE",
             "NEXT_CD_UNTIL", "NEXT_CD_SEC", "TEXT", "ERROR"]
    parts = [f"ACCOUNT={account}", f"EVENT={event}"]
    for k in order:
        if k in fields:
            v = fields[k]
            if k in ("READY_AT", "NEXT_CD_UNTIL") and isinstance(v, (int, float)):
                v = _ts(v)
            parts.append(f"{k}={v}")
    # любые прочие поля, которых нет в order
    for k, v in fields.items():
        if k not in order:
            parts.append(f"{k}={v}")
    comment_logger.info(" | ".join(parts))


# ────────────────────────────────────────────────────────────────────────────────
# МАППИНГ АККАУНТ→ПЕРСОНА (accounts_map.json)
# ────────────────────────────────────────────────────────────────────────────────
def load_accounts_map(path="accounts_map.json"):
    if os.path.exists(path):
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    return {}

def save_accounts_map(map_data, path="accounts_map.json"):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(map_data, f, ensure_ascii=False, indent=2)

def assign_persona(account, personas: Dict[str, Dict], accounts_map: Dict[str, str]):
    if account not in accounts_map:
        if not personas:
            persona = None
        else:
            persona = random.choice(list(personas.keys()))
        accounts_map[account] = persona
        save_accounts_map(accounts_map)
    return accounts_map[account]

# ========== STATE MANAGEMENT ==========
STATE_FILE = 'state.json'

def load_state():
    if os.path.exists(STATE_FILE):
        with open(STATE_FILE, 'r', encoding='utf-8') as f:
            return json.load(f)
    return {}

def save_state(state: dict):
    with open(STATE_FILE, 'w', encoding='utf-8') as f:
        json.dump(state, f, ensure_ascii=False, indent=2)

def save_account_state(name: str):
    state = load_state()
    ctx = accounts[name]
    state[name] = {
        "joined_channels": list(ctx["joined_channels"]),
        "joined_names": ctx["joined_names"],
        "monitored_info": {str(k): v for k, v in ctx["monitored_info"].items()},
        "restricted_until": float(ctx.get("restricted_until") or 0.0),
        "campaign_paused": bool(ctx.get("campaign_paused", False)),  # NEW
    }

    save_state(state)


# ========== TELETHON BOT SETUP ==========
api_id = '21939782'
api_hash = 'ed77229f98d49e2791392c274f06dff'

SESSION_DIR = 'sessions'

accounts = {}
available_sessions = []
active_session_name = None

# ────────────────────────────────────────────────────────────────────────────────
# ПРОКСИ: ПАРСИНГ/ВЫБОР/ПРИМЕНЕНИЕ
# ────────────────────────────────────────────────────────────────────────────────
def _strip_ipv6_brackets(host: str) -> str:
    return host[1:-1] if host and host.startswith("[") and host.endswith("]") else host
def _next_local_midnight_ts() -> float:
    """UNIX-время ближайшей местной полуночи."""
    now = time.time()
    lt = time.localtime(now)
    # полуночь «сегодня»
    midnight_today = time.mktime((lt.tm_year, lt.tm_mon, lt.tm_mday, 0, 0, 0,
                                  lt.tm_wday, lt.tm_yday, lt.tm_isdst))
    # если уже прошла — прибавим сутки
    return (midnight_today + 86400) if now >= midnight_today else midnight_today

def parse_proxy_line(line: str):
    """
    Поддерживаем ОБА формата:

    1) Пробельный:
       "2a02:6b8::1 1080 user pass"
       "[2a02:6b8::1] 1080 user pass"

    2) Двоеточечный:
       "[2a14:...]:30000:tgbot:12345"
       "1.2.3.4:1080:user:pass"

    Возвращает dict: {"host","port","user","pass"} или None.
    """
    if not line:
        return None
    s = line.strip()
    if not s:
        return None

    if (" " in s) or ("\t" in s):
        parts = s.split()
        if len(parts) < 2:
            return None
        host = _strip_ipv6_brackets(parts[0])
        try:
            port = int(parts[1])
        except ValueError:
            return None
        user = parts[2] if len(parts) >= 3 else None
        pwd  = parts[3] if len(parts) >= 4 else None
        return {"host": host, "port": port, "user": user, "pass": pwd}

    if s.startswith("["):
        end = s.find("]")
        if end == -1:
            return None
        host = s[1:end]
        rest = s[end+1:]
        if not rest.startswith(":"):
            return None
        rest = rest[1:]
        parts = rest.split(":", 2)
    else:
        parts = s.split(":", 3)
        host = parts[0]
        parts = parts[1:]

    if not parts:
        return None
    try:
        port = int(parts[0])
    except (ValueError, TypeError):
        return None

    user = parts[1] if len(parts) >= 2 and parts[1] != "" else None
    pwd  = parts[2] if len(parts) >= 3 and parts[2] != "" else None

    host = _strip_ipv6_brackets(host)
    return {"host": host, "port": port, "user": user, "pass": pwd}


def build_telethon_proxy(proxy_dict, tg_proxy_type: str):
    if not proxy_dict:
        return None, None
    host, port, user, pwd = proxy_dict["host"], proxy_dict["port"], proxy_dict["user"], proxy_dict["pass"]
    t = (tg_proxy_type or "socks5").lower()
    if t == "socks5":
        ptype = socks.SOCKS5
    elif t == "socks4":
        ptype = socks.SOCKS4
    elif t in ("http", "https"):
        ptype = socks.HTTP
    else:
        ptype = socks.SOCKS5

    if user or pwd:
        proxy_tuple = (ptype, host, port, True, user, pwd)
    else:
        proxy_tuple = (ptype, host, port)

    hostport = f"[{host}]:{port}" if ":" in host and not host.startswith("[") else f"{host}:{port}"
    return proxy_tuple, hostport

TG_PROXIES = {}
TG_PROXY_TYPE = "socks5"
TG_PROXY_DEFAULT = None
TG_USE_IPV6 = False
CONNECTION_CLASS = ConnectionTcpAbridged  # или ConnectionTcpObfuscated

def resolve_proxy_string_for(name: str):
    """
    Приоритет:
      1) ENV TG_PROXY_<NAME>
      2) sessions/<name>.proxy
      3) config.tg_proxies[name]
      4) config.tg_proxy_default
    """
    env_key = f"TG_PROXY_{name.upper()}"
    if os.environ.get(env_key):
        return os.environ[env_key].strip()

    sidecar = os.path.join(SESSION_DIR, f"{name}.proxy")
    if os.path.isfile(sidecar):
        try:
            with open(sidecar, "r", encoding="utf-8") as f:
                line = f.read().strip()
                if line:
                    return line
        except Exception:
            pass

    raw = TG_PROXIES.get(name) if isinstance(TG_PROXIES, dict) else None
    if raw:
        return raw.strip()

    if TG_PROXY_DEFAULT:
        return TG_PROXY_DEFAULT.strip()

    return None

# main.py
def _make_client(session_path: str, loop, proxy_tuple):
    """
    Создаёт TelegramClient, строго привязанный к loop и текущему классу соединения.
    """
    kwargs = {
        "connection": CONNECTION_CLASS,   # <-- используем глобальную настройку
        "use_ipv6": TG_USE_IPV6,
        "device_model": "CH Parser",
        "system_version": "Windows",
        "lang_code": "en",
        # лёгкий запас по таймаутам/ретраям — не обязательно, но стабилизирует проверки
        "timeout": 10,
        "request_retries": 2,
        "connection_retries": 2,
    }
    if proxy_tuple:
        kwargs["proxy"] = proxy_tuple
    if loop is None:
        loop = asyncio.new_event_loop()
    kwargs["loop"] = loop
    try:
        return TelegramClient(session_path, api_id, api_hash, **kwargs)
    except RuntimeError as e:
        if "no current event loop" in str(e).lower() or "no running event loop" in str(e).lower():
            loop = asyncio.new_event_loop()
            kwargs["loop"] = loop
            return TelegramClient(session_path, api_id, api_hash, **kwargs)
        raise



def apply_proxy_from_current_sources(session_name: str):
    ctx = get_account_context(session_name) if session_name in accounts else None
    loop = ctx["loop"] if ctx else asyncio.new_event_loop()
    session_path = os.path.join(SESSION_DIR, f"{session_name}.session")

    raw = resolve_proxy_string_for(session_name)
    parsed = parse_proxy_line(raw) if raw else None
    proxy_tuple, hostport = build_telethon_proxy(parsed, TG_PROXY_TYPE)

    try:
        asyncio.get_running_loop()
    except RuntimeError:
        asyncio.set_event_loop(loop)

    if ctx and ctx.get("client"):
        try:
            fut = asyncio.run_coroutine_threadsafe(ctx["client"].disconnect(), loop)
            try:
                fut.result(timeout=5)
            except Exception:
                pass
        except Exception:
            pass

    client = _make_client(session_path, loop, proxy_tuple)

    if not ctx:
        accounts[session_name] = {
            "client": client,
            "loop": loop,

            "loop_thread": None,
            "event_handler_added": False,
            "script_running": False,
            "my_msg_ids": {},
            "progress": {"status": "Ожидание запуска", "percent": 0},
            "found_channels": [],
            "joined_channels": set(),
            "joined_names": {},
            "joined_entities": {},
            "monitored_info": {},
            "comment_queue": [],
            "next_send_at": 0.0,
            "comment_worker_started": False,
            "comment_cooldown": COMMENT_COOLDOWN_SECONDS,
            "comment_seq": 0,
            "proxy_tuple": proxy_tuple,
            "proxy_hostport": hostport,
            "proxy_verified": False,
            "persona": None,
            "persona_name": None,
            # антиспам по супергруппам
            "group_last_sent": {},
            "group_sent_log": {},
            "restricted_until": 0.0,
            "campaign_paused": False,

        }

    else:
        ctx["client"] = client
        ctx["proxy_tuple"] = proxy_tuple
        ctx["proxy_hostport"] = hostport
        ctx["proxy_verified"] = False
        ctx["event_handler_added"] = False

    if proxy_tuple:
        log_proxy(session_name, "APPLY", proxy=hostport, details=f"type={TG_PROXY_TYPE};conn={CONNECTION_CLASS.__name__}")
    else:
        log_proxy(session_name, "INIT", details="no proxy -> BLOCK")

# ────────────────────────────────────────────────────────────────────────────────
# ПУЛ ПРОКСИ / АВТО-НАЗНАЧЕНИЕ
# ────────────────────────────────────────────────────────────────────────────────
PROXY_POOL_FILE = "proxies.txt"
PROXY_ASSIGN_FILE = "proxy_assignments.json"

def load_proxy_pool():
    path = PROXY_POOL_FILE or "proxies.txt"
    pool = []
    try:
        with open(path, 'r', encoding='utf-8') as f:
            for raw in f:
                s = raw.strip()
                if not s or s.startswith('#'):
                    continue
                if parse_proxy_line(s):
                    pool.append(s)
                else:
                    proxy_logger.info(f"POOL_BAD_LINE | DETAILS={s}")
    except FileNotFoundError:
        pass
    return pool

def _load_proxy_assignments():
    try:
        with open(PROXY_ASSIGN_FILE, 'r', encoding='utf-8') as f:
            return json.load(f)
    except FileNotFoundError:
        return {}

def _save_proxy_assignments(d: dict):
    with open(PROXY_ASSIGN_FILE, 'w', encoding='utf-8') as f:
        json.dump(d, f, ensure_ascii=False, indent=2)
def filter_proxy_candidates(session_name: str, force: bool = False, filters: Optional[dict] = None) -> List[str]:
    """
    Возвращает список строк прокси из пула с учётом фильтров.
    filters:
      - countries: List[str]  (ISO-коды стран, верхний регистр)
      - only_ok: bool         (только прошедшие проверку OK)
      - occupancy: str        ('free_only' | 'busy_only' | 'any')
    Поведение:
      - если указан countries -> исключаем прокси без страны/не из списка
      - only_ok=True -> исключаем без health или с ok=False
      - occupancy:
          * free_only: used_by пуст
          * busy_only: used_by не пуст
          * any: без фильтра
      - если force=True и у аккаунта уже есть sidecar -> исключаем этот же прокси, чтобы реально сменить
    """
    filters = filters or {}
    countries = {c.upper() for c in (filters.get("countries") or []) if isinstance(c, str) and c.strip()}
    only_ok = bool(filters.get("only_ok", False))
    occupancy = (filters.get("occupancy") or "any").lower()

    pool = load_proxy_pool()
    if not pool:
        return []

    health = load_proxy_health() or {}
    items = health.get("items", {}) or {}

    assigns = _load_proxy_assignments()
    # used_by по строке
    used_by = {}
    for acc, ln in assigns.items():
        used_by.setdefault(ln, []).append(acc)

    # текущий прокси у аккаунта (чтобы не переиспользовать при force=True)
    sidecar = os.path.join(SESSION_DIR, f"{session_name}.proxy")
    current_line = None
    if os.path.isfile(sidecar):
        try:
            with open(sidecar, "r", encoding="utf-8") as f:
                current_line = f.read().strip() or None
        except Exception:
            pass

    out = []
    for line in pool:
        # countries
        if countries:
            cc = (items.get(line) or {}).get("country_code")
            if not cc or cc.upper() not in countries:
                continue

        # only_ok
        if only_ok:
            ok = (items.get(line) or {}).get("ok", None)
            if ok is not True:
                continue

        # occupancy
        ub = used_by.get(line, [])
        if occupancy == "free_only":
            if len(ub) > 0:
                continue
        elif occupancy == "busy_only":
            if len(ub) == 0:
                continue
        # 'any' — без ограничения

        # если force — не предлагать тот же самый прокси
        if force and current_line and line == current_line:
            continue

        out.append(line)

    return out
def auto_assign_proxy(session_name: str, force: bool = False, filters: Optional[dict] = None):
    """
    Автоподбор прокси с учётом filters (см. filter_proxy_candidates).
    Возвращает (assigned: bool, line: Optional[str]).
    """
    sidecar = os.path.join(SESSION_DIR, f"{session_name}.proxy")
    if os.path.isfile(sidecar) and not force:
        # уже назначен, а force=False — не трогаем
        return False, None

    pool = load_proxy_pool()
    if not pool:
        log_proxy(session_name, "ASSIGN_FAIL", details="proxy pool empty")
        return False, None

    # — новая фильтрация —
    candidates = filter_proxy_candidates(session_name, force=force, filters=filters)
    if not candidates:
        # Fallback: если фильтры ничего не дали — НЕ назначаем (чтобы поведение было явным)
        log_proxy(session_name, "ASSIGN_FAIL", details=f"no candidates for filters={filters or {}}")
        return False, None

    # если force=False — прежняя логика исключать уже используемые другими
    if not force:
        assigns = _load_proxy_assignments()
        used = set(assigns.values())
        candidates = [p for p in candidates if p not in used] or candidates

    chosen = random.choice(candidates)

    os.makedirs(SESSION_DIR, exist_ok=True)
    with open(sidecar, "w", encoding="utf-8") as f:
        f.write(chosen + "\n")

    assigns = _load_proxy_assignments()
    assigns[session_name] = chosen
    _save_proxy_assignments(assigns)

    parsed = parse_proxy_line(chosen)
    _, hostport = build_telethon_proxy(parsed, TG_PROXY_TYPE)
    log_proxy(session_name, "ASSIGN", proxy=hostport, details=f"auto; filters={filters or {}}")

    apply_proxy_from_current_sources(session_name)
    return True, chosen


# ────────────────────────────────────────────────────────────────────────────────
# ПРОВЕРКА РАБОТОСПОСОБНОСТИ ПРОКСИ (общая, не привязанная к аккаунту)
# ────────────────────────────────────────────────────────────────────────────────
PROXY_HEALTH_FILE = "proxy_health.json"
# --- GEO helpers --------------------------------------------------------------
def _build_requests_proxies(parsed: dict):
    """
    Сборка proxies-словаря для requests через SOCKS/HTTP прокси.
    Для SOCKS5 используем 'socks5h' (DNS через прокси), для SOCKS4 — 'socks4a'.
    """
    if not parsed:
        return None
    t = (TG_PROXY_TYPE or "socks5").lower()
    if t.startswith("socks5"):
        scheme = "socks5h"
    elif t.startswith("socks4"):
        scheme = "socks4a"
    else:
        scheme = "http"

    auth = ""
    if parsed.get("user") or parsed.get("pass"):
        u = parsed.get("user") or ""
        p = parsed.get("pass") or ""
        auth = f"{u}:{p}@"

    url = f"{scheme}://{auth}{parsed['host']}:{parsed['port']}"
    return {"http": url, "https": url}


def _detect_proxy_country_via_http(line: str, timeout: int = 6):
    """
    Пытаемся выяснить внешний IP и страну, ходя в сеть ЧЕРЕЗ сам прокси.
    1) Внешний IP берём с api.ipify.org (или ifconfig.me резервно)
    2) Страну берём с ip-api.com по этому IP (резервно ipinfo.io)
    Возвращает dict с ключами: {'ip','country','country_code'} либо None.
    """
    parsed = parse_proxy_line(line)
    if not parsed:
        return None

    proxies = _build_requests_proxies(parsed)
    ip = None

    # 1) Внешний IP
    try:
        r = requests.get("https://api.ipify.org?format=json", timeout=timeout, proxies=proxies)
        if r.ok:
            ip = (r.json() or {}).get("ip")
    except Exception:
        pass
    if not ip:
        try:
            r = requests.get("https://ifconfig.me/ip", timeout=timeout, proxies=proxies)
            if r.ok:
                ip = (r.text or "").strip()
        except Exception:
            pass

    ip_or_host = ip or parsed["host"]

    # 2) Гео по IP/хосту (ip-api)
    country = None
    cc = None
    try:
        r = requests.get(
            f"http://ip-api.com/json/{ip_or_host}?fields=status,country,countryCode,query",
            timeout=timeout
        )
        j = r.json() if r.ok else {}
        if j.get("status") == "success":
            country = j.get("country")
            cc = j.get("countryCode")
            ip = j.get("query", ip)
    except Exception:
        pass

    # Резерв: ipinfo.io (даёт хотя бы country code)
    if not country:
        try:
            r = requests.get(f"https://ipinfo.io/{ip_or_host}/json", timeout=timeout)
            j = r.json() if r.ok else {}
            # ipinfo чаще всего отдаёт только код в 'country'
            cc = cc or j.get("country")
            # нормализуем country по коду (без внешних справочников оставляем только код)
            country = country or None
            if not ip:
                ip = j.get("ip") or ip
        except Exception:
            pass

    out = {}
    if ip:
        out["ip"] = ip
    if cc:
        out["country_code"] = cc
    if country:
        out["country"] = country
    return out or None


def load_proxy_health():
    try:
        with open(PROXY_HEALTH_FILE, 'r', encoding='utf-8') as f:
            return json.load(f)
    except FileNotFoundError:
        return {"updated_at": None, "items": {}}
    except Exception:
        return {"updated_at": None, "items": {}}


def save_proxy_health(data: dict):
    try:
        with open(PROXY_HEALTH_FILE, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except Exception as e:
        logging.warning(f"[proxy_health] save failed: {e}")


async def _verify_proxy_line_once(proxy_tuple, conn_cls) -> (bool, str):
    """Пытаемся подключиться и сделать лёгкий запрос. Возвращаем (ok, errstr|None)."""
    loop = asyncio.get_event_loop()
    try:
        client = TelegramClient(
            StringSession(),
            api_id, api_hash,
            loop=loop,
            use_ipv6=TG_USE_IPV6,
            connection=conn_cls,
            timeout=10,
            request_retries=2,
            connection_retries=2,
            proxy=proxy_tuple
        )
        await client.connect()
        await client(functions.help.GetNearestDcRequest())
        try:
            await client.disconnect()
        except Exception:
            pass
        return True, None
    except Exception as e:
        return False, str(e)


async def verify_proxy_line(line: str) -> (bool, str):
    """Проверка одного прокси по строке из пула. Пробуем Abridged → Obfuscated."""
    parsed = parse_proxy_line(line)
    if not parsed:
        return False, "bad line format"
    proxy_tuple, _hp = build_telethon_proxy(parsed, TG_PROXY_TYPE)
    if not proxy_tuple:
        return False, "cannot build proxy tuple"

    ok, err = await _verify_proxy_line_once(proxy_tuple, ConnectionTcpAbridged)
    if ok:
        return True, None

    # если на abridged не пошло — пробуем obfuscated
    ok2, err2 = await _verify_proxy_line_once(proxy_tuple, ConnectionTcpObfuscated)
    if ok2:
        return True, None

    # вернём более информативную ошибку
    return False, (err2 or err or "unknown")


async def check_proxy_pool_async(concurrency: int = 20, per_timeout: int = 20) -> dict:
    """
    Асинхронно проверяет все прокси из пула. Возвращает:
    { line: {ok: bool, error: str|None, hostport: str} }
    """
    pool = load_proxy_pool()
    results = {}

    if not pool:
        return results

    sem = asyncio.Semaphore(concurrency)

    async def worker(line: str):
        parsed = parse_proxy_line(line)
        _, hp = build_telethon_proxy(parsed, TG_PROXY_TYPE) if parsed else (None, None)
        async with sem:
            try:
                res = await asyncio.wait_for(verify_proxy_line(line), timeout=per_timeout)
                ok, err = res
            except asyncio.TimeoutError:
                ok, err = False, "timeout"
            except Exception as e:
                ok, err = False, str(e)
        results[line] = {"ok": bool(ok), "error": (err or None), "hostport": hp}

    await asyncio.gather(*(worker(l) for l in pool))
    return results


def check_proxy_pool_sync() -> dict:
    """
    Синхронная обёртка: проверяет все прокси, добавляет used_by и сохраняет в файл.
    Возвращает {"updated_at": ts, "items": {line: {...}}}
    """
    loop = asyncio.new_event_loop()
    try:
        asyncio.set_event_loop(loop)
        base = loop.run_until_complete(check_proxy_pool_async())
    finally:
        try:
            loop.close()
        except Exception:
            pass

    assigns = _load_proxy_assignments()
    used_by_map = {}
    for acc, ln in assigns.items():
        used_by_map.setdefault(ln, []).append(acc)

    now = int(time.time())
    full = {"updated_at": now, "items": {}}
    for line, info in base.items():
        item = dict(info)
        item["used_by"] = used_by_map.get(line, [])
        item["checked_at"] = now
        full["items"][line] = item
    now = int(time.time())
    full = {"updated_at": now, "items": {}}
    for line, info in base.items():
        item = dict(info)
        item["used_by"] = used_by_map.get(line, [])
        item["checked_at"] = now

        # ✚ Гео-данные (пускаем даже на FAIL, но надёжнее на OK)
        try:
            geo = _detect_proxy_country_via_http(line)
            if geo:
                item.update(geo)  # ip, country, country_code
        except Exception:
            pass

        full["items"][line] = item

    save_proxy_health(full)
    return full


def check_single_proxy_sync(line: str) -> dict:
    """
    Проверка одного прокси и обновление файла здоровья точечно.
    Возвращает {line: {...}}, а также обновляет updated_at.
    """
    loop = asyncio.new_event_loop()
    try:
        asyncio.set_event_loop(loop)
        ok, err = loop.run_until_complete(verify_proxy_line(line))
    finally:
        try:
            loop.close()
        except Exception:
            pass

    parsed = parse_proxy_line(line)
    _, hp = build_telethon_proxy(parsed, TG_PROXY_TYPE) if parsed else (None, None)

    assigns = _load_proxy_assignments()
    used_by = [acc for acc, ln in assigns.items() if ln == line]

    now = int(time.time())
    cur = load_proxy_health()
    cur["updated_at"] = now
    cur.setdefault("items", {})
    cur["items"][line] = {
        "ok": bool(ok),
        "error": (err or None),
        "hostport": hp,
        "used_by": used_by,
        "checked_at": now
    }
    try:
        geo = _detect_proxy_country_via_http(line)
        if geo:
            cur["items"][line].update(geo)
    except Exception:
        pass

    save_proxy_health(cur)
    return {line: cur["items"][line]}


def clear_assigned_proxy(session_name: str):
    sidecar = os.path.join(SESSION_DIR, f"{session_name}.proxy")
    sidecar_removed = False
    if os.path.exists(sidecar):
        try:
            os.remove(sidecar)
            sidecar_removed = True
        except Exception:
            pass

    assigns = _load_proxy_assignments()
    assign_removed = assigns.pop(session_name, None) is not None
    _save_proxy_assignments(assigns)

    try:
        TG_PROXIES.pop(session_name, None)
    except Exception:
        pass

    apply_proxy_from_current_sources(session_name)
    ctx = get_account_context(session_name)
    ctx["proxy_verified"] = False
    log_proxy(session_name, "CLEAR", proxy=ctx.get("proxy_hostport"), details=f"sidecar={sidecar_removed};assign={assign_removed}")
    return {"sidecar_removed": sidecar_removed, "assign_removed": assign_removed}

# ────────────────────────────────────────────────────────────────────────────────
# main.py
def delete_session(name: str, remove_proxy: bool = True) -> dict:
    """
    Удалить аккаунт:
      - отключить клиента и остановить его цикл
      - удалить sessions/<name>.session
      - опционально удалить sessions/<name>.proxy и убрать назначение из proxy_assignments.json
      - убрать из available_sessions и accounts
      - почистить сохранённое состояние и привязку персоны
      - скорректировать active_session_name
    Возвращает подробный отчёт.
    """
    result = {
        "name": name,
        "disconnected": False,
        "session_removed": False,
        "proxy_sidecar_removed": False,
        "proxy_assignment_removed": False,
        "removed_from_available": False,
        "removed_from_state": False,
        "removed_from_accounts_map": False,
        "active_switched_to": None,
    }

    # 1) Отключаем клиента и останавливаем цикл
    ctx = accounts.get(name)
    if ctx:
        try:
            loop = ctx.get("loop")
            client = ctx.get("client")
            if loop and client:
                try:
                    fut = asyncio.run_coroutine_threadsafe(client.disconnect(), loop)
                    try:
                        fut.result(timeout=5)
                    except Exception:
                        pass
                except Exception:
                    pass
            # останавливаем цикл и ждём поток
            try:
                if loop and loop.is_running():
                    loop.call_soon_threadsafe(loop.stop)
                t = ctx.get("loop_thread")
                if t and t.is_alive():
                    t.join(timeout=2)
            except Exception:
                pass
            result["disconnected"] = True
        except Exception:
            pass

    # 2) Удаляем .session
    try:
        sp = os.path.join(SESSION_DIR, f"{name}.session")
        if os.path.exists(sp):
            os.remove(sp)
            result["session_removed"] = True
    except Exception:
        pass

    # 3) Чистим .proxy и назначения (без пересоздания клиента)
    if remove_proxy:
        # sidecar
        try:
            pp = os.path.join(SESSION_DIR, f"{name}.proxy")
            if os.path.exists(pp):
                os.remove(pp)
                result["proxy_sidecar_removed"] = True
        except Exception:
            pass
        # assignments
        try:
            assigns = _load_proxy_assignments()
            if assigns.pop(name, None) is not None:
                _save_proxy_assignments(assigns)
                result["proxy_assignment_removed"] = True
        except Exception:
            pass
        # на всякий — убрать из TG_PROXIES
        try:
            TG_PROXIES.pop(name, None)
        except Exception:
            pass

    # 4) Убираем из списков и контекстов
    try:
        if name in available_sessions:
            available_sessions.remove(name)
            result["removed_from_available"] = True
    except Exception:
        pass
    try:
        accounts.pop(name, None)
    except Exception:
        pass

    # 5) Чистим сохранённое состояние
    try:
        st = load_state()
        if isinstance(st, dict) and name in st:
            st.pop(name, None)
            save_state(st)
            result["removed_from_state"] = True
    except Exception:
        pass

    # 6) Чистим маппинг аккаунт→персона
    try:
        amap = load_accounts_map()
        if isinstance(amap, dict) and name in amap:
            amap.pop(name, None)
            save_accounts_map(amap)
            result["removed_from_accounts_map"] = True
    except Exception:
        pass

    # 7) Перескан — чтобы синхронизировать всё вокруг
    try:
        refresh_sessions(auto_assign_missing_proxy=False)
    except Exception:
        pass

    # 8) Активный → переключить, если нужно
    global active_session_name
    if active_session_name == name:
        active_session_name = available_sessions[0] if available_sessions else None
        result["active_switched_to"] = active_session_name

    return result

def get_account_context(name):
    """Ленивая инициализация TelegramClient и контекста (строго через прокси)."""
    if name not in accounts:
        loop = asyncio.new_event_loop()
        session_path = os.path.join(SESSION_DIR, f"{name}.session")

        raw = resolve_proxy_string_for(name)
        parsed = parse_proxy_line(raw) if raw else None
        proxy_tuple, hostport = build_telethon_proxy(parsed, TG_PROXY_TYPE)

        client = _make_client(session_path, loop, proxy_tuple)

        accounts[name] = {
            "client": client,
            "loop": loop,
            "loop_thread": None,
            "event_handler_added": False,
            "script_running": False,
            "my_msg_ids": {},
            "progress": {"status": "Ожидание запуска", "percent": 0},
            "found_channels": [],
            "joined_channels": set(),
            "joined_names": {},
            "joined_entities": {},
            "monitored_info": {},

            # Комментарии
            "comment_queue": [],
            "next_send_at": 0.0,
            "comment_worker_started": False,
            "comment_cooldown": COMMENT_COOLDOWN_SECONDS,
            "comment_seq": 0,

            #  Подписки
            "join_queue": deque(),  # FIFO очередь ссылок на вступление
            "join_worker_started": False,  # воркер запущен?
            "next_join_at": 0.0,  # когда можно делать следующий join
            "join_daily_count": 0,  # сколько уже сделали сегодня
            "join_daily_reset_ts": 0.0,  # когда обнулить счётчик

            "proxy_tuple": proxy_tuple,
            "proxy_hostport": hostport,
            "proxy_verified": False,
            "persona": None,
            "persona_name": None,

            # антиспам по супергруппам
            "group_last_sent": {},
            "group_sent_log": {},
            "restricted_until": 0.0,
            "campaign_paused": False,
            "last_commented_post_id": {},

        }

        if not proxy_tuple:
            log_proxy(name, "INIT", details="no proxy in sources -> BLOCK")
        else:
            log_proxy(name, "APPLY", proxy=hostport, details=f"type={TG_PROXY_TYPE};conn={CONNECTION_CLASS.__name__}")
    return accounts[name]

# 1) Загрузить сохранённое состояние
saved = load_state()

# 2) Сканируем sessions/
if os.path.isdir(SESSION_DIR):
    for file in os.listdir(SESSION_DIR):
        if file.endswith('.session'):
            name = file[:-8]
            available_sessions.append(name)

# 3) Если один аккаунт — делаем активным
if len(available_sessions) == 1:
    active_session_name = available_sessions[0]

# ────────────────────────────────────────────────────────────────────────────────
# MISTRAL & GEMINI SETTINGS
# ────────────────────────────────────────────────────────────────────────────────
MISTRAL_API_KEY   = os.environ.get("MISTRAL_API_KEY", "")
MISTRAL_MODEL     = os.environ.get("MISTRAL_MODEL", "mistral-large-latest")
UNIVERSAL_PROMPT  = ""
MISTRAL_CHAT_KEY  = ""

PROMPT_VARIANTS: List[str] = [
    "Ответь парой слов по теме поста.",
    "Короткий уместный отклик (1–3 слова).",
    "Скажи что-то естественное и коротко (до 3 слов).",
    "Короткий комментарий как у живого подписчика.",
    "Мини-реакция по сути (не более 3 слов).",
    "Без эмодзи и хэштегов, максимум 3 слова.",
    "Избегай клише, будь простым (1–3 слова).",
]

PERSONAS: Dict[str, Dict] = {
    "casual":  {"phrases": ["Круто", "Норм идея", "Годно", "В точку"], "typo_prob": 0.05},
    "serious": {"phrases": ["Актуально", "Интересно, да", "Уместно", "Солидно"], "typo_prob": 0.04},
    "funny":   {"phrases": ["Смешно", "Забавно", "Звучит ок", "Пойдёт"], "typo_prob": 0.07}
}

try:
    with open('config.json', 'r', encoding='utf-8') as cf:
        config = json.load(cf)

        if not MISTRAL_API_KEY:
            MISTRAL_API_KEY = config.get("mistral_api_key", "")
        MISTRAL_MODEL    = config.get("mistral_model", MISTRAL_MODEL)

        _pvar = config.get("prompt_variants")
        if isinstance(_pvar, list) and _pvar:
            PROMPT_VARIANTS = _pvar

        UNIVERSAL_PROMPT = config.get("universal_prompt", UNIVERSAL_PROMPT)
        MISTRAL_CHAT_KEY = config.get("mistral_chat_key", "")

        GEMINI_API_KEY = config.get("gemini_api_key", "")
        if GEMINI_API_KEY:
            os.environ.setdefault("GEMINI_API_KEY", GEMINI_API_KEY)

        COMMENT_COOLDOWN_SECONDS = int(config.get("comment_cooldown_seconds", COMMENT_COOLDOWN_SECONDS))
        POST_DELAY_SECONDS = int(config.get("post_delay_seconds", POST_DELAY_SECONDS))

        TG_PROXIES = config.get("tg_proxies", {})
        TG_PROXY_TYPE = (config.get("tg_proxy_type", "socks5") or "socks5").lower()
        TG_PROXY_DEFAULT = config.get("tg_proxy_default", None)

        PROXY_POOL_FILE = config.get("tg_proxy_pool_file", PROXY_POOL_FILE)
        # ✚ Настройки аватарок из config.json (имеют приоритет над .env)
        AVATAR_POOL_DIR = config.get("avatar_pool_dir", AVATAR_POOL_DIR) or AVATAR_POOL_DIR
        AVATAR_CACHE_DIR = config.get("avatar_cache_dir", AVATAR_CACHE_DIR) or AVATAR_CACHE_DIR
        PROFILE_UPDATE_INTERVAL_SECONDS = int(
            config.get("profile_update_interval_seconds", PROFILE_UPDATE_INTERVAL_SECONDS))
        PROFILE_UPDATE_DAILY_LIMIT = int(config.get("profile_update_daily_limit", PROFILE_UPDATE_DAILY_LIMIT))

        DESYNC_MIN_SECONDS = int(config.get("desync_min_seconds", DESYNC_MIN_SECONDS))
        DESYNC_MAX_SECONDS = int(config.get("desync_max_seconds", DESYNC_MAX_SECONDS))
        DEDUP_HISTORY_SIZE = int(config.get("dedup_history_size", DEDUP_HISTORY_SIZE))
        # антиспам в супергруппах из config.json
        GROUP_REPLY_PROB = float(config.get("group_reply_prob", GROUP_REPLY_PROB))
        GROUP_MIN_GAP_SECONDS = int(config.get("group_min_gap_seconds", GROUP_MIN_GAP_SECONDS))
        GROUP_MAX_PER_HOUR = int(config.get("group_max_per_hour", GROUP_MAX_PER_HOUR))

        _personas = config.get("personas")
        if isinstance(_personas, dict) and _personas:
            for k, v in _personas.items():
                if k in PERSONAS and isinstance(v, dict):
                    merged = dict(PERSONAS[k]); merged.update(v); PERSONAS[k] = merged
                elif isinstance(v, dict):
                    PERSONAS[k] = v

        DEFAULT_TYPO_PROB = float(config.get("default_typo_prob", DEFAULT_TYPO_PROB))

        TG_USE_IPV6 = bool(config.get("tg_use_ipv6", TG_USE_IPV6))

        tg_conn = (config.get("tg_connection", "abridged") or "abridged").lower()
        if tg_conn == "obfuscated":
            CONNECTION_CLASS = ConnectionTcpObfuscated
        else:
            CONNECTION_CLASS = ConnectionTcpAbridged

except FileNotFoundError:
    config = {}
    TG_PROXIES = {}
    TG_PROXY_TYPE = "socks5"
    TG_PROXY_DEFAULT = None
    TG_USE_IPV6 = False
    CONNECTION_CLASS = ConnectionTcpAbridged

MISTRAL_URL = "https://api.mistral.ai/v1/chat/completions"

# автоподбор тем, у кого прокси не задан
for _name in available_sessions:
    if not resolve_proxy_string_for(_name):
        auto_assign_proxy(_name, force=False)

# Инициализируем контексты и персоны
_accounts_map = load_accounts_map()
for name in available_sessions:
    ctx = get_account_context(name)
    if name in saved:
        st = saved[name]
        ctx["joined_channels"] = set(st.get("joined_channels", []))
        ctx["joined_names"]    = st.get("joined_names", {})
        ctx["monitored_info"]  = {int(k): v for k, v in st.get("monitored_info", {}).items()}
        ctx["restricted_until"] = float(st.get("restricted_until", 0.0))
    ctx["comment_cooldown"] = COMMENT_COOLDOWN_SECONDS

    persona_name = assign_persona(name, PERSONAS, _accounts_map)
    persona_data = dict(PERSONAS.get(persona_name or "", {}))
    if "typo_prob" not in persona_data:
        persona_data["typo_prob"] = DEFAULT_TYPO_PROB
    ctx["persona"] = persona_data
    ctx["persona_name"] = persona_name
    logging.info(f"[persona] account={name} persona={persona_name} -> {persona_data}")


# АНТИ-ДУБЛЬ
# ────────────────────────────────────────────────────────────────────────────────
LAST_SENT_TEXT_BY_DISC: Dict[int, deque] = defaultdict(lambda: deque(maxlen=DEDUP_HISTORY_SIZE))
# ────────────────────────────────────────────────────────────────────────────────
# HOLD/blacklist для дискуссий (чтобы не долбить туда без шансов)
# ────────────────────────────────────────────────────────────────────────────────
# BLOCKED_DISCUSSIONS[account][disc_id] = {"reason": str, "hold_until": ts}
BLOCKED_DISCUSSIONS: Dict[str, Dict[int, dict]] = defaultdict(dict)

def _is_disc_blocked(account: str, disc_id: int) -> Optional[dict]:
    item = BLOCKED_DISCUSSIONS.get(account, {}).get(int(disc_id))
    if not item:
        return None
    if time.time() >= float(item.get("hold_until", 0)):
        try:
            BLOCKED_DISCUSSIONS[account].pop(int(disc_id), None)
        except Exception:
            pass
        return None
    return item

def _block_disc(account: str, disc_id: int, reason: str, hold_sec: int = 3600) -> None:
    BLOCKED_DISCUSSIONS[account][int(disc_id)] = {
        "reason": reason,
        "hold_until": time.time() + max(1, int(hold_sec))
    }
    _log_comment(account, "WRITE_BLOCKED", DISC_ID=int(disc_id),
                 ERROR=reason, ETA_SEC=hold_sec)

def _normalize_text_for_dedup(s: str) -> str:
    s = (s or "").strip().lower()
    for ch in [".", "!", "?", ",", ";", "—", "-", "…"]:
        s = s.replace(ch, " ")
    s = " ".join(s.split())
    return s

def _collect_pending_texts_for_disc(disc_id: int) -> Set[str]:
    seen: Set[str] = set()
    for ctx in accounts.values():
        for ready_at, task in ctx.get("comment_queue", []):
            if task.get("disc_id") == disc_id:
                seen.add(_normalize_text_for_dedup(task.get("text", "")))
    return seen

def _pick_prompt_variant() -> str:
    return random.choice(PROMPT_VARIANTS) if PROMPT_VARIANTS else ""

def _maybe_typo(word: str) -> str:
    if len(word) < 4:
        return word
    i = random.randint(0, len(word) - 2)
    lst = list(word)
    lst[i], lst[i+1] = lst[i+1], lst[i]
    return "".join(lst)

def _apply_persona_style(text: str, persona: Dict) -> str:
    if not persona:
        return text
    phrases = persona.get("phrases") or []
    typo_prob = float(persona.get("typo_prob", DEFAULT_TYPO_PROB))
    t = text.strip()

    GENERIC = {"интересно", "интересно.", "интересно, спасибо", "неплохо", "круто", "класс", "здорово"}
    if phrases and _normalize_text_for_dedup(t) in { _normalize_text_for_dedup(x) for x in GENERIC }:
        if random.random() < 0.5:
            t = random.choice(phrases)

    if random.random() < typo_prob:
        parts = t.split()
        if parts:
            idx = random.randrange(len(parts))
            parts[idx] = _maybe_typo(parts[idx])
            t = " ".join(parts)

    parts = t.replace("\n", " ").split()
    if len(parts) > 20:
        t = " ".join(parts[:20])
    return t

def _enforce_cinema_pitch(text: str) -> str:
    """
    Гарантирует наличие слова «кинотеатр» и законченной вставки про «...в профиле».
    """
    if not text:
        return text

    t = " ".join((text or "").split())
    low = t.lower().strip(" '\"«»”’")

    # выкинуть лишние кавычки и хвосты
    t = low.strip(" '\"«»”’").capitalize()

    # если модель ушла в отказ/извинения — заменим на нейтральную болванку
    if any(x in low for x in ("извин", "не могу помочь", "не могу с этим", "не буду")):
        t = "Лучше просто отвлечься вечером — в профиле у меня есть ссылка на бесплатный онлайн-кинотеатр."

    # обязательное слово «кинотеатр»
    has_cinema = ("кинотеатр" in t)

    # обязательная «привязка» к профилю (варианты)
    profile_ok = any(p in t for p in (
        "в профиле", "в моём профиле", "в био", "у меня наверху"
    ))

    # чинить обрыв «ссылка на ...»
    if re.search(r"(ссылка на|ссылк[ау] на)$", t):
        t += " бесплатный онлайн-кинотеатр"

    if not has_cinema:
        # мягко вшиваем ключ
        if t.endswith("."):
            t = t[:-1]
        t += " — у меня в профиле есть ссылка на бесплатный онлайн-кинотеатр"

    if not profile_ok:
        # уточняем «где»
        if "кинотеатр" not in t:
            t += " — кинотеатр"
        if not t.endswith("."):
            t += "."
        t += " В профиле есть ссылка."

    # ограничение длины — но не обрываем на «ссылка на»
    words = t.split()
    if len(words) > 20:
        t = " ".join(words[:20])
        if re.search(r"(ссылка на|кинотеатр)$", t) and not t.endswith("."):
            t += "."
    # закрыть точкой, если вдруг нет
    if not t.endswith((".", "!", "?")):
        t += "."

    # финальная чистка двойных пробелов/кавычек
    t = " ".join(t.replace("..", ".").split())
    t = t.strip(" '\"«»”’")
    return t

def _local_variation(candidate: str, forbidden_norm: Set[str], persona: Dict) -> Optional[str]:
    seeds = [
        candidate,
        candidate.replace(".", "").replace("!", ""),
        "очень " + candidate,
        "прям " + candidate,
        "в целом " + candidate,
        candidate + " же",
        candidate + " ведь",
    ]
    persona_phrases = (persona or {}).get("phrases") or []
    seeds.extend(persona_phrases)
    seeds.extend(["любопытно", "годно", "резонно", "верно", "в точку", "согласен", "понятно", "неплохо"])
    for s in seeds:
        s = " ".join(s.split())
        parts = s.split()
        if len(parts) > 5:
            s = " ".join(parts[:5])
        if _normalize_text_for_dedup(s) not in forbidden_norm and s.strip():
            return s.strip()
    return None


# ХЕЛПЕРЫ КОННЕКТА
# ────────────────────────────────────────────────────────────────────────────────
async def ensure_client_ready(session_name: str, require_auth: bool = True, enforce_proxy: bool = True) -> bool:
    """
    Безопасный коннект. По умолчанию БЛОКИРУЕТСЯ, если прокси не верифицирован.
    """
    ctx = get_account_context(session_name)

    if enforce_proxy and not ctx.get("proxy_verified", False):
        log_proxy(session_name, "ENFORCE_BLOCK", proxy=ctx.get("proxy_hostport"), details="ensure_client_ready")
        raise RuntimeError("proxy_not_verified")

    client = ctx["client"]

    # если нет прокси-тюпла — вообще не коннектимся
    if not client.is_connected():
        if not ctx.get("proxy_tuple"):
            raise RuntimeError("proxy_missing")
        await client.connect()

    if require_auth:
        if not await client.is_user_authorized():
            raise RuntimeError("Session is not authorized. Use register_session.py to log in.")
    return True

# main.py (где-нибудь рядом с другими корутинами)
async def ensure_client_closed(name: str):
    """
    Отключает Telethon-клиент и освобождает файловые дескрипторы .session.
    Безопасно вызывать даже если клиента нет.
    """
    ctx = accounts.get(name) or {}
    client = ctx.get("client")
    if not client:
        return
    try:
        # мягко отрубим сеть
        await client.disconnect()
    except Exception:
        pass
    # попытка закрыть бэкенд сессии (у SQLiteSession есть close/delete/save)
    try:
        s = getattr(client, "session", None)
        if s:
            if hasattr(s, "save"):
                s.save()
            if hasattr(s, "close"):
                s.close()
    except Exception:
        pass
    # отпустим ссылку
    ctx["client"] = None
    ctx["event_handler_added"] = False

# ────────────────────────────────────────────────────────────────────────────────
# Проверка здоровья/валидности аккаунта
# ────────────────────────────────────────────────────────────────────────────────
async def check_account_health(session_name: str) -> Dict:
    """
    Комплексная проверка (безопасная):
      - коннект через верифицированный прокси
      - авторизация
      - get_me (детект бан/деактивации)
      - лёгкий API-пинг: help.GetConfigRequest()  ← БЕЗ contacts.GetStatuses
      - проба записи в "Saved Messages" (детект запрета записи)
      - + отдаём статус карантина (restricted / restricted_until)
    """
    ctx = get_account_context(session_name)
    client = ctx["client"]
    res = {
        "authorized": False,
        "banned": False,
        "deactivated": False,
        "api_ok": None,
        "can_send_to_self": None,
        "flood_wait": None,
        "username": None,
        "phone": None,
        "error": None,
        # карантинные поля сразу «как есть»
        "restricted": is_restricted(session_name),
        "restricted_until": int(ctx.get("restricted_until") or 0),
    }

    # 0) Жёсткая отсечка без прокси
    if not _enforce_proxy_or_block(session_name, "check_account_health"):
        res["error"] = "proxy_not_verified"
        return res

    # 1) Коннект (без обязательной авторизации), НО только через подтверждённый прокси
    try:
        await ensure_client_ready(session_name, require_auth=False, enforce_proxy=True)
    except Exception as e:
        res["error"] = f"connect: {e}"
        return res

    # 2) Авторизация
    try:
        res["authorized"] = await client.is_user_authorized()
    except Exception as e:
        res["error"] = f"is_authorized: {e}"
        return res
    if not res["authorized"]:
        return res

    # 3) Информация о себе (ловим баны/деактивации)
    try:
        me = await client.get_me()
        res["username"] = getattr(me, "username", None)
        res["phone"] = getattr(me, "phone", None)
    except UserDeactivatedBanError as e:
        res["banned"] = True
        res["authorized"] = False
        res["error"] = str(e)
        return res
    except UserDeactivatedError as e:
        res["deactivated"] = True
        res["authorized"] = False
        res["error"] = str(e)
        return res
    except (AuthKeyUnregisteredError,) as e:
        res["authorized"] = False
        res["error"] = str(e)
        return res
    except RPCError as e:
        res["error"] = f"get_me: {e}"
        return res
    except Exception as e:
        res["error"] = f"get_me: {e}"
        return res

    # 4) Лёгкий API-пинг — БЕЗ contacts.GetStatusesRequest()
    try:
        await client(functions.help.GetConfigRequest())
        res["api_ok"] = True
    except FloodWaitError as e:
        res["api_ok"] = False
        res["flood_wait"] = max(res["flood_wait"] or 0, int(getattr(e, "seconds", 0) or 0))
    except RPCError as e:
        # если пришёл FROZEN_* → карантин
        msg = (getattr(e, "message", "") or str(e) or "").upper()
        if "FROZEN" in msg:
            res["api_ok"] = False
            res["restricted"] = True
            until = mark_restricted(session_name, reason="frozen_method")
            res["restricted_until"] = int(until)
            res["error"] = "frozen_method"
        else:
            res["api_ok"] = False
            res["error"] = f"api: {e}"
    except Exception as e:
        res["api_ok"] = False
        res["error"] = f"api: {e}"

    # 5) Отправка в Saved Messages — ловим write-ban и тоже ставим карантин
    try:
        msg = await client.send_message("me", f"healthcheck {int(time.time())}")
        try:
            await asyncio.sleep(0.05)
            await client.delete_messages("me", [msg.id])
        except Exception:
            pass
        res["can_send_to_self"] = True
    except FloodWaitError as e:
        res["can_send_to_self"] = False
        res["flood_wait"] = max(res["flood_wait"] or 0, int(getattr(e, "seconds", 0) or 0))
    except ChatWriteForbiddenError as e:
        res["can_send_to_self"] = False
        res["restricted"] = True
        until = mark_restricted(session_name, reason="write_forbidden_me")
        res["restricted_until"] = int(until)
        res["error"] = f"write_forbidden: {e}"
    except RPCError as e:
        msg = (getattr(e, "message", "") or str(e) or "").upper()
        if "FROZEN" in msg:
            res["can_send_to_self"] = False
            res["restricted"] = True
            until = mark_restricted(session_name, reason="frozen_on_send_self")
            res["restricted_until"] = int(until)
            res["error"] = "frozen_method"
        else:
            res["can_send_to_self"] = False
            if not res["error"]:
                res["error"] = f"send_self: {e}"
    except Exception as e:
        res["can_send_to_self"] = False
        if not res["error"]:
            res["error"] = f"send_self: {e}"

    # итоговые карантинные поля (на случай, если менялись по ходу)
    res["restricted"] = is_restricted(session_name)
    res["restricted_until"] = int(ctx.get("restricted_until") or 0)
    return res


async def get_account_profile(session_name: str) -> dict:
    if not _enforce_proxy_or_block(session_name, "get_account_profile"):
        return {"ok": False, "error": "proxy_not_verified"}

    ctx = get_account_context(session_name)
    await ensure_client_ready(session_name, require_auth=True)

    try:
        me = await ctx["client"].get_me()
        full = await ctx["client"](functions.users.GetFullUserRequest(id=me))
        bio = (getattr(full.full_user, "about", None) or "").strip()
        return {
            "ok": True,
            "bio": bio,
            "bio_len": len(bio),
            "bio_max": BIO_MAX_LEN,
            "username": getattr(me, "username", None),
            "first_name": getattr(me, "first_name", None),
            "last_name": getattr(me, "last_name", None),
            "phone": getattr(me, "phone", None),
        }
    except FloodWaitError:
        # важно: не «съедаем» FloodWait — пусть его поймает Flask-роутер и вернёт 429
        raise
    except Exception as e:
        return {"ok": False, "error": str(e)}

async def set_account_bio(session_name: str, bio: str) -> dict:
    """
    Обновляет Bio (описание) аккаунта.
    """
    if not _enforce_proxy_or_block(session_name, "set_account_bio"):
        return {"ok": False, "error": "proxy_not_verified"}

    ctx = get_account_context(session_name)
    await ensure_client_ready(session_name, require_auth=True)

    bio = (bio or "").strip()
    if len(bio) > BIO_MAX_LEN:
        bio = bio[:BIO_MAX_LEN]

    try:
        await ctx["client"](functions.account.UpdateProfileRequest(about=bio))
        return {"ok": True, "bio": bio, "bio_len": len(bio), "bio_max": BIO_MAX_LEN}
    except Exception as e:
        return {"ok": False, "error": str(e)}
# ────────────────────────────────────────────────────────────────────────────────
# Верификация прокси (с автосвитчем транспорта при InvalidBufferError)
# ────────────────────────────────────────────────────────────────────────────────

# ────────────────────────────────────────────────────────────────────────────────
# АВАТАРКИ: кэш, смена, безопасные лимиты
# ────────────────────────────────────────────────────────────────────────────────
def _ensure_dirs_for_avatars():
    try:
        os.makedirs(AVATAR_POOL_DIR, exist_ok=True)
        os.makedirs(AVATAR_CACHE_DIR, exist_ok=True)
    except Exception:
        pass


def _avatar_cache_path(session_name: str) -> str:
    safe = re.sub(r"[^A-Za-z0-9_.-]+", "_", session_name)
    return os.path.join(AVATAR_CACHE_DIR, f"{safe}.jpg")


async def refresh_profile_photo_cache(session_name: str) -> dict:
    """
    Качает текущую аватарку аккаунта 'me' в локальный кэш (если есть).
    Возврат: {"ok":True, "path":..., "exists":bool}
    """
    _ensure_dirs_for_avatars()
    if not _enforce_proxy_or_block(session_name, "refresh_profile_photo_cache"):
        return {"ok": False, "error": "proxy_not_verified"}

    ctx = get_account_context(session_name)
    await ensure_client_ready(session_name, require_auth=True)

    dst = _avatar_cache_path(session_name)
    try:
        # скачиваем текущую фотографию профиля; если нет — вернёт None
        fn = await ctx["client"].download_profile_photo("me", file=dst)
        if fn:
            return {"ok": True, "path": fn, "exists": True}
        # нет фото — удалим возможный старый кэш
        try:
            if os.path.exists(dst):
                os.remove(dst)
        except Exception:
            pass
        return {"ok": True, "path": None, "exists": False}
    except FloodWaitError as e:
        return {"ok": False, "error": "FloodWait", "retry_after": int(getattr(e, "seconds", 0) or 1)}
    except Exception as e:
        return {"ok": False, "error": str(e)}


async def set_account_avatar(session_name: str, image_path: str) -> dict:
    """
    Безопасная смена фото профиля с троттлингом и дневным лимитом.
    Работает только через подтверждённый прокси.
    """
    _ensure_dirs_for_avatars()
    if not _enforce_proxy_or_block(session_name, "set_account_avatar"):
        return {"ok": False, "error": "proxy_not_verified"}

    ctx = get_account_context(session_name)

    # дневной лимит с автосбросом к полуночи
    now = time.time()
    reset_ts = ctx.get("profile_daily_reset_ts") or 0.0
    if not reset_ts or now >= reset_ts:
        ctx["profile_daily_reset_ts"] = _next_local_midnight_ts()
        ctx["profile_edits_today"] = 0

    if int(ctx.get("profile_edits_today", 0)) >= PROFILE_UPDATE_DAILY_LIMIT:
        return {
            "ok": False,
            "error": "daily_limit",
            "retry_after": max(1, int(ctx["profile_daily_reset_ts"] - now))
        }

    # интервал между изменениями профиля
    wait_until = float(ctx.get("next_profile_edit_at", 0.0) or 0.0)
    if now < wait_until:
        return {"ok": False, "error": "throttled", "retry_after": int(wait_until - now)}

    await ensure_client_ready(session_name, require_auth=True)

    try:
        # ✅ Новый совместимый способ
        if hasattr(ctx["client"], "upload_profile_photo"):
            # в новых версиях Telethon
            await ctx["client"].upload_profile_photo(image_path)
        else:
            # в старых версиях Telethon — сырое API
            from telethon.tl import functions
            up = await ctx["client"].upload_file(image_path)
            await ctx["client"](functions.photos.UploadProfilePhotoRequest(file=up))

    except FloodWaitError as e:
        delay = int(getattr(e, "seconds", 0) or 1) + 2
        ctx["next_profile_edit_at"] = time.time() + delay
        return {"ok": False, "error": "FloodWait", "retry_after": delay}
    except RPCError as e:
        return {"ok": False, "error": f"RPCError: {e}"}
    except Exception as e:
        return {"ok": False, "error": str(e)}

    # успех → обновим счётчики и локальный кэш
    ctx["profile_edits_today"] = int(ctx.get("profile_edits_today", 0)) + 1
    ctx["next_profile_edit_at"] = time.time() + PROFILE_UPDATE_INTERVAL_SECONDS

    try:
        await refresh_profile_photo_cache(session_name)
    except Exception:
        pass

    return {"ok": True, "edits_today": ctx["profile_edits_today"]}

async def verify_tg_proxy(session_name: str) -> bool:
    ctx = get_account_context(session_name)
    hp = ctx.get("proxy_hostport") or "-"
    if not ctx.get("proxy_tuple"):
        ctx["proxy_verified"] = False
        log_proxy(session_name, "VERIFY_FAIL", proxy=hp, details="proxy missing")
        return False

    tried_obf = False
    for attempt in (1, 2):
        try:
            if not ctx["client"].is_connected():
                await ctx["client"].connect()
            await ctx["client"](functions.help.GetNearestDcRequest())
            ctx["proxy_verified"] = True
            log_proxy(session_name, "VERIFY_OK", proxy=hp)
            return True

        except InvalidBufferError as e:
            if not tried_obf:
                tried_obf = True
                log_proxy(session_name, "SWITCH_CONN", proxy=hp, details=f"{CONNECTION_CLASS.__name__} -> ConnectionTcpObfuscated (InvalidBuffer)")
                _switch_connection_class(ConnectionTcpObfuscated)
                apply_proxy_from_current_sources(session_name)
                ctx = get_account_context(session_name)
                continue
            else:
                ctx["proxy_verified"] = False
                log_proxy(session_name, "VERIFY_FAIL", proxy=hp, details=f"InvalidBuffer after switch: {e}")
                return False

        except Exception as e:
            msg = str(e) if e else ""
            if ("Invalid response buffer" in msg or "HTTP code 404" in msg) and not tried_obf:
                tried_obf = True
                log_proxy(session_name, "SWITCH_CONN", proxy=hp, details=f"{CONNECTION_CLASS.__name__} -> ConnectionTcpObfuscated (str-match)")
                _switch_connection_class(ConnectionTcpObfuscated)
                apply_proxy_from_current_sources(session_name)
                ctx = get_account_context(session_name)
                continue

            ctx["proxy_verified"] = False
            log_proxy(session_name, "VERIFY_FAIL", proxy=hp, details=str(e))
            return False

    ctx["proxy_verified"] = False
    log_proxy(session_name, "VERIFY_FAIL", proxy=hp, details="unknown")
    return False

def _switch_connection_class(conn_cls):
    global CONNECTION_CLASS
    CONNECTION_CLASS = conn_cls

def _enforce_proxy_or_block(session_name: str, op: str) -> bool:
    ctx = get_account_context(session_name)
    if not ctx.get("proxy_verified", False):
        log_proxy(session_name, "ENFORCE_BLOCK", proxy=ctx.get("proxy_hostport"), details=op)
        return False
    return True

# ========== CORE LOGIC ==========
async def has_comments_enabled(chat, session_name):
    if not _enforce_proxy_or_block(session_name, "has_comments_enabled"):
        return False
    ctx = get_account_context(session_name)
    try:
        await ensure_client_ready(session_name, require_auth=False)
        full = await ctx["client"](functions.channels.GetFullChannelRequest(channel=chat))
        return bool(full.full_chat.linked_chat_id)
    except Exception:
        return False

async def search_telegram_chats(session_name, name_queries, link_queries, only_with_comments, limit=500):
    if not _enforce_proxy_or_block(session_name, "search_telegram_chats"):
        return []
    ctx = get_account_context(session_name)
    chats = []

    await ensure_client_ready(session_name, require_auth=False)

    for i, query in enumerate(name_queries, start=1):
        if not ctx["script_running"]:
            ctx["progress"]["status"] = "Скрипт остановлен"
            return chats
        ctx["progress"]["status"] = f"Поиск в Telegram: «{query}» ({i}/{len(name_queries)})"
        try:
            result = await ctx["client"](functions.contacts.SearchRequest(q=query, limit=limit))
        except Exception:
            ctx["loop"].create_task(verify_tg_proxy(session_name))
            break
        for chat in result.chats:
            if not getattr(chat, 'username', None):
                continue
            if only_with_comments:
                if not getattr(chat, 'broadcast', False):
                    continue
                if not await has_comments_enabled(chat, session_name):
                    continue
            link = f"https://t.me/{chat.username}"
            title = getattr(chat, 'title', None) or link
            if any(q.lower() in title.lower() for q in name_queries) or \
               any(lq.lower() in link.lower() for lq in link_queries):
                chats.append((title, link, "Telegram"))
        await asyncio.sleep(2)
        ctx["progress"]["percent"] = int((i / len(name_queries)) * 50)
    return chats

def save_to_excel(chats, session_name):
    filename = f"telegram_chats_{session_name}.xlsx"
    wb = openpyxl.Workbook()
    sheet = wb.active
    sheet.title = "Telegram Chats"
    sheet.append(["Название / URL", "Ссылка", "Источник"])
    for title, link, src in chats:
        sheet.append([title or link, link, src])
    wb.save(filename)
    ctx = get_account_context(session_name)
    ctx["progress"]["status"] = "Файл сохранён"
    ctx["progress"]["percent"] = 100

async def run_search(session_name, search_limit=100):
    if not _enforce_proxy_or_block(session_name, "run_search"):
        return
    ctx = get_account_context(session_name)

    await ensure_client_ready(session_name, require_auth=False)

    cfg = load_keywords()
    ctx["progress"]["status"] = "Поиск в Telegram..."

    tg_results = await search_telegram_chats(
        session_name,
        cfg.get("name_queries", []),
        cfg.get("link_queries", []),
        cfg.get("only_with_comments", False),
        limit=search_limit
    )

    unique_chats = list({c for c in tg_results})

    global global_found_channels
    global_found_channels = unique_chats[:]

    for other_ctx in accounts.values():
        other_ctx["found_channels"] = unique_chats[:]

    save_to_excel(unique_chats, session_name)
    ctx["script_running"] = False

def start_script(session_name=None, search_limit=100):
    if session_name is None:
        session_name = active_session_name
    if session_name is None:
        return
    if not _enforce_proxy_or_block(session_name, "start_script"):
        return
    ctx = get_account_context(session_name)
    if ctx["script_running"]:
        stop_script(session_name)
    ctx["script_running"] = True
    ctx["progress"]["status"] = "Запуск скрипта"
    ctx["progress"]["percent"] = 0
    if not ctx["loop_thread"] or not ctx["loop_thread"].is_alive():
        ctx["loop_thread"] = threading.Thread(target=ctx["loop"].run_forever, daemon=True)
        ctx["loop_thread"].start()
    asyncio.run_coroutine_threadsafe(run_search(session_name, search_limit), ctx["loop"])

def stop_script(session_name=None):
    if session_name is None:
        session_name = active_session_name
    ctx = accounts.get(session_name)
    if not ctx or not ctx["script_running"]:
        return
    ctx["script_running"] = False
    ctx["progress"]["status"] = "Скрипт остановлен"
    ctx["progress"]["percent"] = 0
    for task in asyncio.all_tasks(ctx["loop"]):
        task.cancel()
    ctx["loop"].stop()

async def generate_comment_via_mistral(post_text: str, base_prompt: str, avoid_phrases: Optional[List[str]] = None) -> str:
    """
    Генерируем одну короткую реплику по теме поста
    с обязательным упоминанием кинотеатра в профиле.
    """
    if not MISTRAL_API_KEY:
        print("[generate_comment_via_mistral] ❌ Mistral API key is missing")
        return ""

    # Набор мягко чередуемых формулировок (все содержат «кинотеатр»)
    pitch_variants = [
        "в моём профиле есть ссылка на бесплатный онлайн-кинотеатр",
        "в профиле у меня есть ссылка на бесплатный онлайн-кинотеатр",
        "в био у меня есть ссылка на бесплатный онлайн-кинотеатр",
        "у меня наверху есть ссылка на бесплатный онлайн-кинотеатр",
    ]
    chosen_pitch = random.choice(pitch_variants)

    # Сужаем задачу и предотвращаем «отказы» и вопросы к собеседнику
    system_prompt_parts = []
    if UNIVERSAL_PROMPT:
        system_prompt_parts.append(UNIVERSAL_PROMPT)
    if base_prompt:
        system_prompt_parts.append(base_prompt)

    system_prompt_parts.append(
        "Дай ровно ОДНО короткое предложение по теме поста (10–16 слов). "
        "Пиши нейтрально и дружелюбно, без эмодзи, хэштегов, приказов, ссылок и призывов к действию. "
        "Не задавай вопросов и не проси прислать что-то. "
        "Обязательно упомяни слово «кинотеатр» и сформулируй ненавязчивую вставку про то, что "
        f"{chosen_pitch}. "
        "Если тема поста спорная/некорректная — дай нейтральный комментарий без оценок и всё равно добавь вставку про кинотеатр. "
        "Русский язык."
    )

    if avoid_phrases:
        system_prompt_parts.append("Избегай повторов и фраз: " + ", ".join(list(set(avoid_phrases))[:10]))

    system_prompt = "\n".join([p for p in system_prompt_parts if p])

    messages = [
        {"role": "system", "content": system_prompt},
        {"role": "user",   "content": post_text or ""}
    ]
    payload = {
        "model": MISTRAL_MODEL,
        "messages": messages,
        # поменьше разброс, чтобы меньше «уезжать» от пича
        "temperature": 0.6,
        "top_p": 0.9,
        "max_tokens": 120,
        "stream": False
    }
    headers = {
        "Authorization": f"Bearer {MISTRAL_API_KEY}",
        "Content-Type": "application/json"
    }

    max_retries = 3
    backoff = 1.0

    async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15)) as session:
        for attempt in range(1, max_retries + 1):
            try:
                async with session.post(MISTRAL_URL, headers=headers, json=payload) as resp:
                    status = resp.status
                    text = await resp.text()

                    if status == 200:
                        data = await resp.json()
                        choices = data.get("choices")
                        if choices:
                            comment = choices[0]["message"]["content"].strip()
                            # причесываем: одна фраза, без кавычек/переводов строк
                            comment = " ".join(comment.replace("\n", " ").replace("  ", " ").split())
                            comment = comment.strip(" '\"«»”’")
                            return comment
                        return ""

                    elif status == 429:
                        await asyncio.sleep(backoff); backoff *= 2
                        continue

                    else:
                        print(f"[generate_comment] ⚠️ Error {status}: {text}")
                        return ""

            except Exception as e:
                print(f"[generate_comment] Exception: {e!r}")
                await asyncio.sleep(backoff); backoff *= 2

    return ""



# ────────────────────────────────────────────────────────────────────────────────
# Воркер очереди комментариев
# ────────────────────────────────────────────────────────────────────────────────
async def _comment_worker(session_name: str):
    ctx = accounts[session_name]
    client = ctx["client"]

    while True:
        try:
            # NEW: глобальная пауза рассылки для аккаунта
            if ctx.get("campaign_paused", False):
                await asyncio.sleep(1)
                continue

            if not accounts[session_name].get("proxy_verified", False):
                await asyncio.sleep(1)
                continue

            if not ctx["comment_queue"]:
                await asyncio.sleep(1)
                continue

            ready_at, task = ctx["comment_queue"][0]
            now = time.time()

            if now < ready_at:
                await asyncio.sleep(min(ready_at - now, 5))
                continue

            if now < ctx["next_send_at"]:
                await asyncio.sleep(min(ctx["next_send_at"] - now, 5))
                continue

            heapq.heappop(ctx["comment_queue"])
            task_id = task.get("task_id")
            disc_id = task["disc_id"]
            reply_to = task["reply_to"]
            text = task["text"]
            src_link = task.get("source_link")
            src = task.get("source")  # <— тег источника (prev_post/new_post/group_reply)

            # 5.1 HOLD: если дискуссия под hold — отложим задачу
            hold = _is_disc_blocked(session_name, disc_id)
            if hold:
                delay = max(60, int(hold.get("hold_until", time.time()) - time.time()))
                heapq.heappush(ctx["comment_queue"], (time.time() + delay, task))
                _log_comment(
                    session_name, "HOLD_RESCHEDULE",
                    TASK=task_id, DISC_ID=disc_id, ETA_SEC=delay, ERROR=hold.get("reason")
                )
                await asyncio.sleep(0)  # уступим цикл
                continue

            waited = max(0.0, time.time() - ready_at)
            qsize  = len(ctx["comment_queue"])

            logging.info(f"[comment_worker] ({session_name}) SEND_ATTEMPT task={task_id} disc={disc_id} reply_to={reply_to}")
            _log_comment(
                session_name, "SEND_ATTEMPT",
                TASK=task_id, DISC_ID=disc_id, REPLY_TO=reply_to,
                READY_AT=ready_at, WAITED_SEC=round(waited, 1), QUEUE=qsize,
                SOURCE=src
            )

            try:
                # ► отправляем по entity (если есть), иначе резолвим по id
                target = task.get("peer") or disc_id
                try:
                    if isinstance(target, int):
                        from telethon.tl.types import PeerChannel
                        target = await client.get_input_entity(PeerChannel(target))
                except Exception:
                    # не смогли резолвнуть peer — отложим
                    heapq.heappush(ctx["comment_queue"], (time.time() + 60, task))
                    _log_comment(
                        session_name, "RETRY_SCHEDULED",
                        TASK=task_id, DISC_ID=disc_id, ETA_SEC=60, ERROR="cannot resolve peer"
                    )
                    ctx["loop"].create_task(verify_tg_proxy(session_name))
                    continue

                # 5.2 safety: убедимся, что мы состоим в дискуссии (и попробуем снять капчу)
                ok_join, why = await _ensure_joined_chat_by_id(session_name, disc_id)
                if not ok_join:
                    _block_disc(session_name, disc_id, why or "guest_forbidden", hold_sec=3600)
                    heapq.heappush(ctx["comment_queue"], (time.time() + 900, task))  # через 15 мин повторим
                    _log_comment(session_name, "JOIN_NEEDED", TASK=task_id, DISC_ID=disc_id, ETA_SEC=900, ERROR=why or "-")
                    continue
                try:
                    await _try_simple_captcha_bypass(session_name, disc_id)
                except Exception:
                    pass

                sent = await client.send_message(target, text, reply_to=reply_to)
                ctx["my_msg_ids"].setdefault(disc_id, set()).add(sent.id)

                LAST_SENT_TEXT_BY_DISC[disc_id].append(_normalize_text_for_dedup(text))

                ctx["next_send_at"] = time.time() + ctx["comment_cooldown"]
                logging.info(
                    f"[comment_worker] ({session_name}) SEND_OK task={task_id} id={sent.id}; cooldown={ctx['comment_cooldown']}s")
                _log_comment(
                    session_name, "SEND_OK",
                    TASK=task_id, DISC_ID=disc_id, MSG_ID=sent.id, LINK=src_link or 'unknown',
                    NEXT_CD_UNTIL=ctx["next_send_at"], NEXT_CD_SEC=ctx["comment_cooldown"], TEXT=repr(text),
                    SOURCE=src  # <— ключевая строка для правильных счётчиков
                )

                chat_logger.info(f"ACCOUNT={session_name} | CHAT_ID={disc_id} | ANSWER={text!r}")

            except SlowModeWaitError as e:
                # уважим реальный slow-mode чата
                delay = int(getattr(e, "seconds", 0) or 60) + 5
                retry_at = time.time() + delay
                heapq.heappush(ctx["comment_queue"], (retry_at, task))
                logging.warning(f"[comment_worker] ({session_name}) SLOWMODE_WAIT {delay}s → reschedule task={task_id}")
                _log_comment(session_name, "SLOWMODE_WAIT", TASK=task_id, DISC_ID=disc_id, ETA_SEC=delay)
                ctx["loop"].create_task(verify_tg_proxy(session_name))
                continue

            # 6.1 новые перехваты перед FloodWaitError
            except ChatGuestSendForbiddenError as e:
                # классика: не участник discussion → подождать и попробовать автоджойн
                _log_comment(session_name, "GUEST_FORBIDDEN", TASK=task_id, DISC_ID=disc_id, ERROR=str(e))
                _block_disc(session_name, disc_id, "guest_forbidden", hold_sec=1800)  # 30 минут
                heapq.heappush(ctx["comment_queue"], (time.time() + 900, task))  # через 15 минут
                continue

            except ChannelPrivateError as e:
                # приват/по заявке/закрыто — держим подолгу
                _log_comment(session_name, "CHANNEL_PRIVATE", TASK=task_id, DISC_ID=disc_id, ERROR=str(e))
                _block_disc(session_name, disc_id, "private", hold_sec=6 * 3600)
                # без повторов в ближайшее время
                continue

            # 6.2 переопределённые поведения
            except ChatWriteForbiddenError as e:
                _log_comment(session_name, "WRITE_FORBIDDEN", TASK=task_id, DISC_ID=disc_id, ERROR=str(e))
                _block_disc(session_name, disc_id, "write_forbidden", hold_sec=6 * 3600)
                # не ливаем канал; просто ставим HOLD
                continue

            except UserBannedInChannelError as e:
                logging.warning(f"[comment_worker] ({session_name}) BANNED_IN_CHANNEL: {e}")
                _log_comment(session_name, "BANNED_IN_CHANNEL", TASK=task_id, DISC_ID=disc_id, ERROR=str(e))
                _block_disc(session_name, disc_id, "banned", hold_sec=24 * 3600)
                # подчистим задачи по этой дискуссии, но не выходим из канала/чата
                try:
                    ctx["comment_queue"] = [(t, tk) for (t, tk) in ctx["comment_queue"] if tk.get("disc_id") != disc_id]
                    heapq.heapify(ctx["comment_queue"])
                except Exception:
                    pass
                continue
            except FloodWaitError as e:
                delay = int(getattr(e, "seconds", 0) or 1) + 5
                _apply_account_floodwait(session_name, delay)
                retry_at = time.time() + delay
                heapq.heappush(ctx["comment_queue"], (retry_at, task))
                logging.warning(f"[comment_worker] ({session_name}) FLOOD_WAIT {delay}s → reschedule task={task_id}")
                _log_comment(session_name, "FLOOD_WAIT", TASK=task_id, DISC_ID=disc_id, ETA_SEC=delay)
                ctx["loop"].create_task(verify_tg_proxy(session_name))
                continue



            except RPCError as e:
                # совместимая ветка: в некоторых версиях Telethon CHAT_SEND_PLAIN_FORBIDDEN не имеет своего класса
                emsg = ""
                try:
                    emsg = getattr(e, "message", "") or ""
                except Exception:
                    pass
                if not emsg:
                    try:
                        emsg = getattr(getattr(e, "rpc_error", None), "error_message", "") or ""
                    except Exception:
                        pass
                if not emsg:
                    emsg = str(e) or ""

                if "CHAT_SEND_PLAIN_FORBIDDEN" in emsg or "CHAT_SEND_FORBIDDEN" in emsg:
                    _log_comment(session_name, "WRITE_FORBIDDEN", TASK=task_id, DISC_ID=disc_id, ERROR=emsg)
                    _block_disc(session_name, disc_id, "write_forbidden", hold_sec=6 * 3600)
                    continue

                # прочие RPC-ошибки → мягкий бэкофф 2 минуты
                logging.error(f"[comment_worker] ({session_name}) RPCError: {e}")
                _log_comment(session_name, "RPC_ERROR", TASK=task_id, DISC_ID=disc_id, ERROR=f"{type(e).__name__}: {e}")
                heapq.heappush(ctx["comment_queue"], (time.time() + 120, task))
                ctx["loop"].create_task(verify_tg_proxy(session_name))
                continue

            except Exception as e:
                logging.error(f"[comment_worker] ({session_name}) UNEXPECTED: {e!r}")
                heapq.heappush(ctx["comment_queue"], (time.time() + 60, task))
                _log_comment(session_name, "RETRY_SCHEDULED", TASK=task_id, DISC_ID=disc_id, ETA_SEC=60, ERROR=str(e))
                ctx["loop"].create_task(verify_tg_proxy(session_name))
                continue

        except Exception as loop_err:
            logging.error(f"[comment_worker] ({session_name}) LOOP_ERR: {loop_err!r}")
            await asyncio.sleep(2)

async def _enqueue_comment_for_discussion(
    session_name: str,
    disc_id: int,
    channel_post_id: int,
    reply_to_msg_id: int,
    post_text: str,
    base_prompt: str,
    channel_link: Optional[str],
    source_tag: str  # "new_post" | "prev_post"
) -> None:
    """
    Генерирует комментарий и ставит задачу в очередь, соблюдая те же правила,
    что и для новых постов (дедуп, hold, джиттер, cooldown).
    """
    if accounts.get(session_name, {}).get("campaign_paused", False):
        return
    if not _enforce_proxy_or_block(session_name, "_enqueue_comment_for_discussion"):
        return

    ctx = accounts[session_name]

    # Если дискуссия под HOLD — не ставим
    if _is_disc_blocked(session_name, disc_id):
        _log_comment(session_name, "ENQUEUE_SKIPPED_BLOCKED", DISC_ID=disc_id, SOURCE=source_tag)
        return

    # Не допустить повтор на тот же thread (reply_to)
    for _t_ready, _task in ctx.get("comment_queue", []):
        if _task.get("disc_id") == disc_id and _task.get("reply_to") == reply_to_msg_id:
            return

    # Дедуп по текстам (включая ожидающие)
    forbidden_norm: Set[str] = set(LAST_SENT_TEXT_BY_DISC.get(disc_id, []))
    forbidden_norm |= _collect_pending_texts_for_disc(disc_id)

    comment = await generate_comment_via_mistral(
        post_text or "",
        base_prompt or "",
        avoid_phrases=list(forbidden_norm) if forbidden_norm else None
    )
    comment = _apply_persona_style(comment, ctx.get("persona"))
    comment = _enforce_cinema_pitch(comment)
    if not comment:
        return

    # ещё попытки при совпадении
    tries = 0
    while _normalize_text_for_dedup(comment) in forbidden_norm and tries < 2:
        comment = await generate_comment_via_mistral(
            post_text or "",
            base_prompt or "",
            avoid_phrases=list(forbidden_norm) if forbidden_norm else None
        )
        comment = _apply_persona_style(comment, ctx.get("persona"))
        tries += 1

    if _normalize_text_for_dedup(comment) in forbidden_norm:
        alt = _local_variation(comment, forbidden_norm, ctx.get("persona"))
        if alt:
            comment = alt

    # Запланировать отправку (тот же джиттер/задержка)
    jitter = random.uniform(DESYNC_MIN_SECONDS, DESYNC_MAX_SECONDS)
    ready_at = time.time() + POST_DELAY_SECONDS + jitter
    ctx["comment_seq"] = ctx.get("comment_seq", 0) + 1
    task_id = ctx["comment_seq"]

    task = {
        "task_id": task_id,
        "disc_id": disc_id,
        "reply_to": reply_to_msg_id,
        "text": comment,
        "source_link": channel_link,
        "source": source_tag,  # <— пронесли метку источника в саму задачу
        # для групп мы кладём peer, но здесь — обсуждение канала → резолв по disc_id
    }

    heapq.heappush(ctx["comment_queue"], (ready_at, task))

    # Отметим, что для этой дискуссии мы уже взяли этот пост
    try:
        ctx["last_commented_post_id"][int(disc_id)] = int(channel_post_id)
    except Exception:
        pass

    _log_comment(
        session_name,
        "ENQUEUE",
        TASK=task_id,
        CHAT_ID=disc_id,
        READY_AT=ready_at,
        ETA_SEC=int(ready_at - time.time()),
        TEXT=repr(comment),
        SOURCE=source_tag  # ► пометка для дашборда/аналитики
    )

    if not ctx.get("comment_worker_started"):
        ctx["comment_worker_started"] = True
        ctx["loop"].create_task(_comment_worker(session_name))

async def handle_new_message(event):
    logging.info(f"[handle_new_message] incoming event: is_channel={event.is_channel}, chat_id={event.chat_id}")

    session_name = next((n for n, ctx in accounts.items() if ctx["client"] == event.client), None)
    if not session_name:
        return

    if not _enforce_proxy_or_block(session_name, "handle_new_message"):
        return

    # NEW: если пауза — вовсе не генерим комментарии и не ставим в очередь
    if accounts.get(session_name, {}).get("campaign_paused", False):
        return

    ctx = accounts[session_name]
    from google import genai

    buttons = getattr(event.message, "buttons", None)
    if buttons:
        text = event.message.message or ""
        options = [btn.text for row in buttons for btn in row if hasattr(btn, "text")]
        logging.info(f"[captcha] Detected options: {options}")
        captcha_logger.info(f"Detected options: {options}")

        client = genai.Client()
        prompt = (
            f"Дана капча:\n\"\"\"\n{text}\n\"\"\"\n"
            f"Варианты ответов: {options}\n"
            "Выбери самый правильный вариант и выведи ровно его текст."
        )

        max_attempts = 3
        for attempt in range(1, max_attempts + 1):
            try:
                resp = client.models.generate_content(
                    model="gemini-2.5-flash-lite",
                    contents=prompt,
                    config=genai.types.GenerateContentConfig(
                        thinking_config=genai.types.ThinkingConfig(thinking_budget=0)
                    )
                )
                answer = resp.text.strip()
                logging.info(f"[captcha] Gemini → {answer!r}")
                captcha_logger.info(f"Gemini → {answer!r}")

                for row in buttons:
                    for btn in row:
                        if getattr(btn, "text", None) == answer:
                            await event.click(text=answer)
                            captcha_logger.info(f"clicked button: {answer}")
                            return
                await event.reply(answer)
                captcha_logger.info(f"replied with text: {answer}")
                return

            except Exception as e:
                err = getattr(e, 'error', None) or {}
                code = err.get('status') if isinstance(err, dict) else None
                if code == 'RESOURCE_EXHAUSTED' and attempt < max_attempts:
                    retry_info = next((d.get('retryDelay') for d in err.get('details', []) if d.get('@type', '').endswith('RetryInfo')), None)
                    delay = int(retry_info[:-1]) if retry_info and retry_info.endswith('s') else 10
                    logging.warning(f"[captcha] 429, retrying in {delay}s (attempt {attempt}/{max_attempts})")
                    captcha_logger.warning(f"429 RESOURCE_EXHAUSTED, retry {attempt}/{max_attempts} after {delay}s")
                    await asyncio.sleep(delay)
                    continue

                logging.error(f"[captcha] error solving captcha: {e}")
                captcha_logger.error(f"error solving captcha: {e}")
                break

        fallback = options[0]
        try:
            await event.click(text=fallback)
            captcha_logger.info(f"fallback clicked button: {fallback}")
        except Exception as e2:
            logging.error(f"[captcha] fallback click error: {e2}")
            captcha_logger.error(f"fallback click error: {e2}")
        return

    if not event.is_channel and not buttons:
        text = event.message.message or ""
        logging.info(f"[captcha_text] Detected text-only captcha: {text!r}")
        captcha_logger.info(f"Text-only captcha: {text!r}")

        from google import genai
        client = genai.Client()
        prompt = (
            f"Дана капча (текст):\n\"\"\"\n{text}\n\"\"\"\n"
            "Вычисли ответ и выведи ровно ответ."
        )
        try:
            resp = client.models.generate_content(
                model="gemini-2.5-flash-lite",
                contents=prompt,
                config=genai.types.GenerateContentConfig(
                    thinking_config=genai.types.ThinkingConfig(thinking_budget=0)
                )
            )
            answer = resp.text.strip()
            logging.info(f"[captcha_text] Gemini → {answer!r}")
            captcha_logger.info(f"Gemini text answer → {answer!r}")

            await event.reply(answer)
            captcha_logger.info(f"replied text answer: {answer}")

        except Exception as e:
            logging.error(f"[captcha_text] error solving text-only captcha: {e}")
            captcha_logger.error(f"error solving text-only captcha: {e}")
        return

    # Унифицированная развилка по режиму
    cid = event.chat_id
    key = int(str(cid)[4:]) if str(cid).startswith("-100") else cid
    info = ctx["monitored_info"].get(key)
    if not info:
        return

    # обратная совместимость: (disc_id, prompt) или (disc_id, prompt, mode)
    if isinstance(info, (list, tuple)):
        disc_id, base_prompt = info[0], (info[1] if len(info) >= 2 else "")
        mode = info[2] if len(info) >= 3 else "discussion"
    else:
        # на всякий случай
        disc_id, base_prompt, mode = key, "", "discussion"

    if mode == "discussion":
        if not event.is_channel:
            return

        # 🚫 если дискуссия под HOLD/ban/private — не ставим новые задачи вовсе
        if _is_disc_blocked(session_name, disc_id):
            _log_comment(session_name, "ENQUEUE_SKIPPED_BLOCKED", DISC_ID=disc_id)
            return

        short = (event.message.message or "").replace("\n", " ")
        if len(short) > 120:
            short = short[:117] + "..."
        logging.info(f"[post] ({session_name}) channel_id={key} msg_id={event.id} text='{short}'")

        try:
            resp = await event.client(functions.messages.GetDiscussionMessageRequest(peer=cid, msg_id=event.id))
        except RPCError as e:
            logging.warning(f"[handle_new_message] ({session_name}) GetDiscussionMessageRequest failed: {e}")
            await _force_leave_channel(session_name, key)
            ctx["loop"].create_task(verify_tg_proxy(session_name))
            return

        if not resp.messages:
            return
        group_msg = resp.messages[0]

        channel_link = next(
            (lnk for lnk, ent in ctx["joined_entities"].items() if getattr(ent, "id", None) == key),
            None
        )

        # ► используем общий helper; source_tag = "new_post"
        await _enqueue_comment_for_discussion(
            session_name=session_name,
            disc_id=disc_id,
            channel_post_id=event.id,
            reply_to_msg_id=group_msg.id,
            post_text=event.message.message or "",
            base_prompt=base_prompt,
            channel_link=channel_link,
            source_tag="new_post"
        )
        return

    elif mode == "group":
        # это «просто чат/супергруппа» — мониторим сам чат
        # защитимся от ответов на собственные сообщения
        my_ids = ctx["my_msg_ids"].get(key, set())
        if getattr(event, "out", False):
            return
        if event.reply_to_msg_id and event.reply_to_msg_id in my_ids:
            return

        # --- Антиспам в супергруппах ---
        now = time.time()

        # 1) случайная выборка (не на каждый входящий)
        if random.random() > GROUP_REPLY_PROB:
            return

        # 2) минимальный интервал между нашими сообщениями в этом чате
        last_ts = (ctx.get("group_last_sent") or {}).get(key, 0.0)
        if now - last_ts < GROUP_MIN_GAP_SECONDS:
            return

        # 3) лимит не более N сообщений в час
        sent_log = (ctx.get("group_sent_log") or {}).setdefault(key, [])
        # чистим старше часа
        sent_log = [t for t in sent_log if now - t <= 3600]
        ctx["group_sent_log"][key] = sent_log
        if len(sent_log) >= GROUP_MAX_PER_HOUR:
            return

        # резервируем слот (если не получится отправить — потом перетрём по времени)
        (ctx.get("group_last_sent") or {}).update({key: now})
        sent_log.append(now)
        # --- /антиспам ---

        forbidden_norm: Set[str] = set(LAST_SENT_TEXT_BY_DISC.get(disc_id, []))
        forbidden_norm |= _collect_pending_texts_for_disc(disc_id)

        comment = await generate_comment_via_mistral(
            event.message.message,
            base_prompt,
            avoid_phrases=list(forbidden_norm) if forbidden_norm else None
        )
        comment = _apply_persona_style(comment, ctx.get("persona"))
        comment = _enforce_cinema_pitch(comment)
        if not comment:
            return

        jitter = random.uniform(DESYNC_MIN_SECONDS, DESYNC_MAX_SECONDS)
        ready_at = time.time() + POST_DELAY_SECONDS + jitter
        ctx["comment_seq"] = ctx.get("comment_seq", 0) + 1
        task_id = ctx["comment_seq"]

        # кладём InputPeer сразу (ускорит воркер)
        try:
            peer = await event.get_input_chat()
        except Exception:
            peer = None

        task = {
            "task_id": task_id,
            "disc_id": key,  # сам чат
            "reply_to": event.id,  # отвечаем на конкретное сообщение
            "text": comment,
            "peer": peer  # чтобы воркер не угадывал
        }
        heapq.heappush(ctx["comment_queue"], (ready_at, task))
        _log_comment(
            session_name, "ENQUEUE",
            TASK=task_id, CHAT_ID=key, READY_AT=ready_at,
            ETA_SEC=int(ready_at - time.time()), TEXT=repr(comment),
            SOURCE="group_reply"
        )

        if not ctx["comment_worker_started"]:
            ctx["comment_worker_started"] = True
            ctx["loop"].create_task(_comment_worker(session_name))
        return



async def _force_leave_channel(session_name: str, key: int, reason: str = ""):
    ctx = accounts[session_name]
    link = None
    for lnk, ent in ctx["joined_entities"].items():
        if getattr(ent, 'id', None) == key:
            link = lnk
            break

    if not link:
        logging.error(f"[force_leave] ({session_name}) cannot find link for channel_id={key}")
        return

    try:
        await leave_channel(link, session_name)
    except Exception as e:
        logging.error(f"[force_leave] ({session_name}) leave_channel error for {link}: {e}")

    leave_logger.info(f"ACCOUNT={session_name} | CHANNEL={link} | CHAT_ID={key} | REASON={reason}")

def load_keywords():
    with open('keywords.json', 'r', encoding='utf-8') as f:
        return json.load(f)
USERNAME_RE = re.compile(r'^[A-Za-z0-9_]{5,32}$')

def _extract_username(link: str) -> Optional[str]:
    """
    Возвращает username без @/схемы, либо None если это не username-ссылка.
    Поддержка: https://t.me/foo, t.me/foo, @foo
    """
    if not link: return None
    s = link.strip()
    if s.startswith('@'):
        return s[1:]
    if 't.me/' in s:
        # отрежем всё после / и до ?/#
        part = s.split('t.me/', 1)[1]
        part = re.split(r'[/?#]', part)[0]
        return part or None
    return None

def _is_probably_bad_username(u: str) -> bool:
    return not bool(USERNAME_RE.match(u or ""))
async def _ensure_joined_chat_by_id(session_name: str, chat_id: int) -> (bool, str):
    """
    Проверяем, что состоим в чате/дискуссии chat_id.
    Если нет — пробуем JoinChannelRequest(...).
    Возвращает (ok, reason|None). reason ∈ {"flood_wait:<sec>", "private:...", "write_forbidden:...", "approval_needed", "rpc:...", "unexpected:..."}
    """
    ctx = get_account_context(session_name)
    client = ctx["client"]
    try:
        await ensure_client_ready(session_name, require_auth=True, enforce_proxy=True)
    except Exception as e:
        return False, f"connect:{e}"

    try:
        from telethon.tl.types import PeerChannel
        peer = PeerChannel(chat_id)

        # уже участник?
        try:
            await client(functions.channels.GetParticipantRequest(channel=peer, participant='me'))
            return True, None
        except RPCError:
            pass  # не участник → пробуем вступить

        # пробуем вступить
        ent = await client.get_input_entity(peer)
        await client(functions.channels.JoinChannelRequest(ent))

        # повторная проверка участия
        try:
            await client(functions.channels.GetParticipantRequest(channel=peer, participant='me'))
            return True, None
        except RPCError:
            # запрос на вступление отправлен, но мы ещё не участник
            return False, "approval_needed"

    except FloodWaitError as e:
        return False, f"flood_wait:{e.seconds}"
    except ChannelPrivateError as e:
        return False, f"private:{e}"
    except ChatWriteForbiddenError as e:
        return False, f"write_forbidden:{e}"
    except RPCError as e:
        return False, f"rpc:{e}"
    except Exception as e:
        return False, f"unexpected:{e}"



async def _try_simple_captcha_bypass(session_name: str, chat_id: int, limit: int = 30) -> bool:
    """
    Примитивный автосолвер: кликаем 'я человек/verify', либо решаем 1+2, 3*4 и т.п.
    Это best-effort, без внешних сервисов.
    """
    ctx = get_account_context(session_name)
    client = ctx["client"]
    try:
        from telethon.tl.types import PeerChannel
        peer = await client.get_input_entity(PeerChannel(chat_id))
    except Exception:
        return False

    patt_btn = ('i am not a bot', "i'm not a bot", 'not a bot', 'я человек', 'не бот', 'verify', 'подтвердить')

    def _solve_arith(text: str):
        t = (text or "").replace("×", "x")
        m = re.search(r'(\d+)\s*([+xX*\/\-])\s*(\d+)', t)
        if not m: return None
        a, op, b = int(m.group(1)), m.group(2), int(m.group(3))
        if op in ['+']: return a + b
        if op in ['-']: return a - b
        if op in ['*','x','X']: return a * b
        if op in ['/']: return a // b if b else None
        return None

    try:
        async for msg in client.iter_messages(peer, limit=limit):
            # 1) кнопки
            try:
                if getattr(msg, "buttons", None):
                    for row in msg.buttons:
                        for btn in row:
                            txt = (getattr(btn, "text", "") or "").lower()
                            if any(p in txt for p in patt_btn):
                                try:
                                    await msg.click(btn)
                                    captcha_logger.info(f"ACCOUNT={session_name} | clicked captcha button: {btn.text!r}")
                                    return True
                                except Exception:
                                    pass
            except Exception:
                pass

            # 2) простая арифметика
            ans = _solve_arith(getattr(msg, "raw_text", "") or "")
            if ans is not None:
                try:
                    await client.send_message(peer, str(ans))
                    captcha_logger.info(f"ACCOUNT={session_name} | sent arith answer: {ans}")
                    return True
                except Exception:
                    pass
        return False
    except Exception:
        return False

async def _join_with_retries(ctx, link, max_attempts=3):
    """
    Пробует войти в канал/чат с учётом FloodWait. Возвращает entity либо None.
    """
    client = ctx["client"]
    for attempt in range(1, max_attempts+1):
        try:
            if "/joinchat/" in link or "/+" in link:
                code = link.rsplit('/', 1)[-1].lstrip('+')
                res = await client(functions.messages.ImportChatInviteRequest(code))
                return res.chats[0] if res and res.chats else None
            else:
                ent = await client.get_entity(link)
                await client(functions.channels.JoinChannelRequest(ent))
                return ent



        except FloodWaitError as e:
            delay = int(getattr(e, "seconds", 0) or 1) + 2
            _apply_account_floodwait(next(k for k,v in accounts.items() if v is ctx), delay)
            logging.warning(f"[join] FloodWait {delay}s on {link} (attempt {attempt}/{max_attempts})")
            await asyncio.sleep(delay)
            continue


        except (UsernameInvalidError, UsernameNotOccupiedError) as e:
            logging.warning(f"[join] bad username for link={link}: {e}")
            return None

        except ChannelPrivateError as e:
            logging.warning(f"[join] private/forbidden link={link}: {e}")
            return None

        except RPCError as e:
            logging.warning(f"[join] RPCError on {link}: {e}")
            # мягкий бэкофф и ещё попытка
            await asyncio.sleep(3)
            continue

        except Exception as e:
            logging.warning(f"[join] unexpected on {link}: {e}")
            await asyncio.sleep(2)
            continue

    return None
def enqueue_joins(session_name: str, links: List[str], comment_text: str):
    """
    Потокобезопасно добавляет ссылки в per-account очередь join'ов.
    Не дублирует уже стоящие в очереди/вступленные.
    """
    ctx = get_account_context(session_name)

    # нормализуем список ссылок
    norm = []
    seen = set()
    for raw in links or []:
        s = (raw or "").strip()
        if not s or s in seen:
            continue
        seen.add(s); norm.append(s)

    def _do():
        q = ctx.setdefault("join_queue", deque())
        # не добавляем дубликаты
        queued = {item.get("link") for item in list(q)}
        for link in norm:
            if (link in ctx.get("joined_channels", set())) or (link in queued):
                continue
            q.append({"link": link, "comment": comment_text})

        # инициализируем счётчик/ресет если нужно
        if not ctx.get("join_daily_reset_ts"):
            ctx["join_daily_reset_ts"] = _next_local_midnight_ts()

    # выполнять изменения в потоке event-loop
    ctx["loop"].call_soon_threadsafe(_do)
    _ensure_join_worker(session_name)


def _ensure_join_worker(session_name: str):
    """Стартует воркер join'ов для аккаунта, если он ещё не запущен."""
    ctx = get_account_context(session_name)
    if not ctx.get("join_worker_started"):
        ctx["join_worker_started"] = True
        asyncio.run_coroutine_threadsafe(_join_worker(session_name), ctx["loop"])


async def _perform_join_and_setup(session_name: str, link: str, comment_text: str) -> bool:
    """
    Вступить в канал/группу и настроить мониторинг.
    Возвращает True, если остаёмся подписанными и будем мониторить.
    """
    ctx = get_account_context(session_name)
    client = ctx["client"]

    # sanity: уже внутри?
    try:
        if link in ctx["joined_channels"]:
            # лёгкая проверка факта членства (не обязательно)
            try:
                await client.get_participants(link, limit=1)
                return True
            except Exception:
                # очистим «застрявшее» локальное состояние
                ctx["joined_channels"].discard(link)
                ctx["joined_names"].pop(link, None)
                ctx["joined_entities"].pop(link, None)
    except Exception:
        pass

    # пробуем вступить (внутри уважается FloodWait — ждёт и ретраит)
    ent = await _join_with_retries(ctx, link, max_attempts=3)
    if not ent:
        return False

    # зафиксируем локально
    ctx["joined_channels"].add(link)
    ctx["joined_names"][link]    = getattr(ent, 'title', link)
    ctx["joined_entities"][link] = ent
    save_account_state(session_name)

    # определить тип и настроить мониторинг
    try:
        is_broadcast = bool(getattr(ent, 'broadcast', False))
        is_megagroup = bool(getattr(ent, 'megagroup', False))
        chan_id = getattr(ent, 'id', None)

        if is_broadcast:
            full = await client(functions.channels.GetFullChannelRequest(channel=ent))
            disc_id = full.full_chat.linked_chat_id
            if not disc_id:
                # нет обсуждения — уходим и не мониторим
                try:
                    await leave_channel(link, session_name)
                except Exception:
                    pass
                return False

            # ► корректно вступаем именно в linked discussion по его id
            ok, reason = await _ensure_joined_chat_by_id(session_name, disc_id)
            if not ok:
                if (reason or "").startswith("approval_needed"):
                    # 🟠 заявка на вступление в обсуждение — ставим долгий HOLD и уходим
                    _block_disc(session_name, disc_id, "approval_needed", hold_sec=12 * 3600)
                    try:
                        await leave_channel(link, session_name)
                    except Exception:
                        pass
                    _log_comment(session_name, "JOINED_WITH_APPROVAL_NEEDED", DISC_ID=disc_id)
                    return False

                # приват/форбид/прочее — обычная обработка
                _block_disc(session_name, disc_id, reason or "join_failed", hold_sec=6 * 3600)
                try:
                    await leave_channel(link, session_name)
                except Exception:
                    pass
                _log_comment(session_name, "JOIN_DISCUSSION_FAIL", DISC_ID=disc_id, ERROR=reason or "-")
                return False

            # после вступления — попробуем лёгкую капчу
            try:
                await _try_simple_captcha_bypass(session_name, disc_id)
            except Exception:
                pass

            ctx["monitored_info"][chan_id] = (disc_id, comment_text, "discussion")
            _log_comment(session_name, "JOIN_DISCUSSION_OK", DISC_ID=disc_id)

            # ► БЭКО-КОММЕНТ: попробуем прокомментировать последний пост, если ещё не делали
            try:
                # 1) последний пост канала
                last_posts = await client.get_messages(ent, limit=1)
                if last_posts and last_posts[0]:
                    last_post = last_posts[0]
                    last_post_id = int(last_post.id)

                    # Не дублировать, если уже комментировали этот пост
                    already = int(ctx.get("last_commented_post_id", {}).get(int(disc_id), 0) or 0)
                    if last_post_id != already:
                        # 2) сопоставить пост ↔ сообщение в обсуждении (reply_to)
                        resp = await client(functions.messages.GetDiscussionMessageRequest(
                            peer=ent, msg_id=last_post_id
                        ))
                        if resp and resp.messages:
                            grp_msg = resp.messages[0]
                            # 3) ссылка канала (для логов)
                            channel_link = next(
                                (lnk for lnk, e2 in ctx["joined_entities"].items() if
                                 getattr(e2, "id", None) == chan_id),
                                None
                            )
                            # 4) поставить задачу, как и для «нового поста», но с меткой source_tag="prev_post"
                            await _enqueue_comment_for_discussion(
                                session_name=session_name,
                                disc_id=disc_id,
                                channel_post_id=last_post_id,
                                reply_to_msg_id=int(grp_msg.id),
                                post_text=last_post.message or "",
                                base_prompt=comment_text,
                                channel_link=channel_link,
                                source_tag="prev_post"
                            )
            except Exception as e:
                logging.warning(f"[join_backfill] ({session_name}) backfill failed: {e}")

            return True


        elif is_megagroup:
            ctx["monitored_info"][chan_id] = (chan_id, comment_text, "group")
            return True

        else:
            # неприменимый тип — выйдем
            try:
                await leave_channel(link, session_name)
            except Exception:
                pass
            return False

    except FloodWaitError:
        # уважим, но сам _join_with_retries уже ждал; здесь просто не падаем
        return False
    except Exception:
        # на сбоях не ломаем очередь
        return False



async def _join_worker(session_name: str):
    """
    Один воркер на аккаунт:
    - берёт задания из FIFO-очереди
    - уважает next_join_at (интервал + джиттер)
    - соблюдает дневной лимит JOIN_DAILY_LIMIT
    - ✚ уважает карантин (restricted_until)
    """
    ctx = get_account_context(session_name)

    while True:
        try:
            # ✚ карантин — не вступаем
            ru = float(ctx.get("restricted_until") or 0.0)
            if _now() < ru:
                await asyncio.sleep(min(5, ru - _now()))
                continue

            # 0) прокси не подтверждён — ждём
            if not ctx.get("proxy_verified", False):
                await asyncio.sleep(2)
                continue

            # 1) дневной лимит/сброс
            now = time.time()
            reset_ts = ctx.get("join_daily_reset_ts") or 0.0
            if not reset_ts or now >= reset_ts:
                ctx["join_daily_count"] = 0
                ctx["join_daily_reset_ts"] = _next_local_midnight_ts()

            if ctx.get("join_daily_count", 0) >= JOIN_DAILY_LIMIT:
                await asyncio.sleep(min(60, max(1, int(ctx["join_daily_reset_ts"] - now))))
                continue

            # 2) пустая очередь
            q = ctx.get("join_queue") or deque()
            if not q:
                await asyncio.sleep(1)
                continue

            # 3) выждать next_join_at
            if now < ctx.get("next_join_at", 0.0):
                await asyncio.sleep(min(5, ctx["next_join_at"] - now))
                continue

            # 4) подготовка клиента
            try:
                await ensure_client_ready(session_name, require_auth=True, enforce_proxy=True)
            except Exception:
                await asyncio.sleep(2)
                continue

            # 5) взять задание
            item = q.popleft()
            link = item["link"]
            comment_text = item.get("comment") or ""

            # 6) выполнить
            ok = await _perform_join_and_setup(session_name, link, comment_text)
            if ok:
                ctx["join_daily_count"] = int(ctx.get("join_daily_count", 0)) + 1

            # 7) троттлинг на следующий join
            pause = JOIN_INTERVAL_SECONDS + random.uniform(JOIN_JITTER_MIN, JOIN_JITTER_MAX)
            ctx["next_join_at"] = time.time() + pause

            # 8) зарегистрировать хендлер событий (если ещё нет)
            if not ctx.get("event_handler_added"):
                ctx["client"].add_event_handler(handle_new_message, events.NewMessage())
                ctx["event_handler_added"] = True

        except Exception:
            await asyncio.sleep(2)


async def subscribe_and_listen(selected_links, comment_text, session_name=None):
    """
    Обратная совместимость: вместо немедленных join'ов — постановка в очередь,
    воркер сделает всё с троттлингом.
    """
    if session_name is None:
        session_name = active_session_name
    if not _enforce_proxy_or_block(session_name, "subscribe_and_listen"):
        return
    # фильтрация «битых» username-ссылок (как раньше)
    good = []
    seen = set()
    for raw in (selected_links or []):
        s = (raw or "").strip()
        if not s or s in seen:
            continue
        seen.add(s)
        u = _extract_username(s)
        if u is not None and _is_probably_bad_username(u):
            continue
        good.append(s)

    enqueue_joins(session_name, good, comment_text)



async def leave_channel(link, session_name=None):
    if session_name is None:
        session_name = active_session_name
    if not _enforce_proxy_or_block(session_name, "leave_channel"):
        return False
    ctx = get_account_context(session_name)

    try:
        await ensure_client_ready(session_name, require_auth=True)
    except Exception as e:
        print(f"[leave_channel] warning: ensure_client_ready failed: {e}")
        ctx["loop"].create_task(verify_tg_proxy(session_name))

    try:
        ent = ctx["joined_entities"].get(link) or await ctx["client"].get_entity(link)
        print(f"[leave_channel] ({session_name}) leaving {link}")
        await ctx["client"](functions.channels.LeaveChannelRequest(ent))

        ctx["joined_channels"].discard(link)
        ctx["joined_entities"].pop(link, None)
        ctx["joined_names"].pop(link, None)
        ctx["monitored_info"].pop(getattr(ent, 'id', None), None)
        save_account_state(session_name)

        print(f"[leave_channel] ({session_name}) ✅ Left {link}")
        return True
    except Exception as e:
        print(f"[leave_channel][ERROR] ({session_name}) {e} — cleaning local state anyway")
        ctx["joined_channels"].discard(link)
        ctx["joined_entities"].pop(link, None)
        ctx["joined_names"].pop(link, None)
        try:
            ent  # noqa
            ctx["monitored_info"].pop(getattr(ent, 'id', None), None)
        except Exception:
            pass
        save_account_state(session_name)
        ctx["loop"].create_task(verify_tg_proxy(session_name))
        return False

if __name__ == "__main__":
    if available_sessions:
        session_name = available_sessions[0]
        ctx = get_account_context(session_name)

        if ctx["loop"] is None or ctx["loop"].is_closed():
            ctx["loop"] = asyncio.new_event_loop()
            asyncio.set_event_loop(ctx["loop"])

        # НИКАКИХ прямых connect() до верификации прокси!
        ok = ctx["loop"].run_until_complete(verify_tg_proxy(session_name))
        if ok:
            start_script(session_name)
        else:
            print("Прокси не прошёл проверку, запуск заблокирован.")
    else:
        print("Нет доступных аккаунтов для запуска.")

