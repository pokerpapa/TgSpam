# dashboard.py
import os, re, time, json, math
from datetime import datetime, timedelta
from typing import List, Dict, Any
from flask import Blueprint, render_template, jsonify, request

import main

dashboard_bp = Blueprint("dashboard", __name__)


LOGS = {
    "comments": "comments.log",
    "leaves": "leaves.log",
    "proxy": "proxy.log",
    "captcha": "captcha.log",
    "chat": "chat_replies.log",
}
COMMENT_EVENTS_OK = {"SEND_OK"}        # что считаем успешной отправкой
COMMENT_EVENTS_QUEUE = {"ENQUEUE"}     # что считаем постановкой в очередь

LINE_RE = re.compile(r"^(?P<ts>\d{4}-\d{2}-\d{2}\s+\d{2}:\d{2}:\d{2}) \| (?P<lvl>\w+) \| (?P<rest>.+)$")
KV_RE = re.compile(r"(?P<k>[A-Z0-9_]+)=(?P<v>[^|]+)")
# --- Channel resolution helpers ---------------------------------------------
def _build_entity_index():
    """
    Индекс по id → {label, url, title, link} из всех аккаунтов:
    - label: '@username' или title/ссылка
    - url:   t.me/username или исходная ссылка из joined_entities
    """
    idx = {}
    for ctx in main.accounts.values():
        ents = (ctx.get("joined_entities") or {})
        names = (ctx.get("joined_names") or {})
        for link, ent in ents.items():
            try:
                cid = getattr(ent, "id", None)
            except Exception:
                cid = None
            if cid is None:
                continue
            username = getattr(ent, "username", None)
            title = names.get(link) or getattr(ent, "title", None) or None
            if username:
                label = f"@{username}"
                url = f"https://t.me/{username}"
            else:
                label = title or link
                url = link
            idx[str(cid)] = {"label": label, "url": url, "title": title, "link": link}
    return idx


def _resolve_channel_info(rec, idx=None):
    """
    На вход запись лога (словари из _parse_log_line).
    Возвращает {"label":..., "url":...} максимально человекочитаемо.
    """
    if idx is None:
        idx = _build_entity_index()

    # 1) если уже есть ссылка — используем её
    link = rec.get("LINK")
    if link:
        m = re.search(r"https?://t\.me/([^/\s]+)", link)
        label = f"@{m.group(1)}" if m else link
        return {"label": label, "url": link}

    # 2) пробуем id-поля
    for key in ("CHAT_ID", "DISC_ID", "CHANNEL_ID", "CHAT"):
        cid = rec.get(key)
        if cid is None:
            continue
        s = str(cid)
        info = idx.get(s) or idx.get(s.lstrip("-"))
        if info:  # нашли в индексe
            return {"label": info["label"], "url": info["link"]}
        # fallback: хотя бы показать сам id
        return {"label": f"id:{s}", "url": ""}

    # 3) иначе
    return {"label": "unknown", "url": ""}

def _parse_log_line(line: str) -> Dict[str, Any]:
    """Парсим строку формата: 'YYYY-mm-dd HH:MM:SS | LEVEL | K=V | ...'"""
    m = LINE_RE.match(line.strip())
    if not m:
        return {}
    ts_str = m.group("ts")
    rest = m.group("rest")
    try:
        ts = int(time.mktime(time.strptime(ts_str, "%Y-%m-%d %H:%M:%S")))
    except Exception:
        ts = None
    rec = {"ts": ts, "time": ts_str}
    for kv in rest.split(" | "):
        mm = KV_RE.match(kv.strip())
        if mm:
            k, v = mm.group("k"), mm.group("v").strip()
            # снимем кавычки, если это TEXT='...'
            if k == "TEXT" and len(v) >= 2 and v[0] in ("'", '"') and v[-1] == v[0]:
                v = v[1:-1]
            rec[k] = v
    return rec

def _tail(path: str, max_lines: int = 2000) -> List[str]:
    if not os.path.isfile(path):
        return []
    with open(path, "r", encoding="utf-8", errors="ignore") as f:
        # читаем целиком (обычно логи небольшие). если вырастут — можно сделать блочный tail
        lines = f.readlines()
    return lines[-max_lines:]

def _recent_comments(limit: int = 200, minutes: int = 1440) -> List[Dict[str, Any]]:
    path = LOGS["comments"]
    out = []
    cutoff = time.time() - minutes * 60
    idx = _build_entity_index()  # один раз на выборку

    for line in reversed(_tail(path, 4000)):
        r = _parse_log_line(line)
        if not r or r.get("EVENT") not in (COMMENT_EVENTS_OK | COMMENT_EVENTS_QUEUE):
            continue
        if r.get("ts") and r["ts"] < cutoff:
            if len(out) >= limit:
                break

        # добавим «красивые» поля канала
        ch = _resolve_channel_info(r, idx)
        r["CHANNEL_LABEL"] = ch.get("label")
        r["CHANNEL_URL"]   = ch.get("url")

        out.append(r)
        if len(out) >= limit:
            break

    out.sort(key=lambda x: x.get("ts") or 0, reverse=True)
    return out


def _totals_from_comments(minutes: int = 1440) -> Dict[str, Any]:
    rows = _recent_comments(limit=5000, minutes=minutes)
    sent = [r for r in rows if r.get("EVENT") in COMMENT_EVENTS_OK]
    enq  = [r for r in rows if r.get("EVENT") in COMMENT_EVENTS_QUEUE]

    # ► раздельные счётчики по SOURCE
    sent_prev  = [r for r in sent if (r.get("SOURCE") == "prev_post")]
    sent_new   = [r for r in sent if (r.get("SOURCE") == "new_post")]
    sent_group = [r for r in sent if (r.get("SOURCE") == "group_reply")]

    # топ-каналы по «красивой метке»
    top_channels: Dict[str, int] = {}
    for r in sent:
        key = r.get("CHANNEL_LABEL") or r.get("LINK") or str(r.get("CHAT_ID") or r.get("DISC_ID") or "unknown")
        top_channels[key] = top_channels.get(key, 0) + 1

    top = sorted(top_channels.items(), key=lambda kv: kv[1], reverse=True)[:10]
    return {
        "sent_count": len(sent),
        "enqueued_count": len(enq),
        "top_channels": [{"channel": k, "count": v} for k, v in top],
        # ► новые поля
        "sent_prev_count": len(sent_prev),
        "sent_new_count": len(sent_new),
        "sent_group_count": len(sent_group),
    }



def _minutes_since_midnight_local() -> int:
    """Сколько минут прошло с местной полуночи."""
    now = time.time()
    lt = time.localtime(now)
    midnight = time.mktime((lt.tm_year, lt.tm_mon, lt.tm_mday, 0, 0, 0, lt.tm_wday, lt.tm_yday, lt.tm_isdst))
    return max(1, int((now - midnight) / 60))

def _queue_snapshot() -> Dict[str, Any]:
    snap = {}
    total = 0
    now = time.time()
    for acc, ctx in main.accounts.items():
        q = ctx.get("comment_queue") or []
        total += len(q)
        items = []
        for ready_at, task in sorted(q, key=lambda x: x[0]):
            items.append({
                "ready_in": max(0, int(ready_at - now)),
                "disc_id": task.get("disc_id"),
                "reply_to": task.get("reply_to"),
                "text": task.get("text"),
                "source_link": task.get("source_link"),
                "task_id": task.get("task_id"),
            })
        snap[acc] = {"count": len(q), "items": items[:10]}  # не перегружаем UI
    return {"total": total, "per_account": snap}

def _accounts_overview() -> Dict[str, Any]:
    out = {}
    for acc, ctx in main.accounts.items():
        out[acc] = {
            "persona": ctx.get("persona_name"),
            "proxy_verified": bool(ctx.get("proxy_verified")),
            "proxy": ctx.get("proxy_hostport"),
            "campaign_paused": bool(ctx.get("campaign_paused", False)),

            # комментарии
            "cooldown": int(ctx.get("comment_cooldown") or 0),
            "next_send_at": int(ctx.get("next_send_at") or 0),
            "queue_count": len(ctx.get("comment_queue") or []),

            #  подписки
            "join_queue_count": len(ctx.get("join_queue") or []),
            "next_join_at": int(ctx.get("next_join_at") or 0),
            "join_daily_count": int(ctx.get("join_daily_count") or 0),
            "join_daily_limit": int(getattr(main, "JOIN_DAILY_LIMIT", 0) or 0),

            "joined_count": len(ctx.get("joined_channels") or []),
            "monitored_count": len(ctx.get("monitored_info") or {}),
            "script_running": bool(ctx.get("script_running")),
            "progress": ctx.get("progress") or {},
        }
    return out


@dashboard_bp.route("/dashboard")
def dashboard_page():
    # первичные значения
    kpis_24h = _totals_from_comments(minutes=1440)
    return render_template(
        "dashboard.html",
        totals_last_24h=kpis_24h,
        accounts=list(main.accounts.keys())
    )

@dashboard_bp.route("/api/dashboard/overview")
def dashboard_overview():
    now = int(time.time())
    k24h   = _totals_from_comments(minutes=1440)
    k_today = _totals_from_comments(minutes=_minutes_since_midnight_local())
    queue  = _queue_snapshot()
    accs   = _accounts_overview()
    # последние 50 действий

    # агрегаты
    kpis = {
        "sent_live": k_today["sent_count"],
        "sent_last_24h": k24h["sent_count"],
        "enqueued_now": queue["total"],
        "accounts_total": len(main.accounts),
        "joined_total": sum(a["joined_count"] for a in accs.values()),
        # ► детализация
        "sent_prev_last_24h": k24h.get("sent_prev_count", 0),
        "sent_new_last_24h": k24h.get("sent_new_count", 0),
        "sent_group_last_24h": k24h.get("sent_group_count", 0),
    }

    return jsonify({
        "now": now,
        "kpis": kpis,
        "top_channels": k24h["top_channels"],
        "queue": queue,
        "accounts": accs,
    })

@dashboard_bp.route("/api/dashboard/recent")
def dashboard_recent():
    limit = int(request.args.get("limit", 100))
    minutes = int(request.args.get("minutes", 1440))
    return jsonify({"items": _recent_comments(limit=limit, minutes=minutes)})

@dashboard_bp.route("/api/dashboard/proxy_health")
def dashboard_proxy_health():
    # читаем твоё proxy_health.json, дополняем фактом верификации у аккаунтов
    path = getattr(main, "PROXY_HEALTH_FILE", "proxy_health.json")
    try:
        with open(path, "r", encoding="utf-8") as f:
            health = json.load(f)
    except Exception:
        health = {"updated_at": None, "items": {}}

    acc = {}
    for name, ctx in main.accounts.items():
        acc[name] = {
            "proxy": ctx.get("proxy_hostport"),
            "verified": bool(ctx.get("proxy_verified")),
        }
    return jsonify({"health": health, "accounts": acc})
