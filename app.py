import os
import json
import threading
import asyncio
import requests
from flask import Flask, request, jsonify, render_template, send_file, redirect, current_app as app
from werkzeug.utils import secure_filename
import time
from main import accounts, get_account_context, subscribe_and_listen
import itertools, heapq
import re
from random import choice
from telethon.errors import FloodWaitError
from dashboard import dashboard_bp
from dotenv import load_dotenv
load_dotenv()  # подхватит .env рядом с app.py
from flask import redirect, url_for, request
import main
from main import (
    start_script, stop_script, load_keywords,
    subscribe_and_listen, leave_channel, get_account_context,
    accounts, available_sessions, log_proxy
)
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
proxy_pool_path = os.path.join(BASE_DIR, "proxies.txt")
app = Flask(__name__)
from flask import session, url_for
app.register_blueprint(dashboard_bp)

# короткий кэш профилей (чтобы не долбить API)
_PROFILE_CACHE = {}  # key: session_name -> (expires_ts, payload_json)
_PROFILE_CACHE_TTL = int(os.environ.get("PROFILE_CACHE_TTL", "180"))  # 3 мин
# ── Логин/пароль из .env ───────────────────────────────────────────────────────
ADMIN_LOGIN = os.environ.get('ADMIN_LOGIN', '').strip()
ADMIN_PASSWORD = os.environ.get('ADMIN_PASSWORD', '').strip()
if not ADMIN_LOGIN or not ADMIN_PASSWORD:
    print('[security] ВНИМАНИЕ: ADMIN_LOGIN/ADMIN_PASSWORD не заданы! Установите их в .env')


# ────────────────────────────────────────────────────────────────────────────────
# Аватарки: получить текущую, загрузить пул, поставить случайную
# ────────────────────────────────────────────────────────────────────────────────
AVATAR_CACHE_TTL = 300  # сек
_AVATAR_HOT_CACHE = {}  # name -> (expires_ts, exists_bool)


# Секрет для cookie-сессии
app.config['SECRET_KEY'] = os.environ.get('FLASK_SECRET', 'change-me-please')
app.config['SESSION_COOKIE_HTTPONLY'] = True
app.config['SESSION_COOKIE_SAMESITE'] = 'Lax'
app.config['SESSION_COOKIE_SECURE'] = bool(int(os.environ.get('SESSION_COOKIE_SECURE', '0')))  # 1 при HTTPS

# Куда пускать без логина
_AUTH_EXEMPT = ('/login', '/logout', '/static/', '/ping')  # добавил /logout чтобы выход всегда был доступен
# ============================
# ПОДГОТОВКА АККАУНТОВ (backend API)
# ============================
from threading import Lock

_PREP: dict[str, dict] = {}
_PREP_LOCK = Lock()
_PREP_CANCEL = set()  # имена аккаунтов, подготовку которых попросили отменить

def _prep_upsert(name: str, **kw):
    with _PREP_LOCK:
        item = _PREP.get(name) or {"name": name, "phase": "queued", "progress_pct": 0, "done": False}
        item.update(kw)
        _PREP[name] = item
        return dict(item)

def _prep_get(name: str) -> dict | None:
    with _PREP_LOCK:
        it = _PREP.get(name)
        return dict(it) if it else None

def _prep_remove(name: str):
    with _PREP_LOCK:
        _PREP.pop(name, None)

def _pretty_from_profile(p: dict | None) -> str | None:
    if not p: return None
    if p.get("username"): return "@" + p["username"]
    fn = (p.get("first_name") or "").strip()
    ln = (p.get("last_name") or "").strip()
    if fn or ln: return (fn + " " + ln).strip()
    if p.get("phone"): return "+" + str(p["phone"]).replace(r"[^\d+]", "")
    return None

def _seconds_until(ts: int | float | None) -> int:
    if not ts: return 0
    return max(0, int(ts - time.time()))

def _run_prep_worker(name: str):
    """
    Лёгкий пайплайн:
      1) verify_tg_proxy
      2) refresh_profile_photo_cache (для мини-аватара)
      3) get_account_profile (био/имя — для красивого заголовка)
      4) check_account_health (и, если карантин, показать счётчик)
    """
    try:
        if name not in main.available_sessions:
            _prep_upsert(name, phase="error", step_label="Аккаунт не найден", done=False)
            return

        ctx = main.get_account_context(name)
        ensure_loop_running(ctx)

        # queued -> running
        _prep_upsert(name, phase="running", step_label="Проверка прокси", progress_pct=5)

        # 1) verify proxy
        ok = False
        try:
            fut = asyncio.run_coroutine_threadsafe(main.verify_tg_proxy(name), ctx["loop"])
            ok = bool(fut.result(timeout=30))
        except Exception as e:
            _prep_upsert(name, phase="error", step_label=f"verify_proxy: {e}", done=False)
            return
        if not ok:
            _prep_upsert(name, phase="error", step_label="Прокси не верифицирован", progress_pct=10, done=False)
            return
        if name in _PREP_CANCEL: return

        _prep_upsert(name, step_label="Кэш аватарки", progress_pct=25)
        try:
            fut = asyncio.run_coroutine_threadsafe(main.refresh_profile_photo_cache(name), ctx["loop"])
            fut.result(timeout=30)
        except Exception:
            pass
        if name in _PREP_CANCEL: return

        _prep_upsert(name, step_label="Профиль", progress_pct=45)
        profile = {}
        try:
            fut = asyncio.run_coroutine_threadsafe(main.get_account_profile(name), ctx["loop"])
            res = fut.result(timeout=30)
            if res and res.get("ok"):
                profile = res
        except Exception:
            pass
        pretty = _pretty_from_profile(profile) or name
        if name in _PREP_CANCEL: return

        _prep_upsert(name, step_label="Проверка здоровья", progress_pct=70, pretty=pretty)
        try:
            fut = asyncio.run_coroutine_threadsafe(main.check_account_health(name), ctx["loop"])
            health = fut.result(timeout=45) or {}
        except Exception as e:
            health = {"error": str(e)}

        # карантин / флад — отрисуем блокировку и ETA
        blocked_until = int(health.get("restricted_until") or 0)
        eta = _seconds_until(blocked_until) if blocked_until else int(health.get("flood_wait") or 0)

        if health.get("restricted"):
            _prep_upsert(
                name,
                phase="running",
                step_label="Карантин аккаунта",
                blocked_until_ts=blocked_until,
                eta_sec=eta,
                progress_pct=90,
            )
        elif isinstance(eta, int) and eta > 0:
            _prep_upsert(
                name,
                phase="running",
                step_label=f"FloodWait {eta}s",
                eta_sec=eta,
                progress_pct=90,
            )

        if name in _PREP_CANCEL: return

        # done
        _prep_upsert(name, phase="done", step_label="Готов к работе", progress_pct=100, done=True, pretty=pretty)

    finally:
        # если отменили — подчистим
        if name in _PREP_CANCEL:
            _PREP_CANCEL.discard(name)
            _prep_remove(name)

@app.post("/prep/start/<session_name>")
def prep_start(session_name):
    if session_name not in main.available_sessions:
        return jsonify({"status": "error", "message": "Account not found"}), 404
    # уже в работе — просто вернём состояние
    cur = _prep_get(session_name)
    if cur and cur.get("phase") in ("queued", "running"):
        return jsonify({"status":"ok","item":cur})
    _prep_upsert(session_name, phase="queued", step_label="Ожидание старта", progress_pct=0, done=False)
    t = threading.Thread(target=_run_prep_worker, args=(session_name,), daemon=True)
    t.start()
    return jsonify({"status":"ok","item": _prep_get(session_name)})

@app.get("/prep/list")
def prep_list():
    with _PREP_LOCK:
        items = [dict(v) for v in _PREP.values()]
    return jsonify({"status":"ok","items": items})

@app.get("/prep/status/<session_name>")
def prep_status(session_name):
    it = _prep_get(session_name)
    if not it:
        return jsonify({"status":"ok","item": {"name": session_name, "phase":"idle", "progress_pct":0, "done": False}})
    return jsonify({"status":"ok","item": it})

@app.post("/prep/cancel/<session_name>")
def prep_cancel(session_name):
    _PREP_CANCEL.add(session_name)
    return jsonify({"status":"ok"})

@app.post("/prep/promote/<session_name>")
def prep_promote(session_name):

    _prep_remove(session_name)
    return jsonify({"status":"ok"})

def plan_channel_distribution(channels, account_names):
    """
    Распределяет уникальные ссылки каналов/чатов между аккаунтами БЕЗ повторов.

    """
    # 0) нормализация входа
    order = []
    seen = set()
    for raw in channels or []:
        s = (raw or "").strip()
        if not s or s in seen:
            continue
        seen.add(s); order.append(s)

    accs = [a for a in (account_names or []) if a in accounts]
    if not accs:
        # если галочки не выбраны — возьмём активные из main, но безопаснее явно требовать список
        accs = list(accounts.keys())

    # убедимся, что контексты созданы (joined_channels подтянутся из state)
    for a in accs:
        get_account_context(a)

    assignment = {a: [] for a in accs}
    covered = set()

    # 1) сначала — «кто уже внутри» → закрепляем
    for link in order:
        for a in accs:
            jc = accounts[a].get("joined_channels") or set()
            if link in jc:
                assignment[a].append(link)
                covered.add(link)
                break

    # 2) оставшиеся — по сбалансированному round-robin
    counter = itertools.count()
    heap = [(len(assignment[a]), next(counter), a) for a in accs]
    heapq.heapify(heap)

    for link in order:
        if link in covered:
            continue
        n, _, a = heapq.heappop(heap)
        assignment[a].append(link)
        heapq.heappush(heap, (n + 1, next(counter), a))

    return assignment
@app.get("/avatar/<session_name>")
def serve_avatar(session_name):
    """
    Отдаёт текущий аватар аккаунта из локального кэша.
    Если кэша нет — пробует обновить (с учётом прокси) или отдаёт SVG-заглушку.
    """
    import time
    from flask import Response, send_file

    if session_name not in main.available_sessions:
        return jsonify({"status":"error","message":"Account not found"}), 404

    # если недавно обновляли — не дёргаем Телеграм
    now = time.time()
    hot = _AVATAR_HOT_CACHE.get(session_name)
    path = main._avatar_cache_path(session_name)

    def _svg_placeholder(txt="A"):
        svg = f'''<svg xmlns="http://www.w3.org/2000/svg" width="96" height="96">
<rect width="100%" height="100%" rx="16" ry="16" fill="#e5e7eb"/>
<text x="50%" y="57%" text-anchor="middle" font-family="Arial, Helvetica, sans-serif" font-size="42" fill="#6b7280">{txt}</text>
</svg>'''
        return Response(svg, mimetype="image/svg+xml")

    # есть валидный кэш — отдадим его
    if hot and hot[0] > now and os.path.isfile(path):
        try:
            return send_file(path, mimetype="image/jpeg", conditional=True)
        except Exception:
            pass

    # попробуем обновить кэш (строго через прокси)
    ctx = main.get_account_context(session_name)
    if not ctx.get("proxy_verified", False):
        # нет прокси — отдаём заглушку
        _AVATAR_HOT_CACHE[session_name] = (now + AVATAR_CACHE_TTL, False)
        return _svg_placeholder(session_name[:1].upper())

    # обновим синхронно (жёсткий таймаут)
    fut = asyncio.run_coroutine_threadsafe(main.refresh_profile_photo_cache(session_name), ctx["loop"])
    try:
        res = fut.result(timeout=15)
        if res.get("ok") and res.get("exists") and os.path.isfile(path):
            _AVATAR_HOT_CACHE[session_name] = (now + AVATAR_CACHE_TTL, True)
            return send_file(path, mimetype="image/jpeg", conditional=True)
    except Exception:
        pass

    _AVATAR_HOT_CACHE[session_name] = (now + 120, False)
    return _svg_placeholder(session_name[:1].upper())


@app.post("/avatars/upload_pool")
def upload_avatar_pool():
    """
    Загрузка пачки картинок в пул.
    Ограничения: JPEG/PNG, до 3 МБ, безопасные имена.
    """
    from werkzeug.utils import secure_filename

    files = request.files.getlist("files")
    if not files:
        return jsonify({"status":"error","message":"files[] required (multipart)"}), 400

    os.makedirs(main.AVATAR_POOL_DIR, exist_ok=True)

    saved, skipped = [], []
    for f in files:
        if not f or not f.filename:
            continue
        ext = os.path.splitext(f.filename.lower())[-1]
        if ext not in (".jpg", ".jpeg", ".png"):
            skipped.append({"file": f.filename, "reason": "bad_ext"})
            continue
        f.seek(0, os.SEEK_END)
        size = f.tell()
        f.seek(0)
        if size > 3 * 1024 * 1024:
            skipped.append({"file": f.filename, "reason": "too_big"})
            continue
        name = secure_filename(f.filename)
        dst = os.path.join(main.AVATAR_POOL_DIR, name)
        try:
            f.save(dst)
            saved.append(name)
        except Exception as e:
            skipped.append({"file": f.filename, "reason": str(e)})

    return jsonify({"status":"ok","saved":saved,"skipped":skipped,"pool_dir":main.AVATAR_POOL_DIR})


@app.post("/avatar/set_random/<session_name>")
def set_random_avatar(session_name):
    """
    Выбирает случайную картинку из пула и ставит как аватарку аккаунта.
    Все вызовы идут через event loop аккаунта, с обработкой FLOOD_WAIT.
    """
    if session_name not in main.available_sessions:
        return jsonify({"status":"error","message":"Account not found"}), 404
    if not _proxy_enforced_or_400(session_name, "/avatar/set_random"):
        return jsonify({"status":"error","message":"Proxy not verified"}), 400
    block = _restricted_or_429(session_name, "/avatar/set_random")
    if block: return block


    pool = []
    try:
        for fn in os.listdir(main.AVATAR_POOL_DIR):
            if fn.lower().endswith((".jpg",".jpeg",".png")):
                pool.append(os.path.join(main.AVATAR_POOL_DIR, fn))
    except Exception:
        pass

    if not pool:
        return jsonify({"status":"error","message":"Avatar pool is empty. Upload via /avatars/upload_pool"}), 400

    pic = choice(pool)

    ctx = main.get_account_context(session_name)
    ensure_loop_running(ctx)
    fut = asyncio.run_coroutine_threadsafe(main.set_account_avatar(session_name, pic), ctx["loop"])
    try:
        res = fut.result(timeout=40)
    except Exception as e:
        return jsonify({"status":"error","message":str(e)}), 500

    if not res.get("ok"):
        # корректно отдадим 429, если троттлинг
        if res.get("error") in ("FloodWait","throttled","daily_limit"):
            resp = jsonify({"status":"error", **res})
            resp.status_code = 429
            if "retry_after" in res:
                resp.headers["Retry-After"] = str(int(res["retry_after"]))
            return resp
        return jsonify({"status":"error", **res}), 400

    # Успех — инвалидируем горячий кэш, чтобы картинка обновилась в UI
    main_time = time.time()
    _AVATAR_HOT_CACHE[session_name] = (main_time - 1, True)

    return jsonify({"status":"ok","edits_today":res.get("edits_today",1)})
@app.before_request
def _simple_gate():
    p = request.path or '/'
    if any(p == e or p.startswith(e) for e in _AUTH_EXEMPT):
        return
    if not session.get('authed'):
        return redirect(url_for('login', next=p))

@app.route('/login', methods=['GET', 'POST'])
def login():
    nxt = request.form.get('next') or request.args.get('next') or '/'
    if request.method == 'POST':
        user = (request.form.get('username') or '').strip()
        pwd  = (request.form.get('password') or '').strip()

        if not ADMIN_LOGIN or not ADMIN_PASSWORD:
            return render_template('login.html', error='ADMIN_LOGIN/ADMIN_PASSWORD не заданы на сервере', next=nxt), 500

        if user == ADMIN_LOGIN and pwd == ADMIN_PASSWORD:
            session['authed'] = True
            return redirect(nxt)

        return render_template('login.html', error='Неверные логин или пароль', next=nxt), 401

    return render_template('login.html', next=nxt)


@app.route('/logout')
def logout():
    session.clear()
    return redirect(url_for('login'))


import logging
from main import leave_logger, comment_logger, captcha_logger, chat_logger, proxy_logger

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s | %(levelname)s | %(name)s | %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)

# === Консольный вывод для всех наших именованных логгеров ===

root = logging.getLogger()
if not any(isinstance(h, logging.StreamHandler) for h in root.handlers):
    sh = logging.StreamHandler()
    sh.setLevel(logging.INFO)
    sh.setFormatter(logging.Formatter(
        '%(asctime)s | %(levelname)s | %(name)s | %(message)s',
        datefmt='%Y-%m-%d %H:%M:%S'
    ))
    root.addHandler(sh)


for lg in (leave_logger, comment_logger, captcha_logger, chat_logger, proxy_logger):
    lg.setLevel(logging.INFO)
    lg.propagate = True  # ключевая строка


logging.getLogger("telethon").setLevel(logging.INFO)

MISTRAL_CHAT_KEY = os.environ.get("MISTRAL_CHAT_KEY", "") or getattr(main, "MISTRAL_CHAT_KEY", "")
chat_history = []

def ensure_loop_running(ctx):
    if ctx.get("loop_thread") and ctx["loop_thread"].is_alive():
        return
    def _run_loop():
        asyncio.set_event_loop(ctx["loop"])
        # НЕ вызываем client.connect() здесь, чтобы не было прямого коннекта без прокси
        ctx["loop"].run_forever()
    t = threading.Thread(target=_run_loop, daemon=True)
    t.start()
    ctx["loop_thread"] = t


@app.route('/refresh_sessions', methods=['POST'])
def refresh_sessions_route():
    res = main.refresh_sessions()
    # если активного нет, можно назначить первый
    if main.active_session_name is None and main.available_sessions:
        main.active_session_name = main.available_sessions[0]
    return jsonify({"status":"ok", **res, "all": main.available_sessions})

# helper: внутренняя функция удаления одного аккаунта
def _delete_session_internal(name: str, rm_proxy: bool = False, rm_assign: bool = True) -> dict:
    info = {
        "exists": name in main.available_sessions,
        "deleted": False,
        "proxy_removed": False,
        "assignment_removed": False,
        "error": None,
    }
    if not info["exists"]:
        info["error"] = "Account not found"
        return info

    # если активный — разактивируем
    if main.active_session_name == name:
        main.active_session_name = None

    # аккуратно отключим клиента в его loop
    ctx = main.accounts.get(name) or {}
    loop = ctx.get("loop")
    if loop:
        try:
            fut = asyncio.run_coroutine_threadsafe(main.ensure_client_closed(name), loop)
            fut.result(timeout=10)
        except Exception as e:
            app.logger.warning(f"[delete_session] ensure_client_closed {name}: {e}")

    session_path = os.path.join(main.SESSION_DIR, f"{name}.session")
    proxy_path   = os.path.join(main.SESSION_DIR, f"{name}.proxy")

    last_err = None

    # удалить .session с ретраями (Windows lock)
    for attempt in range(10):
        try:
            if os.path.exists(session_path):
                os.remove(session_path)
            info["deleted"] = not os.path.exists(session_path)
            if info["deleted"]:
                break
        except PermissionError as e:
            last_err = str(e); time.sleep(0.25)
        except Exception as e:
            last_err = str(e); break

    # по желанию удалить .proxy sidecar
    if rm_proxy:
        try:
            if os.path.exists(proxy_path):
                os.remove(proxy_path)
                info["proxy_removed"] = True
        except Exception as e:
            last_err = (last_err or "") + f"; proxy: {e}"

    # по желанию очистить assignment
    if rm_assign:
        try:
            assigns = main._load_proxy_assignments()
            if name in assigns:
                assigns.pop(name, None)
                main._save_proxy_assignments(assigns)
                info["assignment_removed"] = True
        except Exception as e:
            last_err = (last_err or "") + f"; assign: {e}"

    # вычистить из внутренних структур
    try:
        main.available_sessions.remove(name)
    except ValueError:
        pass
    main.accounts.pop(name, None)

    info["error"] = last_err
    return info


@app.route('/delete_session', methods=['POST'])
def delete_session():
    """
    Удаляет один аккаунт (.session), опционально .proxy и assignment.
    """
    data = request.get_json(silent=True) or {}
    name = (data.get('name') or '').strip()
    rm_proxy = bool(data.get('remove_proxy', False))
    rm_assign = bool(data.get('remove_assignment', True))

    res = _delete_session_internal(name, rm_proxy=rm_proxy, rm_assign=rm_assign)
    if not res["exists"]:
        return jsonify({"status": "error", "message": "Account not found"}), 404

    # МАППИНГ под фронт (как ожидает JS)
    return jsonify({
        "status": "ok",
        "session_removed": bool(res["deleted"]),
        "proxy_sidecar_removed": bool(res["proxy_removed"]),
        "proxy_assignment_removed": bool(res["assignment_removed"]),
        "error": res["error"]
    })


# НОВОЕ: массовое удаление нескольких аккаунтов
@app.route('/delete_sessions_bulk', methods=['POST'])
def delete_sessions_bulk():
    """
    Принимает JSON:
    {
      "names": ["acc1", "acc2", ...],
      "remove_proxy": true/false,
      "remove_assignment": true/false
    }
    """
    data = request.get_json(silent=True) or {}
    names = data.get('names') or []
    rm_proxy = bool(data.get('remove_proxy', False))
    rm_assign = bool(data.get('remove_assignment', True))

    if not names:
        return jsonify({"status": "error", "message": "No names provided"}), 400

    results = {}
    ok = err = notfound = 0
    for n in names:
        res = _delete_session_internal(str(n), rm_proxy=rm_proxy, rm_assign=rm_assign)
        results[n] = res
        if not res["exists"]:
            notfound += 1
        elif res["deleted"]:
            ok += 1
        else:
            err += 1

    return jsonify({
        "status": "ok",
        "totals": {"requested": len(names), "deleted": ok, "errors": err, "not_found": notfound},
        "results": results
    })



def _safe_session_filename(fn: str) -> str:
    """
    Безопасное имя файла .session. Гарантируем расширение и убираем мусор.
    """
    base = os.path.basename(fn)
    if not base.endswith('.session'):
        base += '.session'
    # secure_filename может уронить кириллицу — но это безопасно.
    base = secure_filename(base)
    if not base.endswith('.session'):
        base += '.session'
    # запасной вариант имени
    if base == '.session':
        base = f"session_{int(time.time())}.session"
    return base

@app.route('/upload_sessions', methods=['POST'])
def upload_sessions():
    """
    Принимает multipart/form-data с полем 'files' (multiple).
    Параметры (optional):
      - overwrite=0/1
      - auto_proxy=0/1  (назначить прокси новым аккаунтам)
      - verify=0/1      (сразу проверить прокси новых аккаунтов)
    """
    if 'files' not in request.files:
        return jsonify({"status":"error","message":"Нет файлов"}), 400

    overwrite = str(request.form.get('overwrite', '0')).strip() in ('1','true','yes','on')
    auto_proxy = str(request.form.get('auto_proxy', '1')).strip() in ('1','true','yes','on')
    do_verify  = str(request.form.get('verify', '1')).strip() in ('1','true','yes','on')

    os.makedirs(main.SESSION_DIR, exist_ok=True)

    files = request.files.getlist('files')
    saved_names, skipped, overwritten, errors = [], [], [], []

    for f in files:
        try:
            if not f.filename:
                continue
            dst_name = _safe_session_filename(f.filename)
            if not dst_name.endswith('.session'):
                continue

            dst_path = os.path.join(main.SESSION_DIR, dst_name)
            if os.path.exists(dst_path) and not overwrite:
                skipped.append(dst_name)
                continue

            f.save(dst_path)
            if os.path.exists(dst_path) and overwrite:
                overwritten.append(dst_name)
            saved_names.append(dst_name)
        except Exception as e:
            errors.append({"file": f.filename, "error": str(e)})

    # пересканируем список аккаунтов
    res = main.refresh_sessions(auto_assign_missing_proxy=auto_proxy)

    # проверим прокси новых (по желанию)
    verified = {}
    if do_verify:
        for name in res.get("added", []):
            ctx = main.get_account_context(name)
            ensure_loop_running(ctx)
            try:
                ok = asyncio.run_coroutine_threadsafe(main.verify_tg_proxy(name), ctx["loop"]).result(timeout=20)
            except Exception:
                ok = False
            verified[name] = bool(ok)

    return jsonify({
        "status": "ok",
        "saved": saved_names,
        "skipped": skipped,
        "overwritten": overwritten,
        "errors": errors,
        "scan": res,
        "verified": verified,
        "all": main.available_sessions
    })


def _proxy_enforced_or_400(session_name: str, path: str):
    ctx = get_account_context(session_name)
    if not ctx.get("proxy_verified", False):
        log_proxy(session_name, "ENFORCE_BLOCK", proxy=ctx.get("proxy_hostport"), details=path)
        return False
    return True

def _restricted_or_429(session_name: str, path: str):
    ctx = get_account_context(session_name)
    until = float(ctx.get("restricted_until") or 0.0)
    now = time.time()
    if until > now:
        eta = int(until - now)
        app.logger.warning(f"[RESTRICT] block {path} for {session_name} ({eta}s left)")
        resp = jsonify({
            "status": "error",
            "message": "account_restricted",
            "retry_after": eta,
            "restricted_until": int(until)
        })
        resp.status_code = 429
        resp.headers["Retry-After"] = str(eta)
        return resp
    return None

@app.route('/chat_page', methods=['GET'])
def chat_page():
    return render_template('chat.html')

# === В /accounts — список стран и статусы без создания клиентов ===
@app.route('/accounts', methods=['GET'])
def accounts_page():

    statuses = {}
    hostports = {}
    for name in available_sessions:
        ctx = main.accounts.get(name) or {}
        statuses[name] = bool(ctx.get("proxy_verified", False))
        hostports[name] = ctx.get("proxy_hostport")

    # Счётчики аккаунтов
    total_count = len(available_sessions)
    ok_count = sum(1 for n in available_sessions if statuses.get(n))
    fail_count = total_count - ok_count

    pool = main.load_proxy_pool()
    health = main.load_proxy_health()
    items = (health or {}).get("items", {}) or {}

    # уникальные (cc, country) для селекта
    cc_set = set()
    for v in items.values():
        cc = v.get("country_code")
        if cc:
            cc_set.add((cc.upper(), v.get("country")))
    country_options = sorted(cc_set, key=lambda t: (t[1] or t[0]))

    return render_template(
        'accounts.html',
        session_names=available_sessions,
        active_account=main.active_session_name,
        proxy_statuses=statuses,
        proxy_hostports=hostports,
        proxy_pool_path=main.PROXY_POOL_FILE,
        proxy_pool_count=len(pool),
        country_options=country_options,
        total_count=total_count,
        ok_count=ok_count,
        fail_count=fail_count
    )

# === Массовая проверка прокси на аккаунтах ===
@app.post("/verify_proxy_all")
def verify_proxy_all():
    results = {}
    ok = fail = 0
    for name in available_sessions:
        ctx = get_account_context(name)
        ensure_loop_running(ctx)
        fut = asyncio.run_coroutine_threadsafe(main.verify_tg_proxy(name), ctx["loop"])
        try:
            v = bool(fut.result(timeout=30))
            results[name] = {"verified": v}
            if v: ok += 1
            else: fail += 1
        except Exception as e:
            results[name] = {"verified": False, "error": str(e)}
            fail += 1

    return jsonify({
        "status": "ok",
        "results": results,
        "totals": {"accounts": len(available_sessions), "ok": ok, "fail": fail}
    })


@app.route('/accounts/select/<session_name>', methods=['GET'])
def select_account(session_name):
    if session_name not in available_sessions:
        return jsonify({"status": "Account not found"}), 404

    main.active_session_name = session_name
    ctx = get_account_context(session_name)

    ensure_loop_running(ctx)

    fut = asyncio.run_coroutine_threadsafe(main.verify_tg_proxy(session_name), ctx["loop"])
    ok = False
    try:
        ok = bool(fut.result(timeout=20))
    except Exception as e:
        app.logger.warning(f"[verify on select] {e}")

    # Хендлер только если прокси подтверждён
    if ok and ctx.get("monitored_info") and not ctx.get("event_handler_added"):
        ctx["client"].add_event_handler(main.handle_new_message, main.events.NewMessage())
        ctx["event_handler_added"] = True

    return redirect('/')


@app.route('/verify_proxy/<session_name>', methods=['POST'])
def verify_proxy(session_name):
    if session_name not in available_sessions:
        return jsonify({"status":"error","message":"Account not found"}), 404
    ctx = get_account_context(session_name)
    ensure_loop_running(ctx)
    fut = asyncio.run_coroutine_threadsafe(main.verify_tg_proxy(session_name), ctx["loop"])
    try:
        ok = fut.result(timeout=30)
        return jsonify({"status":"ok","verified": bool(ok)})
    except Exception as e:
        return jsonify({"status":"error","message": str(e)}), 500

@app.route('/set_proxy/<session_name>', methods=['POST'])
def set_proxy(session_name):
    if session_name not in available_sessions:
        return jsonify({"status":"error","message":"Account not found"}), 404
    data = request.get_json(silent=True) or {}
    line = (data.get("line") or "").strip()
    if not line:
        return jsonify({"status":"error","message":"Empty proxy line"}), 400

    sidecar = os.path.join(main.SESSION_DIR, f"{session_name}.proxy")
    try:
        with open(sidecar, "w", encoding="utf-8") as f:
            f.write(line + "\n")
    except Exception as e:
        return jsonify({"status":"error","message":str(e)}), 500

    # Применяем новый прокси (пересоздаём клиент)
    main.apply_proxy_from_current_sources(session_name)
    ctx = get_account_context(session_name)
    ensure_loop_running(ctx)

    fut = asyncio.run_coroutine_threadsafe(main.verify_tg_proxy(session_name), ctx["loop"])
    try:
        ok = fut.result(timeout=20)
    except Exception:
        ok = False
    return jsonify({"status":"ok","verified": bool(ok)})

# NEW: автоподбор прокси — один аккаунт (с причинами)
# === /auto_assign/<session_name> — принимаем фильтры ===
@app.route('/auto_assign/<session_name>', methods=['POST'])
def auto_assign_one(session_name):
    if session_name not in available_sessions:
        return jsonify({"status":"error","message":"Account not found"}), 404

    data = request.get_json(silent=True) or {}
    force = bool(data.get("force", True))
    filters = data.get("filters") or {
        "countries": data.get("countries"),
        "only_ok": data.get("only_ok"),
        "occupancy": data.get("occupancy")
    }

    # Сколько кандидатов получилось под фильтры — полезно показать в UI
    cand = main.filter_proxy_candidates(session_name, force=force, filters=filters)
    assigned, line = main.auto_assign_proxy(session_name, force=force, filters=filters)
    pool_count = len(main.load_proxy_pool())

    reason = None
    if not assigned:
        if pool_count == 0:
            reason = 'pool_empty'
        elif len(cand) == 0:
            reason = 'no_candidates'
        else:
            reason = 'unknown'

    ctx = main.get_account_context(session_name)
    ensure_loop_running(ctx)
    fut = asyncio.run_coroutine_threadsafe(main.verify_tg_proxy(session_name), ctx["loop"])
    try:
        ok = fut.result(timeout=20)
    except Exception:
        ok = False
    return jsonify({
        "status":"ok",
        "assigned": bool(assigned),
        "line": line,
        "verified": bool(ok),
        "reason": reason,
        "pool_count": pool_count,
        "pool_path": main.PROXY_POOL_FILE,
        "candidates": len(cand),
        "filters": filters
    })

# === /auto_assign_all — тоже принимаем фильтры и считаем причины ===
@app.route('/auto_assign_all', methods=['POST'])
def auto_assign_all():
    data = request.get_json(silent=True) or {}
    force = bool(data.get("force", False))
    filters = data.get("filters") or {
        "countries": data.get("countries"),
        "only_ok": data.get("only_ok"),
        "occupancy": data.get("occupancy")
    }
    pool_count = len(main.load_proxy_pool())
    results = {}
    for name in available_sessions:
        cand = main.filter_proxy_candidates(name, force=force, filters=filters)
        assigned, line = main.auto_assign_proxy(name, force=force, filters=filters)

        ctx = main.get_account_context(name)
        ensure_loop_running(ctx)
        fut = asyncio.run_coroutine_threadsafe(main.verify_tg_proxy(name), ctx["loop"])
        try:
            ok = fut.result(timeout=20)
        except Exception:
            ok = False

        reason = None
        if not assigned:
            if pool_count == 0:
                reason = 'pool_empty'
            elif os.path.isfile(os.path.join(main.SESSION_DIR, f"{name}.proxy")) and not force:
                reason = 'already_had'
            elif len(cand) == 0:
                reason = 'no_candidates'
            else:
                reason = 'unknown'

        results[name] = {
            "assigned": bool(assigned),
            "line": line,
            "verified": bool(ok),
            "reason": reason,
            "candidates": len(cand)
        }
    return jsonify({"status":"ok","results":results, "pool_count": pool_count, "pool_path": main.PROXY_POOL_FILE, "filters": filters})

#  удалить текущий прокси у аккаунта
@app.route('/clear_proxy/<session_name>', methods=['POST'])
def clear_proxy(session_name):
    if session_name not in available_sessions:
        return jsonify({"status":"error","message":"Account not found"}), 404

    info = main.clear_assigned_proxy(session_name)
    ctx = main.get_account_context(session_name)
    ensure_loop_running(ctx)
    fut = asyncio.run_coroutine_threadsafe(main.verify_tg_proxy(session_name), ctx["loop"])
    try:
        ok = fut.result(timeout=20)
    except Exception:
        ok = False
    return jsonify({
        "status": "ok",
        "cleared": info,
        "verified": bool(ok)
    })

#  проверка валидности всех аккаунтов c учётом прокси
@app.route('/check_accounts', methods=['POST'])
def check_accounts():
    """
    Проверяет здоровье аккаунтов c учётом прокси и детальных флагов:
    banned, deactivated, api_ok, can_send_to_self, flood_wait и т.д.
    """
    results = {}

    for name in available_sessions:
        ctx = get_account_context(name)
        proxy_ok = bool(ctx.get("proxy_verified", False))

        # Если прокси не верифицирован — пропускаем
        if not proxy_ok:
            results[name] = {
                "proxy_verified": False,
                "skipped": True,
                "reason": "proxy_not_verified",
                "checked": False,
                "authorized": None,
                "error": None
            }
            continue

        ensure_loop_running(ctx)
        fut = asyncio.run_coroutine_threadsafe(
            main.check_account_health(name),  # <- детальная проверка
            ctx["loop"]
        )
        try:
            health = fut.result(timeout=40)
            # health содержит: authorized, banned, deactivated, api_ok,
            # can_send_to_self, flood_wait, username, phone, error
            results[name] = {
                "proxy_verified": True,
                "skipped": False,
                "checked": True,
                "authorized": bool(health.get("authorized")),
                **health  # разворачиваем, чтобы сразу видеть banned/deactivated/etc
            }
        except Exception as e:
            results[name] = {
                "proxy_verified": True,
                "skipped": False,
                "checked": True,
                "authorized": None,
                "error": str(e)
            }

    return jsonify({"status": "ok", "results": results})


@app.route('/')
def index():
    if len(available_sessions) > 1 and main.active_session_name is None:
        return redirect('/accounts')
    cfg = load_keywords()
    ctx = get_account_context(main.active_session_name) if main.active_session_name else None
    return render_template(
        'index.html',
        script_running=(ctx["script_running"] if ctx else False),
        percent=(ctx["progress"]["percent"] if ctx else 0),
        name_queries=cfg.get("name_queries", []),
        only_with_comments=cfg.get("only_with_comments", False),
        active_account=main.active_session_name
    )

@app.route('/status', methods=['GET'])
def status():
    if main.active_session_name is None:
        return jsonify({"status": "Нет активного аккаунта", "percent": 0})
    ctx = get_account_context(main.active_session_name)
    return jsonify(ctx["progress"])

@app.route('/start', methods=['POST'])
def start():
    if main.active_session_name is None:
        return jsonify({"status": "No active account selected"}), 400
    if not _proxy_enforced_or_400(main.active_session_name, "/start"):
        return jsonify({"status": "Proxy not verified"}), 400
    if accounts[main.active_session_name]["script_running"]:
        stop_script(main.active_session_name)
    threading.Thread(target=start_script, args=(main.active_session_name,), daemon=True).start()
    return jsonify({"status": "Script started"})

@app.route('/stop', methods=['POST'])
def stop():
    if main.active_session_name is None or not accounts[main.active_session_name]["script_running"]:
        return jsonify({"status": "Script is not running"})
    if not _proxy_enforced_or_400(main.active_session_name, "/stop"):
        return jsonify({"status": "Proxy not verified"}), 400
    stop_script(main.active_session_name)
    return jsonify({"status": "Script stopped"})
@app.get("/campaign/status/<session_name>")
def campaign_status(session_name):
    if session_name not in main.available_sessions:
        return jsonify({"status": "error", "message": "Account not found"}), 404
    ctx = main.get_account_context(session_name)
    return jsonify({"status": "ok", "campaign_paused": bool(ctx.get("campaign_paused", False))})

@app.post("/campaign/pause/<session_name>")
def campaign_pause(session_name):
    if session_name not in main.available_sessions:
        return jsonify({"status": "error", "message": "Account not found"}), 404
    res = main.set_campaign_paused(session_name, True)
    return jsonify({"status": "ok", **res})

@app.post("/campaign/resume/<session_name>")
def campaign_resume(session_name):
    if session_name not in main.available_sessions:
        return jsonify({"status": "error", "message": "Account not found"}), 404
    res = main.set_campaign_paused(session_name, False)
    return jsonify({"status": "ok", **res})

@app.route('/download', methods=['GET'])
def download():
    if main.active_session_name is None:
        return jsonify({"status": "No account selected"}), 400
    file_path = f"telegram_chats_{main.active_session_name}.xlsx"
    if os.path.exists(file_path):
        return send_file(file_path, as_attachment=True)
    return jsonify({"status": "File not found"}), 404

@app.route('/update_keywords', methods=['POST'])
def update_keywords():
    data = request.get_json()
    new_cfg = {
        "name_queries": data.get("name_queries", []),
        "link_queries": data.get("link_queries", []),
        "only_with_comments": data.get("only_with_comments", False)
    }
    with open('keywords.json', 'w', encoding='utf-8') as f:
        json.dump(new_cfg, f, ensure_ascii=False, indent=2)
    return jsonify({"status": "Keywords updated"})

@app.route('/reset_keywords', methods=['POST'])
def reset_keywords():
    default_cfg = {"name_queries": [], "link_queries": [], "only_with_comments": False}
    with open('keywords.json', 'w', encoding='utf-8') as f:
        json.dump(default_cfg, f, ensure_ascii=False, indent=2)
    return jsonify({"status": "Keywords reset"})

@app.route('/subscribe', methods=['GET'])
def subscribe_page():
    # Если много сессий и активная не выбрана — ведём на "Аккаунты"
    if len(available_sessions) > 1 and main.active_session_name is None:
        return redirect('/accounts')

    # Вместо JSON-ошибки показываем красивую плашку на самой странице
    proxy_required = False
    if main.active_session_name is not None and not _proxy_enforced_or_400(main.active_session_name, "/subscribe[GET]"):
        proxy_required = True

    ctx = get_account_context(main.active_session_name) if main.active_session_name else None

    # Фоновые хендлеры подключаем только когда прокси ОК
    if ctx and not proxy_required:
        ensure_loop_running(ctx)
        if ctx["monitored_info"] and not ctx.get("event_handler_added"):
            ctx["client"].add_event_handler(main.handle_new_message, main.events.NewMessage())
            ctx["event_handler_added"] = True

    return render_template(
        'subscribe.html',
        # Если прокси не готов — не грузим тяжёлые списки, отдадим пустые
        channels=(main.global_found_channels if not proxy_required else []),
        joined=(ctx["joined_names"] if ctx and not proxy_required else {}),
        joined_entities=(ctx["joined_entities"] if ctx and not proxy_required else {}),
        monitored_info=(ctx["monitored_info"] if ctx and not proxy_required else {}),
        universal_prompt=main.UNIVERSAL_PROMPT,
        active_account=main.active_session_name,
        account_options=available_sessions,
        proxy_required=proxy_required  # <-- флаг в шаблон
    )


@app.post("/subscribe")
def subscribe_route():
    """
    Принимает JSON:
      {
        "comment": "...",
        "channels": ["https://t.me/...", ...],
        "accounts": ["acc1","acc2", ...],      # опционально
        "assign_mode": "distribute" | "duplicate"  # НОВОЕ
      }
    """
    from flask import request, jsonify
    data = request.get_json(silent=True) or {}

    comment     = (data.get("comment") or "").strip()
    channels    = data.get("channels") or []
    acc_list    = data.get("accounts") or []
    assign_mode = (data.get("assign_mode") or "duplicate").lower()

    # safety
    if not comment or not channels:
        return jsonify({"status": "Ошибка: укажите ссылки и промпт"}), 400

    # фильтруем уникальные ссылки
    norm_channels = []
    seen = set()
    for c in channels:
        s = (c or "").strip()
        if s and s not in seen:
            seen.add(s); norm_channels.append(s)

    if not acc_list:
        # если пользователь не выбрал галочки — используем все известные аккаунты
        acc_list = list(accounts.keys())

    # ── ПЛАН РАСПРЕДЕЛЕНИЯ ──────────────────────────────────────────────────────
    if assign_mode == "distribute" and len(acc_list) > 1:
        assignment = plan_channel_distribution(norm_channels, acc_list)
    else:
        assignment = {a: list(norm_channels) for a in acc_list}

    # ── Запуск подписки для каждого аккаунта ────────────────────────────────────
    results = {}
    started = 0

    for acc, acc_links in assignment.items():
        try:
            ctx = get_account_context(acc)

            # пустое — пропускаем (например, все каналы уже закрепились за другими)
            if not acc_links:
                results[acc] = {"planned": 0, "started": False, "reason": "empty"}
                continue

            # нет прокси/прокси не верифицирован — не ставим задачу
            if not ctx.get("proxy_verified", False):
                results[acc] = {"planned": len(acc_links), "started": False, "reason": "proxy_not_verified"}
                continue
            # ✚ карантин — не стартуем задачи для этого аккаунта
            if (get_account_context(acc).get("restricted_until") or 0) > time.time():
                results[acc] = {"planned": len(acc_links), "started": False, "reason": "account_restricted"}
                continue

            # гарантируем живой цикл перед постановкой задачи
            ensure_loop_running(ctx)

            # ✚ ставим задания в очередь join'ов (не блокирует, воркер сам всё выполнит)
            main.enqueue_joins(acc, acc_links, comment)

            results[acc] = {"planned": len(acc_links), "started": True}
            started += 1


        except Exception as e:
            results[acc] = {"planned": len(acc_links), "started": False, "error": str(e)}

    # Человеко-читаемое резюме
    summary = {acc: len(links) for acc, links in assignment.items()}
    msg = (
        f"Режим: {'распределение' if assign_mode=='distribute' and len(acc_list)>1 else 'дублирование'} · "
        f"аккаунтов: {len(acc_list)} · всего ссылок: {len(norm_channels)}"
    )

    return jsonify({
        "status": msg,
        "assignment": assignment,  # acc -> [links...]
        "summary": summary,        # acc -> count
        "results": results         # статусы запуска по аккаунтам
    })



@app.route('/leave_channel', methods=['POST'])
def leave_channel_route():
    data = request.get_json()
    link = data.get('link')
    if main.active_session_name is None:
        return jsonify({"status": "No active account selected"}), 400
    if not _proxy_enforced_or_400(main.active_session_name, "/leave_channel"):
        return jsonify({"status": "Proxy not verified"}), 400

    ctx = get_account_context(main.active_session_name)
    ensure_loop_running(ctx)

    # предварительная проверка авторизации
    fut_ready = asyncio.run_coroutine_threadsafe(
        main.ensure_client_ready(main.active_session_name, require_auth=True),
        ctx["loop"]
    )
    try:
        fut_ready.result(timeout=10)
    except RuntimeError as e:
        return jsonify({"status": "error", "message": str(e)}), 400
    except Exception as e:
        return jsonify({"status": "error", "message": f"{e}"}), 500

    future = asyncio.run_coroutine_threadsafe(leave_channel(link, main.active_session_name), ctx["loop"])
    try:
        future.result(timeout=15)
    except Exception as e:
        app.logger.warning(f"[leave_channel] error leaving {link}: {e}")

    return jsonify({"status": "Channel left"})

@app.route('/reset_channels', methods=['POST'])
def reset_channels():
    main.global_found_channels.clear()
    for ctx in main.accounts.values():
        if "found_channels" in ctx:
            ctx["found_channels"].clear()
    return jsonify({"status": "ok"})

@app.route('/update_prompt', methods=['POST'])
def update_prompt():
    data = request.get_json()
    link = data.get('link')
    new_prompt = data.get('prompt')
    if main.active_session_name is None:
        return jsonify({"status": "error", "message": "No active account"}), 400
    if not _proxy_enforced_or_400(main.active_session_name, "/update_prompt"):
        return jsonify({"status":"error","message":"Proxy not verified"}), 400
    ctx = get_account_context(main.active_session_name)

    # CHANGED: не требуем entity; ищем по monitored_info/сохранённым id
    chan_id = None
    # 1) если entity есть — берём id
    ent = ctx["joined_entities"].get(link)
    if ent:
        chan_id = getattr(ent, 'id', None)
    # 2) иначе попробуем найти по имени в joined_names
    if chan_id is None:
        for lnk, name in ctx["joined_names"].items():
            if lnk == link:
                ent2 = ctx["joined_entities"].get(lnk)
                if ent2:
                    chan_id = getattr(ent2, 'id', None)
                break

    if chan_id in ctx["monitored_info"]:
        existing = ctx["monitored_info"][chan_id]
        if isinstance(existing, (list, tuple)):
            disc_id = existing[0] if len(existing) >= 1 else chan_id
            mode = existing[2] if len(existing) >= 3 else "discussion"
        else:
            disc_id, mode = chan_id, "discussion"
        ctx["monitored_info"][chan_id] = (disc_id, new_prompt, mode)
        return jsonify({"status": "ok"})


@app.route('/chat', methods=['POST'])
def chat_with_mistral():
    data = request.get_json()
    user_msg = data.get('message')
    if not user_msg:
        return jsonify({"error": "Empty message"}), 400

    chat_history.append({"role": "user", "content": user_msg})
    payload = {
        "model": main.MISTRAL_MODEL,
        "messages": chat_history,
        "temperature": 0.7,
        "top_p": 1,
        "max_tokens": 200,
        "stream": False
    }
    headers = {
        "Authorization": f"Bearer {MISTRAL_CHAT_KEY}",
        "Content-Type": "application/json"
    }
    try:
        resp = requests.post(main.MISTRAL_URL, headers=headers, json=payload, timeout=10)
        resp.raise_for_status()
    except requests.exceptions.HTTPError as e:
        if resp.status_code == 429:
            return jsonify({"error": "Слишком много запросов, попробуйте чуть позже"}), 429
        return jsonify({"error": str(e)}), resp.status_code
    except Exception as e:
        return jsonify({"error": str(e)}), 500

    result = resp.json()
    assistant_reply = result["choices"][0]["message"]["content"].strip()
    chat_history.append({"role": "assistant", "content": assistant_reply})
    return jsonify({"reply": assistant_reply})

@app.route('/reset_chat', methods=['POST'])
def reset_chat():
    global chat_history
    chat_history = []
    return jsonify({"status": "ok"})

@app.route('/remove_found_channel', methods=['POST'])
def remove_found_channel():
    data = request.get_json()
    link = data.get('link')
    if not link:
        return jsonify({"status": "error", "error": "No link provided"}), 400

    main.global_found_channels = [tup for tup in main.global_found_channels if tup[1] != link]
    for ctx in main.accounts.values():
        ctx["found_channels"] = [tup for tup in ctx.get("found_channels", []) if tup[1] != link]

    return jsonify({"status": "ok"})
# ────────────────────────────────────────────────────────────────────────────────
# СТРАНИЦА ПРОКСИ + API
# ────────────────────────────────────────────────────────────────────────────────
@app.route('/proxies', methods=['GET'])
def proxies_page():
    pool = main.load_proxy_pool()
    health = main.load_proxy_health()
    assigns = main._load_proxy_assignments()  # ok как внутренний вызов
    items = health.get("items", {})

    proxies = []
    for line in pool:
        parsed = main.parse_proxy_line(line)
        _, hp = main.build_telethon_proxy(parsed, main.TG_PROXY_TYPE) if parsed else (None, None)
        user = (parsed or {}).get("user")
        used_by = [acc for acc, ln in assigns.items() if ln == line]
        h = items.get(line) or {}
        proxies.append({
            "line": line,
            "hostport": hp,
            "user": user,
            "used_by": used_by,
            "ok": h.get("ok"),
            "error": h.get("error"),
            "checked_at": h.get("checked_at"),
            # ✚ страна/код/ip (могут отсутствовать до первой проверки)
            "country": h.get("country"),
            "country_code": h.get("country_code"),
            "ip": h.get("ip"),
        })


    return render_template(
        'proxies.html',
        proxies=proxies,
        proxy_pool_path=main.PROXY_POOL_FILE,
        proxy_pool_count=len(pool),
        last_updated=health.get("updated_at")
    )

@app.route('/check_proxy_pool', methods=['POST'])
def check_proxy_pool():
    try:
        full = main.check_proxy_pool_sync()
        return jsonify({"status": "ok", "updated_at": full.get("updated_at"), "results": full.get("items", {})})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

@app.route('/check_proxy_line', methods=['POST'])
def check_proxy_line():
    data = request.get_json(silent=True) or {}
    line = (data.get("line") or "").strip()
    if not line:
        return jsonify({"status": "error", "message": "Empty line"}), 400
    try:
        res = main.check_single_proxy_sync(line)
        return jsonify({"status": "ok", "result": res})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

@app.route('/add_proxy', methods=['POST'])
def add_proxy():
    data = request.get_json(force=True)
    lines = data.get('lines') or ([data.get('line')] if data.get('line') else [])
    if not lines:
        return jsonify({'status':'error','message':'Нет строк'})

    added = []
    try:
        with open(main.PROXY_POOL_FILE, 'a', encoding='utf-8') as f:
            for l in lines:
                l = (l or '').strip()
                if not l: continue
                f.write(l+'\n')
                added.append(l)
    except Exception as e:
        return jsonify({'status':'error','message':str(e)})

    return jsonify({'status':'ok','added': len(added), 'lines': added})


@app.route('/profile/<session_name>', methods=['GET'])
def get_profile(session_name):
    if session_name not in main.available_sessions:
        return jsonify({"status": "error", "message": "Account not found"}), 404
    if not _proxy_enforced_or_400(session_name, "/profile[GET]"):
        return jsonify({"status": "error", "message": "Proxy not verified"}), 400

    # 1) быстрый ответ из кэша
    now = time.time()
    cached = _PROFILE_CACHE.get(session_name)
    if cached and cached[0] > now:
        return jsonify(cached[1])

    # 2) живой вызов
    ctx = main.get_account_context(session_name)
    ensure_loop_running(ctx)
    fut = asyncio.run_coroutine_threadsafe(main.get_account_profile(session_name), ctx["loop"])
    try:
        res = fut.result(timeout=20)
    except FloodWaitError as e:
        retry = int(getattr(e, "seconds", 0) or 1)
        body = {"status": "error", "message": "FloodWait", "retry_after": retry}
        resp = jsonify(body)
        resp.status_code = 429
        resp.headers["Retry-After"] = str(retry)
        return resp
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

    if res.get("ok"):
        payload = {"status": "ok", **res}
        _PROFILE_CACHE[session_name] = (now + _PROFILE_CACHE_TTL, payload)
        return jsonify(payload)

    # неуспех без FloodWait → 500, как и раньше
    return jsonify({"status": "error", **res}), 500


@app.route('/set_bio/<session_name>', methods=['POST'])
def set_bio(session_name):
    if session_name not in main.available_sessions:
        return jsonify({"status":"error", "message":"Account not found"}), 404
    if not _proxy_enforced_or_400(session_name, "/set_bio[POST]"):
        return jsonify({"status":"error","message":"Proxy not verified"}), 400
    block = _restricted_or_429(session_name, "/set_bio")
    if block: return block


    data = request.get_json(silent=True) or {}
    bio = (data.get("bio") or "").strip()

    ctx = main.get_account_context(session_name)
    ensure_loop_running(ctx)
    fut = asyncio.run_coroutine_threadsafe(main.set_account_bio(session_name, bio), ctx["loop"])
    try:
        res = fut.result(timeout=20)
    except Exception as e:
        res = {"ok": False, "error": str(e)}

    if res.get("ok"):
        return jsonify({"status":"ok", **res})
    return jsonify({"status":"error", **res}), 500


@app.route('/remove_proxy', methods=['POST'])
def remove_proxy():
    data = request.get_json(silent=True) or {}
    line = (data.get("line") or "").strip()
    if not line:
        return jsonify({"status":"error","message":"Empty proxy line"}), 400

    pool = main.load_proxy_pool()
    if line not in pool:
        return jsonify({"status":"error","message":"Proxy not found"}), 404

    pool = [p for p in pool if p != line]
    try:
        with open(main.PROXY_POOL_FILE, "w", encoding="utf-8") as f:
            f.write("\n".join(pool) + "\n")
    except Exception as e:
        return jsonify({"status":"error","message":str(e)}), 500

    return jsonify({"status":"ok","line": line})

# app.py
if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5001, debug=True, use_reloader=False)
