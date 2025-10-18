# TGSender— панель управления Telegram-аккаунтами, прокси и рассылкой

Удобная веб-панель (Flask + Bootstrap) для работы с пулом Telegram-аккаунтов:

- Загрузка `.session` файлов
- Назначение/проверка прокси
- Подписки, рассылки, комментарии
- KPI и дашборд
- Поддержка API и сервисных утилит

---

## 🧩 Возможности

### 📌 Аккаунты

- Множественная загрузка `.session`
- Автопривязка и валидация прокси
- Карточки с аватаром, статусом, быстрыми действиями
- Редактирование Bio, отображение username, ФИО, телефона
- Массовые действия: удалить, очистить прокси, подготовка

### 🌐 Прокси

- Поддержка формата `HOST:PORT[:USER:PASS]`
- Проверка, гео, статус
- Автоподбор по фильтрам (страна, OK/FAIL)
- Массовое удаление, перемешивание

### 📬 Подписки

- Distribute — равномерное распределение каналов
- Duplicate — подписка всех на всё
- Управление промптами, отписка, очистка

### 📣 Рассылка и комментарии

- Очередь задач по аккаунтам
- Источники: prev_post, new_post, group_reply
- Пауза/возобновление по аккаунтам

### 📊 Дашборд

- KPI: отправлено сегодня/24ч, очередь, аккаунты
- Лента последних событий
- Топ каналов
- Сводка аккаунтов: прокси, мониторинг, cooldown

### ⚙️ UX и надежность

- Ограничение параллельных запросов
- Fetch с обработкой `429 Retry-After`
- Автотроттлинг при свёрнутой вкладке
- Светлая/тёмная тема (Bootswatch)
- Мобильный FAB

---



## 📁 Архитектура проекта

```text
parserCHATS/
├── app.py                  # Flask-приложение
├── dashboard.py            # Blueprint и API для дашборда
├── main.py                 # Ядро логики: аккаунты, очереди, подписки
├── templates/              # HTML-шаблоны (Jinja2)
│   ├── base.html           # Общий шаблон (темы, FAB, навбар)
│   ├── accounts.html       # Вкладка "Аккаунты"
│   ├── proxies.html        # Вкладка "Прокси"
│   ├── subscribe.html      # Подписки
│   ├── dashboard.html      # Дашборд
│   ├── index.html          # Парсинг задач
│   ├── chat.html           # AI-чат
│   └── login.html          # Форма входа
├── sessions/               # Telegram .session файлы (Telethon)
├── avatars_pool/           # Пул аватарок
├── avatars_cache/          # Кэш аватаров
├── config.json             # Конфиг: пути, настройки
├── accounts_map.json       # Привязки аккаунтов
├── proxy_assignments.json  # Назначения прокси
├── proxy_health.json       # Последняя проверка прокси
├── state.json              # Прогресс длительных задач
├── keywords.json           # Ключевые слова (поиск каналов)
└── .env                    # Секреты и логин
```




---

## 🚀 Установка и запуск

> Требуется: Python 3.10+, Git

```bash
git clone https://github.com/pokerpapa/TgSpam.git
cd TgSpam

python -m venv .venv
.venv\Scripts\activate        # Windows
# или
source .venv/bin/activate     # Linux/Mac

pip install -r requirements.txt

python app.py


---

## 🚀 Установка и запуск

> Требуется: Python 3.10+, Git

```bash
git clone https://github.com/pokerpapa/TgSpam.git
cd TgSpam

python -m venv .venv
.venv\Scripts\activate        # Windows
# или
source .venv/bin/activate     # Linux/Mac

pip install -r requirements.txt

python app.py
Открой: http://127.0.0.1:5000

⚙️ Конфигурация .env
Минимум:

ini
Copy code
ADMIN_USER=admin
ADMIN_PASS=change_me
FLASK_SECRET=случайная_строка
Дополнительно:

ini
Copy code
HOST=0.0.0.0
PORT=5000
🧪 Как использовать
1. Загрузка аккаунтов
Вкладка Аккаунты → "Добавить"

.session файлы загружаются пачкой

Опции: перезапись, автопрокси, проверка

2. Прокси
Вкладка Прокси → "Добавить"

Формат: host:port[:user:pass]

Проверка, гео, фильтры

Назначение прокси вручную или авто

3. Подписки
Вкладка Подписки

Слева: найденные каналы

Справа: промпт, аккаунты

Режимы: Distribute / Duplicate

4. Рассылка / Комментарии
Вкладка Дашборд и Аккаунты

Видно: очередь, отправки, статус

Можно: приостановить, возобновить

5. Подготовка
Выдели аккаунты → "Подготовить"

Появится прогресс, этапы, ETA

📡 API (основные маршруты)
Дашборд
GET /dashboard

GET /api/dashboard/overview

GET /api/dashboard/recent

GET /api/dashboard/proxy_health

Аккаунты / Прокси
POST /upload_sessions

POST /verify_proxy/<name>

POST /auto_assign/<name>

GET /profile/<name>

POST /set_bio/<name>

Подготовка
POST /prep/start/<name>

POST /prep/cancel/<name>

GET /prep/status/<name>

Кампания
POST /campaign/pause/<name>

POST /campaign/resume/<name>

🔐 Безопасность и эксплуатация
Авторизация через .env

Запуск за nginx / proxy рекомендован

Используйте HTTPS

Не коммитьте реальные .session и прокси

Храните бэкап sessions/

🧠 FAQ
Q: Где взять .session?
A: Через Telethon или другие Telegram-клиенты.

Q: Какой формат прокси?
A: HOST:PORT[:USER:PASS]

Q: Что значит distribute / duplicate?
A: Distribute — раскидывает по аккаунтам, Duplicate — всем одинаково.

Q: Что такое подготовка?
A: Фоновый прогрев аккаунта с прогрессом и контролем.
