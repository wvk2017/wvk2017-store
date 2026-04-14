import base64
import hashlib
import io
import json
import math
import os
import platform
import re
import errno
import tempfile
import threading
import time
import urllib.request
import uuid
import zipfile
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import urlsplit

try:
    import pg8000  # type: ignore
except Exception:
    pg8000 = None


_DEFAULT_STATIC_DIR = "/app/static" if Path("/app/static").exists() else "/data/ui/static"
STATIC_DIR = Path(os.getenv("STATIC_DIR", _DEFAULT_STATIC_DIR))
MININGCORE_API_URL = os.getenv("MININGCORE_API_URL", "http://miningcore:4000").strip().rstrip("/")
MININGCORE_POOL_ID = os.getenv("MININGCORE_POOL_ID", "dgb-sha256-1").strip()
MININGCORE_POOL_IDS = os.getenv("MININGCORE_POOL_IDS", "").strip()
STRATUM_PORTS = os.getenv("STRATUM_PORTS", "").strip()
MININGCORE_CONF_PATH = Path(os.getenv("MININGCORE_CONF_PATH", "/data/pool/config/miningcore.json"))
NODE_CONF_PATH = Path("/data/node/digibyte.conf")
NODE_LOG_PATH = Path("/data/node/debug.log")
NODE_REINDEX_FLAG_PATH = Path("/data/node/.reindex-chainstate")
NODE_DBCACHE_MB_PATH = Path("/data/node/.dbcache_mb")
STATE_DIR = Path("/data/ui/state")
POOL_SETTINGS_STATE_PATH = STATE_DIR / "pool_settings.json"
INSTALL_ID_PATH = STATE_DIR / "install_id.txt"
NODE_CACHE_PATH = STATE_DIR / "node_cache.json"
NODE_EXTRAS_CACHE_PATH = STATE_DIR / "node_extras_cache.json"
CHECKIN_STATE_PATH = STATE_DIR / "checkin.json"
BLOCKS_STATE_PATH = STATE_DIR / "blocks_state.json"
PAYOUT_HISTORY_PATH = STATE_DIR / "payout_history.json"
BESTSHARE_RESET_PATH = STATE_DIR / "bestshare_reset.json"
# Miningcore requires a syntactically valid payout address in its config at startup.
# This is a deterministic "burn" address (hash160=0x00..00, base58check version=0x1e)
# so no real wallet address is shipped in the repo, and the pool remains "not configured"
# until the user sets their own payout address.
# Placeholder address used to keep Miningcore running before the user configures a payout address.
# Stratum stays bound to localhost until a real address is set.
POOL_PLACEHOLDER_PAYOUT_ADDRESS = "D596YFweJQuHY1BbjazZYmAbt8jJPbKehC"

APP_CHANNEL = os.getenv("APP_CHANNEL", "").strip()
NETWORK_IP = os.getenv("NETWORK_IP", "").strip()
DGB_IMAGE = os.getenv("DGB_IMAGE", "").strip()
MININGCORE_IMAGE = os.getenv("MININGCORE_IMAGE", "").strip()
POSTGRES_IMAGE = os.getenv("POSTGRES_IMAGE", "").strip()
DEFAULT_SUPPORT_BASE_URL = "https://axebench.dreamnet.uk"
INSTALL_ID_HEADER = "X-Install-Id"

def _env_or_default(name: str, default: str) -> str:
    raw = os.getenv(name)
    if raw is None:
        return default
    val = raw.strip()
    return val or default


SUPPORT_CHECKIN_URL = _env_or_default("SUPPORT_CHECKIN_URL", f"{DEFAULT_SUPPORT_BASE_URL}/api/telemetry/ping")
SUPPORT_TICKET_URL = _env_or_default("SUPPORT_TICKET_URL", f"{DEFAULT_SUPPORT_BASE_URL}/api/support/upload")

APP_ID = "willitmod-dev-dgb"
APP_VERSION = "0.9.166"
APP_VERSION_SUFFIX = os.getenv("APP_VERSION_SUFFIX", "").strip()
DISPLAY_VERSION = f"{APP_VERSION}{APP_VERSION_SUFFIX}"

APP_BOOT_ID = os.getenv("APP_BOOT_ID", "").strip() or str(int(time.time()))

DGB_RPC_HOST = os.getenv("DGB_RPC_HOST", "dgbd")
DGB_RPC_PORT = int(os.getenv("DGB_RPC_PORT", "14022"))
DGB_RPC_USER = os.getenv("DGB_RPC_USER", "dgb")
DGB_RPC_PASS = os.getenv("DGB_RPC_PASS", "")

SAMPLE_INTERVAL_S = int(os.getenv("SERIES_SAMPLE_INTERVAL_S", "30"))
BACKSCAN_DEFAULT_INTERVAL_S = int(os.getenv("BACKSCAN_INTERVAL_S", "15"))
BACKSCAN_DEFAULT_MAX_BLOCKS = int(os.getenv("BACKSCAN_MAX_BLOCKS", "20"))
BACKSCAN_MAX_BLOCKS_CAP = int(os.getenv("BACKSCAN_MAX_BLOCKS_CAP", "5000"))
MAX_RETENTION_S = int(os.getenv("SERIES_MAX_RETENTION_S", str(7 * 24 * 60 * 60)))
MAX_SERIES_POINTS = int(os.getenv("SERIES_MAX_POINTS", "20000"))
# How long a worker can go without submitting an accepted share before it is
# considered "stale" and omitted from the worker list. Share cadence varies
# widely by miner + vardiff, so keep this generous by default and let the UI
# decide what's "active" vs "inactive".
WORKER_STALE_SECONDS = int(os.getenv("WORKER_STALE_SECONDS", "86400"))
# How long a worker can go without any evidence of activity before its hashrate
# is treated as 0. Evidence is best-effort: last accepted share time when known,
# otherwise the latest minerstats snapshot time. This prevents stale DB rows from
# pinning the pool hashrate indefinitely after miners disconnect.
WORKER_ACTIVE_SECONDS = int(os.getenv("WORKER_ACTIVE_SECONDS", "300"))

INSTALL_ID = None

_PG_CONF_CACHE = None
_PG_CONF_CACHE_T = 0.0
_PG_CONF_LOCK = threading.Lock()

_DB_DIAG_CACHE = None
_DB_DIAG_CACHE_T = 0.0
_DB_DIAG_LOCK = threading.Lock()

_POOL_WORKERS_CACHE: dict[str, dict] = {}
_POOL_WORKERS_LOCK = threading.Lock()
_POOL_WORKERS_TTL_S = 5.0

_POOL_BLOCKS_SCHEMA_CACHE: dict[str, dict] = {}
_POOL_BLOCKS_SCHEMA_LOCK = threading.Lock()

_BOOT_REPAIR_CACHE = None
_BOOT_REPAIR_CACHE_T = 0.0


def _read_boot_repair():
    global _BOOT_REPAIR_CACHE, _BOOT_REPAIR_CACHE_T
    now = time.time()
    if _BOOT_REPAIR_CACHE is not None and (now - _BOOT_REPAIR_CACHE_T) <= 5.0:
        return _BOOT_REPAIR_CACHE
    path = STATE_DIR / "boot_repair.json"
    try:
        if not path.exists():
            _BOOT_REPAIR_CACHE = None
            _BOOT_REPAIR_CACHE_T = now
            return None
        obj = json.loads(path.read_text(encoding="utf-8", errors="replace"))
        if not isinstance(obj, dict):
            obj = None
        _BOOT_REPAIR_CACHE = obj
        _BOOT_REPAIR_CACHE_T = now
        return obj
    except Exception:
        _BOOT_REPAIR_CACHE = None
        _BOOT_REPAIR_CACHE_T = now
        return None


def _write_boot_repair(report: dict | None) -> None:
    """
    Persist a boot-repair report for visibility in the UI/support.
    Best effort; failures are swallowed.
    """
    try:
        path = STATE_DIR / "boot_repair.json"
        STATE_DIR.mkdir(parents=True, exist_ok=True)
        if not isinstance(report, dict):
            path.write_text("", encoding="utf-8")
        else:
            path.write_text(json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8")
        # Invalidate cache so next read returns latest.
        global _BOOT_REPAIR_CACHE, _BOOT_REPAIR_CACHE_T
        _BOOT_REPAIR_CACHE = report
        _BOOT_REPAIR_CACHE_T = time.time()
    except Exception:
        pass


def _pool_blocks_from_db(pool_id: str, *, limit: int = 25, offset: int = 0) -> list[dict] | None:
    """
    Read Miningcore block history from Postgres (local-only).

    This is more reliable than Miningcore's /blocks API (which can be empty depending on retention/config).
    """
    if pg8000 is None:
        return None
    pg = _pg_conf()
    if not pg:
        return None

    limit = max(1, min(int(limit or 25), 100))
    offset = max(0, int(offset or 0))

    try:
        conn = pg8000.connect(
            host=pg["host"],
            port=pg["port"],
            user=pg["user"],
            password=pg.get("password") or None,
            database=pg["database"],
            timeout=3,
        )
    except Exception:
        return None

    try:
        cur = conn.cursor()

        with _POOL_BLOCKS_SCHEMA_LOCK:
            schema = _POOL_BLOCKS_SCHEMA_CACHE.get(pg["database"])

        if not isinstance(schema, dict):
            schema = {}

            try:
                cur.execute(
                    """
                    SELECT column_name
                    FROM information_schema.columns
                    WHERE table_name = 'blocks'
                    """,
                )
                cols = {str(r[0]).strip().lower() for r in (cur.fetchall() or []) if r and r[0]}
            except Exception:
                cols = set()

            schema = {
                "has_blocks": bool(cols),
                "has_worker": "worker" in cols,
                "has_hash": "hash" in cols,
                "has_networkdifficulty": "networkdifficulty" in cols,
                "has_transactionconfirmationdata": "transactionconfirmationdata" in cols,
                "has_confirmationprogress": "confirmationprogress" in cols,
            }
            with _POOL_BLOCKS_SCHEMA_LOCK:
                _POOL_BLOCKS_SCHEMA_CACHE[pg["database"]] = schema

        if not schema.get("has_blocks"):
            return []

        select_cols = ["created", "blockheight", "status", "miner"]
        if schema.get("has_worker"):
            select_cols.append("worker")
        else:
            select_cols.append("NULL AS worker")
        if schema.get("has_hash"):
            select_cols.append("hash")
        else:
            select_cols.append("NULL AS hash")
        if schema.get("has_networkdifficulty"):
            select_cols.append("networkdifficulty")
        else:
            select_cols.append("NULL AS networkdifficulty")
        if schema.get("has_confirmationprogress"):
            select_cols.append("confirmationprogress")
        else:
            select_cols.append("NULL AS confirmationprogress")
        if schema.get("has_transactionconfirmationdata"):
            select_cols.append("transactionconfirmationdata")
        else:
            select_cols.append("NULL AS transactionconfirmationdata")

        cur.execute(
            f"""
            SELECT {", ".join(select_cols)}
            FROM blocks
            WHERE poolid = %s
            ORDER BY created DESC
            LIMIT %s OFFSET %s
            """,
            (pool_id, limit, offset),
        )
        rows = cur.fetchall() or []

        out: list[dict] = []
        for r in rows:
            try:
                (
                    created,
                    blockheight,
                    status,
                    miner,
                    worker,
                    bhash,
                    networkdifficulty,
                    confirmationprogress,
                    txconfirm,
                ) = r
            except Exception:
                continue

            t = None
            try:
                if isinstance(created, datetime):
                    t = created.astimezone(timezone.utc).isoformat()
                elif created is not None:
                    t = str(created)
            except Exception:
                t = None

            height = None
            try:
                height = int(blockheight) if blockheight is not None else None
            except Exception:
                height = None

            st = None
            try:
                st = int(status) if status is not None else None
            except Exception:
                st = status

            miner_s = str(miner or "").strip() or None
            worker_s = str(worker or "").strip() or None

            hash_s = None
            try:
                hash_s = str(bhash).strip().lower() if bhash is not None else None
            except Exception:
                hash_s = None

            netdiff_f = None
            try:
                netdiff_f = float(networkdifficulty) if networkdifficulty is not None else None
                if netdiff_f is not None and not math.isfinite(netdiff_f):
                    netdiff_f = None
            except Exception:
                netdiff_f = None

            txid = None
            try:
                if isinstance(txconfirm, dict):
                    txid = txconfirm.get("transactionId") or txconfirm.get("TransactionId")
                elif isinstance(txconfirm, str) and txconfirm.strip():
                    obj = json.loads(txconfirm)
                    if isinstance(obj, dict):
                        txid = obj.get("transactionId") or obj.get("TransactionId")
            except Exception:
                txid = None

            ev = {
                "t": t,
                "height": height,
                "status": st,
                "miner": miner_s,
                "worker": worker_s,
                "hash": hash_s,
                "source": "db",
                "network_difficulty": netdiff_f,
            }
            if hash_s:
                ev["explorer_block"] = _dgb_explorer_block(hash_s)
            if isinstance(txid, str) and re.match(r"^[0-9a-fA-F]{64}$", txid.strip()):
                ev["coinbase_txid"] = txid.strip().lower()
                ev["explorer_tx"] = _dgb_explorer_tx(txid)
            out.append(ev)

        return out
    except Exception:
        return None
    finally:
        try:
            conn.close()
        except Exception:
            pass

PAYOUT_SCRIPT_CACHE: dict[str, str] = {}
PAYOUT_SCRIPT_CACHE_LOCK = threading.Lock()

BACKSCAN_STOP_EVENT = threading.Event()


def _backscan_pct(scan: dict) -> int | None:
    try:
        next_h = int(scan.get("nextHeight"))
        start_h = int(scan.get("startHeight"))
        tip_h = scan.get("tipHeightLast")
        tip_h = int(tip_h) if tip_h is not None else int(scan.get("tipHeightAtStart"))
        if tip_h < start_h:
            return None
        denom = max(1, tip_h - start_h + 1)
        return max(0, min(100, int(round(((next_h - start_h) / denom) * 100))))
    except Exception:
        return None


class RpcError(RuntimeError):
    def __init__(self, code: int | None, message: str, raw=None):
        super().__init__(message)
        self.code = code
        self.message = message
        self.raw = raw


def _json(data, status=200):
    body = json.dumps(data).encode("utf-8")
    return status, body, "application/json; charset=utf-8"


def _read_static(rel_path: str):
    # Ignore query-string fragments (e.g. /app.js?v=... for cache-busting).
    rel = urlsplit(rel_path).path.lstrip("/") or "index.html"
    path = (STATIC_DIR / rel).resolve()
    if not str(path).startswith(str(STATIC_DIR.resolve())):
        return 403, b"forbidden", "text/plain; charset=utf-8"
    if not path.exists() or not path.is_file():
        return 404, b"not found", "text/plain; charset=utf-8"
    suffix = path.suffix.lower()
    content_type = "application/octet-stream"
    if suffix in [".html", ".htm"]:
        content_type = "text/html; charset=utf-8"
    elif suffix == ".css":
        content_type = "text/css; charset=utf-8"
    elif suffix == ".js":
        content_type = "application/javascript; charset=utf-8"
    elif suffix == ".svg":
        content_type = "image/svg+xml"
    elif suffix == ".png":
        content_type = "image/png"
    elif suffix == ".webp":
        content_type = "image/webp"

    if rel == "index.html" and content_type.startswith("text/html"):
        try:
            html = path.read_text(encoding="utf-8", errors="replace")
            html = html.replace("__APP_VERSION__", DISPLAY_VERSION)
            html = html.replace("__APP_CHANNEL__", APP_CHANNEL or "")
            return 200, html.encode("utf-8"), content_type
        except Exception:
            pass

    return 200, path.read_bytes(), content_type


def _pg_conf():
    """
    Return Miningcore Postgres config from miningcore.json.
    Cached because UI polls frequently.
    """
    global _PG_CONF_CACHE, _PG_CONF_CACHE_T
    now = time.time()

    def _looks_like_placeholder(value: object) -> bool:
        s = str(value or "").strip()
        if not s:
            return False
        # Common docker-compose templating forms: "$VAR", "${VAR}", "{{VAR}}"
        return s.startswith("$") or ("${" in s and "}" in s) or (s.startswith("{{") and s.endswith("}}"))

    def _pg_env_overrides() -> dict:
        overrides: dict = {}
        host_raw = os.getenv("PGHOST") or os.getenv("POSTGRES_HOST")
        if host_raw:
            host = str(host_raw).strip()
            if host:
                overrides["host"] = host

        port_raw = os.getenv("PGPORT") or os.getenv("POSTGRES_PORT")
        if port_raw:
            try:
                overrides["port"] = int(str(port_raw).strip())
            except Exception:
                pass

        db_raw = os.getenv("PGDATABASE") or os.getenv("POSTGRES_DB")
        if db_raw:
            database = str(db_raw).strip()
            if database:
                overrides["database"] = database

        user_raw = os.getenv("PGUSER") or os.getenv("POSTGRES_USER")
        if user_raw:
            user = str(user_raw).strip()
            if user:
                overrides["user"] = user

        pw_raw = os.getenv("PGPASSWORD") or os.getenv("POSTGRES_PASSWORD")
        if pw_raw is not None:
            password = str(pw_raw).strip()
            if password:
                overrides["password"] = password

        return overrides

    def _pg_conf_from_env_defaults():
        overrides = _pg_env_overrides()
        host = str(overrides.get("host") or "postgres").strip() or "postgres"
        try:
            port = int(overrides.get("port") or 5432)
        except Exception:
            port = 5432
        database = str(overrides.get("database") or "miningcore").strip() or "miningcore"
        user = str(overrides.get("user") or "miningcore").strip() or "miningcore"
        password = str(overrides.get("password") or "").strip()
        return {"host": host, "port": port, "database": database, "user": user, "password": password}

    with _PG_CONF_LOCK:
        if _PG_CONF_CACHE is not None and (now - _PG_CONF_CACHE_T) < 30:
            return _PG_CONF_CACHE
        try:
            # miningcore.json can sometimes be "dirty" during upgrades (multiple JSON
            # objects concatenated, partial writes, etc). Use the tolerant parser used
            # elsewhere so we can still recover the Postgres config.
            raw = MININGCORE_CONF_PATH.read_text(encoding="utf-8", errors="replace")
            cfg = _extract_json_obj(raw) if raw.strip() else {}
            if not isinstance(cfg, dict):
                cfg = {}
            pg = (((cfg or {}).get("persistence") or {}).get("postgres") or {})
            if not isinstance(pg, dict):
                pg = {}
            out = {
                "host": str(pg.get("host") or "postgres"),
                "port": int(pg.get("port") or 5432),
                "database": str(pg.get("database") or "miningcore"),
                "user": str(pg.get("user") or "miningcore"),
                "password": str(pg.get("password") or ""),
            }
            # miningcore.json may include templated values like "${APP_PASSWORD}".
            # Treat those as missing and prefer env overrides when provided.
            if _looks_like_placeholder(out.get("host")):
                out["host"] = "postgres"
            if _looks_like_placeholder(out.get("database")):
                out["database"] = "miningcore"
            if _looks_like_placeholder(out.get("user")):
                out["user"] = "miningcore"
            if _looks_like_placeholder(out.get("port")):
                out["port"] = 5432
            if _looks_like_placeholder(out.get("password")):
                out["password"] = ""

            overrides = _pg_env_overrides()
            # Only override fields that are explicitly set in env.
            if overrides:
                for k, v in overrides.items():
                    if k == "password":
                        if str(v).strip():
                            out["password"] = str(v).strip()
                        continue
                    out[k] = v

            _PG_CONF_CACHE = out
            _PG_CONF_CACHE_T = now
            return out
        except Exception:
            env = _pg_conf_from_env_defaults()
            _PG_CONF_CACHE = env
            _PG_CONF_CACHE_T = now
            return env


def _pool_workers_from_db(pool_id: str):
    """
    Miningcore's /miners endpoint aggregates by payout address and may not expose per-worker rows.
    The minerstats table retains per-(miner, worker) rows, so use it for accurate worker lists.
    """
    if pg8000 is None:
        return None
    pg = _pg_conf()
    if not pg:
        return None

    now = time.time()
    with _POOL_WORKERS_LOCK:
        cached = _POOL_WORKERS_CACHE.get(pool_id)
        if cached and (now - float(cached.get("t") or 0)) < _POOL_WORKERS_TTL_S:
            return cached.get("workers") or []

    def _worker_last_seen_iso(*, last_share_dt: datetime | None, minerstats_created: datetime | None) -> tuple[datetime | None, str | None, float | None]:
        """
        Return (last_seen_dt, last_seen_iso, age_seconds).
        last_seen_dt is best-effort: prefer last accepted share time, fall back to minerstats snapshot time.
        """
        dt = last_share_dt if isinstance(last_share_dt, datetime) else None
        if dt is None and isinstance(minerstats_created, datetime):
            dt = minerstats_created
        if not isinstance(dt, datetime):
            return None, None, None
        try:
            age_s = (datetime.now(timezone.utc) - dt.astimezone(timezone.utc)).total_seconds()
        except Exception:
            age_s = None
        try:
            iso = dt.astimezone(timezone.utc).isoformat()
        except Exception:
            iso = None
        return dt, iso, age_s

    try:
        conn = pg8000.connect(
            host=pg["host"],
            port=pg["port"],
            user=pg["user"],
            password=pg.get("password") or None,
            database=pg["database"],
            timeout=3,
        )
    except Exception:
        return None

    try:
        cur = conn.cursor()

        def has_col(table: str, col: str) -> bool:
            try:
                cur.execute(
                    """
                    SELECT 1
                    FROM information_schema.columns
                    WHERE table_name = %s AND column_name = %s
                    LIMIT 1
                    """,
                    (table, col),
                )
                return bool(cur.fetchone())
            except Exception:
                return False

        minerstats_has_worker = has_col("minerstats", "worker")
        shares_has_worker = has_col("shares", "worker")
        shares_has_actualdifficulty = has_col("shares", "actualdifficulty")

        if minerstats_has_worker:
            minerstats_sql = """
                SELECT DISTINCT ON (miner, worker)
                  miner, worker, hashrate, sharespersecond, created
                FROM minerstats
                WHERE poolid = %s
                ORDER BY miner, worker, created DESC
            """
        else:
            minerstats_sql = """
                SELECT DISTINCT ON (miner)
                  miner, NULL AS worker, hashrate, sharespersecond, created
                FROM minerstats
                WHERE poolid = %s
                ORDER BY miner, created DESC
            """

        cur.execute(
            minerstats_sql,
            (pool_id,),
        )
        rows = cur.fetchall() or []
        minerstats_workers_present = False
        try:
            if minerstats_has_worker:
                for rr in rows:
                    try:
                        _miner, _worker, *_rest = rr
                    except Exception:
                        continue
                    if isinstance(_worker, str):
                        if _worker.strip():
                            minerstats_workers_present = True
                            break
                    elif _worker is not None:
                        minerstats_workers_present = True
                        break
        except Exception:
            minerstats_workers_present = False

        # Pull "last share" timestamps and an estimated hashrate from shares
        # (minerstats.created is a snapshot timestamp, not the last share time).
        #
        # H/s ≈ sum(difficulty) * 2^32 / elapsed_seconds
        #
        # Notes:
        # - We cap elapsed_seconds at the window size (10m) to avoid inflating
        #   hashrate when there are gaps.
        # - We floor elapsed_seconds at 60s to avoid huge spikes on the first
        #   1-2 accepted shares.
        if shares_has_worker:
            shares_sql = """
                SELECT
                  miner,
                  worker,
                  MAX(created) AS last_share,
                  MIN(CASE WHEN created >= NOW() - INTERVAL '10 minutes' THEN created END) AS first_share_10m,
                  MAX(CASE WHEN created >= NOW() - INTERVAL '10 minutes' THEN created END) AS last_share_10m,
                  COALESCE(SUM(CASE WHEN created >= NOW() - INTERVAL '10 minutes' THEN difficulty ELSE 0 END), 0) AS sumdiff_10m
                FROM shares
                WHERE poolid = %s AND created >= NOW() - INTERVAL '2 days'
                GROUP BY miner, worker
            """
        else:
            shares_sql = """
                SELECT
                  miner,
                  NULL AS worker,
                  MAX(created) AS last_share,
                  MIN(CASE WHEN created >= NOW() - INTERVAL '10 minutes' THEN created END) AS first_share_10m,
                  MAX(CASE WHEN created >= NOW() - INTERVAL '10 minutes' THEN created END) AS last_share_10m,
                  COALESCE(SUM(CASE WHEN created >= NOW() - INTERVAL '10 minutes' THEN difficulty ELSE 0 END), 0) AS sumdiff_10m
                FROM shares
                WHERE poolid = %s AND created >= NOW() - INTERVAL '2 days'
                GROUP BY miner
            """

        cur.execute(shares_sql, (pool_id,))
        share_rows = cur.fetchall() or []

        # Per-worker "current diff": latest accepted share difficulty (approx the last vardiff assignment).
        current_diff_by_key: dict[str, float] = {}
        try:
            if shares_has_worker:
                cur.execute(
                    """
                    SELECT DISTINCT ON (miner, worker)
                      miner, worker, difficulty
                    FROM shares
                    WHERE poolid = %s AND created >= NOW() - INTERVAL '2 days'
                    ORDER BY miner, worker, created DESC
                    """,
                    (pool_id,),
                )
            else:
                cur.execute(
                    """
                    SELECT DISTINCT ON (miner)
                      miner, NULL AS worker, difficulty
                    FROM shares
                    WHERE poolid = %s AND created >= NOW() - INTERVAL '2 days'
                    ORDER BY miner, created DESC
                    """,
                    (pool_id,),
                )
            for r in cur.fetchall() or []:
                try:
                    miner, worker, diff = r
                except Exception:
                    continue
                miner_s = str(miner or "")
                worker_s = str(worker or "").strip() or None
                key = (worker_s or miner_s).strip() or miner_s
                try:
                    diff_f = float(diff) if diff is not None else None
                except Exception:
                    diff_f = None
                if diff_f is not None and math.isfinite(diff_f) and diff_f > 0:
                    current_diff_by_key[key] = diff_f
        except Exception:
            current_diff_by_key = {}

        # Per-worker best share "since block" (same window used by the Best Share card).
        best_since_by_worker: dict[str, float] = {}
        try:
            # Determine "since" timestamp: last solved block (prefer local backscan events) OR Miningcore blocks table,
            # but never earlier than a manual reset.
            reset_at_s = None
            try:
                st = _read_json_file(BESTSHARE_RESET_PATH)
                if isinstance(st, dict):
                    v = st.get(pool_id)
                    reset_at_s = int(float(v)) if v is not None else None
            except Exception:
                reset_at_s = None

            reset_at_dt = None
            if reset_at_s and reset_at_s > 0:
                try:
                    reset_at_dt = datetime.utcfromtimestamp(reset_at_s)
                except Exception:
                    reset_at_dt = None

            last_solved_state_dt = None
            try:
                algo_tag = None
                pid = str(pool_id or "").strip().lower()
                if "sha256" in pid:
                    algo_tag = "sha256"
                elif "scrypt" in pid:
                    algo_tag = "scrypt"

                if algo_tag:
                    st = _read_json_file(BLOCKS_STATE_PATH)
                    evs = st.get("events") if isinstance(st, dict) else None
                    if isinstance(evs, list):
                        for ev in evs:
                            if not isinstance(ev, dict):
                                continue
                            if str(ev.get("algo") or "").strip().lower() != algo_tag:
                                continue
                            try:
                                status_i = int(ev.get("status") or 0)
                            except Exception:
                                status_i = 0
                            if status_i <= 0:
                                continue
                            try:
                                t_i = int(ev.get("t") or 0)
                            except Exception:
                                t_i = 0
                            if t_i > 0:
                                dt = datetime.utcfromtimestamp(t_i)
                                if last_solved_state_dt is None or dt > last_solved_state_dt:
                                    last_solved_state_dt = dt
            except Exception:
                last_solved_state_dt = None

            last_block_created = None
            try:
                cur.execute("SELECT MAX(created) FROM blocks WHERE poolid=%s", (pool_id,))
                row = cur.fetchone()
                last_block_created = row[0] if row and row[0] is not None else None
            except Exception:
                last_block_created = None

            def _as_naive_utc(dt: datetime) -> datetime:
                if dt.tzinfo is not None:
                    dt = dt.astimezone(timezone.utc).replace(tzinfo=None)
                return dt

            if isinstance(last_block_created, datetime):
                last_block_created = _as_naive_utc(last_block_created)

            since_at = last_block_created
            if isinstance(last_solved_state_dt, datetime):
                if since_at is None or last_solved_state_dt > since_at:
                    since_at = last_solved_state_dt
            if reset_at_dt is not None and (since_at is None or since_at < reset_at_dt):
                since_at = reset_at_dt

            # If no solved blocks exist yet, fall back to "since first share" so
            # per-worker RECORD values still populate (otherwise UI shows "-").
            if since_at is None:
                try:
                    cur.execute("SELECT MIN(created) FROM shares WHERE poolid=%s", (pool_id,))
                    row = cur.fetchone()
                    since_at = row[0] if row and row[0] is not None else None
                except Exception:
                    since_at = None
                if isinstance(since_at, datetime):
                    since_at = _as_naive_utc(since_at)

            if isinstance(since_at, datetime):
                best_col = "actualdifficulty" if shares_has_actualdifficulty else "difficulty"
                if shares_has_worker:
                    cur.execute(
                        f"""
                        SELECT COALESCE(NULLIF(worker,''), miner) AS w, MAX({best_col}) AS best
                        FROM shares
                        WHERE poolid = %s AND created > %s
                        GROUP BY w
                        """,
                        (pool_id, since_at),
                    )
                else:
                    cur.execute(
                        f"""
                        SELECT miner AS w, MAX({best_col}) AS best
                        FROM shares
                        WHERE poolid = %s AND created > %s
                        GROUP BY miner
                        """,
                        (pool_id, since_at),
                    )
                for r in cur.fetchall() or []:
                    try:
                        w, best = r
                    except Exception:
                        continue
                    key = str(w or "").strip()
                    if not key:
                        continue
                    try:
                        best_f = float(best) if best is not None else None
                    except Exception:
                        best_f = None
                    if best_f is not None and math.isfinite(best_f) and best_f > 0:
                        best_since_by_worker[key] = best_f
        except Exception:
            best_since_by_worker = {}
    except Exception:
        return None
    finally:
        try:
            conn.close()
        except Exception:
            pass

    last_share_by_key: dict[str, datetime] = {}
    hashrate_hs_10m_by_key: dict[str, float] = {}
    for r in share_rows:
        try:
            miner, worker, last_share, first_share_10m, last_share_10m, sumdiff_10m = r
        except Exception:
            continue
        miner_s = str(miner or "")
        worker_s = str(worker or "").strip() or None
        key = (worker_s or miner_s).strip() or miner_s
        if isinstance(last_share, datetime):
            last_share_by_key[key] = last_share
        try:
            sumdiff_f = float(sumdiff_10m) if sumdiff_10m is not None else 0.0
            if math.isfinite(sumdiff_f) and sumdiff_f > 0:
                span_s = None
                try:
                    if isinstance(first_share_10m, datetime) and isinstance(last_share_10m, datetime):
                        span_s = (last_share_10m - first_share_10m).total_seconds()
                    elif isinstance(first_share_10m, datetime):
                        span_s = (datetime.now(timezone.utc) - first_share_10m).total_seconds()
                except Exception:
                    span_s = None

                window_s = 10 * 60
                if span_s is None or not math.isfinite(float(span_s)) or span_s <= 0:
                    span_s = window_s
                span_s = max(60.0, min(float(span_s), float(window_s)))
                hashrate_hs_10m_by_key[key] = (sumdiff_f * (2**32)) / span_s
        except Exception:
            pass

    # Prefer shares.worker as the authoritative per-worker source when minerstats doesn't provide it.
    if share_rows and shares_has_worker and (not minerstats_has_worker or not minerstats_workers_present):
        out = []
        for r in share_rows:
            try:
                miner, worker, last_share, _, _, _ = r
            except Exception:
                continue
            miner_s = str(miner or "")
            worker_s = str(worker or "").strip() or None
            key = (worker_s or miner_s).strip() or miner_s
            last_share_dt = last_share_by_key.get(key)
            _last_seen_dt, last_seen_iso, age_s = _worker_last_seen_iso(last_share_dt=last_share_dt, minerstats_created=None)
            try:
                if age_s is not None and WORKER_STALE_SECONDS > 0 and age_s > WORKER_STALE_SECONDS:
                    continue
            except Exception:
                pass

            hashrate_hs_live = hashrate_hs_10m_by_key.get(key)
            hashrate_ths_live = (hashrate_hs_live / 1e12) if hashrate_hs_live is not None else None
            last_share_iso = None
            try:
                if isinstance(last_share_dt, datetime):
                    last_share_iso = last_share_dt.astimezone(timezone.utc).isoformat()
            except Exception:
                last_share_iso = None

            # If the worker has been quiet beyond the "active" window, force hashrate to 0
            # so stale DB rows don't keep the UI pinned.
            if age_s is not None and WORKER_ACTIVE_SECONDS > 0 and age_s > WORKER_ACTIVE_SECONDS:
                hashrate_hs_live = None
                hashrate_ths_live = 0.0

            out.append(
                {
                    "miner": miner_s,
                    "worker": worker_s,
                    "hashrate_hs": None,
                    "hashrate_ths": hashrate_ths_live,
                    "hashrate_hs_live_10m": hashrate_hs_live,
                    "hashrate_ths_live_10m": hashrate_ths_live,
                    "lastShare": last_share_iso,
                    "lastSeen": last_seen_iso,
                    "sharesPerSecond": None,
                    "current_diff": current_diff_by_key.get(key),
                    "bestshare_since_block": best_since_by_worker.get(key),
                }
            )

        out.sort(key=lambda m: float(m.get("hashrate_ths_live_10m") or 0), reverse=True)
        with _POOL_WORKERS_LOCK:
            _POOL_WORKERS_CACHE[pool_id] = {"t": now, "workers": out}
        return out

    out = []
    for r in rows:
        try:
            miner, worker, hashrate_hs, shares_per_s, created = r
        except Exception:
            continue

        miner_s = str(miner or "")
        worker_s = str(worker or "").strip() or None
        key = (worker_s or miner_s).strip() or miner_s

        try:
            hashrate_hs_f = float(hashrate_hs) if hashrate_hs is not None else None
        except Exception:
            hashrate_hs_f = None
        if hashrate_hs_f is not None and not math.isfinite(hashrate_hs_f):
            hashrate_hs_f = None

        last_share_dt = last_share_by_key.get(key)
        _last_seen_dt, last_seen_iso, age_s = _worker_last_seen_iso(last_share_dt=last_share_dt, minerstats_created=created if isinstance(created, datetime) else None)
        try:
            if age_s is not None and WORKER_STALE_SECONDS > 0 and age_s > WORKER_STALE_SECONDS:
                continue
        except Exception:
            pass

        hashrate_hs_live = hashrate_hs_10m_by_key.get(key)
        hashrate_ths_live = (hashrate_hs_live / 1e12) if hashrate_hs_live is not None else None

        # Prefer live estimate from accepted shares, fallback to Miningcore minerstats estimate.
        hashrate_ths = hashrate_ths_live
        if hashrate_ths is None and hashrate_hs_f is not None:
            hashrate_ths = hashrate_hs_f / 1e12

        # Clamp quiet workers to 0 so stale minerstats rows don't keep the pool hashrate pinned.
        if age_s is not None and WORKER_ACTIVE_SECONDS > 0 and age_s > WORKER_ACTIVE_SECONDS:
            hashrate_hs_f = 0.0
            hashrate_ths = 0.0
            try:
                shares_per_s = 0.0
            except Exception:
                shares_per_s = 0.0

        last_share = None
        try:
            if isinstance(last_share_dt, datetime):
                last_share = last_share_dt.astimezone(timezone.utc).isoformat()
            elif last_share_dt is not None:
                last_share = str(last_share_dt)
        except Exception:
            last_share = None

        out.append(
            {
                "miner": miner_s,
                "worker": worker_s,
                "hashrate_hs": hashrate_hs_f,
                "hashrate_ths": hashrate_ths,
                "hashrate_hs_live_10m": hashrate_hs_live,
                "hashrate_ths_live_10m": hashrate_ths_live,
                "lastShare": last_share,
                "lastSeen": last_seen_iso,
                "sharesPerSecond": shares_per_s,
                "current_diff": current_diff_by_key.get(key),
                "bestshare_since_block": best_since_by_worker.get(key),
            }
        )

    # Miningcore can emit both per-worker rows and an aggregate (worker=null) row for the same miner.
    # If we have any named workers, hide the aggregate row so the UI doesn't under/over-count workers.
    has_named = any(isinstance(m.get("worker"), str) and m.get("worker") for m in out)
    if has_named:
        out = [m for m in out if m.get("worker")]

    out.sort(key=lambda m: float(m.get("hashrate_hs") or 0), reverse=True)
    with _POOL_WORKERS_LOCK:
        _POOL_WORKERS_CACHE[pool_id] = {"t": now, "workers": out}
    return out


def _parse_pool_ids(raw: str) -> dict[str, str]:
    """
    Parse MININGCORE_POOL_IDS like: "sha256:dgb-sha256-1".
    """
    out: dict[str, str] = {}
    for part in (raw or "").split(","):
        part = part.strip()
        if not part:
            continue
        if ":" not in part:
            continue
        k, v = part.split(":", 1)
        k = k.strip().lower()
        v = v.strip()
        if not k or not v:
            continue
        out[k] = v
    return out


def _pool_ids() -> dict[str, str]:
    ids = _parse_pool_ids(MININGCORE_POOL_IDS)
    if ids:
        return ids
    return {"sha256": MININGCORE_POOL_ID}


def _parse_ports(raw: str) -> dict[str, int]:
    out: dict[str, int] = {}
    for part in (raw or "").split(","):
        part = part.strip()
        if not part:
            continue
        if ":" not in part:
            continue
        k, v = part.split(":", 1)
        k = k.strip().lower()
        v = v.strip()
        if not k or not v:
            continue
        try:
            out[k] = int(v)
        except Exception:
            continue
    return out


def _stratum_ports() -> dict[str, int]:
    ports = _parse_ports(STRATUM_PORTS)
    if ports:
        return ports
    return {"sha256": 5678, "scrypt": 5679}


def _algo_from_query(path: str) -> str | None:
    try:
        if "?" not in path:
            return None
        _, query = path.split("?", 1)
        for part in query.split("&"):
            if part.startswith("algo="):
                return part.split("=", 1)[1].strip().lower() or None
    except Exception:
        return None
    return None


def _pool_id_for_algo(algo: str | None) -> str:
    ids = _pool_ids()
    if algo and algo in ids:
        return ids[algo]
    if "sha256" in ids:
        return ids["sha256"]
    return next(iter(ids.values()))


def _rpc_call(method: str, params=None):
    if params is None:
        params = []
    rpc_port = _effective_rpc_port()
    url = f"http://{DGB_RPC_HOST}:{rpc_port}/"
    payload = json.dumps({"jsonrpc": "1.0", "id": "umbrel", "method": method, "params": params}).encode("utf-8")

    auth = base64.b64encode(f"{DGB_RPC_USER}:{DGB_RPC_PASS}".encode("utf-8")).decode("ascii")
    req = urllib.request.Request(
        url,
        data=payload,
        headers={"Content-Type": "application/json", "Authorization": f"Basic {auth}"},
        method="POST",
    )
    last_err = None
    for attempt in range(2):
        try:
            try:
                with urllib.request.urlopen(req, timeout=12) as resp:
                    data = json.loads(resp.read().decode("utf-8"))
            except HTTPError as e:
                # Bitcoin-style JSON-RPC returns HTTP 500 for application errors (e.g. warmup -28).
                # Parse the JSON body so callers can handle structured error codes/messages.
                raw = e.read() or b""
                try:
                    data = json.loads(raw.decode("utf-8", errors="replace"))
                except Exception:
                    snippet = raw.decode("utf-8", errors="replace").strip()
                    snippet = snippet[:200] if snippet else ""
                    msg = f"HTTP {getattr(e, 'code', '')} {getattr(e, 'reason', '')}".strip()
                    if snippet:
                        msg = f"{msg}: {snippet}"
                    raise RpcError(getattr(e, "code", None), msg, raw=snippet or None)
            last_err = None
            break
        except Exception as e:
            last_err = e
            if attempt == 0:
                time.sleep(0.4)
                continue
            raise
    if last_err is not None:
        raise last_err
    if data.get("error"):
        err = data["error"]
        code = None
        msg = None
        if isinstance(err, dict):
            try:
                code = int(err.get("code")) if err.get("code") is not None else None
            except Exception:
                code = None
            msg = str(err.get("message") or "")
        if not msg:
            msg = str(err)
        raise RpcError(code, msg, raw=err)
    return data.get("result")


NODE_STATUS_LOCK = threading.Lock()


def _read_conf_kv_in_section(path: Path, section: str) -> dict:
    if not path.exists():
        return {}
    header = f"[{section}]"
    in_section = False
    out = {}
    for raw in path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("[") and line.endswith("]"):
            in_section = (line == header)
            continue
        if not in_section or "=" not in line:
            continue
        k, v = line.split("=", 1)
        out[k.strip()] = v.strip()
    return out


def _effective_rpc_port() -> int:
    try:
        conf = _read_conf_kv(NODE_CONF_PATH)
        net = "mainnet"
        if conf.get("regtest") == "1":
            net = "regtest"
        elif conf.get("testnet") == "1":
            net = "testnet"

        if net == "testnet":
            sec = _read_conf_kv_in_section(NODE_CONF_PATH, "test")
            if sec.get("rpcport"):
                return int(sec["rpcport"])
            if conf.get("rpcport"):
                return int(conf["rpcport"])
            return 14023

        if net == "regtest":
            sec = _read_conf_kv_in_section(NODE_CONF_PATH, "regtest")
            if sec.get("rpcport"):
                return int(sec["rpcport"])
            if conf.get("rpcport"):
                return int(conf["rpcport"])
            return 18443

        if conf.get("rpcport"):
            return int(conf["rpcport"])
        return int(DGB_RPC_PORT)
    except Exception:
        return int(DGB_RPC_PORT)


def _read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8", errors="replace").strip()
    except Exception:
        return ""


def _write_text(path: Path, value: str):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(value.strip() + "\n", encoding="utf-8")


def _get_or_create_install_id() -> str:
    existing = _read_text(INSTALL_ID_PATH)
    if existing:
        return existing
    new_id = uuid.uuid4().hex
    _write_text(INSTALL_ID_PATH, new_id)
    return new_id


def _read_json(path: Path) -> dict:
    try:
        if not path.exists():
            return {}
        data = json.loads(path.read_text(encoding="utf-8", errors="replace"))
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def _write_json(path: Path, data: dict):
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    except Exception:
        pass


def _post_json(url: str, payload: dict, *, timeout_s: int = 6, headers: dict | None = None):
    body = json.dumps(payload).encode("utf-8")
    all_headers = {"Content-Type": "application/json"}
    if headers:
        all_headers.update(headers)
    req = urllib.request.Request(
        url,
        data=body,
        headers=all_headers,
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout_s) as resp:
            return resp.status, resp.read()
    except HTTPError as e:
        try:
            return int(getattr(e, "code", 0) or 0), e.read() or b""
        except Exception:
            return int(getattr(e, "code", 0) or 0), b""


def _encode_multipart(fields: dict[str, str], files: dict[str, tuple[str, bytes, str]]):
    boundary = uuid.uuid4().hex
    crlf = "\r\n"
    body = bytearray()

    for name, value in fields.items():
        body.extend(f"--{boundary}{crlf}".encode("utf-8"))
        body.extend(f'Content-Disposition: form-data; name="{name}"{crlf}{crlf}'.encode("utf-8"))
        body.extend(value.encode("utf-8"))
        body.extend(crlf.encode("utf-8"))

    for name, (filename, data, content_type) in files.items():
        body.extend(f"--{boundary}{crlf}".encode("utf-8"))
        body.extend(
            f'Content-Disposition: form-data; name="{name}"; filename="{filename}"{crlf}'.encode("utf-8")
        )
        body.extend(f"Content-Type: {content_type}{crlf}{crlf}".encode("utf-8"))
        body.extend(data)
        body.extend(crlf.encode("utf-8"))

    body.extend(f"--{boundary}--{crlf}".encode("utf-8"))
    return boundary, bytes(body)


def _post_support_bundle(url: str, *, bundle_bytes: bytes, filename: str, timeout_s: int = 20):
    boundary, body = _encode_multipart(fields={}, files={"bundle": (filename, bundle_bytes, "application/zip")})
    headers = {
        "Content-Type": f"multipart/form-data; boundary={boundary}",
        INSTALL_ID_HEADER: str(INSTALL_ID or ""),
    }
    req = urllib.request.Request(url, data=body, headers=headers, method="POST")
    try:
        with urllib.request.urlopen(req, timeout=timeout_s) as resp:
            return resp.status, resp.read()
    except HTTPError as e:
        try:
            return int(getattr(e, "code", 0) or 0), e.read() or b""
        except Exception:
            return int(getattr(e, "code", 0) or 0), b""


def _support_payload_base() -> dict:
    return {
        "install_id": INSTALL_ID,
        "app_id": APP_ID,
        "app_version": APP_VERSION,
        "channel": APP_CHANNEL or None,
        "arch": platform.machine(),
        "ts": int(time.time()),
    }


def _support_checkin_once():
    try:
        now = time.time()
        st = _read_json(CHECKIN_STATE_PATH)
        last = float(st.get("last_ping_at") or 0.0)
        if (now - last) < float(24 * 60 * 60):
            return
        payload = {"app": "AxeDGB", "version": APP_VERSION}
        _post_json(SUPPORT_CHECKIN_URL, payload, timeout_s=6, headers={INSTALL_ID_HEADER: str(INSTALL_ID or "")})
        _write_json(CHECKIN_STATE_PATH, {"last_ping_at": now})
    except Exception:
        pass


def _support_checkin_loop(stop_event: threading.Event):
    _support_checkin_once()
    while not stop_event.is_set():
        stop_event.wait(24 * 60 * 60)
        if stop_event.is_set():
            break
        _support_checkin_once()

def _read_conf_kv(path: Path):
    if not path.exists():
        return {}
    out = {}
    in_section = False
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("[") and line.endswith("]"):
            # Values below a section header belong to that section until another
            # header is encountered. Global values are only those above the first
            # section header.
            in_section = True
            continue
        if in_section:
            # Ignore section-scoped settings like [test]/[regtest] so they don't override global values.
            continue
        if "=" not in line:
            continue
        k, v = line.split("=", 1)
        out[k.strip()] = v.strip()
    return out


_CONF_LINE_RE = re.compile(r"^\s*(#\s*)?(?P<key>[A-Za-z0-9_]+)\s*=\s*(?P<value>.*)\s*$")


def _set_conf_key(lines: list[str], key: str, value: str | None, *, comment_out: bool = False):
    found = False
    in_section = False
    for i, line in enumerate(lines):
        s = line.strip()
        if s.startswith("[") and s.endswith("]"):
            in_section = True
            continue
        if in_section:
            # Global keys must not be updated inside sections.
            continue
        m = _CONF_LINE_RE.match(line)
        if not m:
            continue
        if m.group("key") != key:
            continue
        found = True
        if value is None:
            lines[i] = f"# {key}=1"
        else:
            lines[i] = f"{key}={value}" if not comment_out else f"# {key}={value}"
    if not found and value is not None:
        # If the file already contains INI sections (e.g. [test]), ensure that
        # global keys are inserted before the first section header so they do
        # not accidentally become section-scoped.
        insert_at = len(lines)
        for j, raw in enumerate(lines):
            s = raw.strip()
            if s.startswith("[") and s.endswith("]"):
                insert_at = j
                break
        # Keep a visual separation when inserting above a section.
        if insert_at > 0 and lines[insert_at - 1].strip():
            lines.insert(insert_at, "")
            insert_at += 1
        lines.insert(insert_at, f"{key}={value}" if not comment_out else f"# {key}={value}")


def _comment_out_keys_in_sections(lines: list[str], keys: set[str]):
    """
    Comment out occurrences of keys that must be global-only if they appear
    inside any section (e.g. due to older bugs that appended keys after [test]).
    """
    in_section = False
    for i, raw in enumerate(lines):
        s = raw.strip()
        if not s:
            continue
        if s.startswith("[") and s.endswith("]"):
            in_section = True
            continue
        if not in_section:
            continue
        m = _CONF_LINE_RE.match(raw)
        if not m:
            continue
        k = m.group("key")
        if k in keys and not raw.lstrip().startswith("#"):
            lines[i] = f"# {s}"


def _ensure_node_conf_layout():
    """
    Best-effort migration for older installs where some global keys were written
    below a section header (e.g. [test]), making them section-scoped and causing
    the UI to read them back as 0 or the network to appear to flip.
    """
    if not NODE_CONF_PATH.exists():
        return
    try:
        raw_lines = NODE_CONF_PATH.read_text(encoding="utf-8", errors="replace").splitlines()
    except Exception:
        return

    lines = list(raw_lines)

    def first_section_at(ls: list[str]) -> int:
        for idx, ln in enumerate(ls):
            s = ln.strip()
            if s.startswith("[") and s.endswith("]"):
                return idx
        return len(ls)

    first_sec = first_section_at(lines)

    def find_uncommented_value_in_sections(k: str) -> str | None:
        in_section = False
        found_val = None
        for ln in lines:
            s = ln.strip()
            if not s:
                continue
            if s.startswith("[") and s.endswith("]"):
                in_section = True
                continue
            if not in_section:
                continue
            if s.startswith("#") or "=" not in s:
                continue
            kk, vv = s.split("=", 1)
            if kk.strip() == k:
                found_val = vv.strip()
        return found_val

    global_kv = _read_conf_kv(NODE_CONF_PATH)

    changed = False
    for k in ("prune", "txindex", "testnet", "regtest"):
        if (global_kv.get(k) or "").strip():
            continue
        sec_val = find_uncommented_value_in_sections(k)
        if sec_val is None:
            continue
        _set_conf_key(lines, k, sec_val, comment_out=False)
        changed = True

    # Always keep [test] section sane so switching networks works reliably.
    try:
        s, e = _conf_find_section(lines, "test")
        s += 1
        _set_conf_key_in_range(lines, s, e, "port", "12026")
        _set_conf_key_in_range(lines, s, e, "rpcport", "14023")
        _set_conf_key_in_range(lines, s, e, "rpcbind", "0.0.0.0")
        _set_conf_key_in_range(lines, s, e, "zmqpubhashblock", "tcp://0.0.0.0:28344")
        _ensure_addnodes_in_range(
            lines,
            s,
            e,
            [
                "testnet-seed.digibyte.org:12026",
                "95.179.160.53:12026",
                "51.15.113.125:12026",
            ],
        )
    except Exception:
        pass

    _comment_out_keys_in_sections(lines, {"prune", "txindex", "testnet", "regtest"})

    if lines != raw_lines:
        try:
            NODE_CONF_PATH.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")
            changed = True
        except Exception:
            return

    if changed:
        try:
            net = str(_current_settings().get("network") or "mainnet")
            _update_miningcore_daemon_port(net)
        except Exception:
            pass


def _conf_find_section(lines: list[str], name: str) -> tuple[int, int]:
    header = f"[{name}]"
    start = None
    for i, line in enumerate(lines):
        if line.strip() == header:
            start = i
            break
    if start is None:
        if lines and lines[-1].strip():
            lines.append("")
        start = len(lines)
        lines.append(header)
        lines.append("")
        return start, len(lines)

    end = len(lines)
    for j in range(start + 1, len(lines)):
        if lines[j].lstrip().startswith("[") and lines[j].rstrip().endswith("]"):
            end = j
            break
    return start, end


def _set_conf_key_in_range(lines: list[str], start: int, end: int, key: str, value: str):
    found = False
    for i in range(start, end):
        m = _CONF_LINE_RE.match(lines[i])
        if not m:
            continue
        if m.group("key") != key:
            continue
        lines[i] = f"{key}={value}"
        found = True
    if not found:
        insert_at = end
        while insert_at > start and not lines[insert_at - 1].strip():
            insert_at -= 1
        lines.insert(insert_at, f"{key}={value}")


def _ensure_addnodes_in_range(lines: list[str], start: int, end: int, nodes: list[str]):
    existing = set()
    for i in range(start, end):
        line = lines[i].strip()
        if line.startswith("#") or "=" not in line:
            continue
        k, v = line.split("=", 1)
        if k.strip() == "addnode":
            existing.add(v.strip())

    to_add = [n for n in nodes if n not in existing]
    if not to_add:
        return

    insert_at = end
    while insert_at > start and not lines[insert_at - 1].strip():
        insert_at -= 1
    for n in to_add:
        lines.insert(insert_at, f"addnode={n}")
        insert_at += 1


def _update_miningcore_daemon_port(network: str):
    if not MININGCORE_CONF_PATH.exists():
        return
    try:
        conf = _read_miningcore_conf()
        pools = conf.get("pools")
        if not isinstance(pools, list) or not pools:
            return

        port = 14022
        if network == "testnet":
            port = 14023
        elif network == "regtest":
            # Best-effort; regtest is not a supported mining target in AxeDGB.
            port = 18443

        changed = False
        for pool in pools:
            if not isinstance(pool, dict):
                continue
            daemons = pool.get("daemons") or []
            if not isinstance(daemons, list):
                continue
            for d in daemons:
                if isinstance(d, dict):
                    if d.get("port") != int(port):
                        d["port"] = int(port)
                        changed = True
        if changed:
            _write_miningcore_conf(conf)
    except Exception:
        return


def _ensure_miningcore_pool_tuning():
    """
    Best-effort self-heal for older installs where docker-compose/init changes
    are not applied on update (5tratumOS can update images without replacing the
    compose bundle).

    Aim: reduce "duplicate share" rejects for some miners by preventing overly
    aggressive job rebroadcasting.
    """
    if not MININGCORE_CONF_PATH.exists():
        return
    try:
        conf = _read_miningcore_conf()
        pools = conf.get("pools")
        if not isinstance(pools, list) or not pools:
            return

        changed = False
        for pool in pools:
            if not isinstance(pool, dict):
                continue
            if pool.get("id") not in {"dgb-sha256-1", "dgb-scrypt-1"}:
                continue

            bri = pool.get("blockRefreshInterval")
            try:
                bri_int = int(bri) if bri is not None else 0
            except Exception:
                bri_int = 0
            if bri_int < 2000:
                pool["blockRefreshInterval"] = 2000
                changed = True

            jrt = pool.get("jobRebroadcastTimeout")
            try:
                jrt_int = int(jrt) if jrt is not None else 0
            except Exception:
                jrt_int = 0
            if jrt_int < 60:
                pool["jobRebroadcastTimeout"] = 60
                changed = True

        if changed:
            _write_miningcore_conf(conf)
    except Exception:
        return


def _update_node_conf(network: str, prune: int, txindex: int):
    NODE_CONF_PATH.parent.mkdir(parents=True, exist_ok=True)
    if NODE_CONF_PATH.exists():
        lines = NODE_CONF_PATH.read_text(encoding="utf-8", errors="replace").splitlines()
    else:
        lines = []

    network = network.lower().strip()
    if network not in ["mainnet", "testnet", "regtest"]:
        raise ValueError("invalid network")

    _set_conf_key(lines, "txindex", str(int(bool(txindex))))
    _set_conf_key(lines, "prune", str(int(prune)))

    if network == "mainnet":
        _set_conf_key(lines, "port", "12024")
        _set_conf_key(lines, "rpcport", "14022")
        _set_conf_key(lines, "testnet", "1", comment_out=True)
        _set_conf_key(lines, "regtest", "1", comment_out=True)
    elif network == "testnet":
        _set_conf_key(lines, "port", "12026")
        _set_conf_key(lines, "rpcport", "14023")
        _set_conf_key(lines, "testnet", "1", comment_out=False)
        _set_conf_key(lines, "regtest", "1", comment_out=True)
    else:
        _set_conf_key(lines, "port", "18444")
        _set_conf_key(lines, "rpcport", "18443")
        _set_conf_key(lines, "testnet", "1", comment_out=True)
        _set_conf_key(lines, "regtest", "1", comment_out=False)

    # DigiByte only applies several settings to testnet when placed in a section block.
    # Always keep the [test] section sane so switching networks later works reliably.
    s, e = _conf_find_section(lines, "test")
    s += 1
    test_p2p_port = 12026
    test_rpc_port = 14023  # observed default for DigiByte 7.17.x testnet4
    _set_conf_key_in_range(lines, s, e, "port", str(test_p2p_port))
    _set_conf_key_in_range(lines, s, e, "rpcport", str(test_rpc_port))
    _set_conf_key_in_range(lines, s, e, "rpcbind", "0.0.0.0")
    _set_conf_key_in_range(lines, s, e, "zmqpubhashblock", "tcp://0.0.0.0:28344")
    _ensure_addnodes_in_range(
        lines,
        s,
        e,
        [
            "testnet-seed.digibyte.org:12026",
            "95.179.160.53:12026",
            "51.15.113.125:12026",
        ],
    )

    # Ensure these keys remain global-only if older installs placed them inside sections.
    _comment_out_keys_in_sections(lines, {"prune", "txindex", "testnet", "regtest"})

    NODE_CONF_PATH.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")
    _update_miningcore_daemon_port(network)


def _tail_text(path: Path, *, max_bytes: int = 64 * 1024) -> str:
    try:
        if not path.exists():
            return ""
        size = path.stat().st_size
        start = max(0, size - max_bytes)
        with path.open("rb") as f:
            f.seek(start)
            raw = f.read()
        return raw.decode("utf-8", errors="replace")
    except Exception:
        return ""


def _detect_reindex_required() -> bool:
    txt = _tail_text(NODE_LOG_PATH)
    if not txt:
        return False
    lowered = txt.lower()
    return ("previously been pruned" in lowered) and ("reindex" in lowered)


def _request_reindex_chainstate():
    try:
        NODE_REINDEX_FLAG_PATH.parent.mkdir(parents=True, exist_ok=True)
        NODE_REINDEX_FLAG_PATH.write_text(str(int(time.time())) + "\n", encoding="utf-8")
    except Exception:
        pass


def _build_support_bundle_zip(payload: dict) -> tuple[bytes, str]:
    bio = io.BytesIO()
    with zipfile.ZipFile(bio, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        zf.writestr("ticket.json", json.dumps(payload, indent=2, sort_keys=True))
        zf.writestr("about.json", json.dumps(_about(), indent=2, sort_keys=True))
        zf.writestr("settings.json", json.dumps(_current_settings(), indent=2, sort_keys=True))
        # Extra diagnostics
        try:
            zf.writestr("pool_settings.json", json.dumps(_pool_settings(), indent=2, sort_keys=True))
        except Exception:
            pass
        try:
            if MININGCORE_CONF_PATH.exists():
                zf.writestr("miningcore.json", MININGCORE_CONF_PATH.read_text(encoding="utf-8", errors="replace"))
        except Exception:
            pass
        try:
            if NODE_CONF_PATH.exists():
                zf.writestr("digibyte.conf", NODE_CONF_PATH.read_text(encoding="utf-8", errors="replace"))
        except Exception:
            pass
        try:
            # Node and miningcore log tails (best-effort)
            txt = _tail_text(NODE_LOG_PATH, max_bytes=256 * 1024)
            zf.writestr("debug.log.tail", txt)
        except Exception:
            pass
        try:
            pool_id = _pool_ids().get("sha256") or MININGCORE_POOL_ID
            api_pool = _miningcore_pool(pool_id) or {}
            zf.writestr("miningcore_pool.json", json.dumps(api_pool, indent=2, sort_keys=True))
        except Exception:
            pass
        try:
            node = _node_status()
            zf.writestr("node_status.json", json.dumps(node, indent=2, sort_keys=True))
        except Exception:
            pass
        try:
            br = _read_boot_repair()
            if br is not None:
                zf.writestr("boot_repair.json", json.dumps(br, indent=2, sort_keys=True))
        except Exception:
            pass
    name = f"axedgb-support-{int(time.time())}.zip"
    return bio.getvalue(), name


def _current_settings():
    conf = _read_conf_kv(NODE_CONF_PATH)
    net = "mainnet"
    if conf.get("regtest") == "1":
        net = "regtest"
    elif conf.get("testnet") == "1":
        net = "testnet"
    prune = int(conf.get("prune") or 0)
    txindex = int(conf.get("txindex") or 0)
    dbcache_mb = None
    try:
        if NODE_DBCACHE_MB_PATH.exists():
            raw = NODE_DBCACHE_MB_PATH.read_text(encoding="utf-8", errors="replace").strip()
            if raw and raw.lower() != "auto":
                v = int(raw)
                if v > 0:
                    dbcache_mb = v
    except Exception:
        dbcache_mb = None
    try:
        if dbcache_mb is not None and int(dbcache_mb) < 4096:
            dbcache_mb = 4096
    except Exception:
        pass
    return {"network": net, "prune": prune, "txindex": txindex, "dbcacheMb": dbcache_mb}


def _node_status():
    info = _rpc_call("getblockchaininfo")

    blocks = int(info.get("blocks") or 0)
    headers = int(info.get("headers") or blocks)
    progress = float(info.get("verificationprogress") or 0.0)
    ibd = bool(info.get("initialblockdownload", False))

    extras: dict = {}
    cached_extras = _read_node_extras_cache()
    now = int(time.time())
    extras_max_age_s = 60
    if cached_extras and (now - int(cached_extras["t"])) <= extras_max_age_s:
        extras = dict(cached_extras["extras"])
    else:
        try:
            net = _rpc_call("getnetworkinfo")
            mempool = _rpc_call("getmempoolinfo")
            best_block_time = None
            try:
                bh = str(info.get("bestblockhash") or "").strip()
                if bh:
                    hdr = _rpc_call("getblockheader", [bh, True]) or {}
                    if isinstance(hdr, dict) and hdr.get("time") is not None:
                        best_block_time = int(hdr.get("time"))
            except Exception:
                best_block_time = None
            extras = {
                "connections": int(net.get("connections") or 0),
                "subversion": str(net.get("subversion") or ""),
                "mempool_bytes": int(mempool.get("bytes") or 0),
                "best_block_time": best_block_time,
            }
            _write_node_extras_cache(extras)
        except Exception:
            if cached_extras:
                extras = dict(cached_extras["extras"])

    status = {
        "chain": info.get("chain"),
        "blocks": blocks,
        "headers": headers,
        "verificationprogress": progress,
        "initialblockdownload": ibd,
        "difficulty": info.get("difficulty"),
        "difficulties": info.get("difficulties") if isinstance(info.get("difficulties"), dict) else None,
        "connections": int(extras.get("connections") or 0),
        "subversion": str(extras.get("subversion") or ""),
        "mempool_bytes": int(extras.get("mempool_bytes") or 0),
        "size_on_disk": int(info.get("size_on_disk") or 0),
        "pruned": bool(info.get("pruned", False)),
        "best_block_time": extras.get("best_block_time"),
        "median_time": int(info.get("mediantime") or 0),
        "warnings": str(info.get("warnings") or "").strip() or None,
        "bootId": APP_BOOT_ID,
    }
    try:
        status["memory"] = _host_memory_mb()
    except Exception:
        status["memory"] = None
    try:
        status["bootRepair"] = _read_boot_repair()
    except Exception:
        status["bootRepair"] = None

    try:
        STATE_DIR.mkdir(parents=True, exist_ok=True)
        NODE_CACHE_PATH.write_text(json.dumps({"t": int(time.time()), "status": status}) + "\n", encoding="utf-8")
    except Exception:
        pass

    return status


def _read_node_cache():
    try:
        if not NODE_CACHE_PATH.exists():
            return None
        obj = json.loads(NODE_CACHE_PATH.read_text(encoding="utf-8", errors="replace"))
        t = int(obj.get("t") or 0)
        status = obj.get("status") or {}
        if not isinstance(status, dict):
            return None
        return {"t": t, "status": status}
    except Exception:
        return None


def _read_node_extras_cache():
    try:
        if not NODE_EXTRAS_CACHE_PATH.exists():
            return None
        obj = json.loads(NODE_EXTRAS_CACHE_PATH.read_text(encoding="utf-8", errors="replace"))
        t = int(obj.get("t") or 0)
        extras = obj.get("extras") or {}
        if not isinstance(extras, dict):
            return None
        return {"t": t, "extras": extras}
    except Exception:
        return None


def _write_node_extras_cache(extras: dict):
    try:
        STATE_DIR.mkdir(parents=True, exist_ok=True)
        NODE_EXTRAS_CACHE_PATH.write_text(
            json.dumps({"t": int(time.time()), "extras": extras}) + "\n", encoding="utf-8"
        )
    except Exception:
        pass


def _safe_slug(value: str) -> str:
    s = re.sub(r"[^a-zA-Z0-9_.-]+", "_", str(value or "").strip())
    return s or "default"


def _pool_cache_path(pool_id: str) -> Path:
    return STATE_DIR / f"pool_cache_{_safe_slug(pool_id)}.json"


def _pool_series_path(pool_id: str) -> Path:
    return STATE_DIR / f"pool_timeseries_{_safe_slug(pool_id)}.jsonl"


def _write_pool_cache(pool_id: str, status: dict):
    try:
        STATE_DIR.mkdir(parents=True, exist_ok=True)
        _pool_cache_path(pool_id).write_text(json.dumps({"t": int(time.time()), "status": status}) + "\n", encoding="utf-8")
    except Exception:
        pass


def _read_pool_cache(pool_id: str):
    try:
        path = _pool_cache_path(pool_id)
        if not path.exists():
            return None
        obj = json.loads(path.read_text(encoding="utf-8", errors="replace"))
        t = int(obj.get("t") or 0)
        status = obj.get("status") or {}
        if not isinstance(status, dict):
            return None
        return {"t": t, "status": status}
    except Exception:
        return None


def _about():
    node = None
    node_error = None
    try:
        node = _node_status()
    except Exception as e:
        node_error = str(e)

    return {
        "appVersion": APP_VERSION,
        "bootId": APP_BOOT_ID,
        "channel": APP_CHANNEL or None,
        "networkIp": NETWORK_IP or None,
        "bootRepair": _read_boot_repair(),
        "images": {
            "dgbd": DGB_IMAGE or None,
            "miningcore": MININGCORE_IMAGE or None,
            "postgres": POSTGRES_IMAGE or None,
        },
        "poolIds": _pool_ids(),
        "stratumPorts": _stratum_ports(),
        "node": node,
        "nodeError": node_error,
        "pool": _pool_settings(),
    }


def _cgroup_v2_value(path: str) -> int | None:
    try:
        raw = Path(path).read_text(encoding="utf-8", errors="replace").strip()
        if not raw or raw.lower() == "max":
            return None
        v = int(raw)
        return v if v > 0 else None
    except Exception:
        return None


def _cgroup_v1_value(path: str) -> int | None:
    try:
        v = int(Path(path).read_text(encoding="utf-8", errors="replace").strip())
        return v if v > 0 else None
    except Exception:
        return None


def _host_memory_mb() -> dict:
    """
    Best-effort memory stats for UI warnings.

    Returns total/available in MB, preferring cgroup limits when running under docker.
    """
    total_bytes = None
    avail_bytes = None

    # cgroup v2
    limit = _cgroup_v2_value("/sys/fs/cgroup/memory.max")
    current = _cgroup_v2_value("/sys/fs/cgroup/memory.current")
    if limit is not None:
        total_bytes = limit
        if current is not None:
            avail_bytes = max(0, limit - current)

    # cgroup v1
    if total_bytes is None:
        limit = _cgroup_v1_value("/sys/fs/cgroup/memory/memory.limit_in_bytes")
        usage = _cgroup_v1_value("/sys/fs/cgroup/memory/memory.usage_in_bytes")
        # Some systems report a huge sentinel "limit" when unlimited; ignore those.
        if limit is not None and limit < (1 << 60):
            total_bytes = limit
            if usage is not None:
                avail_bytes = max(0, limit - usage)

    # /proc/meminfo fallback
    if (total_bytes is None or avail_bytes is None) and Path("/proc/meminfo").exists():
        try:
            mem_total_kb = None
            mem_avail_kb = None
            for line in Path("/proc/meminfo").read_text(encoding="utf-8", errors="replace").splitlines():
                if line.startswith("MemTotal:"):
                    mem_total_kb = int(line.split()[1])
                if line.startswith("MemAvailable:"):
                    mem_avail_kb = int(line.split()[1])
            if mem_total_kb is not None and total_bytes is None:
                total_bytes = mem_total_kb * 1024
            if mem_avail_kb is not None and avail_bytes is None:
                avail_bytes = mem_avail_kb * 1024
        except Exception:
            pass

    out = {}
    if total_bytes is not None:
        out["totalMb"] = int(total_bytes / (1024 * 1024))
    if avail_bytes is not None:
        out["availableMb"] = int(avail_bytes / (1024 * 1024))
    return out


def _extract_json_obj(text: str):
    s = text.strip()
    if not s:
        raise ValueError("empty json")

    try:
        return json.loads(s)
    except Exception:
        pass

    last = s.rfind("}")
    while last != -1:
        try:
            return json.loads(s[: last + 1])
        except Exception:
            last = s.rfind("}", 0, last)
    raise ValueError("invalid json")


def _read_miningcore_conf() -> dict:
    if not MININGCORE_CONF_PATH.exists():
        return {}
    return _extract_json_obj(MININGCORE_CONF_PATH.read_text(encoding="utf-8", errors="replace"))


def _atomic_write_text(path: Path, text: str, *, encoding: str = "utf-8"):
    path.parent.mkdir(parents=True, exist_ok=True)

    tmp_path = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding=encoding,
            dir=str(path.parent),
            prefix=f".{path.name}.tmp-",
            delete=False,
        ) as f:
            tmp_path = Path(f.name)
            f.write(text)
            f.flush()
            try:
                os.fsync(f.fileno())
            except Exception:
                pass

        try:
            if path.exists():
                os.chmod(tmp_path, path.stat().st_mode)
        except Exception:
            pass

        os.replace(tmp_path, path)
    except Exception:
        if tmp_path is not None:
            try:
                tmp_path.unlink(missing_ok=True)
            except Exception:
                pass
        raise


def _write_miningcore_conf(conf: dict):
    try:
        if isinstance(conf, dict):
            conf.setdefault("notifications", {"enabled": False})
            banning = conf.get("banning")
            if isinstance(banning, dict):
                banning.pop("manager", None)
            pools = conf.get("pools")
            if isinstance(pools, list):
                for pool in pools:
                    if not isinstance(pool, dict):
                        continue
                    pp = pool.get("paymentProcessing")
                    if pp is None:
                        pool["paymentProcessing"] = {"enabled": False}
                    elif isinstance(pp, dict):
                        pp.setdefault("enabled", False)
    except Exception:
        pass
    try:
        _atomic_write_text(MININGCORE_CONF_PATH, json.dumps(conf, indent=2, sort_keys=True) + "\n")
    except OSError as e:
        if getattr(e, "errno", None) not in (errno.EACCES, errno.EROFS):
            raise
        raise ValueError(
            f"Cannot write Miningcore config at '{MININGCORE_CONF_PATH}' (permission denied). "
            "This usually means the file is owned by root due to an older install; restart the app to run migrations, "
            "or fix permissions on /data/pool/config/miningcore.json."
        )


def _read_pool_settings_state() -> dict:
    try:
        if not POOL_SETTINGS_STATE_PATH.exists():
            return {}
        obj = json.loads(POOL_SETTINGS_STATE_PATH.read_text(encoding="utf-8", errors="replace"))
        return obj if isinstance(obj, dict) else {}
    except Exception:
        return {}


def _write_pool_settings_state(obj: dict):
    try:
        STATE_DIR.mkdir(parents=True, exist_ok=True)
        _atomic_write_text(POOL_SETTINGS_STATE_PATH, json.dumps(obj, indent=2, sort_keys=True) + "\n")
    except Exception:
        pass


def _read_json_file(path: Path) -> dict:
    try:
        if not path.exists():
            return {}
        obj = json.loads(path.read_text(encoding="utf-8", errors="replace"))
        return obj if isinstance(obj, dict) else {}
    except Exception:
        return {}


def _write_json_file(path: Path, obj: dict) -> None:
    try:
        STATE_DIR.mkdir(parents=True, exist_ok=True)
        _atomic_write_text(path, json.dumps(obj, indent=2, sort_keys=True) + "\n")
    except Exception:
        pass


def _install_time_s() -> int:
    # Best-effort heuristic used for "since first install" backscans.
    now_s = int(time.time())
    candidates: list[float] = []
    try:
        if INSTALL_ID_PATH.exists():
            candidates.append(INSTALL_ID_PATH.stat().st_mtime)
    except Exception:
        pass
    try:
        if STATE_DIR.exists():
            for p in STATE_DIR.glob("*"):
                try:
                    if p.is_file():
                        candidates.append(p.stat().st_mtime)
                except Exception:
                    continue
    except Exception:
        pass
    try:
        if not candidates:
            return now_s
        # Earliest timestamp we can find.
        return int(max(0, min(candidates)))
    except Exception:
        return now_s


def _parse_month_yyyy_mm(v: object) -> int | None:
    s = str(v or "").strip()
    if not s:
        return None
    m = re.match(r"^(\d{4})-(\d{2})$", s)
    if not m:
        return None
    try:
        y = int(m.group(1))
        mo = int(m.group(2))
        if y < 2009 or mo < 1 or mo > 12:
            return None
        dt = datetime(y, mo, 1, tzinfo=timezone.utc)
        return int(dt.timestamp())
    except Exception:
        return None


def _estimate_start_height(tip_h: int, from_ts: int, spacing_s: int, buffer_blocks: int) -> int:
    now_s = int(time.time())
    age_s = max(0, now_s - int(from_ts))
    approx_blocks = max(0, int(age_s / max(1, int(spacing_s))))
    return max(0, int(tip_h) - approx_blocks - int(buffer_blocks))


def _block_header_time_s(height: int) -> int | None:
    try:
        h = int(height)
        if h < 0:
            return None
    except Exception:
        return None
    try:
        bh = _rpc_call("getblockhash", [h])
    except Exception:
        return None
    if not isinstance(bh, str) or not re.match(r"^[0-9a-fA-F]{64}$", bh):
        return None
    try:
        hdr = _rpc_call("getblockheader", [bh.lower()]) or {}
    except Exception:
        return None
    if not isinstance(hdr, dict):
        return None
    try:
        t = int(hdr.get("time") or 0)
        return t if t > 0 else None
    except Exception:
        return None


def _find_start_height_by_time(*, tip_h: int, from_ts: int, buffer_blocks: int = 20000) -> int | None:
    try:
        tip = int(tip_h)
        target = int(from_ts)
        if tip < 0 or target <= 0:
            return None
    except Exception:
        return None

    # Binary search for the first block whose header time is >= from_ts.
    # Block header times are mostly monotonic (good enough for our purpose).
    lo = 0
    hi = tip
    best = None
    while lo <= hi:
        mid = (lo + hi) // 2
        t = _block_header_time_s(mid)
        if t is None:
            # If the node is warming up or RPC is flaky, bail out and let the caller retry.
            return None
        if t >= target:
            best = mid
            hi = mid - 1
        else:
            lo = mid + 1

    if best is None:
        best = max(0, tip - 1)

    return max(0, int(best) - int(buffer_blocks))


def _read_payout_history_state() -> dict:
    return _read_json_file(PAYOUT_HISTORY_PATH)


def _write_payout_history_state(obj: dict) -> None:
    _write_json_file(PAYOUT_HISTORY_PATH, obj)


def _record_payout_history_address(addr: str) -> None:
    a = (addr or "").strip()
    if not a:
        return
    now_s = int(time.time())
    st = _read_payout_history_state()
    entries = st.get("addresses") if isinstance(st.get("addresses"), list) else []
    out: list[dict] = []
    found = False
    for e in entries:
        if not isinstance(e, dict):
            continue
        ea = str(e.get("addr") or "").strip()
        if not ea:
            continue
        if ea == a:
            found = True
            out.append({"addr": ea, "t": int(e.get("t") or now_s)})
        else:
            out.append({"addr": ea, "t": int(e.get("t") or now_s)})
    if not found:
        out.append({"addr": a, "t": now_s})
    st["addresses"] = out[-20:]
    st["updatedAt"] = now_s
    _write_payout_history_state(st)


def _payout_history_addresses() -> list[str]:
    out: list[str] = []
    try:
        st = _read_payout_history_state()
        entries = st.get("addresses") if isinstance(st.get("addresses"), list) else []
        for e in entries:
            if not isinstance(e, dict):
                continue
            a = str(e.get("addr") or "").strip()
            if a:
                out.append(a)
    except Exception:
        pass
    # Always include current desired payout address (if any).
    try:
        st = _read_pool_settings_state()
        a = str(st.get("payoutAddress") or "").strip()
        if a:
            out.append(a)
    except Exception:
        pass
    seen = set()
    uniq: list[str] = []
    for a in out:
        if a in seen:
            continue
        seen.add(a)
        uniq.append(a)
    return uniq


def _payout_history_earliest_t_s() -> int | None:
    try:
        st = _read_payout_history_state()
        entries = st.get("addresses") if isinstance(st.get("addresses"), list) else []
        ts: list[int] = []
        for e in entries:
            if not isinstance(e, dict):
                continue
            try:
                t = int(e.get("t") or 0)
            except Exception:
                continue
            if t > 0:
                ts.append(t)
        return min(ts) if ts else None
    except Exception:
        return None


def _payout_history_updated_at_s() -> int | None:
    try:
        st = _read_payout_history_state()
        v = st.get("updatedAt")
        if v is None:
            return None
        n = int(float(v))
        return n if n > 0 else None
    except Exception:
        return None


def _payout_scripts_hex(addrs: list[str]) -> set[str]:
    scripts: set[str] = set()
    for a in addrs:
        addr = (a or "").strip()
        if not addr:
            continue
        with PAYOUT_SCRIPT_CACHE_LOCK:
            cached = PAYOUT_SCRIPT_CACHE.get(addr)
        if cached:
            scripts.add(cached)
            continue
        try:
            res = _rpc_call("validateaddress", [addr]) or {}
            spk = str(res.get("scriptPubKey") or "").strip().lower()
            if spk:
                scripts.add(spk)
                with PAYOUT_SCRIPT_CACHE_LOCK:
                    PAYOUT_SCRIPT_CACHE[addr] = spk
        except Exception:
            continue
    return scripts


def _dgb_explorer_tx(txid: str | None) -> str | None:
    t = str(txid or "").strip().lower()
    if not t or not re.match(r"^[0-9a-f]{64}$", t):
        return None
    return f"https://blockchair.com/digibyte/transaction/{t}"


def _dgb_explorer_block(blockhash: str | None) -> str | None:
    h = str(blockhash or "").strip().lower()
    if not h or not re.match(r"^[0-9a-f]{64}$", h):
        return None
    return f"https://blockchair.com/digibyte/block/{h}"


def _is_transient_rpc_issue(err: Exception) -> bool:
    if isinstance(err, RpcError):
        try:
            code = int(err.code) if err.code is not None else None
        except Exception:
            code = None
        msg = str(getattr(err, "message", "") or str(err) or "").lower()
        # -28 is the common "Loading block index..." warmup code.
        if code in (-28, -25):
            return True
        if "warmup" in msg or "loading" in msg or "verifying" in msg or "rewinding" in msg:
            return True
        return False

    msg = str(err or "").lower()
    transient_markers = [
        "connection refused",
        "timed out",
        "timeout",
        "temporarily unavailable",
        "service unavailable",
        "name does not resolve",
        "name or service not known",
        "connection reset",
        "connection aborted",
        "remote end closed connection",
    ]
    return any(m in msg for m in transient_markers)


def _maybe_backscan_blocks(max_blocks: int = 20) -> None:
    # Incremental backscan that finds blocks mined by this pool's payout address(es).
    try:
        addrs = _payout_history_addresses()
        if not addrs:
            return
        addr_hash = hashlib.sha256("|".join(sorted(addrs)).encode("utf-8")).hexdigest()

        state = _read_json_file(BLOCKS_STATE_PATH)
        scan = state.get("backscan") if isinstance(state.get("backscan"), dict) else {}
        prev_hash = str(scan.get("payoutAddrHash") or "").strip().lower() or None
        now_s = int(time.time())
        stop_requested = BACKSCAN_STOP_EVENT.is_set() or bool(scan.get("stopRequested"))

        if stop_requested:
            try:
                scan["enabled"] = False
                scan["stopRequested"] = False
                scan["stopped"] = True
                scan["status"] = "stopped"
                scan["stale"] = bool(scan.get("stale"))
                scan["updatedAt"] = now_s
                scan["stoppedAt"] = now_s
                state["backscan"] = scan
                _write_json_file(BLOCKS_STATE_PATH, state)
            finally:
                BACKSCAN_STOP_EVENT.clear()
            return

        # If payout history has changed since the last completed scan, mark the scan stale so
        # the UI exposes the "rescan" button (otherwise users can get "Complete" + empty list).
        try:
            completed_at = int(scan.get("completedAt") or 0)
        except Exception:
            completed_at = 0
        ph_updated = _payout_history_updated_at_s() or 0
        if bool(scan.get("complete")) and completed_at and ph_updated and ph_updated > completed_at:
            scan["stale"] = True
            scan["enabled"] = False
            scan["updatedAt"] = now_s
            state["backscan"] = scan
            _write_json_file(BLOCKS_STATE_PATH, state)
            return

        if prev_hash and prev_hash != addr_hash:
            if bool(scan.get("complete")):
                scan["stale"] = True
                scan["enabled"] = False
                scan["payoutAddrHash"] = addr_hash
                scan["updatedAt"] = now_s
                state["backscan"] = scan
                _write_json_file(BLOCKS_STATE_PATH, state)
                return
            if not bool(scan.get("enabled")):
                scan["stale"] = True
                scan["enabled"] = False
                scan["payoutAddrHash"] = addr_hash
                scan["updatedAt"] = now_s
                state["backscan"] = scan
                _write_json_file(BLOCKS_STATE_PATH, state)
                return
            # Scan in progress and payout history changed: restart pointers.
            scan = {}

        enabled = bool(scan.get("enabled", False))
        if bool(scan.get("complete")):
            return
        if not enabled:
            return

        scripts = _payout_scripts_hex(addrs)
        if not scripts:
            return

        events = state.get("events") if isinstance(state.get("events"), list) else []
        known = {e.get("hash") for e in events if isinstance(e, dict)}

        interval_raw = scan.get("intervalS")
        try:
            interval_s = int(float(interval_raw)) if interval_raw is not None else int(BACKSCAN_DEFAULT_INTERVAL_S)
        except Exception:
            interval_s = int(BACKSCAN_DEFAULT_INTERVAL_S)
        last_run = int(scan.get("lastRunAt") or 0)
        if interval_s > 0 and last_run and (now_s - last_run) < interval_s:
            return

        max_blocks_raw = scan.get("maxBlocks")
        try:
            max_blocks = int(float(max_blocks_raw)) if max_blocks_raw is not None else int(max_blocks or BACKSCAN_DEFAULT_MAX_BLOCKS)
        except Exception:
            max_blocks = int(max_blocks or BACKSCAN_DEFAULT_MAX_BLOCKS)
        next_h = scan.get("nextHeight")
        start_h = scan.get("startHeight")
        try:
            tip_h = _rpc_call("getblockcount")
        except Exception as e:
            if _is_transient_rpc_issue(e):
                # Node still starting/warming up. Keep the scan enabled so it can resume
                # automatically once RPC is reachable.
                scan["enabled"] = True
                scan["status"] = "waiting"
                scan.pop("error", None)
                scan.pop("errorAt", None)
                scan["updatedAt"] = now_s
                scan["lastRunAt"] = now_s
            else:
                scan["enabled"] = False
                scan["status"] = "error"
                scan["error"] = str(e)
                scan["errorAt"] = now_s
                scan["updatedAt"] = now_s
            state["backscan"] = scan
            _write_json_file(BLOCKS_STATE_PATH, state)
            return
        try:
            tip_h = int(tip_h)
        except Exception:
            return

        if next_h is None or start_h is None:
            install_t = _install_time_s()
            from_t = _payout_history_earliest_t_s()
            base_t = int(from_t) if from_t is not None else int(install_t)
            # Prefer an RPC-based height estimate so month scans don't miss blocks due to
            # block-time variability over long periods.
            start_h_guess = _find_start_height_by_time(tip_h=tip_h, from_ts=base_t, buffer_blocks=20000)
            if start_h_guess is None:
                # Fallback to a simple estimate if RPC isn't ready yet.
                approx_blocks = max(0, int((now_s - int(base_t)) / 15))
                start_h_guess = max(0, tip_h - approx_blocks - 20000)
            start_h = int(start_h_guess)
            next_h = int(start_h)
            scan = {
                "startHeight": int(start_h),
                "nextHeight": int(next_h),
                "tipHeightAtStart": int(tip_h),
                "startedAt": now_s,
                "updatedAt": now_s,
                "enabled": True,
                "complete": False,
                "payoutAddrHash": addr_hash,
                "status": "running",
            }

        blocks_done = 0
        while blocks_done < max_blocks and int(next_h) <= tip_h:
            if BACKSCAN_STOP_EVENT.is_set():
                break
            h = int(next_h)
            next_h = h + 1
            blocks_done += 1

            try:
                blockhash = _rpc_call("getblockhash", [h])
                if not isinstance(blockhash, str) or not re.match(r"^[0-9a-fA-F]{64}$", blockhash):
                    continue
                bh = blockhash.lower()
                if bh in known:
                    continue

                blk = _rpc_call("getblock", [bh, 2]) or {}
                if not isinstance(blk, dict):
                    continue
                txs = blk.get("tx")
                if not isinstance(txs, list) or not txs:
                    continue
                cb = txs[0]
                if not isinstance(cb, dict):
                    continue
                coinbase_txid = cb.get("txid")
                if not isinstance(coinbase_txid, str) or not re.match(r"^[0-9a-fA-F]{64}$", coinbase_txid):
                    continue
                vouts = cb.get("vout")
                if not isinstance(vouts, list):
                    continue

                matched = False
                for v in vouts:
                    if not isinstance(v, dict):
                        continue
                    spk = v.get("scriptPubKey")
                    if not isinstance(spk, dict):
                        continue
                    spk_hex = str(spk.get("hex") or "").strip().lower()
                    if spk_hex and spk_hex in scripts:
                        matched = True
                        break

                if not matched:
                    continue

                pow_algo = None
                try:
                    pow_algo = str(blk.get("pow_algo") or "").strip().lower() or None
                except Exception:
                    pow_algo = None
                algo_tag = None
                if pow_algo == "scrypt":
                    algo_tag = "scrypt"
                elif pow_algo == "sha256d":
                    algo_tag = "sha256"

                t = blk.get("time")
                try:
                    t_i = int(t) if t is not None else now_s
                except Exception:
                    t_i = now_s

                conf = blk.get("confirmations")
                try:
                    conf_i = int(conf) if conf is not None else None
                except Exception:
                    conf_i = None

                status_i = 1 if (conf_i is not None and conf_i > 0) else 0
                netdiff = blk.get("difficulty")
                try:
                    netdiff_f = float(netdiff) if netdiff is not None else None
                    if netdiff_f is not None and not math.isfinite(netdiff_f):
                        netdiff_f = None
                except Exception:
                    netdiff_f = None

                events.append(
                    {
                        "t": t_i,
                        "hash": bh,
                        "height": h,
                        "coinbase_txid": coinbase_txid.lower(),
                        "confirmations": conf_i,
                        "status": status_i,
                        "pow_algo": pow_algo,
                        "algo": algo_tag,
                        "source": "backscan",
                        "explorer_tx": _dgb_explorer_tx(coinbase_txid),
                        "explorer_block": _dgb_explorer_block(bh),
                        "network_difficulty": netdiff_f,
                        "difficulty_hit": _sha256d_difficulty_hit_from_pow_hash(bh) if pow_algo == "sha256d" else None,
                    }
                )
                known.add(bh)
            except Exception:
                continue

        scan["nextHeight"] = int(next_h)
        scan["tipHeightLast"] = int(tip_h)
        scan["updatedAt"] = now_s
        scan["lastRunAt"] = now_s
        scan["complete"] = bool(int(next_h) > tip_h)
        scan["enabled"] = bool(scan.get("enabled", False))
        scan["payoutAddrHash"] = addr_hash
        scan["stopRequested"] = False
        scan.pop("error", None)
        scan.pop("errorAt", None)
        if BACKSCAN_STOP_EVENT.is_set():
            scan["enabled"] = False
            scan["complete"] = False
            scan["stopped"] = True
            scan["status"] = "stopped"
            scan["stoppedAt"] = now_s
            BACKSCAN_STOP_EVENT.clear()
        if scan["complete"]:
            scan["enabled"] = False
            scan["status"] = "complete"
            scan["completedAt"] = now_s
        elif scan.get("enabled"):
            scan["status"] = "running"

        state["backscan"] = scan
        state["events"] = events[-200:]
        _write_json_file(BLOCKS_STATE_PATH, state)
    except Exception:
        return


def _maybe_detect_recent_wins(*, max_blocks: int = 10) -> None:
    """
    Lightweight "tail scan" that checks the most recent blocks for a coinbase paying to our
    configured payout address scripts.

    This acts as a resilient win detector even if Miningcore's blocks table is missing/broken.
    """
    try:
        addrs = _payout_history_addresses()
        if not addrs:
            return
        scripts = _payout_scripts_hex(addrs)
        if not scripts:
            return

        now_s = int(time.time())
        state = _read_json_file(BLOCKS_STATE_PATH)
        live = state.get("live") if isinstance(state.get("live"), dict) else {}
        events = state.get("events") if isinstance(state.get("events"), list) else []
        known = {e.get("hash") for e in events if isinstance(e, dict)}

        try:
            tip_h = int(_rpc_call("getblockcount"))
        except Exception:
            return
        if tip_h <= 0:
            return

        next_h = live.get("nextHeight")
        try:
            next_h_i = int(next_h) if next_h is not None else None
        except Exception:
            next_h_i = None

        # Start near tip on first run.
        start_h = next_h_i if next_h_i is not None else max(0, tip_h - max(2, int(max_blocks)))
        start_h = max(0, min(int(start_h), int(tip_h)))

        checked = 0
        for h in range(start_h, tip_h + 1):
            if checked >= int(max_blocks):
                break
            checked += 1

            try:
                blockhash = _rpc_call("getblockhash", [int(h)])
                if not isinstance(blockhash, str) or not re.match(r"^[0-9a-fA-F]{64}$", blockhash):
                    continue
                bh = blockhash.lower()
                if bh in known:
                    continue

                blk = _rpc_call("getblock", [bh, 2]) or {}
                if not isinstance(blk, dict):
                    continue
                txs = blk.get("tx")
                if not isinstance(txs, list) or not txs:
                    continue
                cb = txs[0]
                if not isinstance(cb, dict):
                    continue
                coinbase_txid = cb.get("txid")
                if not isinstance(coinbase_txid, str) or not re.match(r"^[0-9a-fA-F]{64}$", coinbase_txid):
                    continue
                vouts = cb.get("vout")
                if not isinstance(vouts, list):
                    continue

                matched = False
                for v in vouts:
                    if not isinstance(v, dict):
                        continue
                    spk = v.get("scriptPubKey")
                    if not isinstance(spk, dict):
                        continue
                    spk_hex = str(spk.get("hex") or "").strip().lower()
                    if spk_hex and spk_hex in scripts:
                        matched = True
                        break
                if not matched:
                    continue

                pow_algo = None
                try:
                    pow_algo = str(blk.get("pow_algo") or "").strip().lower() or None
                except Exception:
                    pow_algo = None
                algo_tag = None
                if pow_algo == "scrypt":
                    algo_tag = "scrypt"
                elif pow_algo == "sha256d":
                    algo_tag = "sha256"

                t = blk.get("time")
                try:
                    t_i = int(t) if t is not None else now_s
                except Exception:
                    t_i = now_s

                conf = blk.get("confirmations")
                try:
                    conf_i = int(conf) if conf is not None else None
                except Exception:
                    conf_i = None

                status_i = 1 if (conf_i is not None and conf_i > 0) else 0
                netdiff = blk.get("difficulty")
                try:
                    netdiff_f = float(netdiff) if netdiff is not None else None
                    if netdiff_f is not None and not math.isfinite(netdiff_f):
                        netdiff_f = None
                except Exception:
                    netdiff_f = None

                events.append(
                    {
                        "t": t_i,
                        "hash": bh,
                        "height": int(h),
                        "coinbase_txid": coinbase_txid.lower(),
                        "confirmations": conf_i,
                        "status": status_i,
                        "pow_algo": pow_algo,
                        "algo": algo_tag,
                        "source": "live",
                        "explorer_tx": _dgb_explorer_tx(coinbase_txid),
                        "explorer_block": _dgb_explorer_block(bh),
                        "network_difficulty": netdiff_f,
                        "difficulty_hit": _sha256d_difficulty_hit_from_pow_hash(bh) if pow_algo == "sha256d" else None,
                    }
                )
                known.add(bh)
            except Exception:
                continue

        live["nextHeight"] = int(tip_h + 1)
        live["updatedAt"] = now_s
        state["live"] = live
        state["events"] = events[-200:]
        _write_json_file(BLOCKS_STATE_PATH, state)
    except Exception:
        return


def _to_num(value, default: float) -> float:
    try:
        f = float(value)
        if not math.isfinite(f):
            return float(default)
        return f
    except Exception:
        return float(default)


def _maybe_num(value):
    if value is None:
        return None
    if isinstance(value, bool):
        return None
    if isinstance(value, (int, float)):
        f = float(value)
        if not math.isfinite(f):
            return None
        return f
    s = str(value).strip()
    if not s:
        return None
    try:
        f = float(s)
    except Exception:
        return None
    if not math.isfinite(f):
        return None
    return f


def _pool_settings():
    conf_addr = ""
    mindiff = None
    startdiff = None
    maxdiff = None
    primary_pool_id = _pool_id_for_algo("sha256")

    try:
        conf = _read_miningcore_conf()
        pools = conf.get("pools") or []
        pool_conf = None
        if isinstance(pools, list):
            for item in pools:
                if isinstance(item, dict) and str(item.get("id") or "") == primary_pool_id:
                    pool_conf = item
                    break
            if pool_conf is None:
                for item in pools:
                    if isinstance(item, dict):
                        pool_conf = item
                        break
        if isinstance(pool_conf, dict):
            conf_addr = str(pool_conf.get("address") or "").strip()
            ports = pool_conf.get("ports") or {}
            if isinstance(ports, dict) and ports:
                first = next(iter(ports.values()))
                if isinstance(first, dict):
                    startdiff = first.get("difficulty")
                    vardiff = first.get("varDiff") or {}
                    if isinstance(vardiff, dict):
                        mindiff = vardiff.get("minDiff")
                        maxdiff = vardiff.get("maxDiff")
    except Exception:
        conf_addr = ""

    state = _read_pool_settings_state()
    desired_addr = str(state.get("payoutAddress") or "").strip()
    desired_mindiff = _maybe_num(state.get("mindiff"))
    desired_startdiff = _maybe_num(state.get("startdiff"))
    desired_maxdiff = _maybe_num(state.get("maxdiff"))
    validated = state.get("validated")
    validation_warning = state.get("validationWarning")

    actual_addr = conf_addr
    actual_configured = bool(actual_addr) and actual_addr != POOL_PLACEHOLDER_PAYOUT_ADDRESS

    # If the user saved a new payout address but hasn't restarted yet, surface the
    # saved value in the UI while still indicating the pool isn't configured
    # until Miningcore is updated (via init on restart).
    payout_address = desired_addr or actual_addr
    pending_apply = bool(desired_addr) and desired_addr != actual_addr
    configured = bool(payout_address) and payout_address != POOL_PLACEHOLDER_PAYOUT_ADDRESS and actual_configured and not pending_apply

    if pending_apply:
        validation_warning = (
            "Saved. Restart the app to apply the new payout address and varDiff settings."
            + (f" {validation_warning}" if isinstance(validation_warning, str) and validation_warning.strip() else "")
        )

    if not configured and not pending_apply:
        payout_address = ""
        validated = None
        validation_warning = None

    if validated is not None:
        validated = bool(validated)
    if not isinstance(validation_warning, str):
        validation_warning = None

    return {
        "payoutAddress": payout_address or "",
        "configured": configured,
        "pendingApply": pending_apply,
        "restartRequired": pending_apply,
        "validated": validated,
        "validationWarning": validation_warning,
        "mindiff": _to_num(desired_mindiff if desired_mindiff is not None else mindiff, 1024),
        "startdiff": _to_num(desired_startdiff if desired_startdiff is not None else startdiff, 4096),
        "maxdiff": _to_num(desired_maxdiff if desired_maxdiff is not None else maxdiff, 131072),
        "warning": (
            "Set a payout address before mining, then restart the app. Miningcore uses this address when generating blocks."
            if not configured and not pending_apply
            else None
        ),
    }


def _is_loopback_listen(addr: str | None) -> bool:
    s = str(addr or "").strip().lower()
    if not s:
        return False
    return s in {"127.0.0.1", "localhost", "::1"}


def _stratum_bind_state_for_pool(pool_id: str) -> dict:
    """
    Inspect miningcore.json to infer whether Stratum is bound publicly or locked to localhost.

    Note: Docker maps host ports (e.g. 5678/5679) to the Miningcore container ports declared
    in miningcore.json (typically 3333/3334). If Miningcore listens on 127.0.0.1 inside the
    container, miners outside the container cannot connect even if docker publishes the port.
    """
    try:
        conf = _read_miningcore_conf()
    except Exception as e:
        return {
            "ok": False,
            "error": str(e),
            "ports": [],
            "listenAddresses": [],
            "boundPublic": None,
        }

    pools = conf.get("pools") or []
    pool_conf = None
    if isinstance(pools, list):
        for item in pools:
            if isinstance(item, dict) and str(item.get("id") or "") == pool_id:
                pool_conf = item
                break
        if pool_conf is None:
            for item in pools:
                if isinstance(item, dict):
                    pool_conf = item
                    break

    ports = {}
    if isinstance(pool_conf, dict):
        ports = pool_conf.get("ports") or {}

    listen_addrs: list[str] = []
    port_nums: list[int] = []
    if isinstance(ports, dict):
        for k, v in ports.items():
            try:
                port_nums.append(int(k))
            except Exception:
                pass
            if not isinstance(v, dict):
                continue
            la = v.get("listenAddress")
            if la is None:
                la = v.get("listen_address")
            if la is None:
                continue
            s = str(la).strip()
            if s:
                listen_addrs.append(s)

    listen_addrs = sorted(set(listen_addrs))
    port_nums = sorted(set(port_nums))

    if not listen_addrs:
        bound_public = None
    else:
        bound_public = any(not _is_loopback_listen(a) for a in listen_addrs)

    return {
        "ok": True,
        "ports": port_nums,
        "listenAddresses": listen_addrs,
        "boundPublic": bound_public,
    }


def _stratum_status_for_algo(algo: str | None) -> dict:
    algo_s = (algo or "sha256").strip().lower() or "sha256"
    pool_id = _pool_id_for_algo(algo_s)
    settings = _pool_settings()
    bind = _stratum_bind_state_for_pool(pool_id)

    payout = str(settings.get("payoutAddress") or "").strip()
    configured = bool(settings.get("configured"))
    restart_required = bool(settings.get("restartRequired"))
    pending_apply = bool(settings.get("pendingApply"))

    status = "unknown"
    reason = None

    if not payout:
        status = "locked"
        reason = "Set a payout address in Settings to unlock Stratum."
    elif pending_apply or restart_required:
        status = "locked"
        reason = "Restart required to apply payout/difficulty settings and unlock Stratum."
    elif bind.get("ok") is False:
        status = "error"
        reason = "Cannot read Miningcore config; Stratum state unknown."
    else:
        bound_public = bind.get("boundPublic")
        if bound_public is True:
            status = "open"
        elif bound_public is False:
            status = "locked"
            reason = "Stratum is bound to localhost inside Miningcore (remote miners can't connect)."
        else:
            status = "unknown"

    if not configured and status == "open":
        # Safety: we should never present "ready" when payout isn't configured.
        status = "locked"
        reason = reason or "Set a payout address in Settings, then restart the app."

    return {
        "algo": algo_s,
        "poolId": pool_id,
        "status": status,
        "reason": reason,
        "payoutConfigured": configured,
        "restartRequired": restart_required,
        "listenAddresses": bind.get("listenAddresses") if isinstance(bind, dict) else [],
        "boundPublic": bind.get("boundPublic") if isinstance(bind, dict) else None,
        "containerPorts": bind.get("ports") if isinstance(bind, dict) else [],
    }


def _update_pool_settings(
    *,
    payout_address: str,
    mindiff=None,
    startdiff=None,
    maxdiff=None,
):
    addr = payout_address.strip()
    if not addr:
        raise ValueError("payoutAddress is required")

    validated = None
    validation_warning = None
    try:
        res = _rpc_call("validateaddress", [addr]) or {}
    except Exception:
        raise ValueError("Node is still starting/syncing; can't verify payout address yet. Try again in a few minutes.")
    else:
        validated = bool(res.get("isvalid")) if isinstance(res, dict) else False
        if not validated:
            raise ValueError("payoutAddress is not a valid DigiByte address")

    # Miningcore currently cannot use DigiByte bech32 (dgb1...) payout addresses.
    if addr.lower().startswith("dgb1"):
        raise ValueError("payoutAddress must be a legacy/base58 DigiByte address (not dgb1)")

    md = _maybe_num(mindiff)
    sd = _maybe_num(startdiff)
    xd = _maybe_num(maxdiff)

    use_md = md if md is not None else 1024
    use_sd = sd if sd is not None else max(4096, use_md)
    use_xd = xd if xd is not None else 131072

    if use_md <= 0:
        raise ValueError("mindiff must be > 0")
    if use_sd <= 0:
        raise ValueError("startdiff must be > 0")
    if use_sd < use_md:
        raise ValueError("startdiff must be >= mindiff")
    if use_xd < 0:
        raise ValueError("maxdiff must be 0 (no limit) or >= startdiff")
    if use_xd != 0 and use_xd < use_sd:
        raise ValueError("maxdiff must be 0 (no limit) or >= startdiff")

    # Do not write miningcore.json from the UI container; persist desired settings in
    # a UI-owned state file and let the init container (root) apply them on restart.
    _write_pool_settings_state(
        {
            "payoutAddress": addr,
            "mindiff": use_md,
            "startdiff": use_sd,
            "maxdiff": use_xd,
            "validated": bool(validated) if validated is not None else None,
            "validationWarning": validation_warning,
            "updatedAt": int(time.time()),
        }
    )
    _record_payout_history_address(addr)

    return _pool_settings()


def _miningcore_get_any(path: str, *, timeout_s: int = 8):
    base = MININGCORE_API_URL
    if not base:
        raise RuntimeError("MININGCORE_API_URL not set")
    if not path.startswith("/"):
        path = "/" + path
    url = base + path
    req = urllib.request.Request(url, headers={"accept": "application/json"}, method="GET")
    with urllib.request.urlopen(req, timeout=timeout_s) as resp:
        return json.loads(resp.read().decode("utf-8", errors="replace"))


def _miningcore_get_json(path: str, *, timeout_s: int = 8) -> dict:
    data = _miningcore_get_any(path, timeout_s=timeout_s)
    if not isinstance(data, dict):
        raise RuntimeError(f"Expected JSON object from Miningcore at {path}")
    return data


def _miningcore_try(path: str, *, timeout_s: int = 4) -> dict:
    out = {"ok": False, "error": None}
    try:
        data = _miningcore_get_any(path, timeout_s=timeout_s)
        out["ok"] = True
        # Keep payload small: only surface basic shape for debugging.
        if isinstance(data, dict):
            out["keys"] = sorted([str(k) for k in data.keys()])[:50]
        elif isinstance(data, list):
            out["len"] = len(data)
        return out
    except Exception as e:
        out["error"] = f"{type(e).__name__}: {e}"
        return out


def _db_diag() -> dict:
    """
    Lightweight, sanitized diagnostics for DB/Miningcore connectivity.
    Exposed via /api/debug/db (dev helper).
    """
    global _DB_DIAG_CACHE, _DB_DIAG_CACHE_T
    now = time.time()
    with _DB_DIAG_LOCK:
        if _DB_DIAG_CACHE is not None and (now - _DB_DIAG_CACHE_T) < 5:
            return _DB_DIAG_CACHE

    out: dict = {
        "pg8000": bool(pg8000 is not None),
        "pg_conf": None,
        "pg_connect": {"ok": False, "error": None},
        "tables": {},
        "share_probe": {},
        "miningcore": {},
    }

    cfg = None
    try:
        cfg = _pg_conf()
    except Exception as e:
        out["pg_conf_error"] = f"{type(e).__name__}: {e}"
        cfg = None

    if isinstance(cfg, dict):
        port_i = None
        try:
            port_i = int(cfg.get("port") or 0)
        except Exception:
            port_i = None
        out["pg_conf"] = {
            "host": str(cfg.get("host") or ""),
            "port": port_i,
            "database": str(cfg.get("database") or ""),
            "user": str(cfg.get("user") or ""),
            "password_set": bool(str(cfg.get("password") or "").strip()),
        }

    if pg8000 is None:
        out["pg_connect"]["error"] = "pg8000 not installed"
    elif not isinstance(cfg, dict):
        out["pg_connect"]["error"] = "pg config unavailable"
    else:
        try:
            conn = pg8000.connect(
                host=str(cfg.get("host") or "postgres"),
                port=int(cfg.get("port") or 5432),
                user=str(cfg.get("user") or "miningcore"),
                password=(str(cfg.get("password") or "").strip() or None),
                database=str(cfg.get("database") or "miningcore"),
                timeout=3,
            )
            try:
                cur = conn.cursor()
                cur.execute("SELECT 1")
                cur.fetchone()
                out["pg_connect"]["ok"] = True

                want_tables = ["shares", "minerstats", "blocks", "poolstats"]
                tables: dict[str, bool] = {}
                for t in want_tables:
                    try:
                        cur.execute(
                            "SELECT 1 FROM information_schema.tables WHERE table_schema='public' AND table_name=%s LIMIT 1",
                            (t,),
                        )
                        tables[t] = bool(cur.fetchone())
                    except Exception:
                        tables[t] = False
                out["tables"] = tables

                try:
                    pool_id = _pool_id_for_algo("sha256")
                except Exception:
                    pool_id = MININGCORE_POOL_ID

                if tables.get("shares"):
                    try:
                        cur.execute("SELECT COUNT(*) FROM shares WHERE poolid=%s AND created >= NOW() - INTERVAL '10 minutes'", (pool_id,))
                        row = cur.fetchone()
                        out["share_probe"]["shares_10m"] = int(row[0]) if row and row[0] is not None else None
                    except Exception as e:
                        out["share_probe"]["shares_10m_error"] = f"{type(e).__name__}: {e}"
                    try:
                        cur.execute("SELECT MAX(created) FROM shares WHERE poolid=%s", (pool_id,))
                        row = cur.fetchone()
                        dt = row[0] if row else None
                        out["share_probe"]["last_share_at"] = _iso_z(dt) if isinstance(dt, datetime) else None
                    except Exception as e:
                        out["share_probe"]["last_share_at_error"] = f"{type(e).__name__}: {e}"

                if tables.get("minerstats"):
                    try:
                        cur.execute("SELECT MAX(created) FROM minerstats WHERE poolid=%s", (pool_id,))
                        row = cur.fetchone()
                        dt = row[0] if row else None
                        out["share_probe"]["last_minerstats_at"] = _iso_z(dt) if isinstance(dt, datetime) else None
                    except Exception as e:
                        out["share_probe"]["last_minerstats_at_error"] = f"{type(e).__name__}: {e}"
            finally:
                try:
                    conn.close()
                except Exception:
                    pass
        except Exception as e:
            out["pg_connect"]["error"] = f"{type(e).__name__}: {e}"

    # Miningcore API health (internal network).
    try:
        pool_id = _pool_id_for_algo("sha256")
    except Exception:
        pool_id = MININGCORE_POOL_ID
    out["miningcore"] = {
        "pool": _miningcore_try(f"/api/pools/{pool_id}", timeout_s=4),
        "miners": _miningcore_try(f"/api/pools/{pool_id}/miners", timeout_s=4),
    }

    with _DB_DIAG_LOCK:
        _DB_DIAG_CACHE = out
        _DB_DIAG_CACHE_T = time.time()
    return out


def _dget(obj: dict, *keys, default=None):
    if not isinstance(obj, dict):
        return default
    for key in keys:
        if key in obj:
            return obj.get(key)
    return default


def _avg_hashrate_ths(points: list[dict], *, window_s: int) -> float | None:
    if not points:
        return None
    # Window averages should be computed relative to *now*.
    # Using the last sample timestamp keeps 1m/5m buckets "stuck" after workers disconnect,
    # because the last active window never advances.
    try:
        end_ms = int(_now_ms())
    except Exception:
        end_ms = int(time.time() * 1000)
    cutoff = end_ms - (window_s * 1000)
    vals = []
    for p in points:
        try:
            t = int(p.get("t") or 0)
        except Exception:
            continue
        if t < cutoff or t > end_ms:
            continue

        # If there are no active workers, the effective hashrate is 0 even if a stale
        # sampler point contains a non-zero value.
        try:
            workers_i = int(p.get("workers") or 0)
        except Exception:
            workers_i = 0
        if workers_i <= 0:
            vals.append(0.0)
            continue

        v = p.get("hashrate_ths")
        try:
            fv = float(v)
        except Exception:
            continue
        if math.isfinite(fv):
            vals.append(fv)
    if not vals:
        # If we have history but nothing in the recent window, treat the hashrate as 0.
        # (This is the common "miners disconnected" case.)
        return 0.0
    return sum(vals) / len(vals)


def _pool_status(pool_id: str, *, algo: str | None = None):
    try:
        # Miningcore's HTTP API can return 500s on older/partially-migrated databases.
        # Avoid hard-failing the pool page: use DB-backed stats and node cache as fallbacks.
        data = None
        try:
            data = _miningcore_get_json(f"/api/pools/{pool_id}")
        except Exception:
            data = None

        pool = _dget(data, "pool", "Pool", default={}) if isinstance(data, dict) else {}
        pool = pool if isinstance(pool, dict) else {}
        stats = _dget(pool, "poolStats", "PoolStats", default={}) if isinstance(pool, dict) else {}
        stats = stats if isinstance(stats, dict) else {}
        netstats = _dget(pool, "networkStats", "NetworkStats", default={}) if isinstance(pool, dict) else {}
        netstats = netstats if isinstance(netstats, dict) else {}

        connected = _dget(stats, "connectedMiners", "ConnectedMiners", default=0) or 0
        hashrate_hs = _dget(stats, "poolHashrate", "PoolHashrate", default=0) or 0
        total_blocks = _dget(pool, "totalBlocks", "TotalBlocks", default=None)
        network_difficulty = _dget(netstats, "networkDifficulty", "NetworkDifficulty", default=None)
        network_height = _dget(netstats, "blockHeight", "BlockHeight", default=None)

        # Best-effort network stats from node cache when Miningcore is down.
        if network_height is None or network_difficulty is None:
            node_cached = _read_node_cache()
            node_status = node_cached.get("status") if isinstance(node_cached, dict) else None
            if isinstance(node_status, dict):
                if network_height is None:
                    network_height = node_status.get("blocks")
                if network_difficulty is None:
                    diffs = node_status.get("difficulties")
                    if isinstance(diffs, dict):
                        algo_s = (algo or "sha256").strip().lower() or "sha256"
                        diff_key = {"sha256": "sha256d", "sha256d": "sha256d"}.get(algo_s, algo_s)
                        network_difficulty = diffs.get(diff_key) if diff_key in diffs else network_difficulty

        # Count "active" workers (what users care about) by filtering miners with recent shares / non-zero hashrate.
        # Miningcore can retain workers with no shares (lastShare=null) which inflates ConnectedMiners.
        workers_active_i = None
        try:
            miners_rows = _pool_miners(pool_id) or []
            if not miners_rows:
                workers_active_i = None
            else:
                now_s = int(time.time())
                active = 0
                for m in miners_rows:
                    if not isinstance(m, dict):
                        continue
                    # Prefer explicit share activity when available.
                    last_share = m.get("lastShare") or m.get("last_share") or m.get("last_share_at")
                    if isinstance(last_share, str) and last_share.strip():
                        try:
                            ts = datetime.fromisoformat(last_share.replace("Z", "+00:00")).timestamp()
                            if (now_s - int(ts)) <= 180:
                                active += 1
                                continue
                        except Exception:
                            pass
                    # Fall back to hashrate.
                    try:
                        ths = float(m.get("hashrate_ths_live_10m") or m.get("hashrate_ths") or 0)
                    except Exception:
                        ths = 0.0
                    if math.isfinite(ths) and ths > 0:
                        active += 1
                workers_active_i = active
        except Exception:
            workers_active_i = None

        workers_rows = _pool_workers_from_db(pool_id) or []
        if workers_rows:
            workers_i = len(workers_rows)
            total_hs = 0.0
            any_hashrate = False
            for w in workers_rows:
                if not isinstance(w, dict):
                    continue
                v = w.get("hashrate_hs")
                if v is None:
                    continue
                try:
                    fv = float(v)
                except Exception:
                    continue
                if not math.isfinite(fv):
                    continue
                any_hashrate = True
                total_hs += fv
            # If we have worker rows with hashrate fields, treat "no active hashrate" as 0
            # (prevents stale snapshots from pinning a non-zero number forever).
            hashrate_ths = (total_hs / 1e12) if any_hashrate and total_hs > 0 else (0.0 if any_hashrate else None)
        else:
            # Try local "pool.status" file if Miningcore API isn't healthy.
            workers_i = 0
            hashrate_ths = None
            try:
                workers_i = int(connected)
            except Exception:
                workers_i = 0
            try:
                hashrate_ths = float(hashrate_hs) / 1e12
            except Exception:
                hashrate_ths = None
            hashrate_f = None
            try:
                hashrate_f = float(hashrate_ths) if hashrate_ths is not None else None
            except Exception:
                hashrate_f = None
            if workers_i <= 0 and (hashrate_f is None or not math.isfinite(hashrate_f)):
                try:
                    ps = _parse_pool_status(_read_pool_status_raw())
                    if isinstance(ps, dict):
                        try:
                            workers_i = int(ps.get("workers") or workers_i)
                        except Exception:
                            pass
                        hs = ps.get("hashrate_ths")
                        try:
                            hs_f = float(hs) if hs is not None else None
                        except Exception:
                            hs_f = None
                        if hs_f is not None and math.isfinite(hs_f):
                            hashrate_ths = hs_f
                except Exception:
                    pass

        if workers_active_i is not None:
            workers_total_i = workers_i
            workers_i = int(workers_active_i)
        else:
            workers_total_i = workers_i

        try:
            best = _pool_best_difficulties(pool_id)
        except Exception:
            best = {}

        try:
            share_health = _pool_share_health(pool_id)
        except Exception:
            share_health = {}

        hashrate_ths_best_effort = hashrate_ths
        hashrate_ths_live = None
        try:
            hs10m = share_health.get("hashrate_hs_10m")
            hs10m_f = float(hs10m) if hs10m is not None else None
            if hs10m_f is not None and math.isfinite(hs10m_f) and hs10m_f > 0:
                hashrate_ths_live = hs10m_f / 1e12
        except Exception:
            hashrate_ths_live = None

        if hashrate_ths_live is not None:
            hashrate_ths = hashrate_ths_live

        # Final safety clamp: if we have no active workers and the last accepted share is old,
        # force the displayed pool hashrate to 0 (even if upstream snapshots are stale).
        try:
            if WORKER_ACTIVE_SECONDS > 0 and int(workers_i or 0) <= 0:
                last_share_at = share_health.get("last_share_at")
                ms = _parse_iso_to_ms(last_share_at) if isinstance(last_share_at, str) and last_share_at.strip() else None
                if ms is not None and (_now_ms() - int(ms)) > (WORKER_ACTIVE_SECONDS * 1000):
                    hashrate_ths = 0.0
        except Exception:
            pass

        eta_seconds = None
        try:
            if hashrate_ths and network_difficulty:
                hashrate_hs_f = float(hashrate_ths) * 1e12
                netdiff_f = float(network_difficulty)
                if hashrate_hs_f > 0 and netdiff_f > 0:
                    eta_seconds = (netdiff_f * (2**32)) / hashrate_hs_f
        except Exception:
            eta_seconds = None

        status = {
            "backend": "miningcore",
            "poolId": pool_id,
            "algo": algo,
            "workers": workers_i,
            "workers_total": workers_total_i,
            "hashrate_ths": hashrate_ths,
            "hashrate_ths_best_effort": hashrate_ths_best_effort,
            "hashrate_ths_live_10m": hashrate_ths_live,
            "total_blocks": total_blocks,
            "network_difficulty": network_difficulty,
            "network_height": network_height,
            "best_difficulty_all": best.get("best_difficulty_all"),
            "best_difficulty_since_block": best.get("best_difficulty_since_block"),
            "best_difficulty_since_block_at": best.get("best_difficulty_since_block_at"),
            "best_share_all": best.get("best_share_all") or best.get("best_difficulty_all"),
            "best_share_since_block": best.get("best_share_since_block") or best.get("best_difficulty_since_block"),
            "best_share_since_block_at": best.get("best_share_since_block_at") or best.get("best_difficulty_since_block_at"),
            "best_share_all_worker": best.get("best_share_all_worker"),
            "best_share_since_block_worker": best.get("best_share_since_block_worker"),
            "shares_10m": share_health.get("shares_10m"),
            "shares_1h": share_health.get("shares_1h"),
            "last_share_at": share_health.get("last_share_at"),
            "eta_seconds": eta_seconds,
            # Filled below from our local timeseries sampler; initialize keys so
            # callers always see a stable shape.
            "hashrates_ths": {
                "1m": None,
                "5m": None,
                "15m": None,
                "1h": None,
                "6h": None,
                "1d": None,
                "7d": None,
            },
            "cached": False,
            "lastSeen": int(time.time()),
        }

        try:
            series = _pool_series(pool_id).query(trail="7d", max_points=MAX_SERIES_POINTS)
            now_ms = _now_ms()
            last_t = None
            try:
                last_t = max(int(p.get("t") or 0) for p in series) if series else None
            except Exception:
                last_t = None

            # If the local sampler stalls (e.g. after restarts), the short-window buckets can
            # get stuck at 0/None even while miners are hashing. In that case, fall back to
            # Miningcore's own Postgres snapshots (minerstats).
            stale = (last_t is None) or ((now_ms - int(last_t)) > (3 * 60 * 1000))
            if stale:
                series = _pool_series_from_minerstats(pool_id, trail="7d", max_points=MAX_SERIES_POINTS) or series

            status["hashrates_ths"] = {
                "1m": _avg_hashrate_ths(series, window_s=60),
                "5m": _avg_hashrate_ths(series, window_s=5 * 60),
                "15m": _avg_hashrate_ths(series, window_s=15 * 60),
                "1h": _avg_hashrate_ths(series, window_s=60 * 60),
                "6h": _avg_hashrate_ths(series, window_s=6 * 60 * 60),
                "1d": _avg_hashrate_ths(series, window_s=24 * 60 * 60),
                "7d": _avg_hashrate_ths(series, window_s=7 * 24 * 60 * 60),
            }
            # Prefer short-window hashrate as the primary display metric, but only when we
            # don't have a live shares-based estimate (otherwise the pool card can disagree
            # with the worker cards).
            try:
                if status.get("hashrate_ths_live_10m") is None:
                    hr1m = (status.get("hashrates_ths") or {}).get("1m")
                    if hr1m is not None:
                        hr1m_f = float(hr1m)
                        if math.isfinite(hr1m_f):
                            cur = status.get("hashrate_ths")
                            try:
                                cur_f = float(cur) if cur is not None else None
                            except Exception:
                                cur_f = None
                            # Do not override a good hashrate with a transient 0 bucket.
                            if hr1m_f > 0 or cur_f is None or not math.isfinite(cur_f) or cur_f <= 0:
                                status["hashrate_ths"] = hr1m_f
            except Exception:
                pass
        except Exception:
            pass

        # Cache after computing hashrate windows so cached responses keep the UI populated.
        _write_pool_cache(pool_id, status)

        try:
            status["pool_settings"] = _pool_settings()
        except Exception:
            status["pool_settings"] = None
        try:
            status["stratum"] = _stratum_status_for_algo(algo)
        except Exception:
            status["stratum"] = None

        return status
    except Exception as e:
        cached = _read_pool_cache(pool_id)
        if cached:
            status = dict(cached["status"])
            status.update(
                {
                    "cached": True,
                    "lastSeen": int(cached["t"]),
                    "error": str(e),
                }
            )
            status.setdefault("backend", "miningcore")
            status.setdefault("poolId", pool_id)
            status.setdefault("algo", algo)
            status.setdefault("workers", 0)
            status.setdefault("hashrate_ths", None)
            status.setdefault("total_blocks", None)
            status.setdefault("network_difficulty", None)
            status.setdefault("network_height", None)
            status.setdefault("best_difficulty_all", None)
            status.setdefault("best_difficulty_since_block", None)
            status.setdefault("best_difficulty_since_block_at", None)
            status.setdefault("best_share_all", status.get("best_difficulty_all"))
            status.setdefault("best_share_since_block", status.get("best_difficulty_since_block"))
            status.setdefault("best_share_since_block_at", status.get("best_difficulty_since_block_at"))
            status.setdefault("best_share_all_worker", None)
            status.setdefault("best_share_since_block_worker", None)
            status.setdefault("shares_10m", None)
            status.setdefault("shares_1h", None)
            status.setdefault("last_share_at", None)
            status.setdefault("eta_seconds", None)
            status.setdefault("hashrate_ths_best_effort", None)
            status.setdefault("hashrate_ths_live_10m", None)
            status.setdefault("hashrates_ths", {})
            try:
                status["pool_settings"] = _pool_settings()
            except Exception:
                status["pool_settings"] = None
            try:
                status["stratum"] = _stratum_status_for_algo(algo)
            except Exception:
                status["stratum"] = None
            return status

        status = {
            "backend": "miningcore",
            "poolId": pool_id,
            "algo": algo,
            "workers": 0,
            "hashrate_ths": None,
            "total_blocks": None,
            "network_difficulty": None,
            "network_height": None,
            "best_difficulty_all": None,
            "best_difficulty_since_block": None,
            "best_difficulty_since_block_at": None,
            "best_share_all": None,
            "best_share_since_block": None,
            "best_share_since_block_at": None,
            "best_share_all_worker": None,
            "best_share_since_block_worker": None,
            "shares_10m": None,
            "shares_1h": None,
            "last_share_at": None,
            "eta_seconds": None,
            "hashrate_ths_best_effort": None,
            "hashrate_ths_live_10m": None,
            "hashrates_ths": {},
            "cached": False,
            "lastSeen": int(time.time()),
            "error": str(e),
        }
        try:
            status["pool_settings"] = _pool_settings()
        except Exception:
            status["pool_settings"] = None
        try:
            status["stratum"] = _stratum_status_for_algo(algo)
        except Exception:
            status["stratum"] = None
        return status


def _pool_miners(pool_id: str):
    db_rows = _pool_workers_from_db(pool_id)
    # Treat an empty list as a valid DB result. Falling back to Miningcore's /miners
    # endpoint can yield HTTP 500 on older/partially-migrated databases and causes
    # the UI to show a hard 503.
    if isinstance(db_rows, list):
        # Solo pool UI: only show rows for the currently configured payout
        # address when available (avoids showing old miners from previous
        # configs).
        try:
            st = _read_json_file(POOL_SETTINGS_STATE_PATH)
            payout = str(st.get("payoutAddress") or "").strip() if isinstance(st, dict) else ""
        except Exception:
            payout = ""
        if payout and payout != POOL_PLACEHOLDER_PAYOUT_ADDRESS:
            filtered = [m for m in db_rows if str(m.get("miner") or "").strip() == payout]
            if filtered:
                return filtered
        return db_rows

    miners = None
    try:
        miners = _miningcore_get_any(f"/api/pools/{pool_id}/miners", timeout_s=6)
    except Exception:
        miners = None

    # Miningcore may return HTTP 500 on some schemas; try reading the pool's exported
    # workers list (when present) instead of hard-failing the UI.
    if miners is None:
        try:
            miners = _parse_pool_workers(_read_pool_workers_raw())
        except Exception:
            miners = []

    if isinstance(miners, dict):
        for k in ("miners", "Miners", "data", "Data", "result", "Result", "items", "Items"):
            v = miners.get(k)
            if isinstance(v, list):
                miners = v
                break
    if not isinstance(miners, list):
        return []

    out = []
    for item in miners:
        if not isinstance(item, dict):
            continue

        miner = str(
            item.get("miner")
            or item.get("Miner")
            or item.get("address")
            or item.get("Address")
            or item.get("user")
            or item.get("User")
            or item.get("username")
            or item.get("Username")
            or ""
        )
        worker = item.get("worker") or item.get("Worker") or None
        if isinstance(worker, str) and worker.strip() == "":
            worker = None

        hashrate_hs = item.get("hashrate") if "hashrate" in item else item.get("Hashrate")
        if hashrate_hs is None:
            hashrate_hs = item.get("hashrate_hs") if "hashrate_hs" in item else item.get("hashrateHs")
        try:
            hashrate_hs_f = float(hashrate_hs)
        except Exception:
            hashrate_hs_f = None
        if hashrate_hs_f is not None and not math.isfinite(hashrate_hs_f):
            hashrate_hs_f = None

        hashrate_ths = None
        if hashrate_hs_f is not None:
            hashrate_ths = hashrate_hs_f / 1e12

        out.append(
            {
                "miner": miner,
                "worker": worker,
                "hashrate_hs": hashrate_hs_f,
                "hashrate_ths": hashrate_ths,
                "lastShare": item.get("lastShare")
                or item.get("LastShare")
                or item.get("last_share_at")
                or item.get("last_share")
                or None,
                "sharesPerSecond": item.get("sharesPerSecond") or item.get("SharesPerSecond") or None,
            }
        )

    return out


def _read_pool_status_raw():
    def iter_candidates(filename: str):
        bases = [
            Path("/data/pool/www/pool"),
            Path("/data/pool/www"),
        ]
        seen = set()
        for base in bases:
            if not isinstance(base, Path):
                continue
            for p in [
                base / filename,
                base.parent / filename,
                base / "pool" / filename,
                base.parent / "pool" / filename,
            ]:
                if p in seen:
                    continue
                seen.add(p)
                yield p
            try:
                for p in base.glob(f"*/{filename}"):
                    if p in seen:
                        continue
                    seen.add(p)
                    yield p
            except Exception:
                continue

    entries = []
    for path in iter_candidates("pool.status"):
        if not (path.exists() and path.is_file()):
            continue
        try:
            entries.append((float(path.stat().st_mtime), path.read_text(encoding="utf-8", errors="replace").strip()))
        except Exception:
            continue

    if not entries:
        return ""

    non_empty = [e for e in entries if e[1]]
    if non_empty:
        return max(non_empty, key=lambda x: x[0])[1]
    return max(entries, key=lambda x: x[0])[1]

def _read_pool_workers_raw():
    def iter_candidates(filename: str):
        bases = [
            Path("/data/pool/www/pool"),
            Path("/data/pool/www"),
        ]
        seen = set()
        for base in bases:
            if not isinstance(base, Path):
                continue
            for p in [
                base / filename,
                base.parent / filename,
                base / "pool" / filename,
                base.parent / "pool" / filename,
            ]:
                if p in seen:
                    continue
                seen.add(p)
                yield p
            try:
                for p in base.glob(f"*/{filename}"):
                    if p in seen:
                        continue
                    seen.add(p)
                    yield p
            except Exception:
                continue

    entries = []
    for path in iter_candidates("pool.workers"):
        if not (path.exists() and path.is_file()):
            continue
        try:
            entries.append((float(path.stat().st_mtime), path.read_text(encoding="utf-8", errors="replace").strip()))
        except Exception:
            continue

    if not entries:
        return ""

    non_empty = [e for e in entries if e[1]]
    if non_empty:
        return max(non_empty, key=lambda x: x[0])[1]
    return max(entries, key=lambda x: x[0])[1]


def _parse_pool_status(raw: str):
    if not raw:
        return {"workers": 0, "hashrate_ths": None, "best_share": None}

    def to_int(value):
        try:
            return int(str(value).strip())
        except Exception:
            return 0

    def to_hashrate_ths(value):
        if value is None:
            return None
        if isinstance(value, (int, float)):
            try:
                return float(value)
            except Exception:
                return None

        s = str(value).strip()
        if not s:
            return None
        s = s.replace(",", "")
        # Extract leading float (supports scientific notation).
        m = re.match(r"^\s*([0-9]+(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?)", s)
        if not m:
            return None
        try:
            n = float(m.group(1))
        except Exception:
            return None

        rest = s[m.end() :].strip().replace("/", " ")
        # Find unit token like H/KH/MH/GH/TH/PH/EH, but also handle ckpool's
        # shorthand like "78.6G" / "8.06T" (no "H").
        unit = ""
        unit_match = re.search(r"(?i)\b([kmgtep]?h)\b", rest)
        if unit_match:
            unit = unit_match.group(1).lower().strip()
        else:
            shorthand = re.search(r"(?i)\b([kmgtep])\b", rest)
            if shorthand:
                unit = f"{shorthand.group(1).lower()}h"
            elif re.search(r"(?i)\bh\b", rest):
                unit = "h"

        # No unit: assume TH/s (historical behavior of this app).
        if not unit:
            return n

        scale_to_ths = {
            "h": 1e-12,
            "kh": 1e-9,
            "mh": 1e-6,
            "gh": 1e-3,
            "th": 1.0,
            "ph": 1e3,
            "eh": 1e6,
        }
        factor = scale_to_ths.get(unit)
        if factor is None:
            return None
        return n * factor

    def normalize(data: dict):
        if not isinstance(data, dict):
            return {"workers": 0, "hashrate_ths": None, "best_share": None}
        workers = (
            data.get("workers")
            or data.get("Workers")
            or data.get("Users")
            or data.get("users")
            or data.get("active_workers")
            or data.get("activeWorkers")
        )

        hashrates_raw = {
            "1m": data.get("hashrate1m"),
            "5m": data.get("hashrate5m"),
            "15m": data.get("hashrate15m"),
            "1h": data.get("hashrate1hr") or data.get("hashrate1h"),
            "6h": data.get("hashrate6hr") or data.get("hashrate6h"),
            "1d": data.get("hashrate1d"),
            "7d": data.get("hashrate7d"),
        }
        hashrates_ths = {}
        for k, v in hashrates_raw.items():
            if v is None or (isinstance(v, str) and not v.strip()):
                continue
            hashrates_ths[k] = to_hashrate_ths(v)

        hashrate = (
            data.get("hashrate_ths")
            or data.get("hashrateThs")
            or data.get("hashrate")
            or data.get("Hashrate")
            or data.get("rate")
        )
        if hashrate is None:
            for k in ["1m", "5m", "15m", "1h", "6h", "1d", "7d"]:
                if k in hashrates_raw and hashrates_raw[k] is not None:
                    hashrate = hashrates_raw[k]
                    break

        best_share = data.get("bestshare") or data.get("best_share") or data.get("bestShare") or data.get("best")
        return {
            "workers": to_int(workers),
            "hashrate_ths": to_hashrate_ths(hashrate),
            "best_share": best_share,
            "hashrates_ths": hashrates_ths or None,
        }

    def merge_json_objects(text: str) -> dict | None:
        merged = {}
        found = False
        for line in text.splitlines():
            line = line.strip()
            if not line:
                continue
            if not (line.startswith("{") and line.endswith("}")):
                continue
            try:
                obj = json.loads(line)
            except Exception:
                continue
            if isinstance(obj, dict):
                merged.update(obj)
                found = True
        return merged if found else None

    merged = merge_json_objects(raw)
    if merged is not None:
        return normalize(merged)

    # Prefer JSON (ckpool often writes JSON, but can include extra log noise).
    try:
        return normalize(_extract_json_obj(raw))
    except Exception:
        try:
            start = raw.find("{")
            if start != -1:
                return normalize(_extract_json_obj(raw[start:]))
        except Exception:
            pass

    # Fallback: parse key/value lines.
    data = {}
    for line in raw.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if "=" in line:
            key, val = line.split("=", 1)
        elif ":" in line:
            key, val = line.split(":", 1)
        else:
            continue
        data[key.strip()] = val.strip()

    return normalize(data)

def _parse_pool_workers(raw: str):
    if not raw:
        return []

    # Best case: JSON list or object
    try:
        data = json.loads(raw)
        if isinstance(data, list):
            return data
        if isinstance(data, dict):
            # Some formats store under a key
            for key in ["workers", "data", "result"]:
                if isinstance(data.get(key), list):
                    return data[key]
            # Or a dict keyed by worker
            if all(isinstance(v, dict) for v in data.values()):
                out = []
                for k, v in data.items():
                    item = dict(v)
                    item.setdefault("worker", k)
                    out.append(item)
                return out
    except Exception:
        pass

    # Fallback: parse lines "worker ... lastshare ..."
    out = []
    for line in raw.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = [p for p in line.replace("\t", " ").split(" ") if p]
        if not parts:
            continue
        out.append({"worker": parts[0], "raw": line})
    return out


def _support_ticket_payload(*, subject: str, message: str, email: str | None):
    diagnostics = {}
    try:
        node = _node_status()
        diagnostics["node"] = {
            "chain": node.get("chain"),
            "blocks": node.get("blocks"),
            "headers": node.get("headers"),
            "progress": node.get("verificationprogress"),
            "connections": node.get("connections"),
            "subversion": node.get("subversion"),
            "mempool_bytes": node.get("mempool_bytes"),
        }
    except Exception as e:
        diagnostics["node_error"] = str(e)

    try:
        pool_id = _pool_id_for_algo("sha256")
        pool = _pool_status(pool_id, algo="sha256")
        diagnostics["pool"] = {
            "workers": pool.get("workers"),
            "hashrate_ths": pool.get("hashrate_ths"),
            "best_difficulty_since_block": pool.get("best_difficulty_since_block"),
            "best_difficulty_all": pool.get("best_difficulty_all"),
        }
    except Exception as e:
        diagnostics["pool_error"] = str(e)

    try:
        diagnostics["pool_settings"] = _pool_settings()
    except Exception:
        pass

    try:
        diagnostics["boot_repair"] = _read_boot_repair()
    except Exception:
        pass

    payload = _support_payload_base()
    payload.update(
        {
            "type": "support_ticket",
            "subject": subject,
            "message": message,
            "email": email or None,
            "diagnostics": diagnostics,
        }
    )
    return payload


def _now_ms():
    return int(time.time() * 1000)


def _parse_iso_to_ms(value: str) -> int | None:
    s = str(value or "").strip()
    if not s:
        return None
    try:
        if s.endswith("Z"):
            s = s[:-1] + "+00:00"
        dt = datetime.fromisoformat(s)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return int(dt.timestamp() * 1000)
    except Exception:
        return None


def _maybe_int(value: object) -> int | None:
    try:
        return int(value)  # type: ignore[arg-type]
    except Exception:
        return None


def _trail_to_seconds(trail: str) -> int:
    trail = (trail or "").strip().lower()
    return {
        "30m": 30 * 60,
        "6h": 6 * 60 * 60,
        "12h": 12 * 60 * 60,
        "1d": 24 * 60 * 60,
        "3d": 3 * 24 * 60 * 60,
        "6d": 6 * 24 * 60 * 60,
        "7d": 7 * 24 * 60 * 60,
    }.get(trail, 30 * 60)


def _downsample(points: list[dict], max_points: int) -> list[dict]:
    if len(points) <= max_points:
        return points
    stride = (len(points) + max_points - 1) // max_points
    return points[::stride]


def _pool_series_from_minerstats(pool_id: str, trail: str, max_points: int = 1000) -> list[dict]:
    """
    Fallback series for charts when the local sampler is empty/stale.
    Uses Miningcore Postgres `minerstats` snapshots (low-frequency but reliable).
    """
    if pg8000 is None:
        return []
    # Use the same Postgres config logic as the rest of the app.
    # Some deployments rely on local trust auth and do not provide a password.
    pg = _pg_conf()
    if not pg:
        return []

    seconds = _trail_to_seconds(trail)
    cutoff = datetime.now(timezone.utc) - timedelta(seconds=seconds)

    try:
        conn = pg8000.connect(
            host=pg["host"],
            port=int(pg["port"]),
            user=pg["user"],
            password=pg.get("password") or None,
            database=pg["database"],
            timeout=3,
        )
    except Exception:
        return []

    try:
        cur = conn.cursor()
        cur.execute(
            """
            SELECT
              (extract(epoch from created) * 1000)::bigint AS t,
              (SUM(hashrate) / 1e12)::double precision AS hashrate_ths,
              COUNT(DISTINCT (miner || '.' || COALESCE(worker, '')))::int AS workers
            FROM minerstats
            WHERE poolid = %s AND created >= %s
            GROUP BY created
            ORDER BY created ASC
            """,
            (pool_id, cutoff),
        )
        rows = cur.fetchall() or []

        pts: list[dict] = []
        for r in rows:
            try:
                t = int(r[0])
            except Exception:
                continue
            try:
                hr = float(r[1]) if r[1] is not None else None
            except Exception:
                hr = None
            try:
                workers = int(r[2]) if r[2] is not None else 0
            except Exception:
                workers = 0
            pts.append({"t": t, "workers": workers, "hashrate_ths": hr})

        return _downsample(pts, max_points)
    except Exception:
        return []
    finally:
        try:
            conn.close()
        except Exception:
            pass


class PoolSeries:
    def __init__(self, path: Path):
        self._lock = threading.Lock()
        self._points: list[dict] = []
        self._path = path

    def load(self):
        cutoff_ms = _now_ms() - (MAX_RETENTION_S * 1000)
        points: list[dict] = []
        if self._path.exists():
            for line in self._path.read_text(encoding="utf-8", errors="replace").splitlines():
                line = line.strip()
                if not line:
                    continue
                try:
                    obj = json.loads(line)
                    t = int(obj.get("t") or 0)
                    # Drop obviously bogus debug/test points that can poison graphs and filters.
                    # DigiByte mainnet height is far above 1,000,000; anything below is not real.
                    try:
                        h = int(obj.get("network_height") or 0)
                    except Exception:
                        h = 0
                    if h and h < 1_000_000:
                        continue
                    if t >= cutoff_ms:
                        points.append(obj)
                except Exception:
                    continue

        points.sort(key=lambda p: p.get("t", 0))
        if len(points) > MAX_SERIES_POINTS:
            points = points[-MAX_SERIES_POINTS:]

        with self._lock:
            self._points = points

        # Rewrite the file if we dropped old points or it's missing.
        self._rewrite(points)

    def _rewrite(self, points: list[dict]):
        STATE_DIR.mkdir(parents=True, exist_ok=True)
        tmp = self._path.with_suffix(".tmp")
        tmp.write_text("\n".join(json.dumps(p, separators=(",", ":")) for p in points) + ("\n" if points else ""), encoding="utf-8")
        tmp.replace(self._path)

    def append(self, point: dict):
        cutoff_ms = _now_ms() - (MAX_RETENTION_S * 1000)
        with self._lock:
            self._points.append(point)
            self._points = [p for p in self._points if int(p.get("t") or 0) >= cutoff_ms]
            if len(self._points) > MAX_SERIES_POINTS:
                self._points = self._points[-MAX_SERIES_POINTS:]

            STATE_DIR.mkdir(parents=True, exist_ok=True)
            with self._path.open("a", encoding="utf-8") as f:
                f.write(json.dumps(point, separators=(",", ":")) + "\n")

            # Occasionally compact the file (simple heuristic).
            if self._path.stat().st_size > 10 * 1024 * 1024:
                self._rewrite(self._points)

    def query(self, trail: str, max_points: int = 1000):
        trail = (trail or "").strip().lower()
        seconds = {
            "30m": 30 * 60,
            "6h": 6 * 60 * 60,
            "12h": 12 * 60 * 60,
            "1d": 24 * 60 * 60,
            "3d": 3 * 24 * 60 * 60,
            "6d": 6 * 24 * 60 * 60,
            "7d": 7 * 24 * 60 * 60,
        }.get(trail, 30 * 60)

        cutoff_ms = _now_ms() - (seconds * 1000)
        with self._lock:
            pts = [p for p in self._points if int(p.get("t") or 0) >= cutoff_ms]

        if len(pts) <= max_points:
            return pts

        stride = (len(pts) + max_points - 1) // max_points
        return pts[::stride]


POOL_SERIES_BY_POOL: dict[str, PoolSeries] = {}
POOL_LAST_REQUEST_S: dict[str, float] = {}
POOL_LAST_REQUEST_LOCK = threading.Lock()

_SERIES_LAST_APPEND_MS: dict[str, int] = {}
_SERIES_LAST_APPEND_LOCK = threading.Lock()


def _maybe_append_pool_series(pool_id: str, status: dict):
    """
    Best-effort series writer that runs on-demand from API requests.

    We keep the background sampler thread, but on some installs it can stall or
    be restarted while the UI is active. Since the UI polls `/api/pool` anyway,
    opportunistically append one point per `SAMPLE_INTERVAL_S` to keep charts
    fresh without extra load.
    """
    try:
        now_ms = _now_ms()
        with _SERIES_LAST_APPEND_LOCK:
            last_ms = int(_SERIES_LAST_APPEND_MS.get(pool_id) or 0)
            if last_ms > 0 and (now_ms - last_ms) < (SAMPLE_INTERVAL_S * 1000):
                return
            _SERIES_LAST_APPEND_MS[pool_id] = now_ms

        def to_float(value):
            if value is None:
                return None
            try:
                v = float(value)
            except Exception:
                return None
            return v if math.isfinite(v) else None

        workers_i = _maybe_int(status.get("workers")) or 0
        hashrate_f = to_float(status.get("hashrate_ths"))
        netdiff_f = to_float(status.get("network_difficulty"))
        netheight_i = _maybe_int(status.get("network_height"))

        _pool_series(pool_id).append(
            {
                "t": now_ms,
                "workers": workers_i,
                "hashrate_ths": hashrate_f,
                "network_difficulty": netdiff_f,
                "network_height": netheight_i,
            }
        )
    except Exception:
        try:
            import traceback

            print(f"[series] append failed for {pool_id}: {traceback.format_exc()}")
        except Exception:
            pass
        return


def _pool_series(pool_id: str) -> PoolSeries:
    series = POOL_SERIES_BY_POOL.get(pool_id)
    if series is None:
        series = PoolSeries(_pool_series_path(pool_id))
        POOL_SERIES_BY_POOL[pool_id] = series
    return series


BEST_DIFFICULTY_TTL_S = int(os.getenv("BEST_DIFFICULTY_TTL_S", "15"))
BEST_DIFFICULTY_CACHE: dict[str, dict] = {}
BEST_DIFFICULTY_CACHE_LOCK = threading.Lock()

# Difficulty-1 target used by DigiByte SHA256d (same baseline as Bitcoin).
_SHA256D_DIFF1_TARGET = int("00000000FFFF0000000000000000000000000000000000000000000000000000", 16)


def _iso_z(dt: datetime) -> str:
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    return dt.astimezone(timezone.utc).isoformat().replace("+00:00", "Z")


def _sha256d_difficulty_hit_from_pow_hash(pow_hash_hex: str | None) -> float | None:
    try:
        h = str(pow_hash_hex or "").strip().lower()
        if not re.match(r"^[0-9a-f]{64}$", h):
            return None
        n = int(h, 16)
        if n <= 0:
            return None
        return float(_SHA256D_DIFF1_TARGET / n)
    except Exception:
        return None


def _miningcore_postgres_cfg() -> dict | None:
    try:
        conf = _read_miningcore_conf()
        persistence = conf.get("persistence") if isinstance(conf, dict) else None
        postgres = persistence.get("postgres") if isinstance(persistence, dict) else None
        postgres = postgres if isinstance(postgres, dict) else None
        if not postgres:
            return None
        host = str(postgres.get("host") or "").strip()
        user = str(postgres.get("user") or "").strip()
        password = str(postgres.get("password") or "").strip()
        database = str(postgres.get("database") or "").strip()
        port = _to_int(postgres.get("port"), 5432)
        if not host or not user or not database:
            return None
        return {"host": host, "port": port, "user": user, "password": password, "database": database}
    except Exception:
        return None


def _pool_best_difficulties(pool_id: str) -> dict:
    now = time.time()
    with BEST_DIFFICULTY_CACHE_LOCK:
        cached = BEST_DIFFICULTY_CACHE.get(pool_id)
        if cached and (now - float(cached.get("t") or 0.0)) <= BEST_DIFFICULTY_TTL_S:
            data = cached.get("data")
            return dict(data) if isinstance(data, dict) else {}

    if pg8000 is None:
        return {}

    cfg = _pg_conf()
    if not cfg:
        return {}

    best_diff_all = None
    best_diff_since = None
    best_share_all = None
    best_share_since = None
    best_share_all_worker = None
    best_share_since_worker = None
    last_block_created = None
    since_at = None
    last_solved_state_dt = None
    best_block_hit_all = None

    def _as_naive_utc(dt: datetime) -> datetime:
        if dt.tzinfo is not None:
            dt = dt.astimezone(timezone.utc).replace(tzinfo=None)
        return dt

    reset_at_s = None
    try:
        st = _read_json_file(BESTSHARE_RESET_PATH)
        if isinstance(st, dict):
            v = st.get(pool_id)
            try:
                reset_at_s = int(float(v))
            except Exception:
                reset_at_s = None
    except Exception:
        reset_at_s = None

    reset_at_dt = None
    if reset_at_s and reset_at_s > 0:
        try:
            reset_at_dt = datetime.utcfromtimestamp(reset_at_s)
        except Exception:
            reset_at_dt = None

    # Prefer the local backscan-derived "solved blocks" timeline over Miningcore's blocks table.
    # Miningcore can fail to persist solved blocks depending on DB/schema drift, while our backscan
    # state is built directly from node RPC.
    try:
        algo_tag = None
        pid = str(pool_id or "").strip().lower()
        if "sha256" in pid:
            algo_tag = "sha256"
        elif "scrypt" in pid:
            algo_tag = "scrypt"

        if algo_tag:
            st = _read_json_file(BLOCKS_STATE_PATH)
            evs = st.get("events") if isinstance(st, dict) else None
            if isinstance(evs, list):
                for ev in evs:
                    if not isinstance(ev, dict):
                        continue
                    if str(ev.get("algo") or "").strip().lower() != algo_tag:
                        continue
                    try:
                        status_i = int(ev.get("status") or 0)
                    except Exception:
                        status_i = 0
                    if status_i <= 0:
                        continue
                    try:
                        t_i = int(ev.get("t") or 0)
                    except Exception:
                        t_i = 0
                    if t_i > 0:
                        dt = datetime.utcfromtimestamp(t_i)
                        if last_solved_state_dt is None or dt > last_solved_state_dt:
                            last_solved_state_dt = dt
                    if algo_tag == "sha256":
                        hit = _sha256d_difficulty_hit_from_pow_hash(ev.get("hash"))
                        if hit is None:
                            continue
                        if best_block_hit_all is None or hit > best_block_hit_all:
                            best_block_hit_all = hit
    except Exception:
        last_solved_state_dt = None
        best_block_hit_all = None

    try:
        conn = pg8000.connect(
            user=cfg["user"],
            password=cfg.get("password") or None,
            host=cfg["host"],
            port=int(cfg["port"]),
            database=cfg["database"],
            timeout=3,
        )
        try:
            cur = conn.cursor()
            cur.execute("SELECT MAX(difficulty) FROM shares WHERE poolid=%s", (pool_id,))
            row = cur.fetchone()
            best_diff_all = float(row[0]) if row and row[0] is not None else None

            try:
                cur.execute("SELECT MAX(actualdifficulty) FROM shares WHERE poolid=%s", (pool_id,))
                row = cur.fetchone()
                best_share_all = float(row[0]) if row and row[0] is not None else None
            except Exception:
                best_share_all = None

            if best_share_all is not None:
                try:
                    cur.execute(
                        "SELECT COALESCE(NULLIF(worker,''), miner) FROM shares WHERE poolid=%s AND actualdifficulty=%s ORDER BY created DESC LIMIT 1",
                        (pool_id, best_share_all),
                    )
                    row = cur.fetchone()
                    best_share_all_worker = str(row[0]) if row and row[0] is not None else None
                except Exception:
                    best_share_all_worker = None

            cur.execute("SELECT MAX(created) FROM blocks WHERE poolid=%s", (pool_id,))
            row = cur.fetchone()
            last_block_created = row[0] if row and row[0] is not None else None
            if isinstance(last_block_created, datetime):
                last_block_created = _as_naive_utc(last_block_created)

            since_at = last_block_created
            if isinstance(last_solved_state_dt, datetime):
                if since_at is None or last_solved_state_dt > since_at:
                    since_at = last_solved_state_dt
            if reset_at_dt is not None and (since_at is None or since_at < reset_at_dt):
                since_at = reset_at_dt

            if since_at is not None:
                cur.execute(
                    "SELECT MAX(difficulty) FROM shares WHERE poolid=%s AND created > %s",
                    (pool_id, since_at),
                )
                row = cur.fetchone()
                best_diff_since = float(row[0]) if row and row[0] is not None else None

                try:
                    cur.execute(
                        "SELECT MAX(actualdifficulty) FROM shares WHERE poolid=%s AND created > %s",
                        (pool_id, since_at),
                    )
                    row = cur.fetchone()
                    best_share_since = float(row[0]) if row and row[0] is not None else None
                except Exception:
                    best_share_since = None

                if best_share_since is not None:
                    try:
                        cur.execute(
                            "SELECT COALESCE(NULLIF(worker,''), miner) FROM shares WHERE poolid=%s AND created > %s AND actualdifficulty=%s ORDER BY created DESC LIMIT 1",
                            (pool_id, since_at, best_share_since),
                        )
                        row = cur.fetchone()
                        best_share_since_worker = str(row[0]) if row and row[0] is not None else None
                    except Exception:
                        best_share_since_worker = None
            else:
                # If we have never found a block and the user has not reset the tracker, show the all-time best.
                # If a manual reset is present, keep "since block" empty until new shares arrive after the reset point.
                if reset_at_dt is None:
                    best_diff_since = best_diff_all
                    best_share_since = best_share_all
                    best_share_since_worker = best_share_all_worker

            if best_share_all is None:
                best_share_all = best_diff_all
            if best_share_since is None:
                best_share_since = best_diff_since

            # Ensure solved blocks contribute to all-time best share even if the winning share is not
            # present in the shares table (depends on Miningcore persistence + schema).
            if best_block_hit_all is not None:
                try:
                    if best_share_all is None or float(best_block_hit_all) > float(best_share_all):
                        best_share_all = float(best_block_hit_all)
                        # Worker attribution for the winning block is not reliable when the share row isn't present.
                        best_share_all_worker = None
                except Exception:
                    pass
        finally:
            try:
                conn.close()
            except Exception:
                pass
    except Exception:
        out = {
            "best_difficulty_all": None,
            "best_difficulty_since_block": None,
            "best_difficulty_since_block_at": None,
            "best_share_all": None,
            "best_share_since_block": None,
            "best_share_since_block_at": None,
            "best_share_all_worker": None,
            "best_share_since_block_worker": None,
        }
        with BEST_DIFFICULTY_CACHE_LOCK:
            BEST_DIFFICULTY_CACHE[pool_id] = {"t": now, "data": out}
        return dict(out)

    out = {
        "best_difficulty_all": best_diff_all,
        "best_difficulty_since_block": best_diff_since,
        "best_difficulty_since_block_at": _iso_z(since_at) if isinstance(since_at, datetime) else None,
        "best_share_all": best_share_all,
        "best_share_since_block": best_share_since,
        "best_share_since_block_at": _iso_z(since_at) if isinstance(since_at, datetime) else None,
        "best_share_all_worker": best_share_all_worker,
        "best_share_since_block_worker": best_share_since_worker,
    }

    with BEST_DIFFICULTY_CACHE_LOCK:
        BEST_DIFFICULTY_CACHE[pool_id] = {"t": now, "data": out}
    return out


def _pool_share_health(pool_id: str) -> dict:
    if pg8000 is None:
        return {}
    cfg = _pg_conf()
    if not cfg:
        return {}

    cutoff_10m = datetime.now(timezone.utc) - timedelta(minutes=10)
    cutoff_1h = datetime.now(timezone.utc) - timedelta(hours=1)

    try:
        conn = pg8000.connect(
            user=cfg["user"],
            password=cfg.get("password") or None,
            host=cfg["host"],
            port=int(cfg["port"]),
            database=cfg["database"],
            timeout=3,
        )
        try:
            cur = conn.cursor()
            cur.execute(
                "SELECT COUNT(*), COALESCE(SUM(difficulty), 0), MIN(created), MAX(created) FROM shares WHERE poolid=%s AND created >= %s",
                (pool_id, cutoff_10m),
            )
            row = cur.fetchone()
            shares_10m = int(row[0]) if row and row[0] is not None else 0
            sumdiff_10m = float(row[1]) if row and row[1] is not None else 0.0
            first_share_10m = row[2] if row and len(row) > 2 else None
            last_share_10m = row[3] if row and len(row) > 3 else None

            cur.execute(
                "SELECT COUNT(*) FROM shares WHERE poolid=%s AND created >= %s",
                (pool_id, cutoff_1h),
            )
            row = cur.fetchone()
            shares_1h = int(row[0]) if row and row[0] is not None else 0

            cur.execute(
                "SELECT MAX(created) FROM shares WHERE poolid=%s",
                (pool_id,),
            )
            row = cur.fetchone()
            last_share_created = row[0] if row and row[0] is not None else None
        finally:
            try:
                conn.close()
            except Exception:
                pass
    except Exception:
        return {}

    last_share_iso = _iso_z(last_share_created) if isinstance(last_share_created, datetime) else None
    # Estimate pool hashrate from accepted shares over the last 10 minutes:
    # H/s approx sum(share_difficulty) * 2^32 / elapsed_seconds (capped to 10m, floored to 60s)
    hashrate_hs_10m = None
    try:
        if sumdiff_10m and sumdiff_10m > 0:
            window_s = 10 * 60
            span_s = None
            if isinstance(first_share_10m, datetime) and isinstance(last_share_10m, datetime):
                try:
                    span_s = (last_share_10m - first_share_10m).total_seconds()
                except Exception:
                    span_s = None
            if span_s is None or not math.isfinite(float(span_s)) or span_s <= 0:
                span_s = window_s
            span_s = max(60.0, min(float(span_s), float(window_s)))
            hashrate_hs_10m = (sumdiff_10m * (2**32)) / span_s
    except Exception:
        hashrate_hs_10m = None

    return {
        "shares_10m": shares_10m,
        "shares_1h": shares_1h,
        "last_share_at": last_share_iso,
        "hashrate_hs_10m": hashrate_hs_10m,
    }


def _series_sampler(stop_event: threading.Event):
    while not stop_event.is_set():
        ids = _pool_ids()
        for algo, pool_id in ids.items():
            # Avoid hammering Miningcore for secondary pools during node warmup.
            # Miningcore can return 500s for pools that haven't fully initialized yet.
            if algo != "sha256":
                with POOL_LAST_REQUEST_LOCK:
                    last = float(POOL_LAST_REQUEST_S.get(pool_id) or 0.0)
                if last <= 0 or (time.time() - last) > 120:
                    continue
            try:
                status = _pool_status(pool_id, algo=algo)
                workers = status.get("workers")
                try:
                    workers_i = int(workers)
                except Exception:
                    workers_i = 0

                def to_float(value):
                    if value is None:
                        return None
                    try:
                        return float(value)
                    except Exception:
                        return None

                hashrate_f = to_float(status.get("hashrate_ths"))
                netdiff_f = to_float(status.get("network_difficulty"))
                netheight_i = _maybe_int(status.get("network_height"))

                _pool_series(pool_id).append(
                    {
                        "t": _now_ms(),
                        "workers": workers_i,
                        "hashrate_ths": hashrate_f,
                        "network_difficulty": netdiff_f,
                        "network_height": netheight_i,
                    }
                )
            except Exception:
                try:
                    import traceback

                    print(f"[series] sampler failed for {pool_id}: {traceback.format_exc()}")
                except Exception:
                    pass
                pass

        # Opportunistically backscan for blocks mined by this pool's payout address.
        stop_event.wait(SAMPLE_INTERVAL_S)


def _backscan_worker(stop_event: threading.Event):
    while not stop_event.is_set():
        try:
            _maybe_backscan_blocks(max_blocks=BACKSCAN_DEFAULT_MAX_BLOCKS)
        except Exception:
            pass
        try:
            _maybe_detect_recent_wins(max_blocks=10)
        except Exception:
            pass
        stop_event.wait(0.5)


def _widget_sync():
    try:
        s = _node_status()
        progress = max(0.0, min(1.0, float(s["verificationprogress"])))
        pct = int(progress * 100)
        label = "In progress" if s["initialblockdownload"] else "Synchronized"
        return {
            "type": "text-with-progress",
            "title": "DGB sync",
            "text": f"{pct}%",
            "progressLabel": label,
            "progress": progress,
        }
    except Exception:
        return {
            "type": "text-with-progress",
            "title": "DGB sync",
            "text": "-",
            "progressLabel": "Unavailable",
            "progress": 0,
        }


def _widget_pool():
    pool_id = _pool_id_for_algo("sha256")
    p = _pool_status(pool_id, algo="sha256")
    best = p.get("best_share_since_block") or p.get("best_share_all") or p.get("best_difficulty_since_block") or p.get("best_difficulty_all")
    return {
        "type": "three-stats",
        "items": [
            {"title": "Hashrate", "text": str(p.get("hashrate_ths") or "-"), "subtext": "TH/s"},
            {"title": "Workers", "text": str(p.get("workers") or 0)},
            {"title": "Best share", "text": str(best or "-"), "subtext": ""},
        ],
    }


class Handler(BaseHTTPRequestHandler):
    server_version = f"{APP_ID}/{APP_VERSION}"

    def _send(self, status: int, body: bytes, content_type: str):
        self.send_response(status)
        self.send_header("content-type", content_type)
        self.send_header("content-length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        raw_path = self.path
        path = urlsplit(self.path).path
        if self.path == "/api/about":
            return self._send(*_json(_about()))

        if path == "/api/debug/db":
            return self._send(*_json(_db_diag()))

        if self.path == "/api/settings":
            return self._send(*_json(_current_settings()))

        if self.path == "/api/pool/settings":
            return self._send(*_json(_pool_settings()))

        if self.path == "/api/support/status":
            return self._send(
                *_json(
                    {
                        "ticketEnabled": bool(SUPPORT_TICKET_URL),
                        "checkinEnabled": bool(SUPPORT_CHECKIN_URL),
                    }
                )
            )

        if self.path == "/api/node":
            reindex_requested = NODE_REINDEX_FLAG_PATH.exists()
            reindex_required = _detect_reindex_required()
            cached = _read_node_cache()
            if cached and (int(time.time()) - int(cached["t"])) <= 4:
                payload = dict(cached["status"])
                payload.update(
                    {
                        "cached": True,
                        "lastSeen": int(cached["t"]),
                        "reindexRequested": reindex_requested,
                        "reindexRequired": reindex_required,
                    }
                )
                return self._send(*_json(payload))

            acquired = NODE_STATUS_LOCK.acquire(blocking=False)
            if not acquired:
                if cached:
                    payload = dict(cached["status"])
                    payload.update(
                        {
                            "cached": True,
                            "lastSeen": int(cached["t"]),
                            "error": "busy",
                            "reindexRequested": reindex_requested,
                            "reindexRequired": reindex_required,
                        }
                    )
                    return self._send(*_json(payload))
                return self._send(*_json({"error": "busy"}, status=503))

            try:
                s = _node_status()
                payload = dict(s)
                payload.update(
                    {
                        "cached": False,
                        "lastSeen": int(time.time()),
                        "reindexRequested": reindex_requested,
                        "reindexRequired": False,
                    }
                )
                return self._send(*_json(payload))
            except Exception as e:
                if isinstance(e, RpcError) and e.code == -28:
                    payload = {
                        "cached": False,
                        "lastSeen": int(time.time()),
                        "warmup": True,
                        "warmupMessage": e.message,
                        "reindexRequested": reindex_requested,
                        "reindexRequired": reindex_required,
                    }
                    return self._send(*_json(payload))
                cached = cached or _read_node_cache()
                if cached:
                    payload = dict(cached["status"])
                    payload.update(
                        {
                            "cached": True,
                            "lastSeen": int(cached["t"]),
                            "error": str(e),
                            "warmup": isinstance(e, RpcError) and e.code == -28,
                            "warmupMessage": e.message if isinstance(e, RpcError) and e.code == -28 else None,
                            "reindexRequested": reindex_requested,
                            "reindexRequired": reindex_required,
                        }
                    )
                    return self._send(*_json(payload))
                return self._send(
                    *_json(
                        {
                            "error": str(e),
                            "reindexRequested": reindex_requested,
                            "reindexRequired": reindex_required,
                        },
                        status=503,
                    )
                )
            finally:
                if acquired:
                    try:
                        NODE_STATUS_LOCK.release()
                    except Exception:
                        pass

        if path == "/api/pool":
            algo = _algo_from_query(raw_path)
            pool_id = _pool_id_for_algo(algo)
            with POOL_LAST_REQUEST_LOCK:
                POOL_LAST_REQUEST_S[pool_id] = time.time()
            status = _pool_status(pool_id, algo=algo)
            _maybe_append_pool_series(pool_id, status)
            return self._send(*_json(status))

        if path == "/api/pool/miners" or path == "/api/pool/workers":
            algo = _algo_from_query(raw_path)
            pool_id = _pool_id_for_algo(algo)
            with POOL_LAST_REQUEST_LOCK:
                POOL_LAST_REQUEST_S[pool_id] = time.time()
            try:
                miners = _pool_miners(pool_id)
                return self._send(*_json({"poolId": pool_id, "algo": algo, "miners": miners}))
            except Exception as e:
                return self._send(*_json({"poolId": pool_id, "algo": algo, "miners": [], "error": str(e)}, status=503))

        if path == "/api/backscan":
            blocks_state = _read_json_file(BLOCKS_STATE_PATH)
            scan = blocks_state.get("backscan") if isinstance(blocks_state.get("backscan"), dict) else {}
            if isinstance(scan, dict):
                scan = dict(scan)
                scan["pct"] = _backscan_pct(scan)
            return self._send(*_json({"backscan": scan}))

        if path == "/api/blocks":
            try:
                query = ""
                if "?" in raw_path:
                    _, query = raw_path.split("?", 1)
                algo = None
                page = 0
                page_size = 25
                for part in query.split("&"):
                    if part.startswith("algo="):
                        algo = part.split("=", 1)[1].strip().lower() or None
                    if part.startswith("page="):
                        try:
                            page = int(part.split("=", 1)[1])
                        except Exception:
                            page = 0
                    if part.startswith("pageSize="):
                        try:
                            page_size = int(part.split("=", 1)[1])
                        except Exception:
                            page_size = 25
                page = max(0, page)
                page_size = max(1, min(100, page_size))

                pool_id = _pool_id_for_algo(algo)
                with POOL_LAST_REQUEST_LOCK:
                    POOL_LAST_REQUEST_S[pool_id] = time.time()

                blocks_state = _read_json_file(BLOCKS_STATE_PATH)
                backscan = blocks_state.get("backscan") if isinstance(blocks_state.get("backscan"), dict) else {}
                backscan_events = blocks_state.get("events") if isinstance(blocks_state.get("events"), list) else []

                blocks: list[dict] = []
                # Prefer DB-backed block history when available (local Miningcore instance).
                try:
                    db_rows = _pool_blocks_from_db(pool_id, limit=page_size, offset=(page * page_size))
                    if isinstance(db_rows, list):
                        blocks = db_rows
                except Exception:
                    blocks = []

                # Fall back to Miningcore HTTP API if DB not available.
                if not blocks:
                    try:
                        data = _miningcore_get_any(
                            f"/api/pools/{pool_id}/blocks?page={page}&pageSize={page_size}", timeout_s=6
                        )
                        if isinstance(data, list):
                            blocks = data
                        elif isinstance(data, dict):
                            maybe = data.get("blocks") or data.get("Blocks")
                            if isinstance(maybe, list):
                                blocks = maybe
                    except Exception:
                        blocks = []

                events: list[dict] = []
                for b in blocks if isinstance(blocks, list) else []:
                    if not isinstance(b, dict):
                        continue
                    created = b.get("created") or b.get("Created") or b.get("createdAt") or b.get("CreatedAt")
                    height = b.get("blockHeight") or b.get("BlockHeight") or b.get("height") or b.get("Height")
                    st = b.get("status") if "status" in b else b.get("Status")
                    miner = b.get("miner") if "miner" in b else b.get("Miner")
                    worker = b.get("worker") if "worker" in b else b.get("Worker")
                    h = b.get("hash") if "hash" in b else b.get("Hash")
                    # DB-backed rows already use normalized keys (t/height/etc).
                    if created is None:
                        created = b.get("t")
                    if height is None:
                        height = b.get("height")
                    ev = {
                        "t": created,
                        "height": height,
                        "status": st,
                        "miner": miner,
                        "worker": worker,
                        "hash": str(h).lower() if isinstance(h, str) else h,
                        "source": "miningcore",
                    }
                    # Carry through optional enrichment fields when present.
                    if "coinbase_txid" in b:
                        ev["coinbase_txid"] = b.get("coinbase_txid")
                    if "explorer_tx" in b:
                        ev["explorer_tx"] = b.get("explorer_tx")
                    if "network_difficulty" in b:
                        ev["network_difficulty"] = b.get("network_difficulty")
                    ev["explorer_block"] = _dgb_explorer_block(ev.get("hash"))
                    events.append(ev)

                # Merge with backscan events, deduping by block hash.
                for e in backscan_events:
                    if not isinstance(e, dict):
                        continue
                    ev_algo = str(e.get("algo") or "").strip().lower() or None
                    if algo and ev_algo and ev_algo != str(algo).strip().lower():
                        continue
                    events.append(e)

                def _event_time_s(ev: dict) -> int:
                    v = ev.get("t")
                    if v is None:
                        return 0
                    try:
                        n = int(float(v))
                        # Heuristic: >1e12 means ms.
                        if n > 1_000_000_000_000:
                            return int(n / 1000)
                        return n
                    except Exception:
                        pass
                    try:
                        parsed = int(datetime.fromisoformat(str(v).replace("Z", "+00:00")).timestamp())
                        return parsed
                    except Exception:
                        return 0

                deduped: list[dict] = []
                seen_hash: set[str] = set()
                for e in sorted(events, key=_event_time_s, reverse=True):
                    if not isinstance(e, dict):
                        continue
                    h = e.get("hash")
                    hs = str(h or "").strip().lower()
                    if hs and hs in seen_hash:
                        continue
                    if hs:
                        seen_hash.add(hs)
                    deduped.append(e)

                return self._send(
                    *_json(
                        {
                            "poolId": pool_id,
                            "algo": algo,
                            "page": page,
                            "pageSize": page_size,
                            "events": deduped[: max(25, page_size)],
                            "backscan": backscan,
                        }
                    )
                )
            except Exception as e:
                return self._send(*_json({"error": str(e)}, status=503))

        if path.startswith("/api/timeseries/pool"):
            try:
                query = ""
                if "?" in raw_path:
                    _, query = raw_path.split("?", 1)
                trail = "30m"
                algo = None
                for part in query.split("&"):
                    if part.startswith("trail="):
                        trail = part.split("=", 1)[1]
                    if part.startswith("algo="):
                        algo = part.split("=", 1)[1].strip().lower() or None

                pool_id = _pool_id_for_algo(algo)
                pts = _pool_series(pool_id).query(trail=trail, max_points=1000)
                if not pts:
                    pts = _pool_series_from_minerstats(pool_id, trail=trail, max_points=1000)

                windows = [
                    ("hashrate_1m_ths", 60),
                    ("hashrate_5m_ths", 5 * 60),
                    ("hashrate_15m_ths", 15 * 60),
                    ("hashrate_1h_ths", 60 * 60),
                ]
                enriched = []
                for i, p in enumerate(pts):
                    obj = dict(p)
                    # Compute rolling averages ending at this point's timestamp.
                    try:
                        t = int(obj.get("t") or 0)
                    except Exception:
                        t = 0
                    for key, window_s in windows:
                        cutoff = t - (window_s * 1000)
                        vals = []
                        for q in pts[: i + 1]:
                            try:
                                qt = int(q.get("t") or 0)
                            except Exception:
                                continue
                            if qt < cutoff:
                                continue
                            # If there are no active workers at this sample, treat hashrate as 0.
                            # This prevents poisoned points (workers=0, hashrate>0) from keeping
                            # rolling windows and charts stuck high after disconnects.
                            try:
                                q_workers = int(q.get("workers") or 0)
                            except Exception:
                                q_workers = 0
                            if q_workers <= 0:
                                vals.append(0.0)
                                continue
                            try:
                                fv = float(q.get("hashrate_ths"))
                            except Exception:
                                continue
                            if math.isfinite(fv):
                                vals.append(fv)
                        obj[key] = (sum(vals) / len(vals)) if vals else None
                    enriched.append(obj)

                return self._send(*_json({"trail": trail, "algo": algo, "poolId": pool_id, "points": enriched}))
            except Exception as e:
                return self._send(*_json({"error": str(e)}, status=500))

        if path.startswith("/api/timeseries/difficulty"):
            try:
                query = ""
                if "?" in raw_path:
                    _, query = raw_path.split("?", 1)

                trail = "30m"
                algo = None
                for part in query.split("&"):
                    if part.startswith("trail="):
                        trail = part.split("=", 1)[1]
                    if part.startswith("algo="):
                        algo = part.split("=", 1)[1].strip().lower() or None

                pool_id = _pool_id_for_algo(algo)

                # Prefer our higher-frequency sampler series (updates every ~30s) so 30m views
                # don't go blank between Miningcore's hourly performance buckets.
                series = _pool_series(pool_id).query(trail=trail, max_points=2000)
                pts = []
                for p in series:
                    try:
                        t = int(p.get("t") or 0)
                    except Exception:
                        continue
                    v = p.get("network_difficulty")
                    try:
                        v = float(v) if v is not None else None
                    except Exception:
                        v = None
                    if v is None or not math.isfinite(v):
                        continue
                    # Guard against bogus historical points (e.g. debug lines)
                    # by requiring a plausible chain height when present.
                    try:
                        h = int(p.get("network_height") or 0)
                    except Exception:
                        h = 0
                    if h and h < 1_000_000:
                        continue
                    pts.append({"t": t, "difficulty": v})

                pts.sort(key=lambda p: p.get("t", 0))
                pts = _downsample(pts, 1000)
                if pts:
                    # Ensure at least 2 points so the UI renders a visible line (single-point
                    # series can look "blank" on a sparkline).
                    if len(pts) == 1:
                        pts.append({"t": _now_ms(), "difficulty": float(pts[0]["difficulty"])})
                    return self._send(*_json({"trail": trail, "algo": algo, "poolId": pool_id, "points": pts}))

                # Fallback: Miningcore hourly performance points.
                perf = _miningcore_get_json(f"/api/pools/{pool_id}/performance")
                rows = perf.get("stats") if isinstance(perf, dict) else None
                rows = rows if isinstance(rows, list) else []

                pts = []
                for r in rows:
                    if not isinstance(r, dict):
                        continue
                    t = _parse_iso_to_ms(r.get("created"))
                    if t is None:
                        continue
                    v = r.get("networkDifficulty")
                    try:
                        v = float(v) if v is not None else None
                    except Exception:
                        v = None
                    if v is None or not math.isfinite(v):
                        continue
                    pts.append({"t": int(t), "difficulty": v})

                pts.sort(key=lambda p: p.get("t", 0))
                cutoff_ms = _now_ms() - (_trail_to_seconds(trail) * 1000)
                pts_all = pts
                pts = [p for p in pts_all if int(p.get("t") or 0) >= cutoff_ms]
                # For short trails, Miningcore performance points are hourly. If we filtered
                # everything out, keep the most recent point so the chart doesn't go blank.
                if not pts and pts_all:
                    pts = [pts_all[-1]]
                pts = _downsample(pts, 1000)

                if pts and len(pts) == 1:
                    pts.append({"t": _now_ms(), "difficulty": float(pts[0]["difficulty"])})

                if not pts:
                    # Final fallback: return a flat line at current network difficulty so the UI
                    # shows something meaningful even when no time series exists yet.
                    try:
                        data = _miningcore_get_json(f"/api/pools/{pool_id}", timeout_s=6)
                        pool = _dget(data, "pool", "Pool", default={}) or {}
                        netstats = _dget(pool, "networkStats", "NetworkStats", default={}) or {}
                        v = _dget(netstats, "networkDifficulty", "NetworkDifficulty", default=None)
                        v = float(v) if v is not None else None
                        if v is not None and math.isfinite(v) and v > 0:
                            now_ms = _now_ms()
                            span_ms = _trail_to_seconds(trail) * 1000
                            pts = [
                                {"t": now_ms - span_ms, "difficulty": v},
                                {"t": now_ms, "difficulty": v},
                            ]
                    except Exception:
                        pts = []

                return self._send(*_json({"trail": trail, "algo": algo, "poolId": pool_id, "points": pts}))
            except Exception as e:
                return self._send(*_json({"error": str(e)}, status=500))

        if self.path == "/api/widget/sync":
            return self._send(*_json(_widget_sync()))

        if self.path == "/api/widget/pool":
            return self._send(*_json(_widget_pool()))

        status, body, ct = _read_static(path if path != "/" else "/index.html")
        return self._send(status, body, ct)

    def do_POST(self):
        length = int(self.headers.get("content-length", "0") or "0")
        raw = self.rfile.read(length) if length > 0 else b"{}"
        try:
            body = json.loads(raw.decode("utf-8"))
        except Exception:
            return self._send(*_json({"error": "invalid json"}, status=400))

        if self.path == "/api/settings":
            prev = _current_settings()
            network = str(body.get("network") or "").strip().lower()
            prune_raw = body.get("prune")
            txindex_raw = body.get("txindex")
            dbcache_raw = body.get("dbcacheMb")

            try:
                prune = int(prune_raw)
            except Exception:
                return self._send(*_json({"error": "invalid prune"}, status=400))

            if prune != 0 and prune < 550:
                return self._send(*_json({"error": "prune must be 0 or >= 550"}, status=400))

            txindex = 1 if bool(txindex_raw) else 0
            dbcache_mb = None
            if dbcache_raw is not None:
                try:
                    dbcache_mb = int(dbcache_raw)
                except Exception:
                    return self._send(*_json({"error": "invalid dbcacheMb"}, status=400))
                allowed = {4096, 6144, 8192}
                if dbcache_mb not in allowed:
                    return self._send(*_json({"error": "dbcacheMb must be one of 4096, 6144, 8192, or null"}, status=400))

            needs_node_conf_update = True
            try:
                needs_node_conf_update = (
                    str(prev.get("network") or "") != network
                    or int(prev.get("prune") or 0) != prune
                    or int(prev.get("txindex") or 0) != txindex
                )
            except Exception:
                needs_node_conf_update = True

            if needs_node_conf_update:
                try:
                    _update_node_conf(network=network, prune=prune, txindex=txindex)
                except Exception as e:
                    return self._send(*_json({"error": str(e)}, status=400))

            try:
                NODE_DBCACHE_MB_PATH.parent.mkdir(parents=True, exist_ok=True)
                if dbcache_mb is None:
                    NODE_DBCACHE_MB_PATH.write_text("auto\n", encoding="utf-8")
                else:
                    NODE_DBCACHE_MB_PATH.write_text(f"{dbcache_mb}\n", encoding="utf-8")
            except Exception:
                pass

            reindex_required = False
            try:
                prev_prune = int(prev.get("prune") or 0)
            except Exception:
                prev_prune = 0
            if prev_prune > 0 and prune == 0:
                reindex_required = True
                _request_reindex_chainstate()

            return self._send(*_json({"ok": True, "restartRequired": True, "reindexRequired": reindex_required}))

        if self.path == "/api/pool/settings":
            payout_address = str(body.get("payoutAddress") or "")
            mindiff = body.get("mindiff")
            startdiff = body.get("startdiff")
            maxdiff = body.get("maxdiff")
            try:
                settings = _update_pool_settings(
                    payout_address=payout_address,
                    mindiff=mindiff,
                    startdiff=startdiff,
                    maxdiff=maxdiff,
                )
                return self._send(*_json({"ok": True, "settings": settings, "restartRequired": True}))
            except Exception as e:
                return self._send(*_json({"error": str(e)}, status=400))

        if self.path == "/api/pool/bestshare/reset":
            try:
                now_s = int(time.time())
                STATE_DIR.mkdir(parents=True, exist_ok=True)
                st = _read_json_file(BESTSHARE_RESET_PATH)
                if not isinstance(st, dict):
                    st = {}

                pool_ids = sorted({str(v) for v in _pool_ids().values() if str(v).strip()})
                for pid in pool_ids:
                    st[pid] = now_s

                _write_json_file(BESTSHARE_RESET_PATH, st)
                with BEST_DIFFICULTY_CACHE_LOCK:
                    for pid in pool_ids:
                        BEST_DIFFICULTY_CACHE.pop(pid, None)

                return self._send(*_json({"ok": True, "t": now_s, "poolIds": pool_ids}))
            except Exception as e:
                return self._send(*_json({"error": str(e)}, status=500))

        if self.path == "/api/blocks/backscan":
            enabled_raw = body.get("enabled", None)
            rescan = bool(body.get("rescan")) or bool(body.get("rebuild"))
            reset = bool(body.get("reset")) or bool(body.get("resetAndRescan"))
            from_month = body.get("fromMonth") or body.get("from_month") or body.get("from")
            speed = str(body.get("speed") or "").strip().lower()
            max_blocks_raw = body.get("maxBlocks") if body.get("maxBlocks") is not None else body.get("max_blocks")
            interval_raw = body.get("intervalS") if body.get("intervalS") is not None else body.get("interval_s")
            now_s = int(time.time())

            blocks_state = _read_json_file(BLOCKS_STATE_PATH)
            scan = blocks_state.get("backscan") if isinstance(blocks_state.get("backscan"), dict) else {}
            if reset:
                blocks_state["events"] = []
                scan = {}

            # Manual-only scan settings.
            max_blocks = None
            interval_s = None
            try:
                if max_blocks_raw is not None and str(max_blocks_raw).strip() != "":
                    max_blocks = int(float(max_blocks_raw))
            except Exception:
                max_blocks = None
            try:
                if interval_raw is not None and str(interval_raw).strip() != "":
                    interval_s = int(float(interval_raw))
            except Exception:
                interval_s = None

            if speed in ["slow", "normal", "fast", "unlimited"]:
                scan["speed"] = speed
                if speed == "slow":
                    max_blocks = 25
                    interval_s = 10
                elif speed == "fast":
                    max_blocks = 500
                    interval_s = 0
                elif speed == "unlimited":
                    max_blocks = 2000
                    interval_s = 0
                else:
                    max_blocks = 100
                    interval_s = 2

            if max_blocks is not None:
                scan["maxBlocks"] = max(1, min(BACKSCAN_MAX_BLOCKS_CAP, int(max_blocks)))
            if interval_s is not None:
                scan["intervalS"] = max(0, min(3600, int(interval_s)))

            from_ts = _parse_month_yyyy_mm(from_month)
            if from_ts is not None:
                scan["fromMonth"] = str(from_month)
                scan["fromTs"] = int(from_ts)

            # Enabling with no pointers is treated as a start request.
            if enabled_raw is True and not (scan.get("startHeight") is not None and scan.get("nextHeight") is not None):
                rescan = True

            if rescan or bool(body.get("resetAndRescan")):
                # Start (or restart) an on-chain history scan. It stays OFF by default unless the user enables it.
                try:
                    tip_h = int(_rpc_call("getblockcount"))
                except Exception:
                    tip_h = None

                start_h = None
                if tip_h is not None:
                    if scan.get("fromTs"):
                        start_h = _find_start_height_by_time(tip_h=tip_h, from_ts=int(scan["fromTs"]), buffer_blocks=20000)
                    else:
                        install_t = _install_time_s()
                        start_h = _find_start_height_by_time(tip_h=tip_h, from_ts=int(install_t), buffer_blocks=20000)
                        if start_h is None:
                            approx_blocks = max(0, int((now_s - int(install_t)) / 15))
                            start_h = max(0, tip_h - approx_blocks - 20000)

                # Keep existing events by default; just restart scan pointers (unless reset).
                for k in [
                    "startHeight",
                    "nextHeight",
                    "tipHeightAtStart",
                    "tipHeightLast",
                    "startedAt",
                    "updatedAt",
                    "lastRunAt",
                    "complete",
                    "completedAt",
                    "stale",
                    "stopped",
                    "stoppedAt",
                    "stopRequested",
                ]:
                    scan.pop(k, None)

                if tip_h is not None and start_h is not None:
                    scan["startHeight"] = int(start_h)
                    scan["nextHeight"] = int(start_h)
                    scan["tipHeightAtStart"] = int(tip_h)
                if tip_h is None or start_h is None:
                    # Node may still be warming up. Keep the scan request and let the
                    # background worker retry until RPC becomes available.
                    scan["enabled"] = True if enabled_raw is None else bool(enabled_raw)
                    scan["status"] = "waiting" if scan.get("enabled") else "paused"
                    scan.pop("error", None)
                    scan.pop("errorAt", None)
                    scan["updatedAt"] = now_s
                else:
                    scan["enabled"] = True if enabled_raw is None else bool(enabled_raw)
                    scan["status"] = "running" if scan.get("enabled") else "paused"
                    scan.pop("error", None)
                    scan.pop("errorAt", None)
                    scan["complete"] = False
                    scan["stale"] = False
                    scan["stopped"] = False
                    scan.pop("stoppedAt", None)
                    scan["stopRequested"] = False
                    scan["requestedAt"] = now_s
                    scan["startedAt"] = now_s
                    scan["updatedAt"] = now_s

            if enabled_raw is not None and not rescan:
                scan["enabled"] = bool(enabled_raw)
                if scan["enabled"]:
                    scan["stopped"] = False
                    scan.pop("stoppedAt", None)
                    scan["stopRequested"] = False
                    scan["status"] = "running"
                    scan.pop("error", None)
                    scan.pop("errorAt", None)
                else:
                    scan["status"] = "paused"
                scan["updatedAt"] = now_s

            blocks_state["backscan"] = scan
            _write_json_file(BLOCKS_STATE_PATH, blocks_state)
            return self._send(*_json({"ok": True, "backscan": scan}))

        if self.path == "/api/blocks/backscan/pause":
            blocks_state = _read_json_file(BLOCKS_STATE_PATH)
            scan = blocks_state.get("backscan") if isinstance(blocks_state.get("backscan"), dict) else {}
            now_s = int(time.time())
            BACKSCAN_STOP_EVENT.clear()
            scan["enabled"] = False
            scan["stopRequested"] = False
            scan["stopped"] = False
            scan["status"] = "paused"
            scan["updatedAt"] = now_s
            blocks_state["backscan"] = scan
            _write_json_file(BLOCKS_STATE_PATH, blocks_state)
            return self._send(*_json({"ok": True, "backscan": scan}))

        if self.path == "/api/blocks/backscan/stop":
            blocks_state = _read_json_file(BLOCKS_STATE_PATH)
            scan = blocks_state.get("backscan") if isinstance(blocks_state.get("backscan"), dict) else {}
            now_s = int(time.time())

            BACKSCAN_STOP_EVENT.set()
            scan["enabled"] = False
            scan["stopRequested"] = True
            scan["stopped"] = False
            scan["status"] = "stopping"
            scan["updatedAt"] = now_s
            blocks_state["backscan"] = scan
            _write_json_file(BLOCKS_STATE_PATH, blocks_state)
            return self._send(*_json({"ok": True, "backscan": scan}))

        if self.path == "/api/support/ticket":
            if not SUPPORT_TICKET_URL:
                return self._send(*_json({"error": "support not configured"}, status=503))

            subject = str(body.get("subject") or "").strip()
            message = str(body.get("message") or "").strip()
            email = str(body.get("email") or "").strip()

            if len(subject) < 3 or len(subject) > 120:
                return self._send(*_json({"error": "subject must be 3-120 chars"}, status=400))
            if len(message) < 10 or len(message) > 8000:
                return self._send(*_json({"error": "message must be 10-8000 chars"}, status=400))
            if email and len(email) > 200:
                return self._send(*_json({"error": "email too long"}, status=400))

            payload = _support_ticket_payload(subject=subject, message=message, email=email or None)
            try:
                bundle, filename = _build_support_bundle_zip(payload)
                status, resp = _post_support_bundle(
                    SUPPORT_TICKET_URL, bundle_bytes=bundle, filename=filename, timeout_s=20
                )
                if int(status) >= 400:
                    return self._send(*_json({"error": "support server error"}, status=502))
                try:
                    data = json.loads(resp.decode("utf-8", errors="replace"))
                    ticket = data.get("ticket") if isinstance(data, dict) else None
                except Exception:
                    ticket = None
            except Exception:
                return self._send(*_json({"error": "support server unreachable"}, status=502))

            return self._send(*_json({"ok": True, "ticket": ticket}))

        return self._send(*_json({"error": "not found"}, status=404))


def main():
    STATIC_DIR.mkdir(parents=True, exist_ok=True)
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    for pool_id in _pool_ids().values():
        _pool_series(pool_id).load()

    global INSTALL_ID
    INSTALL_ID = _get_or_create_install_id()

    # Apply best-effort Miningcore config self-heals early (before UI polling).
    _ensure_miningcore_pool_tuning()
    _ensure_node_conf_layout()

    stop_event = threading.Event()
    t = threading.Thread(target=_series_sampler, args=(stop_event,), daemon=True)
    t.start()

    t_backscan = threading.Thread(target=_backscan_worker, args=(stop_event,), daemon=True)
    t_backscan.start()

    t2 = threading.Thread(target=_support_checkin_loop, args=(stop_event,), daemon=True)
    t2.start()

    ThreadingHTTPServer(("0.0.0.0", 3000), Handler).serve_forever()


if __name__ == "__main__":
    main()
