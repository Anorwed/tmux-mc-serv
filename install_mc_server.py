#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
install_mc_server.py
====================
Автоустановка Minecraft-сервера из модпака, экспортированного в Prism Launcher,
в среде Termux + proot-distro.

Запускать в Termux (НЕ внутри proot):

    pkg install -y python
    python install_mc_server.py                       # сам найдёт архив в Загрузках и спросит
    python install_mc_server.py /sdcard/Download/МояСборка.zip

Сервер по умолчанию пускает и лицензионных, и пиратских игроков (online-mode=false).

Туннель для игры с друзьями из интернета:
    python install_mc_server.py --setup-tunnel        # настроить/сменить туннель позже

Настройки сервера:
    python install_mc_server.py --configure           # вопросы по основным настройкам
    python install_mc_server.py --configure --max-players 8 --difficulty hard --set enable-command-block=true

Готовый мир и починка модов:
    python install_mc_server.py --import-world МойМир.zip --world-player Ник
    python install_mc_server.py --fix-mods --autofix  # отключить клиентские моды, из-за которых сервер падает

Полезные флаги:
    --accept-eula     принять Minecraft EULA без вопроса
    --test-run        после установки запустить сервер и проверить, что он стартует
    --ram 4G          сколько памяти отдать серверу (по умолчанию считается сам)
    --whitelist A,B   пускать только перечисленные ники
    --clean           перед установкой удалить старые mods/config
    --help            все остальные опции

Поддерживаются архивы:
    * Prism Launcher "Export Instance" (.zip: mmc-pack.json + .minecraft/)
    * Modrinth .mrpack (модификации скачиваются по ссылкам из манифеста)
Загрузчики: NeoForge, Forge, Fabric, Quilt, а также чистый Vanilla.
"""
from __future__ import annotations

import argparse
import configparser
import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import threading
import time
import shlex
import urllib.error
import urllib.request
import uuid
import zipfile
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path
from urllib.parse import urlparse

# =============================================================================
#  НАСТРОЙКИ (можно править)
# =============================================================================
DEFAULT_DISTRO = "ubuntu"                 # дистрибутив proot-distro (в нём есть Java 8/17/21)
DEFAULT_SERVER_DIR = Path.home() / "mc-server"
USER_AGENT = "mc-termux-installer/1.0"

# Папки/файлы клиента, которые на сервере не нужны (сравнение по имени верхнего уровня, без регистра)
EXCLUDE_TOP = {
    "logs", "crash-reports", "screenshots", "saves", "shaderpacks", "resourcepacks",
    "options.txt", "optionsof.txt", "optionsshaders.txt", "servers.dat", "servers.dat_old",
    "realms_persistence.json", "usercache.json", "command_history.txt", "hotbar.nbt",
    "assets", "versions", "libraries", "natives", "webcache", "webcache2",
    "replay_recordings", "replay_videos", "backups", ".mixin.out", ".fabric", "cache",
    "journeymap", "xaero", "xaeroworldmap", "xaerowaypoints", "icon.png", "instance.cfg",
}

# Клиентские моды, которые падают на сервере. Совпадение ищется в имени .jar (без регистра).
# У Fabric/Quilt клиентские моды определяются автоматически по метаданным внутри .jar,
# этот список в основном для Forge/NeoForge.
CLIENT_ONLY_PATTERNS = [
    "optifine", "optifabric", "sodium", "embeddium", "rubidium", "oculus", "iris",
    "indium", "continuity", "modmenu", "entityculling", "immediatelyfast",
    r"dynamic[-_ ]?fps", r"better[-_ ]?f3", "fpsreducer", "reeses",
    r"accurate[-_ ]?block[-_ ]?placement", r"chest[-_ ]?tracker", r"minecraft[-_ ]?capes",
]

CLEAN_DIRS = ["mods", "mods-client-disabled", "config", "defaultconfigs", "kubejs", "scripts"]

LOADER_UIDS = {                            # uid компонента в mmc-pack.json -> имя загрузчика
    "net.neoforged": "neoforge",
    "net.minecraftforge": "forge",
    "net.fabricmc.fabric-loader": "fabric",
    "org.quiltmc.quilt-loader": "quilt",
}
MRPACK_LOADERS = {
    "neoforge": "neoforge", "forge": "forge",
    "fabric-loader": "fabric", "quilt-loader": "quilt",
}
MRPACK_ALLOWED_HOSTS = {"cdn.modrinth.com", "github.com", "raw.githubusercontent.com", "gitlab.com"}

# =============================================================================
#  ЛОГИРОВАНИЕ И УТИЛИТЫ
# =============================================================================
_log_fh = None


class InstallError(Exception):
    """Ожидаемая ошибка установки: показываем понятное сообщение без traceback."""


def open_log(path: Path) -> None:
    global _log_fh
    path.parent.mkdir(parents=True, exist_ok=True)
    _log_fh = open(path, "a", encoding="utf-8")
    _log_fh.write(f"\n===== {time.strftime('%Y-%m-%d %H:%M:%S')} =====\n")


def log(msg: str = "", *, console: bool = True) -> None:
    if console:
        print(msg, flush=True)
    if _log_fh:
        _log_fh.write(msg + "\n")
        _log_fh.flush()


def step(n: int, total: int, title: str) -> None:
    log(f"\n[{n}/{total}] {title}")
    log("-" * 60)


def ask_yes_no(question: str, default: bool, assume_yes: bool = False) -> bool:
    if assume_yes:
        return True
    if not sys.stdin.isatty():
        return default
    hint = "[Y/n]" if default else "[y/N]"
    ans = input(f"{question} {hint} ").strip().lower()
    if not ans:
        return default
    return ans in ("y", "yes", "д", "да")


def run(cmd, *, cwd=None, capture=False, check=True) -> subprocess.CompletedProcess:
    """Запуск команды. Вывод показывается пользователю и пишется в лог."""
    cmd = [str(c) for c in cmd]
    log("$ " + " ".join(cmd), console=False)
    if capture:
        r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, errors="replace")
        log((r.stdout or "") + (r.stderr or ""), console=False)
    else:
        p = subprocess.Popen(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             text=True, errors="replace", bufsize=1)
        tail: list[str] = []
        assert p.stdout is not None
        for line in p.stdout:
            sys.stdout.write(line)
            if _log_fh:
                _log_fh.write(line)
            tail.append(line)
            tail = tail[-40:]
        p.wait()
        r = subprocess.CompletedProcess(cmd, p.returncode, "".join(tail), "")
    if check and r.returncode != 0:
        raise InstallError(f"Команда завершилась с ошибкой (код {r.returncode}): {' '.join(cmd[:6])} ...\n"
                           f"Подробности в логе установки.")
    return r


def fetch_json(url: str):
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            return json.loads(r.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        raise InstallError(f"Сервер вернул {e.code} для {url}") from e
    except (urllib.error.URLError, TimeoutError, ValueError) as e:
        raise InstallError(f"Не удалось получить {url}: {e}") from e


def _hash_ok(path: Path, sha1: str | None, sha512: str | None) -> bool:
    for algo, expected in (("sha512", sha512), ("sha1", sha1)):
        if expected:
            h = hashlib.new(algo)
            with open(path, "rb") as f:
                for chunk in iter(lambda: f.read(1 << 20), b""):
                    h.update(chunk)
            return h.hexdigest().lower() == expected.lower()
    return True


def download(url: str, dest: Path, *, sha1=None, sha512=None, retries=4, progress=True) -> None:
    """Скачивание с повторами, проверкой хэша и атомарной записью (.part -> файл)."""
    dest.parent.mkdir(parents=True, exist_ok=True)
    if dest.exists() and _hash_ok(dest, sha1, sha512) and (sha1 or sha512):
        return
    tmp = dest.with_suffix(dest.suffix + ".part")
    last_err = None
    for attempt in range(1, retries + 1):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            with urllib.request.urlopen(req, timeout=60) as r, open(tmp, "wb") as f:
                total = int(r.headers.get("Content-Length") or 0)
                done, last_print = 0, 0.0
                while True:
                    chunk = r.read(1 << 18)
                    if not chunk:
                        break
                    f.write(chunk)
                    done += len(chunk)
                    if progress and time.time() - last_print > 0.5:
                        last_print = time.time()
                        pct = f" {done * 100 // total}%" if total else ""
                        print(f"\r  {dest.name}: {done / 1048576:.1f} МБ{pct}   ", end="", flush=True)
            if progress:
                print()
            if not _hash_ok(tmp, sha1, sha512):
                raise InstallError("не совпала контрольная сумма")
            os.replace(tmp, dest)
            return
        except urllib.error.HTTPError as e:
            if e.code in (400, 401, 403, 404):
                raise InstallError(f"Файл недоступен (HTTP {e.code}): {url}") from e
            last_err = e
        except (urllib.error.URLError, TimeoutError, OSError, InstallError) as e:
            last_err = e
        log(f"  попытка {attempt}/{retries} не удалась: {last_err}", console=progress)
        time.sleep(2 * attempt)
    raise InstallError(f"Не удалось скачать {url}: {last_err}")


# =============================================================================
#  ЭТАП 1. ПРОВЕРКА ОКРУЖЕНИЯ
# =============================================================================
def read_meminfo() -> tuple[int, int]:
    info = {}
    try:
        with open("/proc/meminfo") as f:
            for line in f:
                k, v = line.split(":", 1)
                info[k] = int(v.split()[0]) // 1024
    except (OSError, ValueError):
        pass
    return info.get("MemTotal", 0), info.get("MemAvailable", 0)


def check_environment(zip_path: Path, server_dir: Path) -> None:
    if "com.termux" not in os.environ.get("PREFIX", "") and not shutil.which("pkg"):
        raise InstallError("Скрипт нужно запускать в Termux (не найдена команда pkg).")
    arch = platform.machine().lower()
    if arch in ("armv7l", "armv8l", "arm", "i686", "i386"):
        raise InstallError(f"32-битная архитектура ({arch}) не поддерживается: нет современных Java-пакетов.")
    if not zip_path.exists():
        hint = ""
        if str(zip_path).startswith(("/sdcard", "/storage")) and not (Path.home() / "storage").exists():
            hint = "\nПохоже, у Termux нет доступа к памяти. Выполните: termux-setup-storage"
        raise InstallError(f"Файл не найден: {zip_path}{hint}")
    if not zipfile.is_zipfile(zip_path):
        raise InstallError(f"Это не zip-архив: {zip_path}")

    server_dir.parent.mkdir(parents=True, exist_ok=True)
    free_gb = shutil.disk_usage(server_dir.parent).free / 1024 ** 3
    need_gb = 3 + 2 * zip_path.stat().st_size / 1024 ** 3
    log(f"Архитектура: {arch}, свободно места: {free_gb:.1f} ГБ (нужно ~{need_gb:.1f} ГБ)")
    if free_gb < need_gb:
        log("ВНИМАНИЕ: места может не хватить (дистрибутив ~1 ГБ + Java + сборка + мир).")
    total, avail = read_meminfo()
    if total:
        log(f"Память: всего {total} МБ, доступно {avail} МБ")


# =============================================================================
#  ВЫБОР АРХИВА СБОРКИ
# =============================================================================
def ensure_storage_access() -> None:
    """Просит у Android доступ к памяти телефона (появляется системное окно)."""
    storage = Path.home() / "storage"
    if storage.exists() or not shutil.which("termux-setup-storage"):
        return
    log("Запрашиваю доступ к памяти телефона — разрешите его в окне Android...")
    subprocess.run(["termux-setup-storage"], check=False)
    for _ in range(40):
        if storage.exists():
            return
        time.sleep(1)


def is_pack_archive(path: Path) -> bool:
    try:
        with zipfile.ZipFile(path) as zf:
            return any(n.rsplit("/", 1)[-1] in ("mmc-pack.json", "modrinth.index.json") for n in zf.namelist())
    except (zipfile.BadZipFile, OSError):
        return False


def find_pack_candidates() -> list[Path]:
    home = Path.home()
    dirs = [Path.cwd(), home, home / "storage" / "downloads", home / "storage" / "shared" / "Download",
            home / "storage" / "shared" / "Downloads", Path("/sdcard/Download")]
    files: dict[Path, float] = {}
    for d in dirs:
        try:
            if d.is_dir():
                for pattern in ("*.zip", "*.mrpack"):
                    for f in d.glob(pattern):
                        files[f.resolve()] = f.stat().st_mtime
        except OSError:
            continue
    newest = sorted(files, key=files.get, reverse=True)[:30]
    return [f for f in newest if is_pack_archive(f)]


def choose_archive(arg: str | None) -> Path:
    if arg:
        path = Path(arg).expanduser()
        if not path.exists() and str(path).startswith(("/sdcard", "/storage")):
            ensure_storage_access()
        return path
    ensure_storage_access()
    log("Архив не указан — ищу сборки Prism/Modrinth в Загрузках и домашней папке...")
    cands = find_pack_candidates()
    if not sys.stdin.isatty():
        if len(cands) == 1:
            return cands[0]
        raise InstallError("Укажите путь к архиву: python install_mc_server.py /путь/к/сборке.zip")
    if cands:
        for i, c in enumerate(cands, 1):
            st = c.stat()
            log(f"  {i}) {c.name}   ({st.st_size / 1048576:.0f} МБ, {time.strftime('%d.%m.%Y %H:%M', time.localtime(st.st_mtime))})")
        ans = input("Номер архива или путь к другому файлу [1]: ").strip().strip("'\"")
        if not ans:
            return cands[0]
        if ans.isdigit() and 1 <= int(ans) <= len(cands):
            return cands[int(ans) - 1]
        return Path(ans).expanduser()
    ans = input("Подходящих архивов не найдено. Введите путь к zip/mrpack: ").strip().strip("'\"")
    if not ans:
        raise InstallError("Путь к архиву не указан.")
    return Path(ans).expanduser()


# =============================================================================
#  ЭТАП 2. АНАЛИЗ АРХИВА
# =============================================================================
@dataclass
class Pack:
    kind: str                       # "prism" | "mrpack"
    name: str
    mc: str
    loader: str | None              # neoforge | forge | fabric | quilt | None (vanilla)
    loader_ver: str | None
    ram_hint_mb: int | None = None
    base: str = ""                  # префикс папки с mmc-pack.json внутри zip
    game_prefix: str = ""           # префикс .minecraft внутри zip (prism)
    files: list = field(default_factory=list)   # список файлов манифеста (mrpack)


def analyze_pack(zip_path: Path) -> Pack:
    with zipfile.ZipFile(zip_path) as zf:
        names = zf.namelist()
        if "modrinth.index.json" in names:
            return _analyze_mrpack(zf)
        cands = sorted((n for n in names if n.rsplit("/", 1)[-1] == "mmc-pack.json"),
                       key=lambda n: n.count("/"))
        if cands:
            return _analyze_prism(zf, names, cands[0])
        if "manifest.json" in names:
            raise InstallError(
                "Это CurseForge-манифест: в нём нет самих модов, только ID (а скачать их без API-ключа нельзя).\n"
                "Экспортируйте в Prism: Instance -> Export Instance -> формат Prism Launcher (.zip), "
                "либо Modrinth (.mrpack).")
        raise InstallError("Не найден mmc-pack.json — это не экспорт Prism Launcher.")


def _analyze_prism(zf: zipfile.ZipFile, names: list[str], mmc_path: str) -> Pack:
    base = mmc_path[: -len("mmc-pack.json")]
    data = json.loads(zf.read(mmc_path).decode("utf-8-sig"))
    mc = loader = lv = None
    for c in data.get("components", []):
        uid, ver = c.get("uid"), c.get("version") or c.get("cachedVersion")
        if uid == "net.minecraft":
            mc = ver
        elif uid in LOADER_UIDS:
            loader, lv = LOADER_UIDS[uid], ver
    if not mc:
        raise InstallError("В mmc-pack.json не найдена версия Minecraft.")

    name, ram = "Minecraft Server", None
    cfg_name = base + "instance.cfg"
    if cfg_name in names:
        text = zf.read(cfg_name).decode("utf-8-sig", "replace")
        if not text.lstrip().startswith("["):
            text = "[General]\n" + text
        cp = configparser.ConfigParser(interpolation=None, strict=False)
        try:
            cp.read_string(text)
            sec = cp["General"] if cp.has_section("General") else {}
            name = (sec.get("name") or name).strip()
            ram = int(sec["maxmemalloc"]) if "maxmemalloc" in sec else None
        except (configparser.Error, ValueError):
            pass

    game_prefix, best = "", 0
    for cand in (base + ".minecraft/", base + "minecraft/"):
        count = sum(1 for n in names if n.startswith(cand))
        if count > best:
            game_prefix, best = cand, count
    if not best:
        raise InstallError("В архиве нет папки .minecraft/ — Prism экспортировал без файлов?")
    return Pack("prism", name, mc, loader, lv, ram, base, game_prefix)


def _analyze_mrpack(zf: zipfile.ZipFile) -> Pack:
    idx = json.loads(zf.read("modrinth.index.json").decode("utf-8-sig"))
    deps = idx.get("dependencies", {})
    mc = deps.get("minecraft")
    if not mc:
        raise InstallError("В modrinth.index.json нет версии Minecraft.")
    loader = lv = None
    for key, nm in MRPACK_LOADERS.items():
        if key in deps:
            loader, lv = nm, deps[key]
    return Pack("mrpack", idx.get("name", "Minecraft Server"), mc, loader, lv, files=idx.get("files", []))


def required_java(mc: str) -> int:
    """Какая версия Java нужна для данной версии Minecraft (эвристика, можно переопределить --java)."""
    nums = [int(x) for x in re.findall(r"\d+", mc)[:3]]
    if not nums:
        return 21
    if nums[0] >= 26:                      # новая схема нумерации (26.x)
        return 25
    if nums[0] == 1 and len(nums) >= 2:
        minor, patch = nums[1], nums[2] if len(nums) > 2 else 0
        if minor > 20 or (minor == 20 and patch >= 5):
            return 21
        if minor >= 17:
            return 17
        return 8
    return 21


# =============================================================================
#  КОНТЕКСТ УСТАНОВКИ
# =============================================================================
@dataclass
class Ctx:
    args: argparse.Namespace
    zip_path: Path
    server_dir: Path
    distro: str
    pack: Pack | None
    java_major: int = 21
    java_bin: str = ""
    xmx: int = 4096
    xms: int = 2048
    launch: str = ""                # часть команды запуска после JVM-флагов


def proot_cmd(ctx: Ctx, inner: list[str]) -> list[str]:
    return ["proot-distro", "login", ctx.distro, "--bind", f"{ctx.server_dir}:/server", "--"] + inner


def parse_ram(text: str) -> int:
    m = re.fullmatch(r"(\d+(?:\.\d+)?)\s*([gGmM]?)[bB]?", text.strip())
    if not m:
        raise InstallError(f"Не понимаю значение --ram: {text} (пример: 4G или 4096)")
    val = float(m.group(1))
    return int(val * 1024) if m.group(2).lower() == "g" else int(val)


def pick_ram(args, pack: Pack) -> tuple[int, int]:
    if args.ram:
        xmx = parse_ram(args.ram)
    else:
        total, avail = read_meminfo()
        if not total:
            total, avail = 4096, 3072
        xmx = min(int(total * 0.55), int(avail * 0.85), 8192)
        if pack.ram_hint_mb and pack.ram_hint_mb >= 2048:
            xmx = min(xmx, pack.ram_hint_mb)
        xmx = max(xmx // 256 * 256, 1536)
    if xmx < 2048:
        log("ВНИМАНИЕ: меньше 2 ГБ под сервер — большая сборка может не запуститься.")
    return xmx, max(512, xmx // 2)


# =============================================================================
#  ЭТАП 3. proot-distro И ДИСТРИБУТИВ
# =============================================================================
def ensure_proot_distro() -> None:
    if shutil.which("proot-distro"):
        log("proot-distro уже установлен")
        return
    log("Устанавливаю proot-distro...")
    if run(["pkg", "install", "-y", "proot-distro"], check=False).returncode != 0:
        log("Не вышло, обновляю списки пакетов и пробую ещё раз...")
        run(["pkg", "update", "-y"], check=False)
        run(["pkg", "install", "-y", "proot-distro"])


def ensure_distro(ctx: Ctx) -> None:
    probe = run(["proot-distro", "login", ctx.distro, "--", "true"], capture=True, check=False)
    if probe.returncode == 0:
        log(f"Дистрибутив {ctx.distro} уже установлен")
        return
    log(f"Устанавливаю {ctx.distro} (около 1 ГБ, это может занять несколько минут)...")
    run(["proot-distro", "install", ctx.distro])


# =============================================================================
#  ЭТАП 4. JAVA ВНУТРИ ДИСТРИБУТИВА
# =============================================================================
def _find_java_home(ctx: Ctx) -> str:
    major = ctx.java_major
    r = run(proot_cmd(ctx, ["bash", "-lc", f"ls -d /usr/lib/jvm/java-{major}-openjdk-* 2>/dev/null | head -n1"]),
            capture=True, check=False)
    lines = [ln.strip() for ln in (r.stdout or "").splitlines() if ln.strip().startswith("/usr/lib/jvm")]
    return lines[-1] if lines else ""


def ensure_java(ctx: Ctx) -> None:
    home = _find_java_home(ctx)
    if not home:
        log(f"Устанавливаю OpenJDK {ctx.java_major} внутри {ctx.distro}...")
        script = ("export DEBIAN_FRONTEND=noninteractive; apt-get update && "
                  f"apt-get install -y openjdk-{ctx.java_major}-jre-headless ca-certificates curl")
        r = run(proot_cmd(ctx, ["bash", "-lc", script]), check=False)
        home = _find_java_home(ctx)
        if r.returncode != 0 or not home:
            raise InstallError(
                f"Не удалось поставить openjdk-{ctx.java_major}-jre-headless в {ctx.distro}.\n"
                f"Возможно, в этом дистрибутиве нет такого пакета. Попробуйте другой: --distro ubuntu "
                f"(или задайте версию вручную: --java N).")
    ctx.java_bin = f"{home}/bin/java"
    run(proot_cmd(ctx, [ctx.java_bin, "-version"]))


# =============================================================================
#  ЭТАП 5. РАСПАКОВКА СБОРКИ
# =============================================================================
def _safe_parts(rel: str) -> list[str] | None:
    """Разбивает путь из архива на части. None — если путь опасный (zip-slip)."""
    rel = rel.replace("\\", "/")
    if rel.startswith("/") or re.match(r"^[A-Za-z]:", rel):
        return None
    parts = [p for p in rel.split("/") if p and p != "."]
    if any(p == ".." for p in parts):
        return None
    return parts


def _copy_prefix(zf: zipfile.ZipFile, prefix: str, dest: Path, use_exclude: bool = True) -> int:
    count = 0
    for info in zf.infolist():
        if not info.filename.startswith(prefix):
            continue
        parts = _safe_parts(info.filename[len(prefix):])
        if parts is None:
            log(f"  пропущен небезопасный путь: {info.filename}")
            continue
        if not parts:
            continue
        if use_exclude and parts[0].lower() in EXCLUDE_TOP:
            continue
        target = dest.joinpath(*parts)
        if info.is_dir():
            target.mkdir(parents=True, exist_ok=True)
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        with zf.open(info) as src, open(target, "wb") as out:
            shutil.copyfileobj(src, out, 1 << 20)
        count += 1
    return count


def extract_pack(ctx: Ctx) -> None:
    sd = ctx.server_dir
    sd.mkdir(parents=True, exist_ok=True)

    existing = [d for d in CLEAN_DIRS if (sd / d).exists()]
    if existing:
        if ctx.args.clean or ask_yes_no(
                f"В {sd} уже есть {', '.join(existing)}. Удалить перед установкой (мир НЕ трогается)?", True,
                ctx.args.yes):
            for d in existing:
                shutil.rmtree(sd / d, ignore_errors=True)
            log("Старые папки удалены")
        else:
            log("ВНИМАНИЕ: файлы будут смешаны со старыми — возможны дубли модов.")

    with zipfile.ZipFile(ctx.zip_path) as zf:
        if ctx.pack.kind == "prism":
            n = _copy_prefix(zf, ctx.pack.game_prefix, sd)
            log(f"Распаковано файлов: {n}")
        else:
            n = _copy_prefix(zf, "overrides/", sd) + _copy_prefix(zf, "server-overrides/", sd)
            log(f"Распаковано файлов из overrides: {n}")
            _download_mrpack_files(ctx.pack.files, sd)

    mods = sd / "mods"
    count = len(list(mods.glob("*.jar"))) if mods.is_dir() else 0
    log(f"Модов (.jar) в папке mods: {count}")
    if ctx.pack.loader and count == 0:
        log("ВНИМАНИЕ: папка mods пуста. Если в Prism моды были «только в метаданных» — экспортируйте заново "
            "с включёнными файлами модов.")


def _download_mrpack_files(files: list, dest: Path) -> None:
    jobs, skipped = [], 0
    for f in files:
        if (f.get("env") or {}).get("server") == "unsupported":
            skipped += 1
            continue
        parts = _safe_parts(f.get("path", ""))
        if not parts:
            raise InstallError(f"Небезопасный путь в манифесте: {f.get('path')}")
        url = next((u for u in f.get("downloads", []) if urlparse(u).hostname in MRPACK_ALLOWED_HOSTS), None)
        if not url:
            raise InstallError(f"Нет разрешённой ссылки для {f.get('path')}")
        hashes = f.get("hashes", {})
        jobs.append((url, dest.joinpath(*parts), hashes.get("sha1"), hashes.get("sha512")))
    log(f"Скачиваю файлов: {len(jobs)} (клиентских пропущено: {skipped})")
    done = 0
    with ThreadPoolExecutor(max_workers=4) as ex:
        futs = [ex.submit(download, u, p, sha1=s1, sha512=s512, progress=False) for u, p, s1, s512 in jobs]
        for fut in futs:
            fut.result()
            done += 1
            if done % 10 == 0 or done == len(futs):
                print(f"\r  {done}/{len(futs)}", end="", flush=True)
    print()


# =============================================================================
#  ЭТАП 6. ОТСЕВ КЛИЕНТСКИХ МОДОВ
# =============================================================================
def jar_is_client_only(jar: Path) -> bool:
    try:
        with zipfile.ZipFile(jar) as z:
            names = set(z.namelist())
            if "fabric.mod.json" in names:
                d = json.loads(z.read("fabric.mod.json").decode("utf-8-sig"), strict=False)
                return d.get("environment") == "client"
            if "quilt.mod.json" in names:
                d = json.loads(z.read("quilt.mod.json").decode("utf-8-sig"), strict=False)
                return (d.get("minecraft") or {}).get("environment") == "client"
    except (zipfile.BadZipFile, ValueError, KeyError, OSError, AttributeError):
        pass
    return False


def filter_client_mods(server_dir: Path) -> list[str]:
    """Переносит клиентские моды в mods-client-disabled/ (ничего не удаляя)."""
    mods = server_dir / "mods"
    if not mods.is_dir():
        return []
    pattern = re.compile(r"(?<![a-z])(" + "|".join(CLIENT_ONLY_PATTERNS) + r")(?![a-z])", re.I)
    quarantine = server_dir / "mods-client-disabled"
    moved = []
    for jar in sorted(mods.glob("*.jar")):
        if jar_is_client_only(jar) or pattern.search(jar.stem):
            quarantine.mkdir(exist_ok=True)
            shutil.move(str(jar), quarantine / jar.name)
            moved.append(jar.name)
    return moved


# =============================================================================
#  ЭТАП 7. УСТАНОВКА ЗАГРУЗЧИКА / ЯДРА СЕРВЕРА
# =============================================================================
def _run_installer(ctx: Ctx, jar_name: str, extra: str) -> None:
    log("Запускаю установщик (на телефоне это 5–15 минут, не закрывайте Termux)...")
    run(proot_cmd(ctx, ["bash", "-lc", f'cd /server && "{ctx.java_bin}" -jar {jar_name} {extra}']))


def _find_unix_args(sd: Path) -> str | None:
    for p in sorted((sd / "libraries").rglob("unix_args.txt")):
        return p.relative_to(sd).as_posix()
    return None


def install_loader(ctx: Ctx) -> None:
    p, sd = ctx.pack, ctx.server_dir
    mc, lv = p.mc, p.loader_ver

    if p.loader is None:
        meta = fetch_json("https://piston-meta.mojang.com/mc/game/version_manifest_v2.json")
        entry = next((v for v in meta["versions"] if v["id"] == mc), None)
        if not entry:
            raise InstallError(f"Версия {mc} не найдена в манифесте Mojang.")
        srv = fetch_json(entry["url"])["downloads"].get("server")
        if not srv:
            raise InstallError(f"Для {mc} у Mojang нет серверного jar.")
        download(srv["url"], sd / "server.jar", sha1=srv["sha1"])
        ctx.launch = "-jar server.jar"

    elif p.loader == "fabric":
        installers = fetch_json("https://meta.fabricmc.net/v2/versions/installer")
        inst = next((i["version"] for i in installers if i.get("stable")), installers[0]["version"])
        url = f"https://meta.fabricmc.net/v2/versions/loader/{mc}/{lv}/{inst}/server/jar"
        download(url, sd / "fabric-server-launch.jar")
        ctx.launch = "-jar fabric-server-launch.jar"

    elif p.loader == "quilt":
        installers = fetch_json("https://meta.quiltmc.org/v3/versions/installer")
        download(installers[0]["url"], sd / "quilt-installer.jar")
        _run_installer(ctx, "quilt-installer.jar",
                       f"install server {mc} {lv} --download-server --install-dir=/server")
        (sd / "quilt-installer.jar").unlink(missing_ok=True)
        ctx.launch = "-jar quilt-server-launch.jar"

    elif p.loader in ("forge", "neoforge"):
        if p.loader == "forge":
            full = f"{mc}-{lv}"
            url = f"https://maven.minecraftforge.net/net/minecraftforge/forge/{full}/forge-{full}-installer.jar"
        elif mc == "1.20.1":                                  # старая схема NeoForge 47.x
            full = f"{mc}-{lv}"
            url = f"https://maven.neoforged.net/releases/net/neoforged/forge/{full}/forge-{full}-installer.jar"
        else:
            url = f"https://maven.neoforged.net/releases/net/neoforged/neoforge/{lv}/neoforge-{lv}-installer.jar"
        download(url, sd / "loader-installer.jar")
        _run_installer(ctx, "loader-installer.jar", "--installServer")
        (sd / "loader-installer.jar").unlink(missing_ok=True)
        (sd / "loader-installer.jar.log").unlink(missing_ok=True)

        args_file = _find_unix_args(sd)
        if args_file:                                         # Forge 1.17+ / NeoForge
            ctx.launch = f"@{args_file}"
        else:                                                 # старый Forge (<=1.16.5)
            jars = [j for j in sd.glob("forge-*.jar") if "installer" not in j.name]
            if not jars:
                raise InstallError("Установщик отработал, но запускаемый файл сервера не найден.")
            ctx.launch = f"-jar {jars[0].name}"
    else:
        raise InstallError(f"Неизвестный загрузчик: {p.loader}")
    log(f"Команда запуска: java ... {ctx.launch} nogui")


# =============================================================================
#  ЭТАП 8. НАСТРОЙКА: start.sh, server.properties, eula.txt
# =============================================================================
def write_start_scripts(ctx: Ctx) -> None:
    flags = [f"-Xms{ctx.xms}M", f"-Xmx{ctx.xmx}M", "-XX:+UseG1GC", "-XX:+ParallelRefProcEnabled",
             "-XX:MaxGCPauseMillis=200", "-XX:+DisableExplicitGC", "-Dfile.encoding=UTF-8"]
    inner = ctx.server_dir / "start.sh"
    inner.write_text(
        "#!/bin/bash\n"
        "# Запускается ВНУТРИ proot-distro (папка сервера смонтирована как /server)\n"
        'cd "$(dirname "$0")" || exit 1\n'
        f'exec "{ctx.java_bin}" {" ".join(flags)} {ctx.launch} nogui "$@"\n')
    inner.chmod(0o755)

    prefix = os.environ.get("PREFIX", "/data/data/com.termux/files/usr")
    outer = Path.home() / "start-mc.sh"
    outer.write_text(OUTER_START_TEMPLATE.replace("@@PREFIX@@", prefix)
                     .replace("@@SD@@", str(ctx.server_dir)).replace("@@DISTRO@@", ctx.distro))
    outer.chmod(0o755)


OUTER_START_TEMPLATE = """#!@@PREFIX@@/bin/bash
# Запуск сервера из Termux: ./start-mc.sh
SD="@@SD@@"
command -v termux-wake-lock >/dev/null && termux-wake-lock
if [ -x "$SD/.tunnel/run-tunnel.sh" ] && command -v tmux >/dev/null; then
  tmux kill-session -t mc-tunnel 2>/dev/null
  tmux new-session -d -s mc-tunnel "$SD/.tunnel/run-tunnel.sh"
  echo "Туннель запущен в фоне (посмотреть: tmux attach -t mc-tunnel, выйти: Ctrl+B, затем D)"
  [ -s "$SD/.tunnel/address.txt" ] && echo "Адрес для друзей: $(cat "$SD/.tunnel/address.txt")"
fi
proot-distro login @@DISTRO@@ --bind "$SD:/server" -- bash /server/start.sh "$@"
tmux kill-session -t mc-tunnel 2>/dev/null
command -v termux-wake-unlock >/dev/null && termux-wake-unlock
"""


# =============================================================================
#  НАСТРОЙКИ СЕРВЕРА (server.properties)
# =============================================================================
SETTING_FLAGS = {                      # атрибут argparse -> ключ в server.properties
    "motd": "motd", "max_players": "max-players", "difficulty": "difficulty", "gamemode": "gamemode",
    "view_distance": "view-distance", "simulation_distance": "simulation-distance", "pvp": "pvp",
    "allow_flight": "allow-flight", "spawn_protection": "spawn-protection",
    "level_seed": "level-seed", "level_name": "level-name",
}
INT_LIMITS = {"max-players": (1, 1000), "view-distance": (2, 32), "simulation-distance": (2, 32),
              "spawn-protection": (0, 1000), "server-port": (1, 65535)}


def is_offline(args) -> bool:
    """Пиратский режим включён по умолчанию (online-mode=false)."""
    return (args.online_mode or "false") == "false"


def _java_escape(value: str) -> str:
    return value.encode("unicode_escape").decode("ascii") if not value.isascii() else value


def collect_settings(args) -> dict[str, str]:
    """Собирает явно заданные пользователем настройки (--motd, --max-players, --set ключ=значение ...)."""
    result: dict[str, str] = {}
    for attr, key in SETTING_FLAGS.items():
        val = getattr(args, attr, None)
        if val is not None:
            result[key] = str(val).lower() if isinstance(val, bool) else str(val)
    for item in getattr(args, "set", None) or []:
        if "=" not in item:
            raise InstallError(f"--set ожидает формат ключ=значение, получено: {item}")
        key, val = item.split("=", 1)
        result[key.strip()] = val.strip()
    for key, val in result.items():
        if not re.fullmatch(r"[a-z0-9.\-]+", key):
            raise InstallError(f"Недопустимое имя настройки: {key}")
        if key in INT_LIMITS:
            lo, hi = INT_LIMITS[key]
            if not val.lstrip("-").isdigit() or not lo <= int(val) <= hi:
                raise InstallError(f"{key} должно быть числом от {lo} до {hi}, получено: {val}")
        result[key] = _java_escape(val)
    return result


def read_props(path: Path) -> dict[str, str]:
    props = {}
    if path.exists():
        for ln in path.read_text(encoding="utf-8").splitlines():
            if "=" in ln and not ln.startswith("#"):
                k, v = ln.split("=", 1)
                props[k.strip()] = v.strip()
    return props


def ask_settings(current: dict[str, str]) -> dict[str, str]:
    """Короткий интерактивный опрос основных настроек. Enter — оставить как есть."""
    log("Основные настройки сервера (Enter — оставить текущее значение):")
    questions = [
        ("motd", "Описание сервера (MOTD)", None),
        ("max-players", "Максимум игроков", None),
        ("difficulty", "Сложность (peaceful/easy/normal/hard)", {"peaceful", "easy", "normal", "hard"}),
        ("gamemode", "Режим игры (survival/creative/adventure/spectator)",
         {"survival", "creative", "adventure", "spectator"}),
        ("pvp", "PvP между игроками (true/false)", {"true", "false"}),
        ("view-distance", "Дальность прорисовки (2–32, на телефоне 6–8)", None),
    ]
    out: dict[str, str] = {}
    for key, title, choices in questions:
        cur = current.get(key, "")
        ans = input(f"  {title} [{cur}]: ").strip()
        if not ans:
            continue
        if choices and ans.lower() not in choices:
            log(f"    пропущено: допустимо {', '.join(sorted(choices))}")
            continue
        out[key] = ans.lower() if choices else ans
    return out


def apply_settings(server_dir: Path, settings: dict[str, str]) -> None:
    path = server_dir / "server.properties"
    for key, val in settings.items():
        set_property(path, key, _java_escape(val) if not val.isascii() and "\\u" not in val else val)
        log(f"  {key} = {val}")


def configure_server(args, server_dir: Path) -> None:
    """Режим --configure: поменять настройки уже установленного сервера."""
    props = server_dir / "server.properties"
    if not props.exists():
        raise InstallError(f"Нет {props}: сначала установите сервер.")
    settings = collect_settings(args)
    if args.online_mode:
        settings["online-mode"] = args.online_mode
        if args.online_mode == "false":
            settings["enforce-secure-profile"] = "false"
    if args.whitelist:
        settings["white-list"] = settings["enforce-whitelist"] = "true"
    if not settings:
        if not sys.stdin.isatty():
            raise InstallError("Укажите настройки флагами, например: --configure --max-players 8 --difficulty hard")
        settings = ask_settings(read_props(props))
    if not settings and not args.whitelist:
        log("Ничего не изменено.")
        return
    apply_settings(server_dir, settings)
    if args.whitelist:
        write_whitelist(Ctx(args, Path(), server_dir, args.distro, None))
    log("\nГотово. Настройки применятся при следующем запуске сервера (перезапустите ./start-mc.sh).")


def configure_properties(ctx: Ctx) -> None:
    path = ctx.server_dir / "server.properties"
    lines = path.read_text(encoding="utf-8").splitlines() if path.exists() else []
    present = {ln.split("=", 1)[0].strip(): i for i, ln in enumerate(lines) if "=" in ln and not ln.startswith("#")}

    motd = ctx.pack.name if ctx.pack else "Minecraft Server"
    if not motd.isascii():
        motd = motd.encode("unicode_escape").decode("ascii")
    offline = is_offline(ctx.args)
    wanted = {"motd": (motd, False), "view-distance": ("8", False), "simulation-distance": ("6", False),
              "server-port": (str(ctx.args.port), True),
              "online-mode": (ctx.args.online_mode or "false", True)}
    if offline:                                   # пиратские клиенты не имеют подписанных профилей
        wanted["enforce-secure-profile"] = ("false", True)
    if ctx.args.whitelist:
        wanted["white-list"] = ("true", True)
        wanted["enforce-whitelist"] = ("true", True)
    for key, val in collect_settings(ctx.args).items():       # явные настройки пользователя главнее всего
        wanted[key] = (val, True)
    for key, (val, force) in wanted.items():
        if key in present:
            if force:
                lines[present[key]] = f"{key}={val}"
        else:
            lines.append(f"{key}={val}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def offline_uuid(name: str) -> str:
    """UUID игрока в offline-режиме (так его считает сам сервер)."""
    return str(uuid.UUID(bytes=hashlib.md5(f"OfflinePlayer:{name}".encode("utf-8")).digest(), version=3))


def write_whitelist(ctx: Ctx) -> None:
    names = [n.strip() for n in (ctx.args.whitelist or "").split(",") if n.strip()]
    if not names:
        return
    if not is_offline(ctx.args):
        log("ВНИМАНИЕ: --whitelist рассчитан на offline-режим; при online-mode=true добавляйте ники командой "
            "whitelist add в консоли сервера.")
        return
    path = ctx.server_dir / "whitelist.json"
    path.write_text(json.dumps([{"uuid": offline_uuid(n), "name": n} for n in names],
                               ensure_ascii=False, indent=2), encoding="utf-8")
    log(f"Белый список: {', '.join(names)}")


def handle_eula(ctx: Ctx) -> bool:
    accepted = ctx.args.accept_eula
    if not accepted:
        log("Для запуска нужно принять лицензионное соглашение Minecraft: https://aka.ms/MinecraftEULA")
        accepted = ask_yes_no("Вы принимаете EULA?", False)
    (ctx.server_dir / "eula.txt").write_text(f"eula={'true' if accepted else 'false'}\n")
    if not accepted:
        log("EULA не принята: перед первым запуском откройте eula.txt и поставьте eula=true")
    return accepted


# =============================================================================
#  ТУННЕЛЬ (игра с друзьями из интернета)
# =============================================================================
def tunnel_dir(ctx: Ctx) -> Path:
    d = ctx.server_dir / ".tunnel"
    d.mkdir(exist_ok=True)
    return d


def ask_tunnel_kind() -> str:
    log("\nКак друзья будут подключаться из интернета?\n"
        "  1) playit.gg — бесплатно, нужна регистрация на сайте (один раз)\n"
        "  2) Свой VPS через SSH — самый надёжный вариант, нужен арендованный сервер\n"
        "  3) Без туннеля (только одна Wi-Fi сеть или VPN вроде Tailscale)")
    ans = input("Выбор [1]: ").strip()
    return {"": "playit", "1": "playit", "2": "ssh", "3": "none"}.get(ans, "none")


def _ensure_tmux() -> None:
    if not shutil.which("tmux"):
        log("Устанавливаю tmux (нужен, чтобы туннель работал в фоне)...")
        run(["pkg", "install", "-y", "tmux"])


def _write_run_tunnel(ctx: Ctx, body: str) -> None:
    prefix = os.environ.get("PREFIX", "/data/data/com.termux/files/usr")
    f = tunnel_dir(ctx) / "run-tunnel.sh"
    f.write_text(f"#!{prefix}/bin/bash\n{body}\n")
    f.chmod(0o755)


PLAYIT_DOWNLOAD = "https://github.com/playit-cloud/playit-agent/releases/latest/download/"
# Внутри proot: подготовить папки и запустить демон playit (у версии 1.x это отдельная программа)
PLAYIT_DAEMON_CMD = "mkdir -p /etc/playit /var/log/playit /run/playit; exec /server/.tunnel/playitd"


def _fetch_playit(td: Path) -> None:
    """Playit 1.x состоит из двух программ: демон (playitd) и интерфейс (playit-cli)."""
    arch = platform.machine().lower()
    suffix = "aarch64" if arch in ("aarch64", "arm64") else "amd64"
    for local, remote in (("playitd", f"playit-linux-{suffix}"), ("playit-cli", f"playit-cli-linux-{suffix}")):
        try:
            download(PLAYIT_DOWNLOAD + remote, td / local)
        except InstallError as e:
            raise InstallError(f"{e}\nСкачайте вручную со страницы https://github.com/playit-cloud/playit-agent/releases "
                               f"файл {remote} и положите как {td / local}") from e
        (td / local).chmod(0o755)
    (td / "playit").unlink(missing_ok=True)        # старая версия скрипта скачивала не то


def _stop_playit_daemon(ctx: Ctx) -> None:
    subprocess.run(proot_cmd(ctx, ["bash", "-c", "pkill -f playitd || true"]), check=False,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def _setup_playit(ctx: Ctx) -> None:
    td = tunnel_dir(ctx)
    _ensure_tmux()
    _fetch_playit(td)

    prefix = os.environ.get("PREFIX", "/data/data/com.termux/files/usr")
    helper = Path.home() / "playit.sh"                      # команда для управления туннелем позже
    helper.write_text(f"#!{prefix}/bin/bash\n"
                      f'proot-distro login {ctx.distro} --bind "{ctx.server_dir}:/server" -- /server/.tunnel/playit-cli "$@"\n')
    helper.chmod(0o755)
    _write_run_tunnel(ctx, f'exec proot-distro login {ctx.distro} --bind "{ctx.server_dir}:/server" -- '
                           f"bash -c '{PLAYIT_DAEMON_CMD}'")

    if not sys.stdin.isatty():
        log("Нет интерактивного терминала: привязку playit сделайте позже командой\n"
            "  python install_mc_server.py --setup-tunnel")
        return

    # справка по CLI пишется в лог — пригодится, если интерфейс у playit изменится
    run(proot_cmd(ctx, ["/server/.tunnel/playit-cli", "--help"]), capture=True, check=False)

    log("\nСейчас запущу демон playit в фоне, а затем программу playit-cli.\n"
        "ОДИН РАЗ нужно привязать её к вашему аккаунту playit.gg:\n"
        "  1. В playit-cli появится ссылка (https://playit.gg/claim/...) и/или код привязки.\n"
        "     Откройте ссылку в браузере. Если сайт просит «ввести код из программы» — введите этот код.\n"
        "  2. Войдите или зарегистрируйтесь на playit.gg, подтвердите агент.\n"
        "  3. На сайте создайте туннель: тип «Minecraft Java», локальный порт 25565.\n"
        "  4. Скопируйте адрес туннеля и выйдите из playit-cli (клавиша q или Ctrl+C).\n"
        "Позже посмотреть/изменить туннель можно командой ./playit.sh")
    input("Нажмите Enter, чтобы начать... ")

    daemon_log = open(td / "playitd.log", "ab")
    daemon = subprocess.Popen(proot_cmd(ctx, ["bash", "-c", PLAYIT_DAEMON_CMD]),
                              stdout=daemon_log, stderr=subprocess.STDOUT)
    try:
        time.sleep(4)
        if daemon.poll() is not None:
            tail = (td / "playitd.log").read_text(errors="replace")[-1500:]
            raise InstallError(f"Демон playit сразу завершился. Его вывод:\n{tail}")
        try:
            subprocess.run(proot_cmd(ctx, ["/server/.tunnel/playit-cli"]), check=False)
        except KeyboardInterrupt:
            pass
    finally:
        daemon.terminate()
        _stop_playit_daemon(ctx)
        daemon_log.close()

    addr = input("\nВставьте адрес туннеля (например abc.at.ply.gg:12345) или Enter, чтобы пропустить: ").strip()
    (td / "address.txt").write_text(addr + "\n" if addr else "")
    log("Туннель playit настроен: при ./start-mc.sh демон будет запускаться сам.")


def _setup_ssh(ctx: Ctx) -> None:
    target = ctx.args.ssh_target
    if not target and sys.stdin.isatty():
        target = input("SSH-адрес вашего VPS (user@адрес): ").strip()
    if not target or not re.fullmatch(r"[\w.-]+@[\w.:-]+", target):
        raise InstallError("Нужен адрес в формате user@host: --ssh-target user@1.2.3.4")
    remote_port = ctx.args.ssh_remote_port or ctx.args.port
    td = tunnel_dir(ctx)
    _ensure_tmux()
    if not shutil.which("ssh"):
        run(["pkg", "install", "-y", "openssh"])

    key = Path.home() / ".ssh" / "mc_tunnel"
    key.parent.mkdir(mode=0o700, exist_ok=True)
    if not key.exists():
        run(["ssh-keygen", "-t", "ed25519", "-N", "", "-C", "mc-tunnel", "-f", str(key)])
    pub = key.with_suffix(".pub") if key.suffix else Path(str(key) + ".pub")
    pub_line = pub.read_text().strip()
    log("Копирую ключ на VPS (спросит пароль от VPS один раз)...")
    remote = ("mkdir -p ~/.ssh && chmod 700 ~/.ssh && touch ~/.ssh/authorized_keys && "
              f"(grep -qF {shlex.quote(pub_line)} ~/.ssh/authorized_keys || echo {shlex.quote(pub_line)} >> ~/.ssh/authorized_keys) "
              "&& chmod 600 ~/.ssh/authorized_keys")
    r = subprocess.run(["ssh", "-o", "StrictHostKeyChecking=accept-new", target, remote], check=False)
    if r.returncode != 0:
        raise InstallError("Не удалось подключиться к VPS по SSH. Проверьте адрес, пароль и что порт 22 открыт.")

    _write_run_tunnel(ctx, (
        "while true; do\n"
        f'  ssh -N -i "{key}" -o StrictHostKeyChecking=accept-new -o ExitOnForwardFailure=yes \\\n'
        "      -o ServerAliveInterval=20 -o ServerAliveCountMax=3 \\\n"
        f"      -R 0.0.0.0:{remote_port}:127.0.0.1:{ctx.args.port} {target}\n"
        '  echo "SSH-туннель оборвался, переподключение через 5 секунд..."; sleep 5\n'
        "done"))
    host = target.split("@", 1)[1]
    (td / "address.txt").write_text(f"{host}:{remote_port}\n")
    log("SSH-туннель настроен. На VPS (один раз, от root) должно быть сделано:\n"
        '  echo "GatewayPorts clientspecified" >> /etc/ssh/sshd_config\n'
        "  systemctl restart ssh || systemctl restart sshd\n"
        f"  ufw allow {remote_port}/tcp      # если используется файрвол; у некоторых хостеров порт открывают в панели\n"
        f"Друзья подключаются по адресу: {host}:{remote_port}")


def setup_tunnel(ctx: Ctx, kind: str) -> None:
    run_script = ctx.server_dir / ".tunnel" / "run-tunnel.sh"
    if kind == "none":
        run_script.unlink(missing_ok=True)
        log("Туннель отключён.")
    elif kind == "playit":
        _setup_playit(ctx)
    elif kind == "ssh":
        _setup_ssh(ctx)


def tunnel_address(ctx: Ctx) -> str:
    f = ctx.server_dir / ".tunnel" / "address.txt"
    return f.read_text().strip() if f.exists() else ""


# =============================================================================
#  ИСПРАВЛЕНИЕ ПОСЛЕ ПАДЕНИЯ: моды, которые не загрузились на сервере
# =============================================================================
FAILED_MOD_RE = re.compile(
    r"-\s+(.+?)\s+\(([\w.\-]+)\)\s+(?:has failed to load correctly|encountered an error while dispatching[^\r\n]*?event)\s+([^\r\n]+)")


def jar_mod_ids(jar: Path) -> set[str]:
    try:
        with zipfile.ZipFile(jar) as z:
            for name in ("META-INF/neoforge.mods.toml", "META-INF/mods.toml"):
                if name in z.namelist():
                    text = z.read(name).decode("utf-8", "replace")
                    return set(re.findall(r'modId\s*=\s*["\']([^"\']+)["\']', text))
    except (zipfile.BadZipFile, OSError):
        pass
    return set()


def fix_failed_mods(server_dir: Path, assume_yes: bool = False) -> int:
    """Читает последний лог/краш-репорт и переносит упавшие моды в mods-client-disabled/."""
    sources = [server_dir / "logs" / "latest.log"]
    crashes = sorted((server_dir / "crash-reports").glob("crash-*.txt"), key=lambda f: f.stat().st_mtime) \
        if (server_dir / "crash-reports").is_dir() else []
    if crashes:
        sources.append(crashes[-1])
    found: dict[str, tuple[str, str]] = {}
    for src in sources:
        if src.exists():
            for m in FAILED_MOD_RE.finditer(src.read_text(encoding="utf-8", errors="replace")):
                found.setdefault(m.group(2), (m.group(1), m.group(3).strip()))
    if not found:
        log("В логах не найдено упавших модов. Пришлите мне текст ошибки из консоли.")
        return 0

    mods = server_dir / "mods"
    by_jar: dict[Path, list[str]] = {}
    for jar in mods.glob("*.jar"):
        hit = jar_mod_ids(jar) & set(found)
        if hit:
            by_jar[jar] = sorted(hit)
    log("Моды, которые не загрузились на сервере:")
    for mid, (name, reason) in found.items():
        log(f"  - {name} ({mid}): {reason[:110]}")
    if not by_jar:
        log("Не удалось сопоставить их с файлами в mods/. Найдите jar по названию вручную.")
        return 0
    log("\nФайлы, которые будут перенесены в mods-client-disabled/:")
    for jar in by_jar:
        log(f"  {jar.name}")
    if not ask_yes_no("Отключить эти моды?", True, assume_yes):
        return 0
    quarantine = server_dir / "mods-client-disabled"
    quarantine.mkdir(exist_ok=True)
    for jar in by_jar:
        shutil.move(str(jar), quarantine / jar.name)
    log("Готово. Запустите сервер снова: ./start-mc.sh\n"
        "Если упадёт на другом моде — повторите: python install_mc_server.py --fix-mods")
    return len(by_jar)


def autofix_loop(ctx: Ctx, rounds: int = 8) -> bool:
    """Запуск -> падение -> отключение виноватых модов -> снова запуск (до `rounds` раз)."""
    eula = ctx.server_dir / "eula.txt"
    if not eula.exists() or "eula=true" not in eula.read_text():
        raise InstallError("Сначала примите EULA: в файле eula.txt должно быть eula=true")
    for i in range(1, rounds + 1):
        log(f"\n=== Попытка запуска {i}/{rounds} ===")
        if test_run(ctx):
            log("\nСервер запустился без ошибок и был остановлен. Теперь запускайте: ./start-mc.sh")
            return True
        if fix_failed_mods(ctx.server_dir, True) == 0:
            log("\nАвтоматически отключать больше нечего. Пришлите мне последний текст ошибки.")
            return False
    log("\nДостигнут предел попыток. Запустите команду ещё раз или пришлите текст ошибки.")
    return False


# =============================================================================
#  ГОТОВЫЙ МИР
# =============================================================================
def set_property(path: Path, key: str, value: str) -> None:
    lines = path.read_text(encoding="utf-8").splitlines() if path.exists() else []
    for i, ln in enumerate(lines):
        if ln.split("=", 1)[0].strip() == key and not ln.startswith("#"):
            lines[i] = f"{key}={value}"
            break
    else:
        lines.append(f"{key}={value}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _find_world_root(base: Path) -> Path | None:
    for pattern in ("level.dat", "*/level.dat", "*/*/level.dat"):
        for f in sorted(base.glob(pattern)):
            return f.parent
    return None


def _remap_player(world: Path, nick: str, old_uuid: str | None) -> None:
    """Переименовывает файлы игрока под UUID, который сервер выдаёт нику в offline-режиме."""
    pd = world / "playerdata"
    files = sorted(pd.glob("*.dat")) if pd.is_dir() else []
    new = offline_uuid(nick)
    if old_uuid:
        old = old_uuid.strip().lower()
    elif len(files) == 1:
        old = files[0].stem
    elif not files:
        log("В мире нет папки playerdata с данными игрока — инвентарь перенести нельзя.")
        return
    else:
        log("В мире несколько игроков, укажите нужного: --world-old-uuid <UUID> из списка:")
        for f in files:
            log(f"  {f.stem}")
        return
    if old == new:
        log("Данные игрока уже привязаны к этому нику.")
        return
    moved = 0
    for sub, ext in (("playerdata", ".dat"), ("playerdata", ".dat_old"), ("stats", ".json"), ("advancements", ".json")):
        src, dst = world / sub / f"{old}{ext}", world / sub / f"{new}{ext}"
        if src.exists() and not dst.exists():
            src.rename(dst)
            moved += 1
    log(f"Данные игрока перепривязаны к нику {nick} (файлов: {moved})" if moved else
        f"Файлы игрока {old} не найдены — ничего не переименовано.")


def import_world(server_dir: Path, source: str, nick: str | None = None, old_uuid: str | None = None) -> None:
    src = Path(source).expanduser()
    if not src.exists() and str(src).startswith(("/sdcard", "/storage")):
        ensure_storage_access()
    if not src.exists():
        raise InstallError(f"Не найден: {src}")

    props = server_dir / "server.properties"
    level = "world"
    if props.exists():
        for ln in props.read_text(encoding="utf-8").splitlines():
            if ln.startswith("level-name="):
                level = ln.split("=", 1)[1].strip() or "world"

    tmp = None
    if src.is_file():
        if not zipfile.is_zipfile(src):
            raise InstallError("Это не zip-архив и не папка.")
        tmp = server_dir / ".world-import-tmp"
        shutil.rmtree(tmp, ignore_errors=True)
        log("Распаковываю архив мира...")
        with zipfile.ZipFile(src) as zf:
            _copy_prefix(zf, "", tmp, use_exclude=False)
        base = tmp
    else:
        base = src
    root = _find_world_root(base)
    if root is None:
        shutil.rmtree(tmp, ignore_errors=True) if tmp else None
        raise InstallError("Не найден level.dat: укажите папку мира (внутри неё должен лежать level.dat) или zip с ней.")

    target = server_dir / level
    if target.exists():
        backup = server_dir / f"{level}.backup-{time.strftime('%Y%m%d-%H%M%S')}"
        n = 1
        while backup.exists():                    # на случай двух запусков в одну секунду
            n += 1
            backup = server_dir / f"{level}.backup-{time.strftime('%Y%m%d-%H%M%S')}-{n}"
        target.rename(backup)
        log(f"Прежний мир сохранён как {backup.name}")
    log(f"Копирую мир из {root} ...")
    if tmp:
        shutil.move(str(root), str(target))
        shutil.rmtree(tmp, ignore_errors=True)
    else:
        shutil.copytree(root, target)
    (target / "session.lock").unlink(missing_ok=True)
    set_property(props, "level-name", level)
    log(f"Мир установлен в {target} (level-name={level})")
    if nick:
        _remap_player(target, nick, old_uuid)


# =============================================================================
#  ЭТАП 9. ТЕСТОВЫЙ ЗАПУСК
# =============================================================================
def test_run(ctx: Ctx, timeout: int = 1200) -> bool:
    log("Запускаю сервер для проверки (ждём строку «Done», потом остановим)...")
    p = subprocess.Popen(proot_cmd(ctx, ["bash", "/server/start.sh"]), stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, errors="replace", bufsize=1)
    timer = threading.Timer(timeout, p.kill)
    timer.start()
    ok = stopped = False
    try:
        assert p.stdout is not None and p.stdin is not None
        for line in p.stdout:
            sys.stdout.write(line)
            if _log_fh:
                _log_fh.write(line)
            if not stopped and re.search(r"Done \([\d.,]+s\)!", line):
                ok = stopped = True
                p.stdin.write("stop\n")
                p.stdin.flush()
        p.wait(timeout=60)
    except subprocess.TimeoutExpired:
        p.kill()
    finally:
        timer.cancel()
    return ok


# =============================================================================
#  ГЛАВНЫЙ СЦЕНАРИЙ
# =============================================================================
def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Установка Minecraft-сервера из сборки Prism Launcher (Termux + proot-distro)")
    ap.add_argument("zip", nargs="?", help="путь к zip/mrpack архиву сборки")
    ap.add_argument("--dir", type=Path, default=DEFAULT_SERVER_DIR, help=f"папка сервера (по умолчанию {DEFAULT_SERVER_DIR})")
    ap.add_argument("--distro", default=DEFAULT_DISTRO, help="дистрибутив proot-distro (по умолчанию ubuntu)")
    ap.add_argument("--java", type=int, help="принудительно выбрать версию Java (8/17/21/25)")
    ap.add_argument("--ram", help="память под сервер, например 4G или 4096")
    ap.add_argument("--port", type=int, default=25565)
    ap.add_argument("--online-mode", choices=["true", "false"],
                    help="false (по умолчанию) — пускать и пиратов; true — только лицензионные аккаунты")
    ap.add_argument("--whitelist", help="пускать только эти ники, через запятую: Вася,Петя")

    g = ap.add_argument_group("настройки сервера (server.properties)")
    g.add_argument("--configure", action="store_true",
                   help="изменить настройки уже установленного сервера (без флагов — задаст вопросы)")
    g.add_argument("--motd", help="описание сервера в списке серверов")
    g.add_argument("--max-players", type=int, dest="max_players", help="максимум игроков (по умолчанию 20)")
    g.add_argument("--difficulty", choices=["peaceful", "easy", "normal", "hard"])
    g.add_argument("--gamemode", choices=["survival", "creative", "adventure", "spectator"])
    g.add_argument("--view-distance", type=int, dest="view_distance", help="дальность прорисовки, 2–32 (у нас по умолчанию 8)")
    g.add_argument("--simulation-distance", type=int, dest="simulation_distance", help="дальность симуляции, 2–32 (по умолчанию 6)")
    g.add_argument("--pvp", choices=["true", "false"])
    g.add_argument("--allow-flight", choices=["true", "false"], dest="allow_flight",
                   help="не кикать за полёт (нужно некоторым модам: джетпаки, крылья)")
    g.add_argument("--spawn-protection", type=int, dest="spawn_protection", help="радиус защиты спавна (0 — выключить)")
    g.add_argument("--level-seed", dest="level_seed", help="сид нового мира (на готовый мир не влияет)")
    g.add_argument("--level-name", dest="level_name", help="имя папки мира (по умолчанию world)")
    g.add_argument("--set", action="append", metavar="КЛЮЧ=ЗНАЧЕНИЕ",
                   help="любая другая настройка, можно несколько раз: --set enable-command-block=true")

    ap.add_argument("--tunnel", choices=["none", "playit", "ssh"], help="тип туннеля для игры из интернета")
    ap.add_argument("--fix-mods", action="store_true",
                    help="после падения сервера: найти в логе моды, которые не загрузились (обычно клиентские), и отключить их")
    ap.add_argument("--import-world", metavar="ПУТЬ", help="использовать готовый мир: папка с level.dat или zip-архив мира")
    ap.add_argument("--world-player", metavar="НИК", help="с --import-world: привязать сохранённый инвентарь/прогресс к этому нику")
    ap.add_argument("--world-old-uuid", metavar="UUID", help="с --world-player: UUID старого игрока (если в мире их несколько)")
    ap.add_argument("--autofix", action="store_true",
                    help="вместе с --fix-mods: запускать сервер и отключать упавшие моды по кругу, пока не запустится")
    ap.add_argument("--setup-tunnel", action="store_true", help="только настроить/сменить туннель (сервер уже установлен)")
    ap.add_argument("--ssh-target", help="для --tunnel ssh: user@адрес-вашего-VPS")
    ap.add_argument("--ssh-remote-port", type=int, help="для --tunnel ssh: порт на VPS (по умолчанию как --port)")
    ap.add_argument("--accept-eula", action="store_true", help="принять Minecraft EULA")
    ap.add_argument("--test-run", action="store_true", help="после установки проверить запуск сервера")
    ap.add_argument("--clean", action="store_true", help="удалить старые mods/config перед установкой")
    ap.add_argument("--keep-client-mods", action="store_true", help="не отсеивать клиентские моды")
    ap.add_argument("-y", "--yes", action="store_true", help="отвечать «да» на все вопросы")
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    server_dir = args.dir.expanduser().resolve()

    if shutil.which("termux-wake-lock"):
        subprocess.run(["termux-wake-lock"], check=False)     # чтобы Android не усыпил Termux
    try:
        server_dir.mkdir(parents=True, exist_ok=True)
        open_log(server_dir / "install.log")

        # ---------- режим «изменить настройки» ----------
        if args.configure:
            configure_server(args, server_dir)
            return 0

        # ---------- режим «подставить готовый мир» ----------
        if args.import_world:
            import_world(server_dir, args.import_world, args.world_player, args.world_old_uuid)
            log("Готово. Запустите сервер: ./start-mc.sh")
            return 0

        # ---------- режим «починить упавшие моды» ----------
        if args.fix_mods:
            if not (server_dir / "mods").is_dir():
                raise InstallError(f"В {server_dir} нет папки mods — сервер ещё не установлен.")
            if args.autofix:
                autofix_loop(Ctx(args, Path(), server_dir, args.distro, None))
            else:
                fix_failed_mods(server_dir, args.yes)
            return 0

        # ---------- режим «только туннель» ----------
        if args.setup_tunnel:
            if not (server_dir / "start.sh").exists():
                raise InstallError(f"В {server_dir} ещё не установлен сервер. Сначала запустите установку.")
            ctx = Ctx(args, Path(), server_dir, args.distro, None)
            kind = args.tunnel or (ask_tunnel_kind() if sys.stdin.isatty() else "none")
            setup_tunnel(ctx, kind)
            addr = tunnel_address(ctx)
            log(f"\nГотово. Адрес для друзей: {addr or 'смотрите в окне playit (tmux attach -t mc-tunnel)'}")
            return 0

        # ---------- полная установка ----------
        zip_path = choose_archive(args.zip)
        total_steps = 10 + (1 if args.test_run else 0)

        step(1, total_steps, "Проверка окружения")
        check_environment(zip_path, server_dir)

        step(2, total_steps, "Анализ архива сборки")
        pack = analyze_pack(zip_path)
        ctx = Ctx(args, zip_path, server_dir, args.distro, pack)
        ctx.java_major = args.java or required_java(pack.mc)
        ctx.xmx, ctx.xms = pick_ram(args, pack)
        log(f"Сборка: {pack.name} [{pack.kind}]")
        log(f"Minecraft {pack.mc}, загрузчик: {pack.loader or 'vanilla'} {pack.loader_ver or ''}")
        log(f"Java: {ctx.java_major}, память сервера: {ctx.xmx} МБ")

        step(3, total_steps, "proot-distro и дистрибутив")
        ensure_proot_distro()
        ensure_distro(ctx)

        step(4, total_steps, f"Java {ctx.java_major}")
        ensure_java(ctx)

        step(5, total_steps, "Распаковка сборки")
        extract_pack(ctx)

        step(6, total_steps, "Отсев клиентских модов")
        if args.keep_client_mods:
            log("Пропущено (--keep-client-mods)")
        else:
            moved = filter_client_mods(server_dir)
            for name in moved:
                log(f"  отключён: {name}")
            log(f"Перенесено в mods-client-disabled/: {len(moved)}")

        step(7, total_steps, "Установка загрузчика / ядра сервера")
        install_loader(ctx)

        step(8, total_steps, "Настройка сервера")
        write_start_scripts(ctx)
        configure_properties(ctx)
        write_whitelist(ctx)
        eula_ok = handle_eula(ctx)

        step(9, total_steps, "Туннель для игры из интернета")
        already = (server_dir / ".tunnel" / "run-tunnel.sh").exists()
        if args.tunnel:
            setup_tunnel(ctx, args.tunnel)
        elif already:
            log("Туннель уже настроен (изменить: python install_mc_server.py --setup-tunnel)")
        elif sys.stdin.isatty():
            setup_tunnel(ctx, ask_tunnel_kind())
        else:
            log("Пропущено (задайте --tunnel playit|ssh или запустите позже с --setup-tunnel)")

        if args.test_run:
            step(10, total_steps, "Тестовый запуск")
            if not eula_ok:
                log("Пропущено: EULA не принята")
            elif test_run(ctx):
                log("\nСервер успешно запустился и был остановлен.")
            else:
                log("\nСервер не дошёл до «Done». Смотрите вывод выше и папку crash-reports/.\n"
                    "Частая причина — клиентский мод: найдите его в сообщении об ошибке и перенесите из mods/ "
                    "в mods-client-disabled/ (или наоборот, верните оттуда нужный мод).")

        step(total_steps, total_steps, "Готово")
        log(f"Папка сервера: {server_dir}")
        log("Запуск:         ./start-mc.sh        (из домашней папки Termux)")
        log("Остановка:      команда  stop  в консоли сервера")
        log(f"В одной сети:   <IP телефона>:{args.port}")
        addr = tunnel_address(ctx)
        if addr:
            log(f"Из интернета:   {addr}")
        log("Изменить настройки позже: python install_mc_server.py --configure")
        if is_offline(args):
            log("\nРежим: пиратские и лицензионные игроки допускаются (online-mode=false).\n"
                "Сервер не проверяет аккаунты — любой, кто знает адрес, может зайти под любым ником.\n"
                "Не выдавайте op по нику без белого списка (флаг --whitelist Ник1,Ник2).")
        log(f"Лог установки:  {server_dir / 'install.log'}")
        return 0
    except InstallError as e:
        log(f"\nОШИБКА: {e}")
        return 1
    except KeyboardInterrupt:
        log("\nПрервано пользователем. Скрипт можно запустить повторно — готовые шаги будут пропущены.")
        return 130
    finally:
        if shutil.which("termux-wake-unlock"):
            subprocess.run(["termux-wake-unlock"], check=False)


if __name__ == "__main__":
    sys.exit(main())
