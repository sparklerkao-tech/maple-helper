# -*- coding: utf-8 -*-
"""
楓之谷輔助小工具（外部、純畫面辨識 + 模擬按鍵）
- 顯示角色在小地圖上的座標
- 定時自動施放技能 / Buff、持續攻擊
- 路線循環：走到指定 X、爬繩、跳躍、下跳、等待、攻擊
不讀寫遊戲記憶體、不修改遊戲檔案。

熱鍵：F10 開始/暫停   F12 緊急停止
"""
import ctypes
import json
import os
import queue
import random
import re
import shutil
import subprocess
import sys
import tempfile
import threading
from collections import deque
import time
import tkinter as tk
import tkinter.font as tkfont
import hashlib
import traceback
import urllib.error
import urllib.request
import zipfile
from tkinter import ttk, messagebox, simpledialog, filedialog

import numpy as np
import cv2
from PIL import Image, ImageTk

IS_WIN = sys.platform == "win32"
if IS_WIN:
    import mss
    from ctypes import wintypes
    user32 = ctypes.windll.user32
    user32.GetForegroundWindow.restype = wintypes.HWND
    user32.GetAncestor.restype = wintypes.HWND
    user32.GetAncestor.argtypes = [wintypes.HWND, ctypes.c_uint]
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except Exception:
        try:
            user32.SetProcessDPIAware()
        except Exception:
            pass

APP_VERSION = "v4.1.8"
UPDATE_REPOSITORY = "sparklerkao-tech/maple-helper"
UPDATE_API = f"https://api.github.com/repos/{UPDATE_REPOSITORY}/releases/latest"
MODE_NAMES = {"buff": "BUFF機", "anchor": "定點掛機"}
APP_DIR = os.path.dirname(os.path.abspath(sys.argv[0]))
CONFIG_PATH = os.path.join(APP_DIR, "config.json")
MAPS_DIR = os.path.join(APP_DIR, "maps")
MAP_PROFILE_KEYS = (
    "minimap", "player_hsv_low", "player_hsv_high", "min_dot_area",
    "route", "route_loop", "patrol", "patrol_opt", "goto_tolerance", "rope_tolerance",
    "anchor", "mode", "loot", "map_macro", "map_macros", "map_macro_options",
)

# --------------------------------------------------------------------------
# 設定
# --------------------------------------------------------------------------
DEFAULT_CONFIG = {
    "window_title": "MapleStory",
    "minimap": None,  # [x, y, w, h]，相對遊戲視窗客戶區
    "player_hsv_low": [20, 120, 150],
    "player_hsv_high": [40, 255, 255],
    "min_dot_area": 2,
    "keys": {"jump": "alt", "attack": "ctrl", "left": "left", "right": "right",
             "up": "up", "down": "down"},
    "attack": {"enabled": False, "interval": 0.6},
    "buff_start_wait": 1.0,   # 開始時放完全部 Buff 後，再等幾秒才開始移動（等最後一個 Buff 動作結束）
    "rope_prehold": True,     # 快走到繩子時先按住上（不用跳的繩子），到繩下馬上抓住
    "rope_prehold_dist": 4,   # 距離繩子幾格（小地圖 px）內開始先按住上
    "skills": [
        {"name": "Buff 範例", "key": "home", "interval": 180, "enabled": False, "delay": 0.8},
    ],
    "route": [],
    "route_loop": True,
    "mode": "route",  # "route" 照順序 / "random" 隨機巡邏
    "map_macro": None,  # 此地圖的完整鍵盤錄製（BUFF 機循環播放）
    "map_macros": [],    # 多條完整錄製路線；BUFF 機每輪隨機選一條
    # record：完全照錄製時的按鍵／點擊播放；guarded：另外用小地圖座標監看偏移，偏太久即暫停。
    "map_macro_options": {"play_mode": "record", "position_tolerance": 10},
    "patrol": [],     # {"type": "point"|"rope", "x", "y", "lands_y"(爬繩後落點，自動學習)}
    "patrol_opt": {"attack_min": 3, "attack_max": 8, "stay_min": 0.0, "stay_max": 2.0,
                   "x_jitter": 4, "plat_tol": 4, "rope_as_target": True},
    "goto_tolerance": 3,
    "rope_tolerance": 1,
    "only_when_focused": True,
    "diagnostics": False,          # 記錄診斷資料（小地圖影片＋按鍵與座標紀錄）
    "key_repeat": True,            # 按住的鍵持續送出訊號（模擬實體鍵盤按住）
    "minimize_on_start": True,     # 按開始時縮小本工具並切到遊戲
    "restore_on_pause": True,      # 暫停／停止時還原本工具視窗
    "hotkeys": {"toggle": "f10", "stop": "f12", "record": "f8"},
    "topmost": False,
    "yolo_dataset": {"interval_sec": 2.0},  # AI 資料收集的自動截圖間隔
    "yolo": {
        "enabled": True,
        "model": "yolo_data/models/monster_current_map_v2.pt",
        "confidence": 0.45,
        "imgsz": 960,
        # 路線爬繩時，先用畫面上的 YOLO 繩子框做最後對位；沒有結果會自動退回原本的小地圖／微調流程。
        "rope_assist": True,
        # 各類別信心門檻（低於門檻的框不採用）；道具與繩子的信心通常比怪物、人物低
        "class_conf": {"monster": 0.45, "item": 0.35, "rope": 0.25, "player": 0.45},
    },
    "lie_detector": {"enabled": True, "threshold": 0.8, "beep": True},
    "elite": {
        "enabled": False,
        "threshold": 0.8,
        "end_sec": 3.0,        # 畫面上看不到菁英特徵幾秒後，視為結束
        "max_sec": 180,        # 菁英模式最長持續秒數（超過就回原模式並警報）
        "turn_sec": 4.0,       # 每隔幾秒轉身一次（兩邊都打得到）；0 = 不轉身
        "attack_key": "",      # 菁英模式主攻擊鍵，空白＝用一般攻擊鍵
        "attack_interval": 0.5,
        "beep": False,
        "hold_attack": False,  # 主攻擊鍵改為按住（不連點）
        "skills": [],          # {"name", "key", "cooldown", "delay", "enabled"}
    },
    "combat": {
        "enabled": False,
        "threshold": 0.7,       # 怪物範本相似度門檻
        "tag_threshold": 0.75,  # 角色名牌相似度門檻
        "auto_detect": True,    # 無怪物範本時，以畫面動態差異偵測活動目標
        "motion_threshold": 28, # 自動偵測的畫面差異門檻（高＝較少誤判）
        "motion_min_area": 12,  # 自動偵測的最小活動區塊面積（縮小後像素）
        "scale": 0.5,           # 辨識時縮小比例（越小越快、越不準）
        "scan_interval": 0.2,
        "char_offset_y": -35,   # 角色身體中心 = 名牌上緣 + 這個值（負＝往上）
        "y_range": 60,          # 與角色高度相差多少 px 內算「同一層」
        "single": {"key": "", "range": 200, "interval": 0.5},   # key 空白＝一般攻擊鍵
        "aoe": {"key": "", "range": 250, "min_count": 3, "cooldown": 0, "delay": 0.7},
        "approach": True,       # 怪太遠就走過去
        "approach_max_sec": 4.0,    # 每一隻怪最多追幾秒
        "search_sec": 0.8,      # 沒有巡邏點時，左右找怪的單向巡查秒數；0=不移動
        "screen_per_minimap": 15,   # 遊戲畫面 px／小地圖 1 格（用來估計別層怪物的高度）
        "engage_max_sec": 40,   # 單次交戰最長秒數（防止一直打背景誤判）
        "always_face": False,   # 每次攻擊前都按一次方向鍵
        "fallback_blind": True, # 攻擊點沒看到怪時，照舊盲打
    },
    "loot": {
        "key": "z",             # 撿物鍵
        "enabled": True,        # 撿物總開關；關閉時 BUFF 機只移動（不連點、不走去撿、不掃地）
        "auto_tap": True,       # BUFF機模式下持續連點撿物鍵
        "tap_interval": 0.12,
        "threshold": 0.7,       # 物品範本相似度門檻
        "scale": 1.0,           # 物品很小，預設用原尺寸辨識
        "y_range": 70,          # 與角色高度差多少 px 內算同一層
        "range": 1000,          # 多遠以內的物品會走過去撿（畫面 px）
        "pick_radius": 15,      # 物品與角色水平距離小於這個值就算站在物品上
        "max_tries": 3,         # 同一個位置撿幾次撿不起來就放棄（30 秒內不再理會）
        "sweep_sec": 0.5,       # 到巡邏點後左右掃地的秒數（0 = 不掃）
    },
    "anchor": {
        "x": None, "y": None,   # （舊版單一定點，會自動轉成 points）
        "points": [],           # 多個定點 [[x, y], ...]
        "rotate_min": 60,       # 每個定點停留秒數（隨機，最少）
        "rotate_max": 120,      #                    （最多）
        "random_order": True,   # 隨機挑下一個點；否則依序輪流
        "hold_key": "shift",    # 一直按住的鍵（例如範圍技）
        "repeat": True,         # 按住期間持續送出按下訊號（模擬鍵盤連發）
        "tol_x": 4,             # 左右偏離幾 px 算離開定點
        "drift_sec": 0.6,       # 離開定點多久才回去（避免被擊退一下就移動）
        "release_for_buff": True,
        "turn_sec": 0,          # 每隔幾秒轉身一次；0 = 不轉
    },
    "red_dot": {
        "enabled": True,
        "pause": True,          # 出現紅點時是否暫停自動
        "beep": True,
        "min_area": 2,
        "max_area": 12,
        "max_size": 5,
        "confirm_sec": 0.3,     # 連續出現多久才算（避免閃一下就誤報）
        "ranges": [[[0, 150, 150], [8, 255, 255]], [[172, 150, 150], [179, 255, 255]]],
    },
}

TEMPLATE_DIR = os.path.join(APP_DIR, "templates")
ELITE_DIR = os.path.join(TEMPLATE_DIR, "elite")
MON_DIR = os.path.join(TEMPLATE_DIR, "monsters")
TAG_DIR = os.path.join(TEMPLATE_DIR, "char")
TAG_PATH = os.path.join(TAG_DIR, "nametag.png")
ITEM_DIR = os.path.join(TEMPLATE_DIR, "items")
ROPE_DIR = os.path.join(TEMPLATE_DIR, "ropes")
YOLO_DATA_DIR = os.path.join(APP_DIR, "yolo_data")
YOLO_IMAGES_DIR = os.path.join(YOLO_DATA_DIR, "images")
YOLO_LABELS_DIR = os.path.join(YOLO_DATA_DIR, "labels")
YOLO_INBOX_DIR = os.path.join(YOLO_DATA_DIR, "把圖片丟這裡")          # 使用者自己截的圖丟進來，一鍵匯入
YOLO_AUTO_LIST = os.path.join(YOLO_DATA_DIR, "auto_labeled.txt")     # 模型自動標註、還沒人工確認的圖片
IMAGE_EXTS = (".png", ".jpg", ".jpeg", ".bmp", ".webp")
VIDEO_EXTS = (".mp4", ".mkv", ".avi", ".mov", ".wmv", ".flv", ".webm")
YOLO_CLASS_NAMES = ("monster", "item", "rope", "player")
YOLO_CLASS_LABELS = ("怪物", "道具", "繩子", "人物")
YOLO_CLASS_COLORS = ("#00ff66", "#ff4fd8", "#ffb000", "#00d9ff")
# 內建 YOLO 模型（怪物／道具／繩子／人物四類）。一鍵更新不會覆蓋已存在的模型檔（可能是自己訓練的），
# 所以模型另外用這組資訊檢查與下載：SHA-256 不同且缺少繩子／道具類別時，會詢問是否更新（舊檔備份成 .bak）。
BUILTIN_MODEL = {
    "file": "monster_current_map_v2.pt",
    "version": "map_multiclass_v4",
    "sha256": "18443e6e2cfa60229b91349ccf5d281f2153d794e9815196fb56961f56cf9047",
    "url": "https://github.com/sparklerkao-tech/maple-helper/releases/download/v4.1.8/monster_current_map_v2.pt",
}


def file_sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


ROPE_DX_MAX = 40      # 抓得到繩子時，名牌中心與 YOLO 繩子中心最多差幾 px（超過就是量錯）
ALIGN_MAX_PX = 50     # 走到小地圖位置後，畫面對位最多修正幾 px；更遠表示對到別條繩子
YOLO_CLASS_CONF_DEFAULT = {"monster": 0.45, "item": 0.35, "rope": 0.25, "player": 0.45}


def imread_unicode(path):
    data = np.fromfile(path, dtype=np.uint8)
    return cv2.imdecode(data, cv2.IMREAD_COLOR)


def imwrite_unicode(path, img):
    ok, buf = cv2.imencode(".png", img)
    if ok:
        buf.tofile(path)
    return ok


def new_template_path(folder, prefix):
    """產生不重複的範本檔名，避免同一秒連續新增時覆寫既有範本。"""
    os.makedirs(folder, exist_ok=True)
    stem = f"{prefix}_{time.time_ns()}"
    path = os.path.join(folder, stem + ".png")
    n = 2
    while os.path.exists(path):
        path = os.path.join(folder, f"{stem}_{n}.png")
        n += 1
    return path


def load_templates(folder=None):
    """讀取資料夾中的範本（灰階）。預設＝測謊範本；菁英怪範本在 templates/elite"""
    folder = folder or TEMPLATE_DIR
    out = []
    if os.path.isdir(folder):
        for fn in sorted(os.listdir(folder)):
            if fn.lower().endswith(".png"):
                img = imread_unicode(os.path.join(folder, fn))
                if img is not None:
                    out.append((fn, cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)))
    return out


def match_any(screen_bgr, templates, threshold):
    """在畫面中找任一範本，回傳 (檔名, 分數) 或 None"""
    gray = cv2.cvtColor(screen_bgr, cv2.COLOR_BGR2GRAY)
    best = None
    for name, t in templates:
        if t.shape[0] > gray.shape[0] or t.shape[1] > gray.shape[1]:
            continue
        score = float(cv2.minMaxLoc(cv2.matchTemplate(gray, t, cv2.TM_CCOEFF_NORMED))[1])
        if score >= threshold and (best is None or score > best[1]):
            best = (name, score)
    return best


def deep_merge(base, user):
    """把使用者設定遞迴合併進預設值：舊版設定缺少的新欄位會補上預設值"""
    for k, v in user.items():
        if isinstance(v, dict) and isinstance(base.get(k), dict):
            deep_merge(base[k], v)
        else:
            base[k] = v
    return base


def load_config():
    cfg = json.loads(json.dumps(DEFAULT_CONFIG))
    if os.path.exists(CONFIG_PATH):
        try:
            with open(CONFIG_PATH, "r", encoding="utf-8-sig") as f:
                user = json.load(f)
            if not isinstance(user, dict):
                raise ValueError("設定檔最外層必須是物件")
            deep_merge(cfg, user)
        except (json.JSONDecodeError, UnicodeDecodeError, ValueError) as e:
            # 保留原檔，避免下一次儲存把仍可人工救回的設定直接覆寫掉。
            stamp = time.strftime("%Y%m%d-%H%M%S") + f"-{time.time_ns() % 1_000_000_000:09d}"
            backup = os.path.join(APP_DIR, f"config.corrupt-{stamp}.json")
            try:
                os.replace(CONFIG_PATH, backup)
                log(f"設定檔格式錯誤，已備份至：{backup}", "error")
            except OSError as backup_error:
                log(f"設定檔格式錯誤，但備份失敗：{backup_error}", "error")
            log(f"讀取設定失敗（改用預設值）：{e}", "error")
        except OSError as e:
            log(f"讀取設定失敗（改用預設值）：{e}", "error")
    # v3.8 起主畫面只保留定點掛機與 BUFF 機；舊模式安全回到定點掛機。
    if cfg.get("mode") not in ("anchor", "buff"):
        cfg["mode"] = "anchor"
    # 自動戰鬥暫時不對外提供，避免隱藏功能仍在背景掃描或輸入。
    cfg.setdefault("combat", {})["enabled"] = False
    return cfg


def migrate_config(cfg):
    # 清掉明顯錯誤的繩子資料：落點沒有比繩子底部高、錄製的終點沒有比起點高（被撞下來或太早結束）
    tol = int(cfg.get("patrol_opt", {}).get("plat_tol", 4))
    for r in cfg.get("patrol", []):
        if r.get("type") != "rope":
            continue
        mac = r.get("macro")
        if mac and (not mac.get("start") or not mac.get("end") or mac["end"][1] >= mac["start"][1] - tol):
            r.pop("macro", None)
            r["macro_invalid"] = True
        if r.get("lands_y") is not None and r["lands_y"] >= r["y"] - tol:
            r.pop("lands_y", None)
    a = cfg.get("anchor", {})
    if not a.get("points") and a.get("x") is not None:
        a["points"] = [[a["x"], a["y"]]]
    if cfg.get("mode") not in ("anchor", "buff"):
        cfg["mode"] = "anchor"
    # 舊版只有一條 map_macro。升級後自動把它保留為第一條隨機路線。
    routes = cfg.setdefault("map_macros", [])
    legacy = cfg.get("map_macro")
    if not routes and isinstance(legacy, dict) and legacy.get("events"):
        routes.append(legacy)
    cfg["map_macros"] = [r for r in routes if isinstance(r, dict) and r.get("events")]
    if cfg["map_macros"]:
        cfg["map_macro"] = cfg["map_macros"][0]  # 保留相容舊版讀取位置
    cfg.setdefault("combat", {})["enabled"] = False
    # v3.8.6 起錄製結束改用 F8；先前預設的 F10 自動轉換，仍可在手動校正頁改回其他 F 鍵。
    hotkeys = cfg.setdefault("hotkeys", {})
    if hotkeys.get("toggle") in (None, "f9"):
        hotkeys["toggle"] = "f10"
    if hotkeys.get("record") in (None, "f10"):
        hotkeys["record"] = "f8"
    # v4.0.2 起預設不置頂，避免設定視窗長時間遮住遊戲；使用者仍可在設定頁手動開啟。
    if not cfg.get("topmost_preference_migrated"):
        cfg["topmost"] = False
        cfg["topmost_preference_migrated"] = True
    return cfg


_SAVE_LOCK = threading.Lock()
LOG_DIR = os.path.join(APP_DIR, "logs")
LOG_KEEP_DAYS = 14


class EventLog:
    """全程式共用的日誌：寫到 logs/日期.log，並通知介面（任何執行緒都可呼叫）"""

    def __init__(self):
        self.lock = threading.Lock()
        self.recent = deque(maxlen=600)
        self.listeners = []
        self._cleaned = False

    @staticmethod
    def stamp(t=None):
        lt = time.localtime(t)
        return f"[{lt.tm_year}/{lt.tm_mon}/{lt.tm_mday} {time.strftime('%H:%M:%S', lt)}]"

    def _cleanup(self):
        self._cleaned = True
        try:
            cutoff = time.time() - LOG_KEEP_DAYS * 86400
            for name in os.listdir(LOG_DIR):
                path = os.path.join(LOG_DIR, name)
                if name.endswith(".log") and os.path.getmtime(path) < cutoff:
                    os.remove(path)
        except OSError:
            pass

    def write(self, msg, level="info"):
        msg = str(msg).replace("\r", "").strip()
        if not msg:
            return
        line = f"{self.stamp()} {msg}"
        with self.lock:
            self.recent.append((line, level))
            try:
                os.makedirs(LOG_DIR, exist_ok=True)
                if not self._cleaned:
                    self._cleanup()
                tag = {"error": "錯誤", "warn": "注意"}.get(level)
                with open(os.path.join(LOG_DIR, time.strftime("%Y-%m-%d") + ".log"), "a", encoding="utf-8") as f:
                    f.write((line if not tag else f"{line} 〔{tag}〕") + "\n")
            except OSError:
                pass
            listeners = list(self.listeners)
        for fn in listeners:
            try:
                fn(line, level)
            except Exception:
                pass


EVENT_LOG = EventLog()


def log(msg, level="info"):
    EVENT_LOG.write(msg, level)


def log_exception(prefix, exc=None):
    """記錄錯誤訊息＋完整追蹤（追蹤只寫進檔案的下一行，畫面只顯示一行）"""
    detail = traceback.format_exc() if exc is not None else ""
    log(f"{prefix}：{exc}" if exc is not None else prefix, "error")
    if detail and "NoneType: None" not in detail:
        try:
            with EVENT_LOG.lock:
                os.makedirs(LOG_DIR, exist_ok=True)
                with open(os.path.join(LOG_DIR, time.strftime("%Y-%m-%d") + ".log"), "a", encoding="utf-8") as f:
                    f.write("".join("    " + ln + "\n" for ln in detail.rstrip().splitlines()))
        except OSError:
            pass


def save_config(cfg):
    """先寫暫存檔再取代，避免多個執行緒同時寫入或寫到一半關閉造成設定檔損毀"""
    with _SAVE_LOCK:
        tmp = CONFIG_PATH + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(cfg, f, ensure_ascii=False, indent=2)
        os.replace(tmp, CONFIG_PATH)


def version_key(value):
    """將 v3.8.1 等版本字串轉成可比較的數字元組。"""
    parts = [int(n) for n in re.findall(r"\d+", str(value))]
    return tuple((parts + [0, 0, 0])[:3])


def latest_github_release():
    """讀取公開 GitHub Release；尚未建立 Release 時回傳 None。"""
    req = urllib.request.Request(UPDATE_API, headers={
        "Accept": "application/vnd.github+json",
        "User-Agent": f"MapleHelper/{APP_VERSION}",
    })
    try:
        with urllib.request.urlopen(req, timeout=5) as response:
            data = json.load(response)
    except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, ValueError):
        return None
    if not isinstance(data, dict) or data.get("draft") or data.get("prerelease"):
        return None
    return data


def map_profile_path(name):
    """把地圖名稱轉為安全檔名；實際名稱仍保存在 JSON 裡。"""
    clean = "".join("_" if c in '<>:"/\\|?*' else c for c in name).strip(". ")
    return os.path.join(MAPS_DIR, (clean or "未命名地圖") + ".json")


def map_snapshot(cfg):
    """只擷取與地圖相關的設定，避免地圖切換覆蓋全域按鍵、技能與警報設定。"""
    return {key: json.loads(json.dumps(cfg[key], ensure_ascii=False))
            for key in MAP_PROFILE_KEYS if key in cfg}


def list_map_profiles():
    """回傳 [(名稱, 路徑)]；壞掉的地圖檔會略過，不影響工具啟動。"""
    if not os.path.isdir(MAPS_DIR):
        return []
    profiles = []
    for fn in os.listdir(MAPS_DIR):
        if not fn.lower().endswith(".json"):
            continue
        path = os.path.join(MAPS_DIR, fn)
        try:
            with open(path, "r", encoding="utf-8-sig") as f:
                data = json.load(f)
            name = str(data.get("name") or os.path.splitext(fn)[0]).strip()
            if isinstance(data.get("map"), dict) and name:
                profiles.append((name, path))
        except (OSError, ValueError, TypeError):
            continue
    return sorted(profiles, key=lambda item: item[0].casefold())


# --------------------------------------------------------------------------
# 按鍵輸入（SendInput + 掃描碼，DirectInput 遊戲才收得到）
# --------------------------------------------------------------------------
# 名稱 -> (scancode, extended)
SCANCODES = {
    "esc": (0x01, False), "1": (0x02, False), "2": (0x03, False), "3": (0x04, False),
    "4": (0x05, False), "5": (0x06, False), "6": (0x07, False), "7": (0x08, False),
    "8": (0x09, False), "9": (0x0A, False), "0": (0x0B, False), "-": (0x0C, False),
    "=": (0x0D, False), "backspace": (0x0E, False), "tab": (0x0F, False),
    "q": (0x10, False), "w": (0x11, False), "e": (0x12, False), "r": (0x13, False),
    "t": (0x14, False), "y": (0x15, False), "u": (0x16, False), "i": (0x17, False),
    "o": (0x18, False), "p": (0x19, False), "[": (0x1A, False), "]": (0x1B, False),
    "enter": (0x1C, False), "ctrl": (0x1D, False), "a": (0x1E, False), "s": (0x1F, False),
    "d": (0x20, False), "f": (0x21, False), "g": (0x22, False), "h": (0x23, False),
    "j": (0x24, False), "k": (0x25, False), "l": (0x26, False), ";": (0x27, False),
    "'": (0x28, False), "`": (0x29, False), "shift": (0x2A, False), "\\": (0x2B, False),
    "z": (0x2C, False), "x": (0x2D, False), "c": (0x2E, False), "v": (0x2F, False),
    "b": (0x30, False), "n": (0x31, False), "m": (0x32, False), ",": (0x33, False),
    ".": (0x34, False), "/": (0x35, False), "rshift": (0x36, False), "alt": (0x38, False),
    "space": (0x39, False), "f1": (0x3B, False), "f2": (0x3C, False), "f3": (0x3D, False),
    "f4": (0x3E, False), "f5": (0x3F, False), "f6": (0x40, False), "f7": (0x41, False),
    "f8": (0x42, False), "f9": (0x43, False), "f10": (0x44, False), "f11": (0x57, False),
    "f12": (0x58, False),
    "home": (0x47, True), "up": (0x48, True), "pageup": (0x49, True), "left": (0x4B, True),
    "right": (0x4D, True), "end": (0x4F, True), "down": (0x50, True), "pagedown": (0x51, True),
    "insert": (0x52, True), "delete": (0x53, True), "rctrl": (0x1D, True), "ralt": (0x38, True),
}

if IS_WIN:
    ULONG_PTR = ctypes.c_size_t

    class KEYBDINPUT(ctypes.Structure):
        _fields_ = [("wVk", wintypes.WORD), ("wScan", wintypes.WORD), ("dwFlags", wintypes.DWORD),
                    ("time", wintypes.DWORD), ("dwExtraInfo", ULONG_PTR)]

    class MOUSEINPUT(ctypes.Structure):
        _fields_ = [("dx", wintypes.LONG), ("dy", wintypes.LONG), ("mouseData", wintypes.DWORD),
                    ("dwFlags", wintypes.DWORD), ("time", wintypes.DWORD), ("dwExtraInfo", ULONG_PTR)]

    class _INPUTUNION(ctypes.Union):
        _fields_ = [("ki", KEYBDINPUT), ("mi", MOUSEINPUT)]

    class INPUT(ctypes.Structure):
        _fields_ = [("type", wintypes.DWORD), ("u", _INPUTUNION)]

VK_FKEYS = {f"f{i}": 0x6F + i for i in range(1, 13)}   # F1=0x70 … F12=0x7B

# 錄製用：按鍵名稱 -> 虛擬鍵碼（GetAsyncKeyState）
VK_NAMES = dict(VK_FKEYS)
VK_NAMES.update({chr(c).lower(): c for c in range(ord("A"), ord("Z") + 1)})
VK_NAMES.update({str(d): 0x30 + d for d in range(10)})
VK_NAMES.update({
    "ctrl": 0xA2, "rctrl": 0xA3, "alt": 0xA4, "ralt": 0xA5, "shift": 0xA0, "rshift": 0xA1,
    "space": 0x20, "enter": 0x0D, "esc": 0x1B, "tab": 0x09, "backspace": 0x08,
    "left": 0x25, "up": 0x26, "right": 0x27, "down": 0x28,
    "home": 0x24, "end": 0x23, "pageup": 0x21, "pagedown": 0x22, "insert": 0x2D, "delete": 0x2E,
    ";": 0xBA, "=": 0xBB, ",": 0xBC, "-": 0xBD, ".": 0xBE, "/": 0xBF, "`": 0xC0,
    "[": 0xDB, "\\": 0xDC, "]": 0xDD, "'": 0xDE,
})
KEYEVENTF_EXTENDEDKEY = 0x0001
KEYEVENTF_KEYUP = 0x0002
KEYEVENTF_SCANCODE = 0x0008
MOUSE_BUTTONS = {"left": 0x01, "right": 0x02, "middle": 0x04}
MOUSE_FLAGS = {
    "left": (0x0002, 0x0004),
    "right": (0x0008, 0x0010),
    "middle": (0x0020, 0x0040),
}


class InputSendError(RuntimeError):
    """Windows 拒絕 SendInput 時拋出，避免程式誤以為按鍵已送達。"""
    pass


class Keyboard:
    REPEAT_DELAY = 0.25    # 按住多久後開始連發（和 Windows 預設差不多）
    REPEAT_EVERY = 0.033   # 連發間隔（約每秒 30 次）

    def __init__(self, repeat=True):
        self.held = set()
        self.lock = threading.Lock()
        self.last_sent = {}   # 按鍵名稱 -> 最後送出時間
        self.held_since = {}
        self.repeat = repeat  # 按住的鍵持續送出「按下」訊號，像真的一直按著
        threading.Thread(target=self._repeater, daemon=True).start()

    def _repeater(self):
        last = {}
        while True:
            time.sleep(0.01)
            if not self.repeat or not self.held:
                continue
            now = time.time()
            with self.lock:
                for name in list(self.held):
                    since = self.held_since.get(name, now)
                    if now - since >= self.REPEAT_DELAY and now - last.get(name, 0) >= self.REPEAT_EVERY:
                        try:
                            self._send(name, False)
                        except Exception:
                            pass
                        last[name] = now

    on_key = None   # 診斷記錄用：on_key(name, up)

    def _send(self, name, up):
        name = name.lower().strip()
        if name not in SCANCODES:
            raise ValueError(f"不支援的按鍵：{name}")
        if self.on_key and (up or name not in self.held):
            try:
                self.on_key(name, up)
            except Exception:
                pass
        sc, ext = SCANCODES[name]
        if not IS_WIN:
            self.last_sent[name] = time.time()
            return True
        flags = KEYEVENTF_SCANCODE | (KEYEVENTF_EXTENDEDKEY if ext else 0) | (KEYEVENTF_KEYUP if up else 0)
        inp = INPUT(type=1)
        inp.u.ki = KEYBDINPUT(0, sc, flags, 0, 0)
        ctypes.set_last_error(0)
        sent = user32.SendInput(1, ctypes.byref(inp), ctypes.sizeof(INPUT))
        if sent != 1:
            # UIPI／權限不足時 Windows 常回傳 0，且不一定提供最後錯誤碼。
            err = ctypes.get_last_error()
            suffix = f"（Windows 錯誤 {err}）" if err else "（可能是權限不同或遊戲防護攔截）"
            raise InputSendError(f"按鍵「{name}」未送達{suffix}")
        self.last_sent[name] = time.time()
        return True

    def down(self, name):
        with self.lock:
            self._send(name, False)
            if name not in self.held:
                self.held_since[name] = time.time()
            self.held.add(name)

    def up(self, name):
        with self.lock:
            self._send(name, True)
            self.held.discard(name)
            self.held_since.pop(name, None)

    def tap(self, name, hold=0.05):
        self.down(name)
        time.sleep(hold)
        self.up(name)

    def release_all(self):
        for k in list(self.held):
            try:
                self.up(k)
            except Exception:
                pass


def mouse_button_at(hwnd, x, y, button, up=False):
    """在遊戲客戶區相對座標送出滑鼠按下／放開；用於全圖錄製回放。"""
    if button not in MOUSE_FLAGS:
        raise ValueError(f"不支援的滑鼠按鍵：{button}")
    if not IS_WIN or not hwnd:
        return False
    left, top, width, height = client_rect(hwnd)
    sx = max(left, min(left + max(0, width - 1), left + int(x)))
    sy = max(top, min(top + max(0, height - 1), top + int(y)))
    user32.SetCursorPos(sx, sy)
    inp = INPUT(type=0)
    inp.u.mi = MOUSEINPUT(0, 0, 0, MOUSE_FLAGS[button][1 if up else 0], 0, 0)
    ctypes.set_last_error(0)
    if user32.SendInput(1, ctypes.byref(inp), ctypes.sizeof(INPUT)) != 1:
        err = ctypes.get_last_error()
        suffix = f"（Windows 錯誤 {err}）" if err else "（可能是權限不同或遊戲防護攔截）"
        raise InputSendError(f"滑鼠「{button}」未送達{suffix}")
    return True


# --------------------------------------------------------------------------
# 視窗與畫面
# --------------------------------------------------------------------------
def list_visible_windows():
    """回傳所有可見、具有標題的最上層視窗，供手動挑選目標視窗使用。"""
    if not IS_WIN:
        return []
    result = []

    @ctypes.WINFUNCTYPE(ctypes.c_bool, wintypes.HWND, wintypes.LPARAM)
    def cb(hwnd, _):
        if user32.IsWindowVisible(hwnd):
            n = user32.GetWindowTextLengthW(hwnd)
            if n:
                buf = ctypes.create_unicode_buffer(n + 1)
                user32.GetWindowTextW(hwnd, buf, n + 1)
                if buf.value.strip():
                    result.append((hwnd, buf.value.strip()))
        return True

    user32.EnumWindows(cb, 0)
    return result


def find_window(title_part):
    title_part = (title_part or "").strip().lower()
    if not title_part:
        return None
    for hwnd, title in list_visible_windows():
        if title_part in title.lower():
            return hwnd
    return None


def client_rect(hwnd):
    """回傳遊戲視窗客戶區在螢幕上的 (left, top, w, h)"""
    r = wintypes.RECT()
    user32.GetClientRect(hwnd, ctypes.byref(r))
    pt = wintypes.POINT(0, 0)
    user32.ClientToScreen(hwnd, ctypes.byref(pt))
    return pt.x, pt.y, r.right - r.left, r.bottom - r.top


def rect_visible(rect):
    """遊戲視窗縮到最小時，Windows 會回報 (-32000, -32000, 0, 0)；這時不能截圖"""
    return bool(rect) and rect[2] > 0 and rect[3] > 0 and rect[0] > -30000 and rect[1] > -30000


def activate_window(hwnd):
    """把遊戲視窗切到前景（本工具是前景程式時，Windows 允許這麼做）"""
    if not (IS_WIN and hwnd):
        return False
    try:
        if user32.IsIconic(hwnd):
            user32.ShowWindow(hwnd, 9)   # SW_RESTORE
        return bool(user32.SetForegroundWindow(hwnd))
    except Exception:
        return False


def is_foreground(hwnd):
    return IS_WIN and hwnd and user32.GetForegroundWindow() == hwnd


def player_candidates(minimap_bgr, low, high, min_area=2):
    """小地圖上所有符合角色顏色的色塊：[(x, y, 面積), ...]"""
    hsv = cv2.cvtColor(minimap_bgr, cv2.COLOR_BGR2HSV)
    mask = cv2.inRange(hsv, np.array(low, np.uint8), np.array(high, np.uint8))
    n, _, stats, cents = cv2.connectedComponentsWithStats(mask, 8)
    out = []
    for i in range(1, n):
        area = int(stats[i, cv2.CC_STAT_AREA])
        if area >= min_area:
            cx, cy = cents[i]
            out.append((int(round(cx)), int(round(cy)), area))
    return out


class PlayerTracker:
    """從多個黃色色塊中挑出角色。

    小地圖上常有固定的黃色圖示或文字。規則：
    1. 已有位置時，跟著最近的色塊（角色每幀只會移動幾格）。
    2. 但如果目前跟的色塊超過 1 秒沒動，而畫面上有「別的色塊在移動」，就改跟會動的那個
       （避免一開始黏到固定圖示後，角色怎麼走座標都不變）。
    3. 沒有歷史位置時，挑面積最接近取色時記錄的角色點大小（沒記錄時挑最小的）。
    """

    MOVE_MIN, MOVE_MAX = 1, 8   # 一幀之間「移動」的距離範圍（px）；更遠的視為新出現/消失，不算移動

    def __init__(self):
        self.pos = None
        self.prev = []
        self.last_move = 0.0
        self.missing_since = None
        self.candidates = []

    def seed(self, x, y):
        """使用者在取色時點的位置：直接指定角色"""
        self.pos = (int(x), int(y))
        self.last_move = time.time()

    @staticmethod
    def _by_area(cands, ref):
        if ref:
            return min(cands, key=lambda c: (abs(c[2] - ref), c[2]))
        return min(cands, key=lambda c: c[2])

    def update(self, cands, now=None, ref_area=None):
        now = time.time() if now is None else now
        self.candidates = cands
        if not cands:
            self.prev = []
            # 技能特效、UI 閃爍時常會讓角色點消失一兩幀。保留很短的最後位置，
            # 避免座標顯示和錄製路徑不必要地跳成「--」；超過時間仍視為找不到。
            self.missing_since = self.missing_since or now
            if self.pos is not None and now - self.missing_since <= 0.35:
                return self.pos
            self.pos = None
            return None
        self.missing_since = None
        moved = []
        if self.prev:
            for c in cands:
                d = min(max(abs(c[0] - p[0]), abs(c[1] - p[1])) for p in self.prev)
                if self.MOVE_MIN <= d <= self.MOVE_MAX:
                    moved.append(c)
        if self.pos is None:
            pick = self._by_area(moved or cands, ref_area)
        else:
            near = min(cands, key=lambda c: (c[0] - self.pos[0]) ** 2 + (c[1] - self.pos[1]) ** 2)
            dist = max(abs(near[0] - self.pos[0]), abs(near[1] - self.pos[1]))
            pick = near if dist <= 20 else self._by_area(moved or cands, ref_area)
        if moved and pick not in moved and now - self.last_move > 1.0:
            pick = self._by_area(moved, ref_area)   # 目前跟的點一直不動，別的點在動 → 那才是角色
        p = (pick[0], pick[1])
        if p != self.pos:
            self.last_move = now
        self.pos = p
        self.prev = cands
        return p


def find_player(minimap_bgr, low, high, min_area=2, previous=None, ref_area=None):
    """單張影像找角色點（相容舊程式／測試用）；即時辨識改用 PlayerTracker"""
    cands = player_candidates(minimap_bgr, low, high, min_area)
    if not cands:
        return None
    t = PlayerTracker()
    if previous is not None:
        t.pos = tuple(previous)
    return t.update(cands, ref_area=ref_area)


def find_dots(minimap_bgr, ranges, min_area=2, max_area=12, max_size=5):
    """找出小地圖上的玩家紅點；以面積與外框過濾固定紅色介面圖示。"""
    hsv = cv2.cvtColor(minimap_bgr, cv2.COLOR_BGR2HSV)
    mask = None
    for low, high in ranges:
        m = cv2.inRange(hsv, np.array(low, np.uint8), np.array(high, np.uint8))
        mask = m if mask is None else cv2.bitwise_or(mask, m)
    if mask is None:
        return []
    n, _, stats, cents = cv2.connectedComponentsWithStats(mask, 8)
    dots = []
    for i in range(1, n):
        area = int(stats[i, cv2.CC_STAT_AREA])
        w, h = int(stats[i, cv2.CC_STAT_WIDTH]), int(stats[i, cv2.CC_STAT_HEIGHT])
        # 其他玩家通常是小而近似方形的點；文字、圖示、邊框多半較大或細長。
        if not (min_area <= area <= max_area and w <= max_size and h <= max_size):
            continue
        if max(w, h) > min(w, h) * 2 + 1:
            continue
        dots.append((int(round(cents[i][0])), int(round(cents[i][1]))))
    return dots


def load_monster_templates():
    """怪物範本＋左右翻轉版本"""
    out = []
    for name, t in load_templates(MON_DIR):
        out.append((name, t))
        out.append((name + "(翻轉)", cv2.flip(t, 1)))
    return out


def load_tag_template():
    if os.path.exists(TAG_PATH):
        img = imread_unicode(TAG_PATH)
        if img is not None:
            return cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
    return None


def _rescale(img, s):
    if s == 1:
        return img
    return cv2.resize(img, (max(1, int(img.shape[1] * s)), max(1, int(img.shape[0] * s))),
                      interpolation=cv2.INTER_AREA)


def find_all(gray, templates, threshold, max_hits=40):
    """多範本找出所有符合的位置（含非極大值抑制），回傳 [(cx, cy, score, name), ...]"""
    cands = []
    for name, t in templates:
        th, tw = t.shape[:2]
        if th > gray.shape[0] or tw > gray.shape[1] or th < 4 or tw < 4:
            continue
        res = cv2.matchTemplate(gray, t, cv2.TM_CCOEFF_NORMED)
        ys, xs = np.where(res >= threshold)
        if len(xs) == 0:
            continue
        sc = res[ys, xs]
        if len(sc) > 400:
            top = np.argpartition(-sc, 400)[:400]
            ys, xs, sc = ys[top], xs[top], sc[top]
        for x, y, v in zip(xs, ys, sc):
            cands.append((float(v), x + tw / 2, y + th / 2, max(tw, th), name))
    cands.sort(key=lambda c: -c[0])
    picked = []
    for v, cx, cy, size, name in cands:
        if all(abs(cx - px) > size * 0.5 or abs(cy - py) > size * 0.5 for _, px, py, _, _ in picked):
            picked.append((v, cx, cy, size, name))
            if len(picked) >= max_hits:
                break
    return [(cx, cy, v, name) for v, cx, cy, _, name in picked]


# ---------------- 畫面精準對位（繩子） ----------------
# 小地圖 1 格≈遊戲 10～15 px，不夠抓繩子。改用遊戲畫面：
#   記錄繩子時，以角色為中心截一段「頭頂上方的繩子＋背景」當地標；
#   爬繩前在畫面上找回這個地標，和角色名牌的位置比較，就知道還差幾個 px。
def locate_char(img_bgr, tag_tpl, thr=0.65):
    """用名牌找角色：回傳 (角色中心 x, 名牌上緣 y, 名牌高, 相似度) 或 None"""
    if tag_tpl is None or img_bgr is None:
        return None
    gray = cv2.cvtColor(img_bgr, cv2.COLOR_BGR2GRAY)
    th, tw = tag_tpl.shape[:2]
    if th > gray.shape[0] or tw > gray.shape[1]:
        return None
    _, mx, _, loc = cv2.minMaxLoc(cv2.matchTemplate(gray, tag_tpl, cv2.TM_CCOEFF_NORMED))
    if mx < thr:
        return None
    return int(loc[0] + tw / 2), int(loc[1]), th, float(mx)


def make_rope_anchor(img_bgr, tag_tpl):
    """角色站在抓得到繩子的位置時呼叫：截取地標，回傳 (灰階地標, 位置資訊) 或 (None, 原因)"""
    c = locate_char(img_bgr, tag_tpl)
    if c is None:
        return None, "畫面上找不到你的名牌"
    cx, ty, th, _ = c
    H, W = img_bgr.shape[:2]
    gray = cv2.cvtColor(img_bgr, cv2.COLOR_BGR2GRAY)
    for half in (32, 48, 64):
        x0, x1 = max(0, cx - half), min(W, cx + half)
        # 優先用頭頂上方（往上的繩子）；太靠近畫面上緣就改用腳下（往下的繩子）
        top, bot = max(0, ty - 260), max(0, ty - 90)
        if bot - top < 60:
            top, bot = min(H, ty + th + 10), min(H, ty + th + 150)
        if bot - top < 40 or x1 - x0 < 30:
            continue
        crop = gray[top:bot, x0:x1]
        if float(crop.std()) >= 10:      # 要有足夠的花紋才找得回來
            return crop.copy(), {"dx": cx - x0, "dy": top - ty, "w": x1 - x0, "h": bot - top}
    return None, "角色附近的畫面太單調，找不到可用的地標"


def find_rope_anchor(img_bgr, tag_tpl, anchor_gray, meta, search=320, thr=0.55):
    """在目前畫面找回地標。回傳 (角色應該在的 x, 角色目前 x, 相似度) 或 None"""
    c = locate_char(img_bgr, tag_tpl)
    if c is None or anchor_gray is None:
        return None
    cx, ty, _, _ = c
    H, W = img_bgr.shape[:2]
    h, w = anchor_gray.shape[:2]
    y0 = max(0, ty + int(meta["dy"]) - 60)
    y1 = min(H, ty + int(meta["dy"]) + h + 60)
    x0 = max(0, cx - search)
    x1 = min(W, cx + search)
    if y1 - y0 < h or x1 - x0 < w:
        return None
    gray = cv2.cvtColor(img_bgr[y0:y1, x0:x1], cv2.COLOR_BGR2GRAY)
    _, mx, _, loc = cv2.minMaxLoc(cv2.matchTemplate(gray, anchor_gray, cv2.TM_CCOEFF_NORMED))
    if mx < thr:
        return None
    return x0 + loc[0] + int(meta["dx"]), cx, float(mx)


def analyze_combat(img_bgr, cb, mon_tpls, tag_tpl, yolo=None):
    """回傳 (角色畫面座標 or None, 怪物列表 [(x, y, score, name)])，座標為原始解析度"""
    s = float(cb.get("scale", 0.5))
    gray = _rescale(cv2.cvtColor(img_bgr, cv2.COLOR_BGR2GRAY), s)
    char = None
    tag_box = None
    if tag_tpl is not None:
        t = _rescale(tag_tpl, s)
        if t.shape[0] <= gray.shape[0] and t.shape[1] <= gray.shape[1]:
            _, mx, _, loc = cv2.minMaxLoc(cv2.matchTemplate(gray, t, cv2.TM_CCOEFF_NORMED))
            if mx >= float(cb.get("tag_threshold", 0.75)):
                x, y = loc
                tag_box = (x / s, y / s, t.shape[1] / s, t.shape[0] / s)
                char = (int(tag_box[0] + tag_box[2] / 2), int(tag_box[1] + float(cb.get("char_offset_y", -35))))
    # YOLO 成功載入時優先使用它；未安裝、模型不存在或偵測失敗才退回既有範本辨識。
    mons = yolo.detect(img_bgr) if yolo is not None else None
    if mons is None:
        mons = []
        scaled = [(n, _rescale(t, s)) for n, t in mon_tpls]
        for cx, cy, v, name in find_all(gray, scaled, float(cb.get("threshold", 0.7))):
            X, Y = cx / s, cy / s
            mons.append((int(X), int(Y), float(v), name))
    if tag_box and char:
        mons = [(x, y, v, name) for x, y, v, name in mons
                if not (tag_box[0] - 10 <= x <= tag_box[0] + tag_box[2] + 10 and abs(y - char[1]) < 40)]
    return char, mons


def detect_motion_targets(img_bgr, previous_gray, cb, char):
    """以相鄰畫面差異找活動目標，讓自動戰鬥不必先建立怪物範本。

    這是保守的輔助偵測：只保留角色附近、大小合理的活動區塊；範本辨識仍優先且較準。
    """
    s = float(cb.get("scale", 0.5))
    gray = _rescale(cv2.cvtColor(img_bgr, cv2.COLOR_BGR2GRAY), s)
    if previous_gray is None or previous_gray.shape != gray.shape or char is None:
        return gray, []
    diff = cv2.absdiff(gray, previous_gray)
    _, mask = cv2.threshold(diff, int(cb.get("motion_threshold", 28)), 255, cv2.THRESH_BINARY)
    mask = cv2.morphologyEx(mask, cv2.MORPH_OPEN, np.ones((2, 2), np.uint8))
    mask = cv2.dilate(mask, np.ones((3, 3), np.uint8), iterations=1)
    n, _, stats, cents = cv2.connectedComponentsWithStats(mask, 8)
    out = []
    min_area = int(cb.get("motion_min_area", 12))
    yr = float(cb.get("y_range", 60))
    for i in range(1, n):
        area = int(stats[i, cv2.CC_STAT_AREA])
        w, h = int(stats[i, cv2.CC_STAT_WIDTH]), int(stats[i, cv2.CC_STAT_HEIGHT])
        if not (min_area <= area <= 1800 and 3 <= w <= 120 and 3 <= h <= 120):
            continue
        x, y = int(cents[i][0] / s), int(cents[i][1] / s)
        # 排除玩家本身、技能特效與介面動畫；只保留可交戰的同層附近活動物件。
        if abs(x - char[0]) < 45 and abs(y - char[1]) < 70:
            continue
        if abs(y - char[1]) > yr * 1.6:
            continue
        out.append((x, y, 0.5, "動態目標"))
    return gray, out


def analyze_items(img_bgr, loot, cb, item_tpls, yolo=None):
    """找地上物品，回傳 [(x, y, score, name)]（原始解析度）"""
    if yolo is not None and yolo.has_class("item"):
        detected = yolo.detect_classes(img_bgr, "item")
        if detected is not None:
            return detected
    if not item_tpls:
        return []
    s = float(loot.get("scale", 1.0))
    gray = _rescale(cv2.cvtColor(img_bgr, cv2.COLOR_BGR2GRAY), s)
    scaled = [(n, _rescale(t, s)) for n, t in item_tpls]
    return [(int(cx / s), int(cy / s), float(v), n)
            for cx, cy, v, n in find_all(gray, scaled, float(loot.get("threshold", 0.75)), max_hits=60)]


def yolo_preview_image(img, boxes):
    """在畫面上用四種顏色畫出 YOLO 框（怪物綠、道具粉、繩子橘、人物藍），左上角加圖例"""
    out = img.copy()
    bgr = {}
    for k, hexc in zip(YOLO_CLASS_NAMES, YOLO_CLASS_COLORS):
        r, g, b = int(hexc[1:3], 16), int(hexc[3:5], 16), int(hexc[5:7], 16)
        bgr[k] = (b, g, r)
    for x1, y1, x2, y2, conf, name in boxes:
        color = bgr.get(name, (255, 255, 255))
        cv2.rectangle(out, (x1, y1), (x2, y2), color, 2)
        cv2.putText(out, f"{name} {conf:.2f}", (x1, max(12, y1 - 4)), cv2.FONT_HERSHEY_SIMPLEX, 0.45, color, 1,
                    cv2.LINE_AA)
    y = 18
    for k in YOLO_CLASS_NAMES:
        n = sum(1 for b in boxes if b[5] == k)
        cv2.rectangle(out, (6, y - 11), (18, y + 1), bgr[k], -1)
        cv2.putText(out, f"{k}: {n}", (24, y), cv2.FONT_HERSHEY_SIMPLEX, 0.5, (0, 0, 0), 3, cv2.LINE_AA)
        cv2.putText(out, f"{k}: {n}", (24, y), cv2.FONT_HERSHEY_SIMPLEX, 0.5, bgr[k], 1, cv2.LINE_AA)
        y += 18
    return out


class YoloMonsterDetector:
    """可選的 YOLO 怪物偵測器。延後載入，沒裝套件／沒有模型時不影響既有功能。"""

    def __init__(self, app):
        self.app = app
        self.model = None
        self.loaded_path = None
        self.error = None
        self.lock = threading.Lock()
        self.class_names = {}      # 模型路徑 -> 類別名稱集合（避免介面每 0.1 秒去搶模型鎖）
        self.device = None
        self._bg_loading = False

    def model_path(self):
        raw = str(self.app.cfg.get("yolo", {}).get("model", "")).strip()
        return raw if os.path.isabs(raw) else os.path.join(APP_DIR, raw)

    def invalidate(self):
        with self.lock:
            self.model = None
            self.loaded_path = None
            self.error = None
            self.class_names = {}
            self.device = None

    def available(self):
        cfg = self.app.cfg.get("yolo", {})
        return bool(cfg.get("enabled") and os.path.isfile(self.model_path()))

    def has_class(self, wanted):
        """目前載入的模型是否含有指定類別；避免舊怪物模型誤取代道具辨識。
        類別清單會快取；主執行緒（介面）呼叫時不等待模型載入，改在背景載入。"""
        if not self.available():
            return False
        path = self.model_path()
        names = self.class_names.get(path)
        if names is None:
            if threading.current_thread() is threading.main_thread():
                if not self._bg_loading and not self.error:
                    self._bg_loading = True

                    def bg():
                        try:
                            with self.lock:
                                self._load()
                        finally:
                            self._bg_loading = False
                    threading.Thread(target=bg, daemon=True).start()
                return False
            with self.lock:
                if not self._load():
                    return False
            names = self.class_names.get(path, set())
        return str(wanted).lower() in names

    def _load(self):
        path = self.model_path()
        if self.model is not None and self.loaded_path == path:
            return True
        if not os.path.isfile(path):
            self.error = "找不到模型檔"
            return False
        try:
            from ultralytics import YOLO
            self.model = YOLO(path)
            self.loaded_path = path
            self.error = None
            names = getattr(self.model, "names", {}) or {}
            self.class_names[path] = {str(n).lower() for n in names.values()}
            want = str(self.app.cfg.get("yolo", {}).get("device", "auto")).lower()
            if want in ("", "auto"):
                try:
                    import torch
                    self.device = 0 if torch.cuda.is_available() else "cpu"
                except Exception:
                    self.device = "cpu"
            else:
                self.device = int(want) if want.isdigit() else want
            log(f"YOLO 模型已載入（{os.path.basename(path)}，{'GPU' if self.device == 0 else 'CPU'}）")
            missing = {"item", "rope"} - self.class_names[path]
            if missing and hasattr(self.app, "offer_model_update"):
                label = "、".join(YOLO_CLASS_LABELS[YOLO_CLASS_NAMES.index(k)] for k in sorted(missing))
                log(f"目前的 YOLO 模型沒有{label}類別（較舊的模型）", "warn")
                self.app.ui(lambda: self.app.offer_model_update(f"目前的模型沒有{label}類別，繩子對位與道具辨識不會生效。"))
            return True
        except Exception as e:
            self.model = None
            self.error = f"YOLO 無法載入：{e}"
            log(self.error, "error")
            return False

    def class_conf(self):
        cfg = self.app.cfg.get("yolo", {})
        out = dict(YOLO_CLASS_CONF_DEFAULT)
        for k, v in (cfg.get("class_conf") or {}).items():
            try:
                out[str(k).lower()] = float(v)
            except (TypeError, ValueError):
                pass
        return out

    def detect_classes(self, img_bgr, wanted=None):
        """成功時回傳指定類別（或全部）的 YOLO 結果 [(x, y, 信心, "YOLO_類別")]；模型未可用時回傳 None。"""
        boxes = self.detect_boxes(img_bgr, wanted)
        if boxes is None:
            return None
        return [(int(round((x1 + x2) / 2)), int(round((y1 + y2) / 2)), conf, "YOLO_" + name)
                for x1, y1, x2, y2, conf, name in boxes]

    def detect_boxes(self, img_bgr, wanted=None):
        """回傳 [(x1, y1, x2, y2, 信心, 類別)]，每個類別套用自己的信心門檻。"""
        if not self.available():
            return None
        with self.lock:
            if not self._load():
                return None
            cfg = self.app.cfg.get("yolo", {})
            try:
                th = self.class_conf()
                low = min(th.values()) if wanted is None else th.get(wanted, float(cfg.get("confidence", 0.45)))
                kw = dict(conf=max(0.05, low), imgsz=int(cfg.get("imgsz", 960)), verbose=False)
                try:
                    result = self.model.predict(img_bgr, device=self.device if self.device is not None else "cpu",
                                                **kw)[0]
                except Exception:
                    if self.device == "cpu":
                        raise
                    self.device = "cpu"   # GPU 不能用（沒有 CUDA、顯示卡記憶體不足…）→ 改用 CPU 再試一次
                    log("YOLO 改用 CPU 偵測（GPU 無法使用）", "warn")
                    result = self.model.predict(img_bgr, device="cpu", **kw)[0]
            except Exception as e:
                if self.error != f"YOLO 偵測失敗：{e}":
                    log(f"YOLO 偵測失敗：{e}", "error")
                self.error = f"YOLO 偵測失敗：{e}"
                return None
        out = []
        names = result.names or {}
        th = self.class_conf()
        fallback = float(cfg.get("confidence", 0.45))
        for xyxy, conf, class_id in zip(result.boxes.xyxy.cpu().tolist(), result.boxes.conf.cpu().tolist(),
                                        result.boxes.cls.cpu().tolist()):
            name = str(names.get(int(class_id), class_id)).lower()
            if wanted is not None and name != wanted:
                continue
            if conf < th.get(name, fallback):
                continue
            x1, y1, x2, y2 = xyxy
            out.append((int(x1), int(y1), int(x2), int(y2), float(conf), name))
        return out

    def detect(self, img_bgr):
        """相容舊的怪物偵測介面。"""
        return self.detect_classes(img_bgr, "monster")


class CombatScanner(threading.Thread):
    """背景掃描整個遊戲畫面，找角色名牌與怪物"""

    def __init__(self, app):
        super().__init__(daemon=True)
        self.app = app
        self.mon_templates = load_monster_templates()
        self.tag_template = load_tag_template()
        self.item_templates = load_templates(ITEM_DIR)
        self.snap = None          # (time, char, monsters, items)
        self.force_until = 0
        self.running = True
        self.ms = 0.0
        self.motion_gray = None
        self.yolo = YoloMonsterDetector(app)

    def scan_ready(self):
        """有範本或啟用內部動態偵測時即可掃描。"""
        cb = self.app.cfg["combat"]
        return bool(cb.get("enabled") and (self.mon_templates or cb.get("auto_detect", True)))

    def ready(self):
        """自動戰鬥還需要角色名牌，否則無法判斷相對距離。"""
        return bool(self.scan_ready() and self.tag_template is not None)

    def loot_ready(self):
        return bool(self.tag_template is not None and (self.item_templates or self.yolo.has_class("item")))

    def reload(self):
        self.mon_templates = load_monster_templates()
        self.tag_template = load_tag_template()
        self.item_templates = load_templates(ITEM_DIR)

    def run(self):
        sct = mss.mss() if IS_WIN else None
        while self.running:
            cb = self.app.cfg["combat"]
            v = self.app.vision
            active = self.app.bot.active.is_set() or time.time() < self.force_until
            want_loot = (self.app.cfg.get("mode") == "buff" and self.app.cfg["loot"].get("enabled", True)
                         and self.loot_ready())
            if not (sct and (self.scan_ready() or want_loot) and active and v.hwnd and v.rect):
                self.motion_gray = None
                time.sleep(0.2)
                continue
            try:
                L, T, W, H = v.rect
                t0 = time.time()
                shot = sct.grab({"left": L, "top": T, "width": W, "height": H})
                img = np.ascontiguousarray(np.array(shot)[:, :, :3])
                char, mons = analyze_combat(img, cb, self.mon_templates if self.scan_ready() else [],
                                            self.tag_template, self.yolo)
                if char is not None:
                    self.last_char = (time.time(), char)
                elif getattr(self, "last_char", None) and time.time() - self.last_char[0] < 2.0:
                    char = self.last_char[1]   # 名牌被技能特效／其他玩家擋住一下：沿用剛才的位置
                if cb.get("auto_detect", True):
                    self.motion_gray, moving = detect_motion_targets(img, self.motion_gray, cb, char)
                    for target in moving:
                        if not any(abs(target[0] - m[0]) < 24 and abs(target[1] - m[1]) < 24 for m in mons):
                            mons.append(target)
                else:
                    self.motion_gray = None
                items = analyze_items(img, self.app.cfg["loot"], cb, self.item_templates, self.yolo) if want_loot else []
                self.snap = (time.time(), char, mons, items)
                self.ms = (time.time() - t0) * 1000
            except Exception as e:
                if time.time() - getattr(self, "_err_logged", 0) > 30:
                    self._err_logged = time.time()
                    log_exception("畫面掃描錯誤", e)
                time.sleep(0.5)
            time.sleep(float(cb.get("scan_interval", 0.2)))


DIAG_DIR = os.path.join(APP_DIR, "diag")


class DiagRecorder(threading.Thread):
    """診斷記錄：輔助執行中，每 0.25 秒記錄小地圖（標出角色、候選色塊、繩子）、狀態、座標、按鍵。

    產出（每次開始都覆蓋）：
      diag/minimap.avi   小地圖影片（放大 4 倍、有標示）
      diag/log.csv       時間、狀態、座標、候選色塊、目前按住的鍵
      diag/keys.csv      每一次按下／放開
      diag/game_*.png    開始時與之後每 15 秒的整個遊戲畫面（最多 8 張）
      diag/config.json   當時的設定
    """

    def __init__(self, app):
        super().__init__(daemon=True)
        self.app = app
        self.running = True
        self.session = None
        self.lock = threading.Lock()

    def key_event(self, name, up):
        with self.lock:
            if self.session:
                self.session["keys"].write(f"{time.time() - self.session['t0']:.3f},{name},{'up' if up else 'down'}\n")

    def _open(self):
        os.makedirs(DIAG_DIR, exist_ok=True)
        for fn in os.listdir(DIAG_DIR):
            if fn.startswith("game_") and fn.endswith(".png"):
                try:
                    os.remove(os.path.join(DIAG_DIR, fn))
                except OSError:
                    pass
        log = open(os.path.join(DIAG_DIR, "log.csv"), "w", encoding="utf-8-sig")
        log.write("t,status,pos_x,pos_y,candidates(x:y:area),held_keys\n")
        keys = open(os.path.join(DIAG_DIR, "keys.csv"), "w", encoding="utf-8-sig")
        keys.write("t,key,action\n")
        with open(os.path.join(DIAG_DIR, "config.json"), "w", encoding="utf-8") as f:
            json.dump(self.app.cfg, f, ensure_ascii=False, indent=1)
        return {"t0": time.time(), "log": log, "keys": keys, "video": None, "shots": 0, "last_shot": 0}

    def _close(self):
        with self.lock:
            s, self.session = self.session, None
        if s:
            for k in ("log", "keys"):
                s[k].close()
            if s["video"] is not None:
                s["video"].release()

    def _frame(self, s):
        v, cfg = self.app.vision, self.app.cfg
        with v.lock:
            img = None if v.minimap is None else v.minimap.copy()
            p = v.pos
            cands = list(v.tracker.candidates)
        t = time.time() - s["t0"]
        held = " ".join(sorted(self.app.kb.held))
        cs = " ".join(f"{c[0]}:{c[1]}:{c[2]}" for c in cands)
        status = self.app.bot.status.replace(",", "，")
        s["log"].write(f"{t:.2f},{status},{p[0] if p else ''},{p[1] if p else ''},{cs},{held}\n")
        s["log"].flush()
        s["keys"].flush()
        if img is not None:
            z = 4
            big = cv2.resize(img, (img.shape[1] * z, img.shape[0] * z), interpolation=cv2.INTER_NEAREST)
            for r in cfg["patrol"]:
                if r.get("type") == "rope":
                    x, y = r["x"] * z + z // 2, r["y"] * z + z // 2
                    top = (r.get("lands_y", r["y"] - 15)) * z
                    cv2.line(big, (x, y), (x, top), (0, 165, 255), 1)
            for c in cands:
                cv2.circle(big, (c[0] * z + z // 2, c[1] * z + z // 2), 7, (160, 160, 160), 1)
            if p:
                cv2.drawMarker(big, (p[0] * z + z // 2, p[1] * z + z // 2), (0, 255, 255), cv2.MARKER_CROSS, 14, 2)
            band = np.zeros((40, big.shape[1], 3), np.uint8)
            cv2.putText(band, f"t={t:.1f} pos={p} held={held}"[:80], (4, 16), cv2.FONT_HERSHEY_SIMPLEX, 0.45,
                        (255, 255, 255), 1)
            frame = np.vstack([band, big])
            if s["video"] is None:
                s["size"] = (frame.shape[1], frame.shape[0])
                s["video"] = cv2.VideoWriter(os.path.join(DIAG_DIR, "minimap.avi"),
                                             cv2.VideoWriter_fourcc(*"MJPG"), 4, s["size"])
            if (frame.shape[1], frame.shape[0]) == s["size"]:
                s["video"].write(frame)
        if s["shots"] < 8 and time.time() - s["last_shot"] >= 15:
            full = v.grab_client() if IS_WIN else None
            if full is not None:
                imwrite_unicode(os.path.join(DIAG_DIR, f"game_{s['shots'] + 1}.png"), full)
                s["shots"] += 1
            s["last_shot"] = time.time()

    def run(self):
        while self.running:
            want = self.app.cfg.get("diagnostics") and self.app.bot.active.is_set()
            try:
                if want and self.session is None:
                    sess = self._open()
                    with self.lock:
                        self.session = sess
                elif not want and self.session is not None:
                    self._close()
                if self.session is not None:
                    self._frame(self.session)
            except Exception as e:
                if time.time() - getattr(self, "_err_logged", 0) > 30:
                    self._err_logged = time.time()
                    log_exception("診斷記錄錯誤", e)
            time.sleep(0.25)
        self._close()


class Vision(threading.Thread):
    """背景持續擷取畫面並更新角色座標"""

    def __init__(self, app):
        super().__init__(daemon=True)
        self.app = app
        self.lock = threading.Lock()
        self.pos = None
        self.minimap = None
        self.hwnd = None
        self.rect = None
        self.running = True
        self.fps = 0.0
        self.tracker = PlayerTracker()
        self.templates = load_templates()
        self.elite_templates = load_templates(ELITE_DIR)
        self.last_ld_check = 0
        self.last_elite_check = 0
        self.elite_seen_at = 0     # 最後一次看到菁英特徵的時間
        self.elite_score = 0.0
        self.red_dots = []
        self.red_since = None      # 紅點開始連續出現的時間
        self.red_clear_since = None
        self.red_armed = True      # 觸發後要等紅點消失 3 秒才會再次警報

    def check_red_dots(self, img):
        rd = self.app.cfg.get("red_dot", {})
        if not rd.get("enabled"):
            self.red_dots = []
            return
        dots = find_dots(img, rd["ranges"], int(rd.get("min_area", 2)),
                         int(rd.get("max_area", 12)), int(rd.get("max_size", 5)))
        with self.lock:
            self.red_dots = dots
        now = time.time()
        if dots:
            self.red_clear_since = None
            self.red_since = self.red_since or now
            if self.red_armed and now - self.red_since >= float(rd.get("confirm_sec", 0.3)):
                self.red_armed = False
                self.app.trigger_alarm("red", f"小地圖出現 {len(dots)} 個紅點（其他玩家）",
                                       pause=rd.get("pause", True), beep=rd.get("beep", True))
        else:
            self.red_since = None
            self.red_clear_since = self.red_clear_since or now
            if not self.red_armed and now - self.red_clear_since >= 3:
                self.red_armed = True
                self.app.red_cleared()

    def check_screen(self, sct):
        """掃描整個遊戲畫面：測謊（每 1 秒）、菁英怪（每 0.5 秒），共用同一張截圖"""
        cfg = self.app.cfg
        ld, el = cfg.get("lie_detector", {}), cfg.get("elite", {})
        now = time.time()
        do_ld = (ld.get("enabled") and self.templates and self.app.alarm_kind != "lie"
                 and now - self.last_ld_check >= 1.0)
        do_el = el.get("enabled") and self.elite_templates and now - self.last_elite_check >= 0.5
        if not (do_ld or do_el):
            return
        L, T, W, H = self.rect
        shot = sct.grab({"left": L, "top": T, "width": W, "height": H})
        img = np.ascontiguousarray(np.array(shot)[:, :, :3])
        if do_el:
            self.last_elite_check = now
            hit = match_any(img, self.elite_templates, float(el.get("threshold", 0.8)))
            self.elite_score = hit[1] if hit else 0.0
            if hit:
                self.elite_seen_at = time.time()
        if not do_ld:
            return
        self.last_ld_check = now
        hit = match_any(img, self.templates, float(ld.get("threshold", 0.8)))
        if hit:
            self.app.trigger_alarm("lie", f"偵測到測謊（{hit[0]}，相似度 {hit[1]:.2f}）",
                                   pause=True, beep=ld.get("beep", True))

    def run(self):
        sct = mss.mss() if IS_WIN else None
        last_find = 0
        frames, t0 = 0, time.time()
        while self.running:
            cfg = self.app.cfg
            try:
                if not self.hwnd or (IS_WIN and not user32.IsWindow(self.hwnd)):
                    if time.time() - last_find > 1:
                        self.hwnd = find_window(cfg["window_title"])
                        last_find = time.time()
                    if not self.hwnd:
                        with self.lock:
                            self.pos, self.minimap, self.rect = None, None, None
                        time.sleep(0.3)
                        continue
                rect = client_rect(self.hwnd)
                if not rect_visible(rect):               # 遊戲縮到最小：先不辨識，等視窗還原
                    with self.lock:
                        self.pos, self.minimap, self.rect = None, None, None
                    time.sleep(0.3)
                    continue
                self.rect = rect
                mm = cfg.get("minimap")
                if mm and sct:
                    L, T, _, _ = self.rect
                    shot = sct.grab({"left": L + mm[0], "top": T + mm[1], "width": mm[2], "height": mm[3]})
                    img = np.ascontiguousarray(np.array(shot)[:, :, :3])
                    cands = player_candidates(img, cfg["player_hsv_low"], cfg["player_hsv_high"],
                                              cfg["min_dot_area"])
                    with self.lock:
                        p = self.tracker.update(cands, ref_area=cfg.get("player_area_ref"))
                        self.pos, self.minimap = p, img
                    self.check_red_dots(img)
                if sct:
                    self.check_screen(sct)
                frames += 1
                if time.time() - t0 >= 1:
                    self.fps, frames, t0 = frames / (time.time() - t0), 0, time.time()
            except Exception as e:
                if time.time() - getattr(self, "_err_logged", 0) > 30:
                    self._err_logged = time.time()
                    log_exception("畫面辨識錯誤", e)
                self.hwnd = None
                time.sleep(0.5)
            time.sleep(0.03)

    def get_pos(self):
        with self.lock:
            return self.pos

    def grab_client(self):
        """擷取整個遊戲客戶區（用於框選小地圖）"""
        if not self.hwnd:
            return None
        L, T, W, H = client_rect(self.hwnd)
        if not rect_visible((L, T, W, H)):
            return None
        with mss.mss() as s:
            shot = s.grab({"left": L, "top": T, "width": W, "height": H})
        return np.ascontiguousarray(np.array(shot)[:, :, :3])


# --------------------------------------------------------------------------
# 自動執行
# --------------------------------------------------------------------------
class KeyRecorder(threading.Thread):
    """錄製鍵盤與滑鼠點擊（輪詢 GetAsyncKeyState，不安裝任何鉤子）。

    從第一個按鍵開始計時；按「錄製結束」熱鍵（預設 F8）結束，按「緊急停止」熱鍵取消。
    """

    def __init__(self, app, on_done, max_sec=60):
        super().__init__(daemon=True)
        self.app = app
        self.on_done = on_done
        self.max_sec = max_sec
        self.active = True
        self.cancelled = False
        self.start_img = None

    def run(self):
        try:
            self._run()
        except Exception as e:
            self.active = False
            self.cancelled = True
            log_exception("錄製發生錯誤，已取消", e)
            self.app.ui(lambda: self.on_done(None, True))

    def _run(self):
        hk = self.app.cfg.get("hotkeys", {})
        stop_vk = VK_FKEYS.get(hk.get("record", "f8"), 0x77)       # 結束錄製
        cancel_vk = VK_FKEYS.get(hk.get("stop", "f12"), 0x7B)      # 取消錄製
        skip = {VK_FKEYS.get(hk.get(k, d)) for k, d in (("toggle", "f10"), ("stop", "f12"), ("record", "f8"))}
        watch = {n: vk for n, vk in VK_NAMES.items() if n in SCANCODES and vk not in skip}
        # 啟動時已經按著的鍵（例如剛按的滑鼠/熱鍵）不算
        state = {n: bool(user32.GetAsyncKeyState(vk) & 0x8000) for n, vk in watch.items()} if IS_WIN else {}
        mouse_state = {n: bool(user32.GetAsyncKeyState(vk) & 0x8000) for n, vk in MOUSE_BUTTONS.items()} if IS_WIN else {}
        hotkey_down = True   # 等熱鍵先放開，避免一開始就被當成「結束」
        events, positions, t0, start_pos = [], [], None, None
        last_coord = None
        begin = time.perf_counter()

        def sample_position(now, force=False):
            nonlocal last_coord
            if t0 is None:
                return
            p = self.app.vision.get_pos()
            if p is None:
                return
            point = (int(p[0]), int(p[1]))
            # 座標有變化就記下；同一點不重複存，長時間錄製也不會膨脹。
            if force or point != last_coord:
                positions.append([round(now - t0, 3), point[0], point[1]])
                last_coord = point

        def begin_record(now):
            nonlocal t0, start_pos
            if t0 is not None:
                return True
            t0 = now
            start_pos = self.app.vision.get_pos()
            sample_position(now, force=True)
            try:
                self.start_img = self.app.vision.grab_client()
            except Exception:
                self.start_img = None
            return True

        def mouse_pos():
            if not IS_WIN:
                return None
            pt = wintypes.POINT()
            user32.GetCursorPos(ctypes.byref(pt))
            rect = self.app.vision.rect
            if not rect and self.app.vision.hwnd:
                rect = client_rect(self.app.vision.hwnd)
            if not rect:
                return None
            x, y = int(pt.x - rect[0]), int(pt.y - rect[1])
            if not (0 <= x < rect[2] and 0 <= y < rect[3]):
                return None
            return [x, y]

        while self.active and time.perf_counter() - begin < self.max_sec:
            if IS_WIN:
                hs = bool(user32.GetAsyncKeyState(stop_vk) & 0x8000)
                hc = bool(user32.GetAsyncKeyState(cancel_vk) & 0x8000)
                if hc:
                    self.cancelled = True
                    break
                if hs and not hotkey_down:
                    break
                hotkey_down = hs
                now = time.perf_counter()
                for n, vk in watch.items():
                    down = bool(user32.GetAsyncKeyState(vk) & 0x8000)
                    if down != state[n]:
                        state[n] = down
                        if t0 is None:
                            if not down:
                                continue
                            begin_record(now)
                        events.append([round(now - t0, 4), n, 1 if down else 0])
                for n, vk in MOUSE_BUTTONS.items():
                    down = bool(user32.GetAsyncKeyState(vk) & 0x8000)
                    if down != mouse_state[n]:
                        mouse_state[n] = down
                        if t0 is None:
                            if not down:
                                continue
                            begin_record(now)
                        pos = mouse_pos()
                        if pos is not None:
                            events.append({"t": round(now - t0, 4), "kind": "mouse", "button": n,
                                           "down": 1 if down else 0, "x": pos[0], "y": pos[1]})
                sample_position(now)
            time.sleep(0.004)
        self.active = False
        if t0 is not None:   # 結束時還按著的鍵補上放開
            end_t = round(time.perf_counter() - t0, 4)
            held_keys, held_mouse = {}, {}
            for event in events:
                if isinstance(event, dict) and event.get("kind") == "mouse":
                    held_mouse[event.get("button")] = event.get("down")
                elif isinstance(event, (list, tuple)) and len(event) >= 3:
                    held_keys[event[1]] = event[2]
            events += [[end_t, n, 0] for n, d in held_keys.items() if d]
            pos = mouse_pos()
            if pos is not None:
                events += [{"t": end_t, "kind": "mouse", "button": n, "down": 0, "x": pos[0], "y": pos[1]}
                           for n, d in held_mouse.items() if d]
        time.sleep(0.6)   # 等角色落地再記終點
        rec = None
        if not self.cancelled and events:
            end_pos = self.app.vision.get_pos()
            sample_position(time.perf_counter(), force=True)
            rec = {"events": events,
                   "start": list(start_pos) if start_pos else None,
                   "end": list(end_pos) if end_pos else None,
                   "duration": end_t,
                   "path": positions,
                   "ropes": infer_rope_segments(positions, events),
                   "start_img": self.start_img}
        self.app.ui(lambda: self.on_done(rec, self.cancelled))


def macro_summary(rec):
    if not rec:
        return "（無）"
    keys = sum(1 for e in rec["events"] if isinstance(e, (list, tuple)) and len(e) >= 3 and e[2])
    clicks = sum(1 for e in rec["events"] if isinstance(e, dict) and e.get("kind") == "mouse" and e.get("down"))
    detail = f"{keys} 個按鍵" + (f"、{clicks} 次點擊" if clicks else "")
    points = len(rec.get("path") or [])
    if points:
        detail += f"、{points} 個座標"
    ropes = len(rec.get("ropes") or [])
    if ropes:
        detail += f"、{ropes} 條繩子"
    return f"{detail}、{rec.get('duration', 0):.1f} 秒"


def macro_position_at(path, elapsed):
    """取得錄製路徑在指定時間的預期小地圖座標（相鄰採線性插值）。"""
    rows = [r for r in (path or []) if isinstance(r, (list, tuple)) and len(r) >= 3]
    if not rows:
        return None
    if elapsed <= float(rows[0][0]):
        return int(rows[0][1]), int(rows[0][2])
    previous = rows[0]
    for current in rows[1:]:
        t0, t1 = float(previous[0]), float(current[0])
        if elapsed <= t1:
            if t1 <= t0:
                return int(current[1]), int(current[2])
            fraction = (elapsed - t0) / (t1 - t0)
            return (int(round(float(previous[1]) + (float(current[1]) - float(previous[1])) * fraction)),
                    int(round(float(previous[2]) + (float(current[2]) - float(previous[2])) * fraction)))
        previous = current
    return int(previous[1]), int(previous[2])


def infer_rope_segments(path, events):
    """由錄製期間的上／下鍵與小地圖座標軌跡，找出實際爬過的繩子。"""
    if len(path or []) < 3:
        return []
    keys = [e for e in events if isinstance(e, (list, tuple)) and len(e) >= 3]
    keys.sort(key=lambda e: float(e[0]))
    held, ei, runs = set(), 0, []
    current = None
    for a, b in zip(path, path[1:]):
        if len(a) < 3 or len(b) < 3:
            continue
        t, x, y = float(a[0]), int(a[1]), int(a[2])
        nt, nx, ny = float(b[0]), int(b[1]), int(b[2])
        while ei < len(keys) and float(keys[ei][0]) <= t:
            _kt, name, down = keys[ei][:3]
            if name in ("up", "down"):
                (held.add if down else held.discard)(name)
            ei += 1
        direction = "up" if "up" in held else ("down" if "down" in held else None)
        vertical = (ny - y) * (-1 if direction == "up" else 1) if direction else 0
        # 繩子上通常 X 幾乎不動，且與按住的方向一致；跳躍、平台位移會被排除。
        valid = direction and vertical > 0 and abs(nx - x) <= 2 and nt > t
        if valid:
            if current and (current["direction"] != direction or abs(x - current["xs"][-1]) > 3):
                runs.append(current)
                current = None
            if current is None:
                current = {"direction": direction, "start_t": t, "end_t": nt,
                           "points": [(x, y), (nx, ny)], "xs": [x, nx]}
            else:
                current["end_t"] = nt
                current["points"].append((nx, ny))
                current["xs"].append(nx)
        elif current:
            runs.append(current)
            current = None
    if current:
        runs.append(current)

    ropes = []
    for run in runs:
        pts = run["points"]
        ys = [p[1] for p in pts]
        span = max(ys) - min(ys)
        if span < 5 or run["end_t"] - run["start_t"] < 0.15:
            continue
        x = int(round(sum(run["xs"]) / len(run["xs"])))
        ropes.append({"x": x, "bottom_y": max(ys), "top_y": min(ys),
                      "direction": run["direction"], "duration": round(run["end_t"] - run["start_t"], 2)})
    # 同一條繩子往返爬時只保留一份範圍最大的資料。
    merged = []
    for rope in ropes:
        same = next((r for r in merged if abs(r["x"] - rope["x"]) <= 2
                     and not (rope["bottom_y"] < r["top_y"] - 2 or rope["top_y"] > r["bottom_y"] + 2)), None)
        if same:
            same["bottom_y"] = max(same["bottom_y"], rope["bottom_y"])
            same["top_y"] = min(same["top_y"], rope["top_y"])
        else:
            merged.append(rope)
    return merged


class StopBot(Exception):
    pass


class LootInterrupt(Exception):
    """BUFF機模式：移動途中看到地上物品，中斷去撿"""
    pass


class CombatInterrupt(Exception):
    """全自動戰鬥模式：移動途中看到怪，中斷去打"""
    pass


class EliteInterrupt(Exception):
    """偵測到菁英怪：中斷目前步驟，切換菁英模式"""
    pass


class Bot(threading.Thread):
    def __init__(self, app):
        super().__init__(daemon=True)
        self.app = app
        self.kb = app.kb
        self.active = threading.Event()  # 執行中（非暫停）
        self.alive = True
        self.step_idx = 0
        self.status = "待機"
        self.skill_last = {}
        self.startup_buffs_pending = False
        self.attack_last = 0
        self.climbing = False
        self.last_target = None
        self.nav_fail = 0
        self.in_elite = False
        self.elite_last = {}
        self.in_combat = False
        self.facing = None
        self.aoe_last = 0
        self.combat_quiet_until = 0
        self.in_loot = False
        self.drift_since = None
        self.anchor_idx = 0
        self.anchor_dwell = None
        self.anchor_since = None
        self.hold_sent = 0
        self.last_turn = 0
        self.loot_ignore = []      # [(小地圖x, 小地圖y, 到期時間)]：撿不起來而放棄的位置
        self.loot_tries = {}
        self.loot_k = None         # 畫面 px / 小地圖 px（移動中自動學習）
        self.loot_k_hist = []
        self.last_map_macro_index = None
        threading.Thread(target=self._loot_tapper, daemon=True).start()

    # ---- 工具 ----
    @property
    def cfg(self):
        return self.app.cfg

    def key(self, role):
        return self.cfg["keys"][role]

    def choose_map_macro(self):
        """每一輪從完整錄製路線中隨機挑一條，盡量不連續重複。"""
        routes = [r for r in self.cfg.get("map_macros", []) if isinstance(r, dict) and r.get("events")]
        if not routes:
            legacy = self.cfg.get("map_macro")
            routes = [legacy] if isinstance(legacy, dict) and legacy.get("events") else []
        if not routes:
            return None, None
        choices = list(range(len(routes)))
        if len(choices) > 1 and self.last_map_macro_index in choices:
            choices.remove(self.last_map_macro_index)
        index = random.choice(choices)
        self.last_map_macro_index = index
        return routes[index], index

    def elite_present(self):
        el = self.cfg.get("elite", {})
        return el.get("enabled") and time.time() - self.app.vision.elite_seen_at < float(el.get("end_sec", 3))

    def check(self, allow_elite=True):
        """每個迴圈都會呼叫：暫停/失焦時停下並放開所有按鍵；看到菁英怪就中斷"""
        if not self.alive:
            raise StopBot()
        while True:
            if not self.active.is_set():
                self.kb.release_all()
                raise StopBot()
            if (allow_elite and not self.climbing and not self.in_elite and self.cfg.get("mode") != "buff"
                    and self.elite_present()):
                self.kb.release_all()
                raise EliteInterrupt()
            if (allow_elite and self.cfg.get("mode") == "buff" and not self.climbing and not self.in_loot
                    and not self.in_elite and self.loot_targets()[1]):
                self.kb.release_all()
                raise LootInterrupt()
            if (allow_elite and self.cfg.get("mode") == "combat" and not self.climbing and not self.in_combat
                    and not self.in_elite and time.time() > self.combat_quiet_until and self.target_in_reach()):
                self.kb.release_all()
                raise CombatInterrupt()
            if self.cfg.get("only_when_focused") and IS_WIN and not is_foreground(self.app.vision.hwnd):
                self.kb.release_all()
                self.status = "遊戲視窗不在前景，等待中…"
                time.sleep(0.3)
                continue
            return

    def sleep(self, sec, do_skills=True):
        end = time.time() + sec
        while time.time() < end:
            self.check()
            if do_skills:
                self.tick_skills()
            time.sleep(min(0.03, max(0, end - time.time())))

    def pos(self):
        return self.app.vision.get_pos()

    def tick_skills(self, allow_attack=False):
        if self.climbing:
            return
        now = time.time()
        for i, s in enumerate(self.cfg["skills"]):
            if not s.get("enabled"):
                continue
            if now - self.skill_last.get(i, 0) >= float(s["interval"]):
                self.status = f"施放：{s['name']}"
                extra = []
                if self.cfg.get("mode") == "anchor" and self.cfg["anchor"].get("release_for_buff", True):
                    extra = [self.cfg["anchor"]["hold_key"]]
                held = [k for k in (self.key("left"), self.key("right"), *extra) if k in self.kb.held]
                for k in held:
                    self.kb.up(k)
                self.kb.tap(s["key"])
                self.skill_last[i] = time.time()
                time.sleep(float(s.get("delay", 0.6)))
                for k in held:
                    self.kb.down(k)
        if allow_attack:
            a = self.cfg["attack"]
            if a.get("enabled") and now - self.attack_last >= float(a["interval"]):
                self.kb.tap(self.key("attack"))
                self.attack_last = time.time()

    def quiet_wait(self, sec):
        """等待：只檢查暫停／前景，不放技能、不被撿物或菁英中斷（開始時放 Buff 用）"""
        end = time.time() + sec
        while time.time() < end:
            self.check(allow_elite=False)
            time.sleep(min(0.03, max(0, end - time.time())))

    def cast_startup_buffs(self):
        """每次按開始時先完整輪流放一輪 Buff，全部放完、動作結束後，才進入任何攻擊／移動流程。

        按開始後本工具會縮小並把遊戲切到前景（約 0.15 秒）；先等遊戲真的在前景再送鍵，
        避免第一個 Buff 送到別的視窗。每個 Buff 之間等它的「施放後等待」，最後再等「放完 Buff 後等待」，
        讓最後一個 Buff 的施放動作完整結束，錄製路線才從頭開始。"""
        enabled = [(i, s) for i, s in enumerate(self.cfg["skills"]) if s.get("enabled")]
        if not enabled:
            return
        # 不讓先前殘留的方向鍵、定點按住攻擊等干擾 Buff。
        self.kb.release_all()
        self.status = "啟動 Buff：等待遊戲視窗…"
        if IS_WIN and not self.cfg.get("only_when_focused"):
            end = time.time() + 3.0
            while time.time() < end and not is_foreground(self.app.vision.hwnd):
                self.check(allow_elite=False)
                time.sleep(0.05)
        self.check(allow_elite=False)             # 「只在前景送鍵」開啟時，會等到遊戲在前景
        self.quiet_wait(0.25)          # 切到遊戲後給一點時間，按鍵才不會被吃掉
        for i, s in enabled:
            self.check(allow_elite=False)
            self.status = f"啟動 Buff：{s['name']}"
            self.kb.tap(s["key"])
            self.skill_last[i] = time.time()
            self.quiet_wait(max(0.0, float(s.get("delay", 0.6))))
        wait = max(0.0, float(self.cfg.get("buff_start_wait", 1.0)))
        if wait:
            self.status = f"Buff 放完，{wait:g} 秒後開始"
            self.quiet_wait(wait)
        log(f"開始時 Buff 放完（{len(enabled)} 個），開始移動")

    # ---- 動作 ----
    def goto(self, tx, tol=None, timeout=10, prehold=None, prehold_dist=4):
        """走到小地圖 X 座標：方向鍵全程按住，到點才放開（走過頭就按住反方向）。

        只有在要求非常精準（tol ≤ 1，例如對準繩子）且剩最後 2 格時，才用短按微調。
        prehold＝快到目標（距離 ≤ prehold_dist）時先按住的鍵（例如上），經過繩子時就會直接抓住；
        一旦角色開始往上爬，就設 self.early_grab 並結束（按住的鍵交給呼叫端放開）。
        """
        tol = self.cfg["goto_tolerance"] if tol is None else tol
        self.early_grab = False
        self._prehold_y0 = None
        self.status = f"移動到 X={tx}"
        start = time.time()
        last_x, last_move = None, time.time()
        cur_dir = None
        settle = None
        fine_hold, fine_sign = 0.04, 0     # 精準對位的短按長度；來回衝過頭時自動減半
        try:
            while time.time() - start < timeout:
                self.check()
                p = self.pos()
                if p is None:
                    time.sleep(0.03)
                    continue
                dx = tx - p[0]
                if prehold:
                    if self._prehold_y0 is None:
                        self._prehold_y0 = p[1]
                    if abs(dx) <= prehold_dist and prehold not in self.kb.held:
                        self.kb.down(prehold)
                        self.status = f"接近繩子，先按住上（X={tx}）"
                    if p[1] <= self._prehold_y0 - 2:      # 已經抓到繩子往上爬了
                        self.early_grab = True
                        return True
                if abs(dx) <= tol and prehold and prehold in self.kb.held:
                    # 已在繩下且按住上：站著按住上本來就會抓住，等一下看看有沒有開始往上爬
                    if cur_dir:
                        self.kb.up(cur_dir)
                        cur_dir = None
                    end_wait = time.time() + 0.35
                    while time.time() < end_wait:
                        self.check()
                        q = self.pos()
                        if q and q[1] <= self._prehold_y0 - 2:
                            self.early_grab = True
                            return True
                        time.sleep(0.03)
                    return True
                if abs(dx) <= tol:
                    if cur_dir:   # 到點：放開，等角色停穩再確認一次
                        self.kb.up(cur_dir)
                        cur_dir = None
                        settle = time.time()
                    if settle is None or time.time() - settle >= 0.12:
                        p2 = self.pos()
                        if p2 is None or abs(tx - p2[0]) <= tol:
                            return True
                        settle = None
                    time.sleep(0.02)
                    continue
                settle = None
                want = self.key("right") if dx > 0 else self.key("left")
                fine = tol <= 1 and abs(dx) <= 2
                if fine:
                    # 精準對位：短按一下就放開，避免衝過頭
                    if cur_dir:
                        self.kb.up(cur_dir)
                        cur_dir = None
                    sign = 1 if dx > 0 else -1
                    if fine_sign and sign != fine_sign:          # 上一下衝過頭了 → 下一下按短一點
                        fine_hold = max(0.01, fine_hold * 0.5)
                    fine_sign = sign
                    self.kb.tap(want, fine_hold)
                    self.facing = "right" if dx > 0 else "left"
                    time.sleep(0.1)
                elif cur_dir != want:
                    if cur_dir:
                        self.kb.up(cur_dir)
                    self.kb.down(want)
                    cur_dir = want
                    self.facing = "right" if dx > 0 else "left"
                # 卡住偵測：按住方向 1.2 秒都沒動就跳一下
                if last_x is None or p[0] != last_x:
                    last_x, last_move = p[0], time.time()
                elif cur_dir and time.time() - last_move > 1.2:
                    self.kb.tap(self.key("jump"))
                    last_move = time.time()
                self.tick_skills()
                time.sleep(0.02)
            return False
        finally:
            if cur_dir:
                self.kb.up(cur_dir)

    # ---- 繩子：上繩／下繩（全程按住） ----
    def wait_landed(self, timeout=3.0, stable=0.35):
        """等角色停穩（y 連續 stable 秒不變），回傳最後位置"""
        start = time.time()
        p = self.pos()
        last, since = p, time.time()
        while time.time() - start < timeout:
            self.check()
            time.sleep(0.03)
            p = self.pos()
            if p is None:
                continue
            if last is None or p[1] != last[1]:
                last, since = p, time.time()
            elif time.time() - since >= stable:
                break
        return last

    def _anchor_gray(self, anchor):
        cache = self.__dict__.setdefault("_anchor_cache", {})
        f = anchor.get("file")
        if f not in cache:
            img = imread_unicode(os.path.join(ROPE_DIR, f)) if f else None
            cache[f] = None if img is None else cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
        return cache[f]

    def screen_align(self, anchor, max_iter=12):
        """用遊戲畫面把角色對到記錄繩子時的精確位置（誤差 3 px 內）。回傳是否對準"""
        tag = self.app.scanner.tag_template
        tpl = self._anchor_gray(anchor) if anchor else None
        if tag is None or tpl is None:
            return False
        px_time = self.__dict__.get("_px_time", 0.008)    # 每走 1 px 要按多久（會自動修正）
        last = None
        for _ in range(max_iter):
            self.check()
            img = self.app.vision.grab_client()
            r = find_rope_anchor(img, tag, tpl, anchor)
            if r is None:
                self.status = "精準對位：畫面上找不到繩子地標（改用小地圖位置）"
                return False
            want, cx, score = r
            d = want - cx
            if abs(d) > ALIGN_MAX_PX:
                self.status = f"精準對位：差 {d:+d} px 太遠，可能對到旁邊的繩子，改用小地圖位置"
                log(self.status, "warn")
                return False
            self.status = f"精準對位：差 {d:+d} px"
            if abs(d) <= 3:
                return True
            if last is not None:
                moved = abs(last[0] - d)
                if moved >= 2 and last[1] > 0:
                    px_time = min(0.03, max(0.002, 0.6 * px_time + 0.4 * (last[1] / moved)))
            hold = min(0.35, max(0.015, abs(d) * px_time))
            self.kb.tap(self.key("right") if d > 0 else self.key("left"), hold)
            last = (d, hold)
            time.sleep(0.12)
        self._px_time = px_time
        return False

    def yolo_rope_delta(self, img=None, max_distance=120):
        """畫面上最近的繩子中心 − 角色中心（px）；找不到回傳 None"""
        yolo_cfg = self.cfg.get("yolo", {})
        detector = self.app.scanner.yolo
        tag = self.app.scanner.tag_template
        if not yolo_cfg.get("rope_assist", True) or tag is None or not detector.has_class("rope"):
            return None
        if img is None:
            img = self.app.vision.grab_client()
        if img is None:
            return None
        char = locate_char(img, tag)
        ropes = detector.detect_classes(img, "rope")
        if char is None or not ropes:
            return None
        rope = min(ropes, key=lambda r: abs(r[0] - char[0]))
        delta = int(rope[0] - char[0])
        return delta if abs(delta) <= max_distance else None

    def learn_rope_dx(self, rope, delta, save=True):
        """角色確定站在抓得到繩子的位置時呼叫：只記在這一根繩子上（不同繩子不互相影響），1.5 秒後自動存檔"""
        if delta is None or rope is None:
            return
        if abs(int(delta)) > ROPE_DX_MAX:
            # 角色站在抓得到繩子的位置時，名牌和繩子不會差這麼多：多半是 YOLO 沒看到腳下的繩子、量到旁邊那條
            log(f"繩子 X={rope.get('x')} 的 YOLO 偏移 {int(delta):+d} px 不合理，不採用（可能量到旁邊的繩子）", "warn")
            return
        if rope.get("yolo_dx") != int(delta):
            rope["yolo_dx"] = int(delta)
            log(f"學到繩子 X={rope.get('x')} 的 YOLO 偏移 {int(delta):+d} px")
            if save and hasattr(self.app, "schedule_save"):
                self.app.ui(self.app.schedule_save)

    def yolo_align_rope(self, max_distance=180, rope=None):
        """依畫面辨識到的繩子做最後水平對位。

        小地圖座標先負責走到「哪一根繩子」附近；這一步再用 YOLO 的繩子框修正實際畫面
        的左右誤差，特別適合小地圖格子與角色實際抓繩點不完全一致的情況。
        找不到人物名牌、模型或足夠近的繩子時安全地交回既有流程。
        """
        measured = self.yolo_rope_delta(max_distance=max_distance)
        if measured is None:
            return False
        # 角色抓得到繩子時，名牌中心和 YOLO 繩子中心本來就有固定偏移；對到「學到的偏移」而不是 0
        target = (rope or {}).get("yolo_dx")
        if target is not None and abs(int(target)) > ROPE_DX_MAX:
            rope.pop("yolo_dx", None)          # 舊版學到的不合理偏移：丟掉，之後重新學
            target = None
        if target is None:
            # 這根繩子還沒學到「抓得到時」的偏移：不用 YOLO 推位置（名牌中心和繩子中心本來就有差，也不借用別根繩子的值）
            return False
        target = int(target)
        delta = int(measured - target)
        if abs(delta) > ALIGN_MAX_PX:
            self.status = f"YOLO 繩子對位：差 {delta:+d} px 太遠，可能看到別條繩子，不採用"
            log(self.status, "warn")
            return False
        if abs(delta) <= 6:
            self.status = "YOLO 繩子對位完成"
            return True
        # 只做一次短距離修正；接下來仍由 grab_rope 的微調保證不會因誤判跑到遠處。
        px_time = self.__dict__.get("_px_time", 0.008)
        hold = min(0.38, max(0.025, abs(delta) * px_time))
        self.status = f"YOLO 繩子對位：差 {delta:+d} px（偏移 {target:+d}）"
        self.kb.tap(self.key("right") if delta > 0 else self.key("left"), hold)
        self.sleep(0.10, do_skills=False)
        return True

    def nudge_to(self, tx, max_taps=6):
        """短按方向鍵，一格一格挪到 tx（不放開已按住的上／下鍵）"""
        for _ in range(max_taps):
            self.check()
            p = self.pos()
            if p is None or p[0] == tx:
                return
            self.kb.tap(self.key("right") if tx > p[0] else self.key("left"), 0.03)
            time.sleep(0.12)

    def grab_rope(self, vkey, rope_x, direction, jump_to_grab=False):
        """按住 vkey（上或下）抓繩；抓不到就在按住的狀態下左右微調。direction=-1 往上、+1 往下"""
        def moving(p0, wait):
            end = time.time() + wait
            while time.time() < end:
                self.check()
                p = self.pos()
                if p and (p[1] - p0[1]) * direction >= 2:
                    return True
                time.sleep(0.03)
            return False

        p0 = self.pos()
        if p0 is None:
            return False
        self.kb.down(vkey)
        if jump_to_grab:
            self.sleep(0.05, do_skills=False)
            self.kb.tap(self.key("jump"))
        if moving(p0, 0.6):
            return True
        # 沒抓到：在繩子附近一步一步挪，每挪一次就「放開再重按」上／下
        # （有些版本只有按下的瞬間在繩子範圍內才抓得到，按住走過去不算）
        step = max(0.03, min(0.08, self.__dict__.get("_px_time", 0.008) * 8))   # 每步約 8 px
        for direction_key, n in ((self.key("right"), 4), (self.key("left"), 8), (self.key("right"), 4)):
            for _ in range(n):
                self.check()
                self.status = f"{'上' if direction < 0 else '下'}繩：微調位置找抓點"
                self.kb.up(vkey)
                self.kb.tap(direction_key, step)
                time.sleep(0.05)
                p0 = self.pos() or p0
                self.kb.down(vkey)
                if moving(p0, 0.3):
                    return True
        if direction < 0 and not jump_to_grab:   # 繩子離地有點高：按住上再跳一下
            p0 = self.pos() or p0
            self.kb.up(vkey)
            self.kb.down(vkey)
            self.kb.tap(self.key("jump"))
            if moving(p0, 0.7):
                return True
        return False

    def ride_rope(self, direction, stop_y=None):
        """已抓到繩子：繼續按住，直到不再移動（到頂／到底）、到達 stop_y、或被撞下繩"""
        best = self.pos()
        last_progress = time.time()
        start = time.time()
        while time.time() - start < 12:
            self.check()
            p = self.pos()
            if p is not None and best is not None:
                if (p[1] - best[1]) * direction > 0:
                    best, last_progress = p, time.time()
                elif (best[1] - p[1]) * direction > int(self.popt("plat_tol")):
                    return False          # 往反方向掉了一段：被撞下繩
                if stop_y is not None and (p[1] - stop_y) * direction >= 0:
                    return True
            if time.time() - last_progress > 0.9:
                return True
            time.sleep(0.03)
        return True

    def climb_rope(self, rope_x, top_y=None, attempts=3, jump_to_grab=False, anchor=None, rope=None):
        """上繩：走向繩子（快到時先按住上）→ 精準對位 → 按住上（抓不到就微調）→ 按住到頂 → 確認到了上一層"""
        tol = int(self.popt("plat_tol"))
        self.last_climb_land = None
        up = self.key("up")
        prehold = up if (not jump_to_grab and self.cfg.get("rope_prehold", True)) else None
        prehold_dist = max(1, int(self.cfg.get("rope_prehold_dist", 4)))
        for attempt in range(attempts):
            p0 = None
            try:
                if not self.goto(rope_x, tol=self.cfg["rope_tolerance"], prehold=prehold,
                                 prehold_dist=prehold_dist):
                    continue
                if prehold:
                    log(f"爬繩 X={rope_x}：" + ("接近時已提前抓到繩子" if self.early_grab
                                                else f"接近時（{prehold_dist} 格內按住上）沒抓到，改用對位後抓繩"))
                if self.early_grab:                       # 走過去時已經抓到繩子
                    p0 = (rope_x, self._prehold_y0)
                else:
                    self.quiet_wait(0.12)
                    aligned = bool(anchor) and self.screen_align(anchor)
                    if aligned:
                        # 精準地標對準＝角色站在記錄時抓得到繩子的位置：順便記下 YOLO 偏移，之後沒有地標時也對得準
                        if rope is not None and "yolo_dx" not in rope:
                            self.learn_rope_dx(rope, self.yolo_rope_delta())
                    else:
                        self.yolo_align_rope(rope=rope)
                    p0 = self.pos()
                if p0 is None or p0[1] is None:
                    continue
                self.status = f"爬繩 X={rope_x}（第 {attempt + 1} 次）"
                self.climbing = True
                if self.early_grab or self.grab_rope(up, rope_x, -1, jump_to_grab):
                    self.status = f"爬繩中 X={rope_x}"
                    self.ride_rope(-1, top_y)
            finally:
                self.kb.up(up)
                self.climbing = False
            land = self.wait_landed()
            if land and land[1] < p0[1] - tol:       # 真的到了比較高的地方
                self.last_climb_land = land
                return True
            self.status = f"沒爬上去（可能被撞下繩），重試 {attempt + 1}/{attempts}"
            self.sleep(0.3, do_skills=False)
        self.status = "爬繩失敗，跳過"
        return False

    def climb_down(self, rope_x, bottom_y=None, rope=None):
        """下繩：走到繩子頂端 → 按住下（抓不到就微調）→ 按住到底、角色落地 → 確認真的到了下一層"""
        tol = int(self.popt("plat_tol"))
        if not self.goto(rope_x, tol=self.cfg["rope_tolerance"]):
            return False
        self.quiet_wait(0.12)
        self.yolo_align_rope(rope=rope)
        p0 = self.pos()
        if p0 is None:
            return False
        self.status = f"下繩 X={rope_x}"
        self.climbing = True
        down = self.key("down")
        try:
            if self.grab_rope(down, rope_x, +1):
                self.status = f"下繩中 X={rope_x}"
                # 不在 bottom_y 就放開：小地圖 1 格約 12～15 px，到那一格時角色常常還掛在繩子上
                self.ride_rope(+1, None)
                self.quiet_wait(0.25)                     # 到底後再多按一下，確定落地
        finally:
            self.kb.up(down)
            self.climbing = False
        land = self.wait_landed()
        return bool(land and land[1] > p0[1] + tol)

    def do_step(self, st):
        t = st["type"]
        if t == "goto":
            self.goto(int(st["x"]))
        elif t == "rope":
            if st.get("macro") and self.play_macro(st["macro"]):
                pass
            else:
                self.climb_rope(int(st["x"]), st.get("top_y"), jump_to_grab=st.get("jump_to_grab", False))
        elif t == "macro":
            ok = self.play_macro(st, align=st.get("align", True))   # 錄製動作對起點很敏感，用精準對位
            if not ok:
                self.status = "錄製動作的終點和錄製時不同（繼續下一步）"
        elif t == "jump":
            d = st.get("dir", "")
            dk = self.key("left") if d == "left" else self.key("right") if d == "right" else None
            self.status = "跳躍"
            if dk:
                self.kb.down(dk)
            for _ in range(int(st.get("times", 1))):
                self.kb.tap(self.key("jump"))
                self.sleep(0.12, do_skills=False)
                if st.get("double"):
                    self.kb.tap(self.key("jump"))
                self.sleep(float(st.get("after", 0.5)), do_skills=False)
            if dk:
                self.kb.up(dk)
        elif t == "downjump":
            self.status = "下跳"
            self.kb.down(self.key("down"))
            time.sleep(0.08)
            self.kb.tap(self.key("jump"))
            time.sleep(0.15)
            self.kb.up(self.key("down"))
            self.sleep(float(st.get("after", 0.8)), do_skills=False)
        elif t == "attack":
            if self.combat_ready():
                acted = self.combat_engage()
                if acted or not self.cfg["combat"].get("fallback_blind", True):
                    return
            self.status = "攻擊"
            n = int(st.get("times", 5))
            interval = float(st.get("interval", self.cfg["attack"]["interval"]))
            d = st.get("dir", "")
            if d in ("left", "right"):
                self.kb.tap(self.key(d), 0.06)
            for _ in range(n):
                self.check()
                self.kb.tap(self.key("attack"))
                self.sleep(interval)
        elif t == "key":
            self.status = f"按鍵 {st['key']}"
            self.kb.tap(st["key"], float(st.get("hold", 0.05)))
            self.sleep(float(st.get("after", 0.3)))
        elif t == "wait":
            self.status = f"等待 {st['sec']} 秒"
            end = time.time() + float(st["sec"])
            while time.time() < end:
                self.check()
                self.tick_skills(allow_attack=True)
                time.sleep(0.03)

    # ---- 隨機巡邏（自動找路） ----
    def popt(self, k):
        return self.cfg["patrol_opt"][k]

    def down_jump_move(self):
        """下跳，回傳是否真的往下掉到別層"""
        p0 = self.pos()
        if p0 is None:
            return False
        self.status = "下跳"
        self.kb.down(self.key("down"))
        try:
            time.sleep(0.1)
            self.kb.tap(self.key("jump"))
            time.sleep(0.3)        # ↓ 持續按住到開始往下掉
        finally:
            self.kb.up(self.key("down"))
        # 等落地：y 連續 0.4 秒不變
        start, last_y, stable = time.time(), p0[1], time.time()
        while time.time() - start < 3:
            self.check()
            p = self.pos()
            if p and p[1] != last_y:
                last_y, stable = p[1], time.time()
            elif time.time() - stable > 0.4 and time.time() - start > 0.5:
                break
            time.sleep(0.03)
        return last_y - p0[1] > self.popt("plat_tol")

    def drop_at(self, r):
        """走到下跳點下跳；第一次跳會記住落在哪一層（之後找路會優先用下跳點，比下繩快）"""
        tol = int(self.popt("plat_tol"))
        self.status = f"前往下跳點 X={r['x']}"
        if not self.goto(int(r["x"])):
            return False
        self.kb.release_all()
        self.quiet_wait(0.1)
        p0 = self.pos()
        ok = self.down_jump_move()
        p = self.wait_landed()
        if ok and p and p0 and p[1] > p0[1] + tol:
            if r.get("lands_y") != p[1]:
                r["lands_y"] = p[1]
                log(f"下跳點 X={r['x']}：落在 Y={p[1]}")
                if hasattr(self.app, "schedule_save"):
                    self.app.ui(self.app.schedule_save)
                self.app.ui(self.app.reload_patrol)
            return True
        self.status = f"下跳點 X={r['x']}：沒有往下掉（下面可能沒有平台）"
        log(self.status, "warn")
        return False

    # ---- 找路：繩子（上／下）與跳台當成「通道」，規劃最短路線 ----
    def nav_links(self):
        tol = int(self.popt("plat_tol"))
        links = []
        for r in self.cfg["patrol"]:
            t = r.get("type")
            mac = r.get("macro")
            if t == "rope":
                sx = int(mac["start"][0]) if mac and mac.get("start") else int(r["x"])
                ly = r.get("lands_y")
                if ly is not None and ly < r["y"] - tol:
                    links.append({"kind": "up", "sx": sx, "sy": r["y"], "ex": sx, "ey": ly, "ref": r})
                    links.append({"kind": "down", "sx": sx, "sy": ly, "ex": sx, "ey": r["y"], "ref": r})
            elif t == "drop" and r.get("lands_y") is not None and r["lands_y"] > r["y"] + tol:
                links.append({"kind": "drop", "sx": int(r["x"]), "sy": int(r["y"]), "ex": int(r["x"]),
                              "ey": int(r["lands_y"]), "ref": r})
            if t == "rope":   # 繩組後面的下跳點也當成往下的通道（學到落點後）
                for d in r.get("chain") or []:
                    if d.get("lands_y") is not None and d["lands_y"] > d["y"] + tol:
                        links.append({"kind": "drop", "sx": int(d["x"]), "sy": int(d["y"]), "ex": int(d["x"]),
                                      "ey": int(d["lands_y"]), "ref": d})
            elif t == "jump" and mac and mac.get("start") and mac.get("end"):
                links.append({"kind": "jump", "sx": int(mac["start"][0]), "sy": int(mac["start"][1]),
                              "ex": int(mac["end"][0]), "ey": int(mac["end"][1]), "ref": r})
        return links

    def plan_path(self, cx, cy, tx, ty, banned=()):
        """Dijkstra：狀態＝「在某個位置」，邊＝走到通道起點＋通過通道。回傳通道清單或 None"""
        tol = int(self.popt("plat_tol"))
        links = [l for l in self.nav_links() if id(l["ref"]) not in banned or l["kind"] == "down"]
        WALK = 1 / 25.0                       # 走 25 格≈通過一個通道的成本
        import heapq
        start = (cx, cy)
        best = {start: 0.0}
        heap = [(0.0, 0, start, [])]
        seq = 1
        goal_cost, goal_path = None, None
        while heap:
            cost, _, (x, y), path = heapq.heappop(heap)
            if goal_cost is not None and cost >= goal_cost:
                break
            if abs(y - ty) <= tol:
                c = cost + abs(x - tx) * WALK
                if goal_cost is None or c < goal_cost:
                    goal_cost, goal_path = c, path
            if len(path) >= 8:
                continue
            for l in links:
                if abs(l["sy"] - y) > tol or (l in path):
                    continue
                c = cost + abs(x - l["sx"]) * WALK + {"jump": 1.2, "drop": 0.6, "down": 1.6}.get(l["kind"], 1.0)   # 往下優先下跳點，其次下繩
                nxt = (l["ex"], l["ey"])
                if c < best.get(nxt, 1e9):
                    best[nxt] = c
                    heapq.heappush(heap, (c, seq, nxt, path + [l]))
                    seq += 1
        return goal_path

    def run_link(self, l):
        tol = int(self.popt("plat_tol"))
        r = l["ref"]
        if l["kind"] == "up":
            return self.climb_and_learn(r)
        if l["kind"] == "down":
            return self.climb_down(l["sx"], l["ey"], rope=r)
        if l["kind"] == "drop":
            return self.drop_at(r)
        # 跳台：重播錄製的跳躍，確認落在錄製時的位置
        self.status = f"跳台：({l['sx']},{l['sy']}) → ({l['ex']},{l['ey']})"
        self.play_macro(r["macro"], anchor=r.get("screen_anchor"))
        p = self.pos()
        return bool(p and abs(p[1] - l["ey"]) <= tol and abs(p[0] - l["ex"]) <= 8)

    def navigate(self, tx, ty, max_hops=12):
        """移動到 (tx, ty)。同層就走；不同層先用記錄的繩子／跳台規劃路線，沒有路線才用舊方法（試沒爬過的繩子、下跳）"""
        tol = int(self.popt("plat_tol"))
        fails = 0
        banned = set()
        for _ in range(max_hops):
            self.check()
            p = self.pos()
            if p is None:
                self.sleep(0.2)
                continue
            cx, cy = p
            if abs(cy - ty) <= tol:
                return self.goto(tx)
            if ty > cy + tol:   # 要往下：本層有還沒跳過的下跳點，先用它（學到落點後，之後找路就會優先走下跳）
                drops = [r for r in self.cfg["patrol"] if r.get("type") == "drop" and abs(r["y"] - cy) <= tol
                         and r.get("lands_y") is None and id(r) not in banned]
                if drops:
                    r = min(drops, key=lambda r: abs(r["x"] - cx))
                    if not self.drop_at(r):
                        banned.add(id(r))
                        fails += 1
                    continue
            path = self.plan_path(cx, cy, tx, ty, banned)
            if path:
                l = path[0]
                self.status = f"路線：還有 {len(path)} 段（下一段：{ {'up': '上繩', 'down': '下繩', 'jump': '跳台', 'drop': '下跳'}[l['kind']] }）"
                if self.run_link(l):
                    continue
                fails += 1
                banned.add(id(l["ref"]))     # 這次找路先不用這條通道
                if fails >= 4:
                    return False
                continue
            # 沒有已知路線：退回舊方法
            if ty < cy:  # 目標在上面 → 試本層還沒爬過的繩子
                ropes = [r for r in self.cfg["patrol"] if r["type"] == "rope" and abs(r["y"] - cy) <= tol
                         and id(r) not in banned]
                if ropes:
                    r = min(ropes, key=lambda r: (r.get("lands_y") is not None, abs(r["x"] - cx), random.random()))
                    if not self.climb_and_learn(r):
                        banned.add(id(r))
                        fails += 1
                    continue
                if not self.down_jump_move():
                    fails += 1
            else:        # 目標在下面 → 走到目標上方附近下跳
                self.goto(tx, timeout=6)
                if not self.down_jump_move():
                    fails += 1
            if fails >= 3:
                return False
        return False

    def play_macro(self, rec, align=True, align_tol=None, anchor=None, suppress_loot=False, allow_buffs=False):
        """重播錄製的按鍵。align=True 時先走到錄製起點。回傳是否到達錄製終點（無終點資料時回傳 True）"""
        if not rec or not rec.get("events"):
            return False
        tol = int(self.popt("plat_tol"))
        start, end = rec.get("start"), rec.get("end")
        if align and start:
            p = self.pos()
            if p and abs(p[1] - start[1]) > tol:
                self.navigate(int(start[0]), int(start[1]))
            self.goto(int(start[0]), tol=self.cfg["rope_tolerance"] if align_tol is None else align_tol)
            self.sleep(0.15, do_skills=False)
            anchor = anchor or rec.get("screen_anchor")
            if anchor:
                self.screen_align(anchor)
                self.sleep(0.08, do_skills=False)
        self.status = f"重播錄製動作（{macro_summary(rec)}）"
        pressed = set()
        self.climbing = not allow_buffs
        old_in_loot = self.in_loot
        if suppress_loot:
            self.in_loot = True       # 全圖錄製優先完整重播，不中途轉去撿物
        try:
            t0 = time.perf_counter()
            monitor_path = rec.get("path") if rec.get("play_mode") == "guarded" else None
            monitor_tolerance = max(3, int(rec.get("position_tolerance", 10)))
            monitor_bad_since = None
            monitor_checked_at = 0.0
            for event in rec["events"]:
                if isinstance(event, dict) and event.get("kind") == "mouse":
                    t = event.get("t", 0)
                    name, down = event.get("button"), event.get("down")
                    is_mouse = True
                else:
                    t, name, down = event[:3]
                    is_mouse = False
                while True:
                    wait_started = time.perf_counter()
                    self.check(allow_elite=False)
                    # 「座標監看」不嘗試猜測地圖、也不亂按方向修正；只在連續偏離時安全暫停。
                    # 這能避免傳送、斷線、被撞偏後仍把整段錄製操作送進遊戲。
                    now = time.perf_counter()
                    if monitor_path and now - monitor_checked_at >= 0.10:
                        monitor_checked_at = now
                        expected = macro_position_at(monitor_path, now - t0)
                        actual = self.pos()
                        if expected and actual:
                            error = max(abs(actual[0] - expected[0]), abs(actual[1] - expected[1]))
                            if error > monitor_tolerance:
                                monitor_bad_since = monitor_bad_since or now
                                if now - monitor_bad_since >= 0.8:
                                    self.status = (f"路徑座標偏離 {error} 格（容許 {monitor_tolerance}），"
                                                   "已安全暫停")
                                    self.active.clear()
                                    self.app.ui(lambda: (self.app._after_pause(), self.app.notify(
                                        "錄製路徑與目前座標偏離，已暫停；請回到錄製起點後再開始。", error=True)))
                                    return False
                            else:
                                monitor_bad_since = None
                    # 全圖錄製播放時，只在沒有按住移動鍵的空檔補 Buff；補 Buff 的時間不算進錄製節奏。
                    if allow_buffs and not pressed:
                        self.tick_skills()
                    t0 += time.perf_counter() - wait_started
                    wait = t0 + float(t) - time.perf_counter()
                    if wait <= 0:
                        break
                    time.sleep(min(wait, 0.01))
                if is_mouse:
                    mouse_button_at(self.app.vision.hwnd, event.get("x", 0), event.get("y", 0), name,
                                    up=not bool(down))
                elif down:
                    self.kb.down(name)
                    pressed.add(name)
                else:
                    self.kb.up(name)
                    pressed.discard(name)
        finally:
            for k in pressed:
                try:
                    self.kb.up(k)
                except Exception:
                    pass
            self.climbing = False
            self.in_loot = old_in_loot
        p = self.wait_landed()
        if not end:
            return True
        return bool(p and abs(p[1] - end[1]) <= tol)

    def climb_and_learn(self, r):
        """爬一條繩子：有有效的錄製動作就先重播（最多 2 次），不行再自動爬；確認爬上去才記落點"""
        tol = int(self.popt("plat_tol"))
        mac = r.get("macro")
        if mac and (not mac.get("end") or not mac.get("start") or mac["end"][1] >= mac["start"][1] - tol):
            mac = None   # 無效的錄製（終點沒有比起點高）不使用
        if mac:
            for attempt in range(2):
                self.status = f"爬繩（錄製動作，第 {attempt + 1} 次）"
                self.play_macro(mac, anchor=r.get("screen_anchor"))
                p = self.pos()
                if p and p[1] < mac["start"][1] - tol:      # 真的爬到比起點高
                    if r.get("lands_y") != p[1]:
                        r["lands_y"] = p[1]
                        save_config(self.cfg)
                        self.app.ui(self.app.reload_patrol)
                    return True
                self.sleep(0.5, do_skills=False)
            self.status = "錄製動作沒有爬上去，改用自動爬繩"
        ok = self.climb_rope(int(r["x"]), jump_to_grab=r.get("jump_to_grab", False), rope=r,
                             anchor=r.get("screen_anchor"))
        land = getattr(self, "last_climb_land", None)
        if ok and land and r.get("lands_y") != land[1]:   # 只有確認爬上去、站穩後才記落點
            r["lands_y"] = land[1]
            save_config(self.cfg)
            self.app.ui(self.app.reload_patrol)
        return ok

    def rope_pairs(self):
        """有設定「繩上定點」的繩子＝一組（繩下點＋繩上點）"""
        return [i for i, t in enumerate(self.cfg["patrol"]) if t.get("type") == "rope" and t.get("top")]

    def pair_patrol_once(self):
        """BUFF 機：隨機挑一組繩子 → 走到繩下 → 爬上去 → 走到繩上定點 → 停一下（不攻擊）"""
        pairs = self.rope_pairs()
        cands = [i for i in pairs if i != self.last_target] or pairs
        i = random.choice(cands)
        r = self.cfg["patrol"][i]
        n = pairs.index(i) + 1
        self.last_target = i
        self.app.highlight_patrol(i)
        tx, ty = int(r["top"][0]), int(r["top"][1])
        self.status = f"繩組 {n}：前往繩下 ({r['x']},{r['y']})"
        if not self.navigate(int(r["x"]), int(r["y"])):
            self.nav_fail += 1
            self.status = f"繩組 {n}：到不了繩下，換下一組"
            log(self.status, "warn")
            if self.nav_fail >= 5:
                self.app.trigger_alarm("stuck", "BUFF機連續 5 次到不了繩組，可能卡住了", pause=True, beep=True)
                self.nav_fail = 0
            return
        self.status = f"繩組 {n}：爬繩"
        if not self.climb_and_learn(r):
            self.nav_fail += 1
            self.status = f"繩組 {n}：沒爬上去，換下一組"
            log(self.status, "warn")
            return
        self.status = f"繩組 {n}：走到繩上定點 ({tx},{ty})"
        p = self.pos()
        ok = self.navigate(tx, ty) if (p is None or abs(p[1] - ty) > int(self.popt("plat_tol"))) \
            else self.goto(tx)
        self.nav_fail = 0 if ok else self.nav_fail + 1
        self.kb.release_all()                 # 到點就停住，不左右掃
        lo, hi = sorted((float(self.popt("stay_min")), float(self.popt("stay_max"))))
        self.status = f"繩組 {n}：到達，停留"
        self.sleep(random.uniform(lo, hi))
        # 接在這組後面的下跳點：依記錄順序走過去下跳（例如上層 → 中層 → 地面）
        tol = int(self.popt("plat_tol"))
        for k, d in enumerate(r.get("chain") or []):
            p = self.pos()
            if p is None:
                break
            if abs(p[1] - int(d["y"])) > tol:
                self.status = f"繩組 {n}：前往第 {k + 1} 個下跳點 ({d['x']},{d['y']})"
                if not self.navigate(int(d["x"]), int(d["y"])):
                    log(f"繩組 {n}：到不了第 {k + 1} 個下跳點，結束這一組", "warn")
                    break
            self.status = f"繩組 {n}：第 {k + 1} 個下跳點"
            if not self.drop_at(d):
                log(f"繩組 {n}：第 {k + 1} 個下跳點沒有往下掉，結束這一組", "warn")
                break
            self.kb.release_all()

    def patrol_once(self, attack=True):
        pts = self.cfg["patrol"]
        cands = [i for i, t in enumerate(pts)
                 if (t["type"] == "point" or (t["type"] == "rope" and self.popt("rope_as_target")))
                 and i != self.last_target]
        if not cands:
            cands = [i for i, t in enumerate(pts) if t["type"] in ("point", "rope")] or [0]
        i = random.choice(cands)
        t = pts[i]
        self.last_target = i
        self.app.highlight_patrol(i)
        kind = ("巡邏點" if not attack else "攻擊點") if t["type"] == "point" else "繩子"
        self.status = f"隨機目標 #{i + 1}：{kind} ({t['x']},{t['y']})"
        jit = int(self.popt("x_jitter")) if t["type"] == "point" else 0
        tx = int(t["x"]) + random.randint(-jit, jit)
        if not self.navigate(tx, int(t["y"])):
            self.nav_fail += 1
            self.status = f"到不了目標 #{i + 1}，換下一個"
            if self.nav_fail >= 5:
                self.app.trigger_alarm("stuck", "隨機巡邏連續 5 次到不了目標，可能卡住了", pause=True, beep=True)
                self.nav_fail = 0
            return
        self.nav_fail = 0
        if t["type"] == "rope":
            self.climb_and_learn(t)
        elif self.cfg.get("mode") == "buff":
            self.sweep()
        elif attack:
            if self.combat_ready():
                acted = self.combat_engage()
                if acted or not self.cfg["combat"].get("fallback_blind", True):
                    lo, hi = sorted((float(self.popt("stay_min")), float(self.popt("stay_max"))))
                    self.sleep(random.uniform(lo, hi))
                    return
            a, b = sorted((int(self.popt("attack_min")), int(self.popt("attack_max"))))
            n = random.randint(a, b)
            if n > 0:
                self.kb.tap(self.key(random.choice(("left", "right"))), 0.03)
                for _ in range(n):
                    self.check()
                    self.status = f"攻擊點 #{i + 1}：攻擊"
                    self.kb.tap(self.key("attack"))
                    self.sleep(float(self.cfg["attack"]["interval"]) * random.uniform(0.9, 1.2))
        lo, hi = sorted((float(self.popt("stay_min")), float(self.popt("stay_max"))))
        self.sleep(random.uniform(lo, hi))


    # ---- BUFF機：撿物 ----
    def _loot_tapper(self):
        """BUFF機模式下持續連點撿物鍵（爬繩時不按）"""
        while self.alive:
            lt = self.cfg["loot"]
            ok = (self.active.is_set() and self.cfg.get("mode") == "buff" and lt.get("enabled", True)
                  and lt.get("auto_tap", True)
                  and lt.get("key") and not self.climbing and self.app.alarm_kind != "lie")
            if ok and self.cfg.get("only_when_focused") and IS_WIN and not is_foreground(self.app.vision.hwnd):
                ok = False
            if ok:
                try:
                    self.kb.tap(lt["key"], 0.03)
                except Exception:
                    pass
            time.sleep(float(lt.get("tap_interval", 0.12)))

    def _item_mm_x(self, dx, p):
        """把物品的畫面水平距離換算成小地圖 X（需要已學到比例）"""
        if self.loot_k and p:
            return p[0] + dx / self.loot_k
        return None

    def _ignored(self, dx, p, now):
        for ix, iy, exp in self.loot_ignore:
            if exp < now or p is None or abs(p[1] - iy) > 3:
                continue
            mx = self._item_mm_x(dx, p)
            if mx is not None and abs(mx - ix) <= 2:
                return True
            if mx is None and abs(p[0] - ix) <= 1 and abs(dx) <= 30:   # 還沒學到比例：只能判斷腳下這個
                return True
        return False

    def _learn_k(self, p0, d0, p1, items_after):
        """角色移動後，用同一個物品的畫面位移 / 小地圖位移 估計比例"""
        if not (p0 and p1 and items_after) or abs(p1[0] - p0[0]) < 2:
            return
        dm = p1[0] - p0[0]
        guess = self.loot_k or 10.0
        d1 = min((t[0] for t in items_after), key=lambda d: abs(d - (d0 - dm * guess)))
        k = (d0 - d1) / dm
        if 2 <= k <= 60:
            self.loot_k_hist = (self.loot_k_hist + [k])[-7:]
            self.loot_k = sorted(self.loot_k_hist)[len(self.loot_k_hist) // 2]

    def loot_targets(self):
        """回傳 (角色座標, [(dx, x, y), ...])：同一層、範圍內、沒被放棄的物品"""
        sc = self.app.scanner
        if not self.cfg["loot"].get("enabled", True) or not sc.loot_ready():
            return None, []
        snap = sc.snap
        if not snap or len(snap) < 4 or time.time() - snap[0] > 1.0 or snap[1] is None:
            return None, []
        char, items = snap[1], snap[3]
        lt = self.cfg["loot"]
        now = time.time()
        p = self.pos()
        out = []
        for x, y, _, _ in items:
            dx = x - char[0]
            if abs(y - char[1]) > float(lt["y_range"]) or abs(dx) > float(lt["range"]):
                continue
            if self.loot_ignore and self._ignored(dx, p, now):
                continue
            out.append((dx, x, y))
        return char, out

    def loot_items(self, max_sec=25):
        """走到每個看得到的同層物品上撿起來，直到看不到為止"""
        lt = self.cfg["loot"]
        key = lt.get("key") or "z"
        radius = float(lt.get("pick_radius", 15))
        start = last_seen = time.time()
        self.in_loot = True
        picked = 0
        try:
            while time.time() - start < max_sec:
                self.check()
                self.tick_skills()
                char, items = self.loot_targets()
                if not items:
                    if time.time() - last_seen > 0.6:
                        break
                    time.sleep(0.05)
                    continue
                last_seen = time.time()
                dx, ix, iy = min(items, key=lambda t: abs(t[0]))
                if abs(dx) <= radius:
                    p = self.pos() or (0, 0)
                    b = (p[0], p[1])
                    self.loot_tries[b] = self.loot_tries.get(b, 0) + 1
                    self.status = f"撿物（第 {self.loot_tries[b]} 次）"
                    if self.loot_tries[b] > 1 and abs(dx) > 4:   # 上次沒撿到：再往物品挪一點
                        self.kb.tap(self.key("right" if dx > 0 else "left"), 0.03)
                        time.sleep(0.1)
                    for _ in range(3):
                        self.kb.tap(key, 0.04)
                        time.sleep(0.08)
                    time.sleep(0.15)
                    if self.loot_tries[b] >= int(lt.get("max_tries", 3)):
                        self.status = "這個物品撿不起來，30 秒內先略過"
                        self.loot_ignore.append((p[0] + dx / self.loot_k if self.loot_k else p[0], p[1],
                                                 time.time() + 30))
                        self.loot_tries.pop(b, None)
                    picked += 1
                    continue
                side = "right" if dx > 0 else "left"
                k = self.key(side)
                self.status = f"走向物品（{'右' if side == 'right' else '左'} {abs(int(dx))}px，同層 {len(items)} 個）"
                if abs(dx) < 70:   # 接近時用點按微調，避免走過頭
                    self.kb.tap(k, 0.05 if abs(dx) > 35 else 0.03)
                    time.sleep(0.12)
                else:
                    p0 = self.pos()
                    self.kb.down(k)
                    t0 = time.time()
                    its = None
                    while time.time() - t0 < 1.2:
                        self.check()
                        _, its = self.loot_targets()
                        if not its or min(abs(t[0]) for t in its) < 70:
                            break
                        time.sleep(0.03)
                    self.kb.up(k)
                    time.sleep(0.05)
                    self._learn_k(p0, dx, self.pos(), self.loot_targets()[1])
                self.facing = side
            # 清掉過期的忽略紀錄
            now = time.time()
            self.loot_ignore = [e for e in self.loot_ignore if e[2] > now]
        finally:
            self.in_loot = False
            self.kb.release_all()
        return picked

    def sweep(self):
        """在原地左右掃一小段，補撿沒辨識到的物品"""
        sec = float(self.cfg["loot"].get("sweep_sec", 0.5))
        if sec <= 0 or not self.cfg["loot"].get("enabled", True):
            return
        first = random.choice(("left", "right"))
        second = "left" if first == "right" else "right"
        for side, dur in ((first, sec), (second, sec * 2), (first, sec)):
            self.status = "掃地撿物"
            k = self.key(side)
            self.kb.down(k)
            try:
                self.sleep(dur * random.uniform(0.85, 1.15))
            finally:
                self.kb.up(k)

    # ---- 定點掛機 ----
    def anchor_points(self):
        a = self.cfg["anchor"]
        if a.get("points"):
            return a["points"]
        if a.get("x") is not None and a.get("y") is not None:   # 舊版單一定點
            return [[a["x"], a["y"]]]
        return []

    def anchor_xy(self):
        pts = self.anchor_points()
        if not pts:
            return None
        self.anchor_idx %= len(pts)
        return int(pts[self.anchor_idx][0]), int(pts[self.anchor_idx][1])

    def anchor_drifted(self, p):
        a = self.cfg["anchor"]
        ax, ay = self.anchor_xy()
        if not a.get("use_ropes", False):      # 不爬繩：只看左右，掉到別層就在那一層的定點 X 繼續打
            return abs(p[0] - ax) > int(a.get("tol_x", 4))
        return (abs(p[0] - ax) > int(a.get("tol_x", 4))
                or abs(p[1] - ay) > int(self.cfg["patrol_opt"]["plat_tol"]))

    def anchor_return(self, reason="離開定點"):
        """放開所有鍵，走／爬到目前的定點"""
        a = self.cfg["anchor"]
        ax, ay = self.anchor_xy()
        self.kb.release_all()
        self.status = f"{reason}，前往定點 #{self.anchor_idx + 1} ({ax},{ay})"
        self.app.highlight_anchor(self.anchor_idx)
        if not a.get("use_ropes", False):
            # 定點掛機不爬繩：只在目前這一層左右走回定點 X
            ok = self.goto(ax, tol=int(a.get("tol_x", 4)))
            self.nav_fail = 0 if ok else self.nav_fail + 1
            if self.nav_fail >= 6:
                self.app.trigger_alarm("stuck", "定點掛機：連續多次走不到定點", pause=True, beep=True)
                self.nav_fail = 0
            return ok
        ok = self.navigate(ax, ay)
        if ok:
            self.nav_fail = 0
            self.goto(ax, tol=int(a.get("tol_x", 4)))
        else:
            self.nav_fail += 1
            self.status = "到不了定點，重試中…（請確認「隨機巡邏」頁有記錄需要的繩子）"
            if self.nav_fail >= 3 and len(self.anchor_points()) > 1:
                self.next_anchor()          # 這個點一直到不了，先換別的點
            if self.nav_fail >= 6:
                self.app.trigger_alarm("stuck", "定點掛機：連續多次到不了定點", pause=True, beep=True)
                self.nav_fail = 0
        return ok

    def next_anchor(self):
        a = self.cfg["anchor"]
        n = len(self.anchor_points())
        if n > 1:
            if a.get("random_order", True):
                self.anchor_idx = random.choice([i for i in range(n) if i != self.anchor_idx])
            else:
                self.anchor_idx = (self.anchor_idx + 1) % n
        lo, hi = sorted((float(a.get("rotate_min", 60)), float(a.get("rotate_max", 120))))
        self.anchor_dwell = random.uniform(lo, hi)
        self.anchor_since = None   # 抵達後才開始計時

    def anchor_once(self):
        a = self.cfg["anchor"]
        if not self.anchor_points():
            self.status = "定點掛機：尚未記錄定點（「定點」頁）"
            time.sleep(0.3)
            return
        if self.anchor_dwell is None:
            self.next_anchor()
            self.anchor_idx = 0 if not a.get("random_order", True) else \
                random.randrange(len(self.anchor_points()))
        p = self.pos()
        if p is None:
            self.kb.release_all()
            self.status = "找不到角色座標"
            self.sleep(0.2)
            return
        now = time.time()
        if self.anchor_drifted(p):
            self.drift_since = self.drift_since or now
            first = self.anchor_since is None
            if first or now - self.drift_since >= float(a.get("drift_sec", 0.6)):
                self.anchor_return("換點" if first else "離開定點")
                self.drift_since = None
            else:
                time.sleep(0.03)
            return
        self.drift_since = None
        if self.anchor_since is None:
            self.anchor_since = now
        # 換點時間到
        if len(self.anchor_points()) > 1 and now - self.anchor_since >= self.anchor_dwell:
            self.kb.release_all()
            self.next_anchor()
            return
        hk = a.get("hold_key")
        if hk:
            if hk not in self.kb.held or (a.get("repeat", True) and now - self.hold_sent >= 0.2):
                self.kb.down(hk)
                self.hold_sent = now
        left = (f"，{int(self.anchor_dwell - (now - self.anchor_since))} 秒後換點"
                if len(self.anchor_points()) > 1 else "")
        self.status = f"定點 #{self.anchor_idx + 1}：按住 {hk}{left}"
        ts = float(a.get("turn_sec", 0))
        if ts > 0 and now - self.last_turn >= ts:
            self.facing = "left" if self.facing == "right" else "right"
            self.kb.tap(self.key(self.facing), 0.03)
            self.last_turn = now
        self.tick_skills()
        time.sleep(0.03)

    # ---- 自動戰鬥 ----
    def combat_ready(self):
        return self.app.scanner.ready()

    def combat_targets(self):
        """回傳 (角色座標, [同一層怪物與角色的水平距離 dx ...])；資料過舊回傳 (None, [])"""
        snap = self.app.scanner.snap
        if not snap or time.time() - snap[0] > 1.0:
            return None, []
        char, mons = snap[1], snap[2]
        if char is None:
            return None, []
        yr = float(self.cfg["combat"]["y_range"])
        return char, [mx - char[0] for mx, my, _, _ in mons if abs(my - char[1]) <= yr]

    def combat_other_layers(self):
        """同層以外、畫面上看得到的怪：回傳 [(dx, dy) 畫面 px]"""
        snap = self.app.scanner.snap
        if not snap or time.time() - snap[0] > 1.0 or snap[1] is None:
            return []
        char, mons = snap[1], snap[2]
        yr = float(self.cfg["combat"]["y_range"])
        return [(mx - char[0], my - char[1]) for mx, my, _, _ in mons if abs(my - char[1]) > yr]

    def go_toward_layer(self, dy_screen):
        """往有怪的那一層移動：挑記錄點中高度最接近的位置，走過去（看到同層有怪就會中途停下來打）"""
        p = self.pos()
        if p is None:
            return False
        tol = int(self.popt("plat_tol"))
        k = float(self.cfg["combat"].get("screen_per_minimap", 15))
        est_y = p[1] + dy_screen / k
        spots = []
        for t in self.cfg["patrol"]:
            spots.append((t["x"], t["y"]))
            if t.get("lands_y") is not None:
                spots.append((t["x"], t["lands_y"]))
            end = (t.get("macro") or {}).get("end")
            if end:
                spots.append(tuple(end))
        spots += [tuple(a) for a in self.anchor_points()]
        spots = [sp for sp in spots if abs(sp[1] - p[1]) > tol and (sp[1] - p[1]) * dy_screen > 0]
        if not spots:
            return False
        tx, ty = min(spots, key=lambda sp: (abs(sp[1] - est_y), abs(sp[0] - p[0])))
        self.status = f"同層沒怪，{'上' if dy_screen < 0 else '下'}面有怪 → 前往 ({tx},{ty})"
        return self.navigate(int(tx), int(ty))

    def blind_sweep(self):
        """到點了還是沒偵測到怪：左右各打兩下（打到辨識不到的怪）"""
        cb = self.cfg["combat"]
        key = (cb["single"].get("key") or "").strip().lower() or self.key("attack")
        for side in ("left", "right"):
            self.face(side)
            for _ in range(2):
                self.check()
                self.status = "沒偵測到怪：左右試打"
                self.kb.tap(key)
                self.sleep(float(cb["single"].get("interval", 0.5)))
                if self.combat_targets()[1]:
                    return

    def combat_search(self):
        """未記錄巡邏點時，在目前平台左右巡查；一看到怪就交回戰鬥邏輯。"""
        sec = float(self.cfg["combat"].get("search_sec", 0.8))
        if sec <= 0:
            self.status = "畫面上沒有怪（請記錄巡邏點，或啟用左右巡查）"
            self.tick_skills()
            time.sleep(0.15)
            return False
        first = random.choice(("left", "right"))
        for side in (first, "right" if first == "left" else "left"):
            if self.combat_targets()[1]:
                return True
            self.status = f"搜尋怪物：往{'左' if side == 'left' else '右'}巡查"
            key = self.key(side)
            self.kb.down(key)
            try:
                end = time.time() + sec
                while time.time() < end:
                    self.check()
                    if self.combat_targets()[1]:
                        return True
                    time.sleep(0.03)
            finally:
                self.kb.up(key)
        return bool(self.combat_targets()[1])

    def target_in_reach(self):
        if not self.combat_ready():
            return False
        cb = self.cfg["combat"]
        _, dxs = self.combat_targets()
        reach = max(float(cb["single"]["range"]), float(cb["aoe"]["range"]))
        return any(abs(d) <= reach for d in dxs)

    def face(self, side):
        if self.facing != side or self.cfg["combat"].get("always_face"):
            self.kb.tap(self.key(side), 0.03)
            self.facing = side

    def combat_engage(self, max_sec=None):
        """鎖定畫面上同一層的怪物攻擊，直到看不到怪。回傳攻擊次數"""
        cb = self.cfg["combat"]
        single, aoe = cb["single"], cb["aoe"]
        max_sec = float(max_sec if max_sec is not None else cb.get("engage_max_sec", 40))
        start = last_seen = time.time()
        acted = 0
        prev_n, prev_d = None, None
        best_gap, last_progress = None, time.time()   # 追擊：只要距離一直在縮短就繼續追
        self.in_combat = True
        try:
            while True:
                self.check()
                now = time.time()
                if now - start > max_sec:
                    self.status = "交戰超時，先離開（可能是誤判的背景）"
                    self.combat_quiet_until = now + 5
                    break
                char, dxs = self.combat_targets()
                if char is None or not dxs:
                    if now - last_seen > 0.8:
                        break
                    time.sleep(0.05)
                    continue
                last_seen = now
                # 怪變少（打死了）或換了一隻目標：追擊時間重新計算，馬上追下一隻
                near = min(dxs, key=abs)
                if prev_n is not None and (len(dxs) < prev_n or (prev_d is not None and abs(abs(near) - abs(prev_d)) > 150)):
                    best_gap, last_progress = None, now            # 換目標：重新計算
                    start = now if now - start > max_sec * 0.5 else start
                prev_n, prev_d = len(dxs), near
                ar = float(aoe["range"])
                left = sum(1 for d in dxs if -ar <= d < 0)
                right = sum(1 for d in dxs if 0 <= d <= ar)
                side, cnt = ("left", left) if left > right else ("right", right)
                # 範圍技：同一側怪物數量足夠且冷卻好了
                if aoe.get("key") and cnt >= int(aoe["min_count"]) and now - self.aoe_last >= float(aoe["cooldown"]):
                    self.status = f"⚔ 範圍攻擊（{side}，{cnt} 隻）"
                    self.face(side)
                    self.kb.tap(aoe["key"])
                    self.aoe_last = time.time()
                    acted += 1
                    self.sleep(float(aoe.get("delay", 0.7)))
                    continue
                d = min(dxs, key=abs)
                side = "right" if d >= 0 else "left"
                if abs(d) <= float(single["range"]):
                    self.status = f"⚔ 單體攻擊（{side}，距離 {abs(int(d))}px，畫面上同層 {len(dxs)} 隻）"
                    self.face(side)
                    self.kb.tap((single.get("key") or "").strip().lower() or self.key("attack"))
                    acted += 1
                    self.sleep(float(single.get("interval", 0.5)))
                elif cb.get("approach") and now - last_progress < float(cb.get("approach_max_sec", 4)):
                    self.status = f"追擊：往{'右' if side == 'right' else '左'}（距離 {abs(int(d))}px）"
                    k = self.key(side)
                    self.kb.down(k)
                    self.facing = side
                    t0 = time.time()
                    while time.time() - t0 < 0.25:
                        self.check()
                        _, dd = self.combat_targets()
                        if dd and min(abs(x) for x in dd) <= float(single["range"]) * 0.8:
                            break
                        time.sleep(0.03)
                    self.kb.up(k)
                    _, dd = self.combat_targets()
                    gap = min(abs(x) for x in dd) if dd else abs(d)
                    if best_gap is None or gap < best_gap - 8:     # 有更接近：繼續追
                        best_gap, last_progress = gap, time.time()
                else:
                    self.status = f"追不到這隻（{abs(int(d))}px，可能隔著坑或牆），換別的目標"
                    self.combat_quiet_until = time.time() + 3
                    break
        finally:
            self.in_combat = False
            self.kb.release_all()
        return acted

    # ---- 菁英模式 ----
    def elite_fight(self):
        el = self.cfg["elite"]
        self.in_elite = True
        self.elite_last = {}
        start = time.time()
        last_turn = time.time()
        last_atk = 0
        facing = random.choice(("left", "right"))
        atk_key = (el.get("attack_key") or "").strip().lower() or self.key("attack")
        if el.get("beep") and IS_WIN:
            threading.Thread(target=lambda: [__import__("winsound").Beep(1000, 120) for _ in range(2)],
                             daemon=True).start()
        hold = bool(el.get("hold_attack"))
        drift_since = None
        try:
            while True:
                self.check(allow_elite=False)
                now = time.time()
                # 定點掛機：菁英戰中被打離定點也要回去
                if self.cfg.get("mode") == "anchor" and self.anchor_points():
                    p = self.pos()
                    if p and self.anchor_drifted(p):
                        drift_since = drift_since or now
                        if now - drift_since >= float(self.cfg["anchor"].get("drift_sec", 0.6)):
                            self.anchor_return()
                            drift_since = None
                            continue
                    else:
                        drift_since = None
                if not self.elite_present():
                    self.status = "菁英怪已消失，回到原本模式"
                    return
                if now - start > float(el.get("max_sec", 180)):
                    self.app.trigger_alarm("stuck", "菁英模式超過最長時間，已回到原本模式",
                                           pause=False, beep=True)
                    self.app.vision.elite_seen_at = 0
                    return
                self.status = f"⚔ 菁英模式（{int(now - start)} 秒）"
                # 菁英技能（依冷卻）
                casted = False
                for i, sk in enumerate(el.get("skills", [])):
                    if sk.get("enabled", True) and now - self.elite_last.get(i, 0) >= float(sk["cooldown"]):
                        self.status = f"⚔ 菁英模式：{sk['name']}"
                        if hold and atk_key in self.kb.held:
                            self.kb.up(atk_key)
                        self.kb.tap(sk["key"])
                        self.elite_last[i] = time.time()
                        self.sleep(float(sk.get("delay", 0.6)), do_skills=False)
                        casted = True
                        break
                if casted:
                    continue
                # 轉身
                ts = float(el.get("turn_sec", 0))
                if ts > 0 and now - last_turn >= ts:
                    facing = "left" if facing == "right" else "right"
                    self.kb.tap(self.key(facing), 0.03)
                    last_turn = now
                # 一般 Buff 照常
                self.tick_skills()
                # 主攻擊
                if hold:
                    if atk_key not in self.kb.held or now - last_atk >= 0.2:
                        self.kb.down(atk_key)
                        last_atk = now
                elif now - last_atk >= float(el.get("attack_interval", 0.5)):
                    self.kb.tap(atk_key)
                    last_atk = time.time()
                time.sleep(0.03)
        finally:
            self.in_elite = False
            if self.anchor_since is not None:
                self.anchor_since += time.time() - start   # 菁英戰時間不算進定點停留時間
            self.kb.release_all()

    def run(self):
        while self.alive:
            if not self.active.wait(0.2):
                if self.kb.held:
                    self.kb.release_all()   # 暫停時確保沒有任何按鍵被按住
                self.status = "暫停中"
                continue
            try:
                if self.startup_buffs_pending:
                    self.startup_buffs_pending = False
                    self.cast_startup_buffs()
                    if not self.active.is_set():
                        continue
                self.check()
                if self.cfg.get("mode") == "anchor":
                    self.anchor_once()
                    continue
                if self.cfg.get("mode") == "buff":
                    map_macro, map_macro_index = self.choose_map_macro()
                    if map_macro and map_macro.get("events"):
                        # 錄好的全圖路徑優先；每輪結束後會再次檢查到期的 Buff。
                        self.tick_skills()
                        if map_macro_index is not None:
                            self.status = f"隨機路線 {map_macro_index + 1}／{len(self.cfg.get('map_macros') or [map_macro])}：準備播放"
                        self.play_macro(map_macro, align=False, suppress_loot=True, allow_buffs=True)
                    elif self.loot_targets()[1]:
                        self.loot_items()
                    elif self.rope_pairs():
                        self.pair_patrol_once()          # 有繩組：只在繩組之間移動
                    elif self.cfg["patrol"]:
                        self.patrol_once(attack=False)
                    else:
                        self.status = "BUFF機：沒有繩組或巡邏點，原地放 Buff"
                        self.tick_skills()
                        self.sweep()
                        self.sleep(1.0)
                    continue
                if self.cfg.get("mode") == "combat":
                    if not self.combat_ready():
                        self.status = "全自動戰鬥：尚未設定角色名牌或怪物範本（見「自動戰鬥」頁）"
                        time.sleep(0.3)
                        continue
                    if self.target_in_reach() or (self.cfg["combat"].get("approach") and self.combat_targets()[1]):
                        self.combat_engage()
                    elif self.combat_other_layers() and (self.cfg["patrol"] or self.anchor_points()):
                        others = self.combat_other_layers()
                        dx, dy = min(others, key=lambda o: abs(o[1]) + abs(o[0]) * 0.3)
                        if not self.go_toward_layer(dy):
                            self.patrol_once(attack=False)
                    elif self.cfg["patrol"]:
                        self.status = "畫面上沒有怪，換位置"
                        self.patrol_once(attack=False)
                        if not self.combat_targets()[1] and self.cfg["combat"].get("fallback_blind", True):
                            self.blind_sweep()
                    else:
                        self.combat_search()
                    continue
                if self.cfg.get("mode") == "random":
                    if self.cfg["patrol"]:
                        self.patrol_once()
                    else:
                        self.status = "隨機巡邏：尚未記錄任何點（改為原地模式）"
                        self.tick_skills(allow_attack=True)
                        time.sleep(0.03)
                    continue
                route = self.cfg["route"]
                if not route:
                    self.status = "原地模式：自動技能 / 攻擊"
                    self.tick_skills(allow_attack=True)
                    time.sleep(0.03)
                    continue
                if self.step_idx >= len(route):
                    if self.cfg.get("route_loop", True):
                        self.step_idx = 0
                    else:
                        self.status = "路線完成"
                        self.active.clear()
                        continue
                self.app.highlight_step(self.step_idx)
                self.do_step(route[self.step_idx])
                self.step_idx += 1
            except LootInterrupt:
                try:
                    self.loot_items()
                except StopBot:
                    self.kb.release_all()
                except EliteInterrupt:
                    try:
                        self.elite_fight()
                    except StopBot:
                        self.kb.release_all()
                self.last_target = None
            except CombatInterrupt:
                try:
                    self.combat_engage()
                except StopBot:
                    self.kb.release_all()
                except EliteInterrupt:
                    try:
                        self.elite_fight()
                    except StopBot:
                        self.kb.release_all()
                self.last_target = None
            except EliteInterrupt:
                self.climbing = False
                try:
                    self.elite_fight()
                except StopBot:
                    self.kb.release_all()
                self.last_target = None  # 隨機巡邏重新挑目標；路線模式會重做目前步驟
            except StopBot:
                self.kb.release_all()
                self.climbing = False
            except Exception as e:
                self.kb.release_all()
                self.status = f"錯誤：{e}"
                log_exception("自動執行發生錯誤，已暫停", e)
                self.active.clear()


# --------------------------------------------------------------------------
# GUI
# --------------------------------------------------------------------------
STEP_TYPES = {
    "goto": "走到 X",
    "rope": "爬繩",
    "jump": "跳躍",
    "downjump": "下跳",
    "attack": "攻擊",
    "key": "按鍵",
    "wait": "等待",
    "macro": "錄製動作",
}


def describe_step(s):
    t = s["type"]
    if t == "macro":
        a = "先走到起點" if s.get("align", True) else "原地播放"
        return f"● 錄製動作（{macro_summary(s)}，{a}）"
    if t == "goto":
        return f"走到 X={s['x']}"
    if t == "rope":
        return f"爬繩 X={s['x']}" + (f"，爬到 Y≤{s['top_y']}" if s.get("top_y") is not None else "")
    if t == "jump":
        d = {"left": "往左", "right": "往右"}.get(s.get("dir", ""), "原地")
        return f"{d}跳 ×{s.get('times', 1)}" + ("（二段跳）" if s.get("double") else "")
    if t == "downjump":
        return "下跳"
    if t == "attack":
        return f"攻擊 ×{s.get('times', 5)}" + {"left": "（面向左）", "right": "（面向右）"}.get(s.get("dir", ""), "")
    if t == "key":
        return f"按 {s['key']}"
    if t == "wait":
        return f"等待 {s['sec']} 秒（期間自動技能/攻擊）"
    return str(s)


# --------------------------------------------------------------------------
# 介面小元件
# --------------------------------------------------------------------------
UI_FONT = "Microsoft JhengHei UI"   # 啟動時會依電腦上實際有的字型改掉（見 init_ui_metrics）
UI_SCALE = 1.0                       # 依 DPI 計算的縮放倍率（100% = 1.0、150% = 1.5）
FONT_CANDIDATES = ("Microsoft JhengHei UI", "Microsoft JhengHei", "Segoe UI",
                   "Noto Sans CJK TC", "PingFang TC", "Noto Sans CJK JP")


def px(n):
    """把設計時（100% 縮放）的像素值換算成目前 DPI 的像素"""
    return int(round(n * UI_SCALE))


def init_ui_metrics(root):
    """挑選電腦上有的字型、計算 DPI 縮放倍率"""
    global UI_FONT, UI_SCALE
    try:
        fams = set(tkfont.families(root))
    except Exception:
        fams = set()
    for name in FONT_CANDIDATES:
        if name in fams:
            UI_FONT = name
            break
    else:
        UI_FONT = tkfont.nametofont("TkDefaultFont").actual().get("family", "TkDefaultFont")
    dpi = None
    if IS_WIN:
        try:
            dpi = ctypes.windll.user32.GetDpiForSystem()        # Windows 10 以上
        except Exception:
            try:
                hdc = ctypes.windll.user32.GetDC(0)
                dpi = ctypes.windll.gdi32.GetDeviceCaps(hdc, 88)   # LOGPIXELSX
                ctypes.windll.user32.ReleaseDC(0, hdc)
            except Exception:
                dpi = None
    if not dpi:
        try:   # Tk 的 scaling＝每點多少像素；96 DPI 時約 1.333
            dpi = float(root.tk.call("tk", "scaling")) * 72.0
        except Exception:
            dpi = 96.0
    UI_SCALE = max(1.0, min(3.0, dpi / 96.0))
    return UI_FONT, UI_SCALE


def work_area(root):
    """螢幕工作區（扣掉工作列）：(left, top, width, height)"""
    if IS_WIN:
        try:
            r = wintypes.RECT()
            if ctypes.windll.user32.SystemParametersInfoW(0x0030, 0, ctypes.byref(r), 0):  # SPI_GETWORKAREA
                return r.left, r.top, r.right - r.left, r.bottom - r.top
        except Exception:
            pass
    return 0, 0, root.winfo_screenwidth(), root.winfo_screenheight()
C_ACCENT = "#1565c0"
C_MUTED = "#6b7280"
C_OK = "#2e7d32"
C_BAD = "#c62828"
C_WARN = "#b26a00"

MODE_INFO = {
    "anchor": ("◎ 定點掛機", "站在定點按住範圍技，定時換點；不爬繩，被撞開會在同一層走回定點 X。"),
    "buff": ("✚ BUFF機", "只移動不攻擊：照錄製路線或在繩組之間移動、放 Buff；撿物可開關。"),
}
MODE_ORDER = ["anchor", "buff"]


class Collapsible(ttk.Frame):
    """可摺疊區塊：預設收起，點標題展開"""

    def __init__(self, parent, title="進階設定", opened=False, **kw):
        super().__init__(parent, **kw)
        self._title = title
        self._open = opened
        self._hdr = ttk.Label(self, style="Link.TLabel", cursor="hand2")
        self._hdr.pack(anchor="w", pady=(2, 0))
        self._hdr.bind("<Button-1>", lambda e: self.toggle())
        self.body = ttk.Frame(self, padding=(14, 2, 0, 4))
        self._sync()

    def toggle(self):
        self._open = not self._open
        self._sync()

    def _sync(self):
        self._hdr.config(text=("▾ " if self._open else "▸ ") + self._title)
        if self._open:
            self.body.pack(fill="x")
        else:
            self.body.pack_forget()


class ScrollFrame(ttk.Frame):
    """可上下捲動的區域（滑鼠滾輪可用）"""

    def __init__(self, parent, **kw):
        super().__init__(parent, **kw)
        self.canvas = tk.Canvas(self, highlightthickness=0, borderwidth=0)
        self.vsb = ttk.Scrollbar(self, orient="vertical", command=self.canvas.yview)
        self.inner = ttk.Frame(self.canvas)
        self._win = self.canvas.create_window((0, 0), window=self.inner, anchor="nw")
        self.canvas.configure(yscrollcommand=self.vsb.set)
        self.canvas.pack(side="left", fill="both", expand=True)
        self.vsb.pack(side="right", fill="y")
        self.inner.bind("<Configure>", lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
        self.canvas.bind("<Configure>", lambda e: self.canvas.itemconfigure(self._win, width=e.width))
        self.bind_all("<MouseWheel>", self._wheel, add="+")
        self.bind_all("<Button-4>", lambda e: self._scroll(-1), add="+")
        self.bind_all("<Button-5>", lambda e: self._scroll(1), add="+")

    def _under_mouse(self):
        w = self.winfo_containing(*self.winfo_pointerxy())
        while w is not None:
            if w is self:
                return True
            w = getattr(w, "master", None)
        return False

    def _scroll(self, step):
        if self._under_mouse():
            self.canvas.yview_scroll(step, "units")

    def _wheel(self, e):
        self._scroll(-1 if e.delta > 0 else 1)

    def to_top(self):
        self.canvas.yview_moveto(0)


def autowrap(lbl, pad=8):
    """讓 Label 依實際寬度自動換行（避免一兩個字被擠到下一行）"""
    lbl.bind("<Configure>", lambda e: lbl.config(wraplength=max(px(120), e.width - px(pad))))
    return lbl


def hint(parent, text, **pack):
    lb = ttk.Label(parent, text=text, style="Hint.TLabel", justify="left")
    lb.pack(fill="x", anchor="w", **pack)
    return autowrap(lb)


# ---------------- 下拉選單 ----------------
KEY_LABELS = {"ctrl": "Ctrl", "alt": "Alt", "shift": "Shift", "space": "空白鍵", "enter": "Enter", "esc": "Esc",
              "tab": "Tab", "backspace": "Backspace", "insert": "Insert", "delete": "Delete", "home": "Home",
              "end": "End", "pageup": "PageUp", "pagedown": "PageDown", "left": "← 左", "right": "→ 右",
              "up": "↑ 上", "down": "↓ 下", "rctrl": "右 Ctrl", "ralt": "右 Alt", "rshift": "右 Shift"}
KEY_ORDER = (["ctrl", "alt", "shift", "space"] + [chr(c) for c in range(ord("a"), ord("z") + 1)]
             + [str(d) for d in range(10)] + [f"f{i}" for i in range(1, 13)]
             + ["insert", "delete", "home", "end", "pageup", "pagedown", "left", "right", "up", "down",
                "enter", "esc", "tab", "backspace", "`", "-", "=", "[", "]", "\\", ";", "'", ",", ".", "/",
                "rctrl", "ralt", "rshift"])


def key_label(k):
    return KEY_LABELS.get(k, k.upper() if len(k) <= 3 else k)


def choice_spec(values, labels=None, empty=None):
    """下拉選單設定：values＝實際存的值；labels＝顯示文字；empty＝空白選項的顯示文字（None＝不提供空白）"""
    disp = [labels(v) if callable(labels) else (labels or {}).get(v, v) for v in values]
    pairs = ([(empty, "")] if empty else []) + list(zip(disp, values))
    return {"pairs": pairs}


KEY_SPEC = choice_spec([k for k in KEY_ORDER if k in SCANCODES], key_label)
FKEY_SPEC = choice_spec([f"f{i}" for i in range(1, 13)], key_label)
YESNO_SPEC = choice_spec(["1", "0"], {"1": "是", "0": "否"})
DIR_SPEC = choice_spec(["left", "right"], {"left": "← 左", "right": "→ 右"}, empty="（不轉向）")


def key_spec(empty=None):
    return KEY_SPEC if not empty else choice_spec([k for k in KEY_ORDER if k in SCANCODES], key_label, empty)


def make_choice(parent, var, spec, width=12, on_change=None):
    """建立唯讀下拉選單；var 存實際值，選單顯示友善文字"""
    to_val = {d: v for d, v in spec["pairs"]}
    to_disp = {v: d for d, v in spec["pairs"]}
    shown = tk.StringVar(value=to_disp.get(str(var.get()).lower(), to_disp.get(str(var.get()), var.get())))
    cb = ttk.Combobox(parent, textvariable=shown, values=[d for d, _ in spec["pairs"]], state="readonly",
                      width=width, height=16)

    def picked(_e=None):
        var.set(to_val.get(shown.get(), shown.get()))
        if on_change:
            on_change()
    cb.bind("<<ComboboxSelected>>", picked)

    def synced(*_):   # 程式改了實際值（例如載入地圖）時，選單顯示跟著更新
        want = to_disp.get(str(var.get()).lower(), to_disp.get(str(var.get()), var.get()))
        if shown.get() != want:
            shown.set(want)
    var.trace_add("write", synced)
    cb._shown = shown
    return cb


def form_grid(parent, items, src, store, on_save, width=8, cols=2, key_prefix=None, label_min=150, choice_min=12):
    """建立「標籤＋輸入框／下拉選單」表格。items=[(key, label) 或 (key, label, 選單設定)]；改完自動儲存"""
    for i, item in enumerate(items):
        k, label = item[0], item[1]
        spec = item[2] if len(item) > 2 else None
        r, c = divmod(i, cols)
        ttk.Label(parent, text=label).grid(row=r, column=c * 2, sticky="w", padx=(0 if c == 0 else 16, 6), pady=2)
        v = tk.StringVar(value="" if src.get(k) is None else str(src.get(k)))
        if spec:
            e = make_choice(parent, v, spec, width=max(width, choice_min), on_change=on_save)
        else:
            e = ttk.Entry(parent, textvariable=v, width=width)
            e.bind("<FocusOut>", lambda _e: on_save())
            e.bind("<Return>", lambda _e: on_save())
        e.grid(row=r, column=c * 2 + 1, sticky="w", pady=2)
        store[(key_prefix, k) if key_prefix is not None else k] = v
    parent.columnconfigure(0, minsize=px(label_min))
    if cols > 1:
        parent.columnconfigure(2, minsize=px(min(130, label_min)))
    return parent


def make_tree(parent, cols, height=5):
    """cols=[(id, 標題, 寬度)]"""
    tv = ttk.Treeview(parent, columns=[c[0] for c in cols], show="headings", height=height, selectmode="browse")
    for cid, title, w in cols:
        tv.heading(cid, text=title)
        last = cid == cols[-1][0]
        tv.column(cid, width=px(w), anchor="w" if last and w >= 200 else "center", stretch=last)
    return tv


def section(parent, title, hint_text=None):
    """有標題的區塊；回傳內容 frame"""
    box = ttk.LabelFrame(parent, text=" " + title + " ", padding=(10, 6))
    box.pack(fill="x", pady=(0, 8))
    if hint_text:
        hint(box, hint_text, pady=(0, 4))
    return box


def button_row(parent, buttons, pady=(4, 0)):
    r = ttk.Frame(parent)
    r.pack(fill="x", pady=pady)
    for spec in buttons:
        text, cmd = spec[0], spec[1]
        style = spec[2] if len(spec) > 2 else "TButton"
        ttk.Button(r, text=text, command=cmd, style=style).pack(side="left", padx=(0, 6))
    return r


class App:
    def __init__(self, root):
        self.root = root
        self.cfg = migrate_config(load_config())
        self.kb = Keyboard(repeat=self.cfg.get("key_repeat", True))
        root.title(f"楓之谷輔助工具 {APP_VERSION}")
        init_ui_metrics(root)
        wl, wt, ww, wh = work_area(root)
        # 左邊設定分頁＋右邊配置／日誌，預設放在螢幕右側，避免蓋住遊戲左上角的小地圖
        w = min(px(1020), ww - 20)
        h = min(px(700), wh - 40)
        root.geometry(f"{w}x{h}+{wl + max(0, ww - w - 20)}+{wt + 10}")
        root.minsize(min(px(720), ww - 20), min(px(480), wh - 40))
        root.attributes("-topmost", False)          # 一律不置頂開啟，避免蓋住遊戲
        root.protocol("WM_DELETE_WINDOW", self.on_close)
        self._base_tk_scaling = float(root.tk.call("tk", "scaling"))
        self._ui_ratio = None
        self._setup_style()
        root.bind("<Configure>", self._on_root_resize, add="+")

        self.alarm_kind = None   # None / "red" / "lie" / "stuck"
        self.yolo_collecting = False
        self._yolo_capture_job = None
        self._ui_queue = queue.Queue()   # 背景執行緒要更新介面時，放進這裡由主執行緒執行
        self._note_job = None
        self._tick = 0
        self._status_norm = None
        self._status_logged = {}
        self.alive_ui = False
        self.vision = Vision(self)
        self.bot = Bot(self)
        self.scanner = CombatScanner(self)

        self.build_banners(root)
        body = ttk.Panedwindow(root, orient="horizontal")
        body.pack(fill="both", expand=True, padx=px(6), pady=(0, px(6)))
        self.body_pane = body
        left = ttk.Frame(body)
        right = ttk.Frame(body, padding=(px(6), 0, 0, 0))
        body.add(left, weight=1)
        body.add(right, weight=0)
        self.side_frame = right
        self._side_compact = None
        self._side_pref = int(self.cfg.get("side_width") or px(300))   # 使用者拖曳後的右側寬度
        self._last_root_w = None
        self.build_side(right)          # 先建右側（建分頁時可能就會呼叫 notify）
        right.bind("<Configure>", self._on_side_resize, add="+")
        body.bind("<ButtonRelease-1>", self._on_sash_drag, add="+")
        self.nb = ttk.Notebook(left)
        self.nb.pack(fill="both", expand=True)
        self.nb.bind("<Configure>", self._fit_tab_titles, add="+")
        self.tabs = {}
        self._tab_titles = {}
        self._tabs_short = None
        for key, title, builder, scroll in (("settings", "設定", self.build_settings, True),
                                            ("map", "掛機地圖", self.build_home, False),
                                            ("alarm", "警報", self.build_alarm, True),
                                            ("yolo", "AI 辨識", self.build_yolo_dataset, True),
                                            ("adv", "校正", self.build_detect_adv, True),
                                            ("setup", "首次設定", self.build_wizard, False)):
            if scroll:
                outer = ScrollFrame(self.nb)
                inner = ttk.Frame(outer.inner, padding=(8, 6))
                inner.pack(fill="both", expand=True)
            else:
                outer = inner = ttk.Frame(self.nb, padding=(8, 6))
            self.nb.add(outer, text=f" {title} ")
            self.tabs[key] = outer
            self._tab_titles[key] = title
            builder(inner)
        self.tab_home = self.tabs["map"]
        self.tab_setup = self.tabs["setup"]
        self._autowrap_hints(self.nb)
        self.show_mode_panel()

        self.vision.start()
        self.bot.start()
        self.scanner.start()
        self.diag = DiagRecorder(self)
        self.kb.on_key = self.diag.key_event
        self.diag.start()
        self._hotkey_state = {}
        self.alive_ui = True
        for line, level in list(EVENT_LOG.recent):    # 介面出來之前的訊息（例如設定檔錯誤）
            self._append_log(line, level)
        EVENT_LOG.listeners.append(self._on_log)
        log(f"配置加載：{APP_VERSION}，模式 {MODE_INFO.get(self.cfg.get('mode'), ('?',))[0]}"
            + (f"，配置「{self.cfg.get('active_profile')}」" if self.cfg.get("active_profile") else ""))
        self._drain_ui()
        self.refresh()
        self.poll_hotkeys()
        self.root.after(1200, self.check_for_updates)
        self.root.after(3000, self.check_model_present)
        # 啟動時只看存檔的設定（遊戲視窗、角色點要等辨識跑起來才知道）
        if self.missing_required(skip=("game", "dot")):
            self.nb.select(self.tab_setup)

    # ---------------- 外觀 ----------------
    def _setup_style(self):
        st = ttk.Style()
        if IS_WIN:
            try:
                st.theme_use("vista")
            except Exception:
                pass
        self._style = st
        self._apply_ui_ratio(1.0)

    def _apply_ui_ratio(self, ratio):
        """視窗變窄時同步縮小字體與 ttk 間距，讓內容不只剩外框變小。"""
        ratio = max(0.72, min(1.0, ratio))
        if self._ui_ratio is not None and abs(self._ui_ratio - ratio) < 0.025:
            return
        self._ui_ratio = ratio
        size = lambda n: max(7, int(round(n * ratio)))
        st = self._style
        base = (UI_FONT, size(9))
        st.configure(".", font=base)
        st.configure("TLabelframe.Label", font=(UI_FONT, size(9), "bold"), foreground="#374151")
        st.configure("Hint.TLabel", foreground=C_MUTED, font=(UI_FONT, size(8)))
        st.configure("Link.TLabel", foreground=C_ACCENT, font=(UI_FONT, size(8), "bold"))
        st.configure("Pos.TLabel", font=(UI_FONT, size(15), "bold"))
        st.configure("Status.TLabel", foreground=C_ACCENT, font=(UI_FONT, size(9), "bold"))
        st.configure("TNotebook.Tab", padding=(size(10), size(3)))
        if hasattr(self, "txt_log"):
            self.txt_log.configure(font=(UI_FONT, size(9)))
        st.configure("Big.TButton", font=(UI_FONT, size(10), "bold"), padding=(size(9), size(4)))
        st.configure("Treeview", rowheight=max(px(17), int(px(21) * ratio)))
        st.configure("Treeview.Heading", font=(UI_FONT, size(8), "bold"))
        self.root.option_add("*Font", base)
        self._rescale_plain_widgets(self.root, ratio)

    def _rescale_plain_widgets(self, parent, ratio):
        """ttk 以 style 縮放；一般 Tk 控制項則逐一調整，確保已建立的內容真的會變小。"""
        plain = (tk.Label, tk.Button, tk.Radiobutton, tk.Checkbutton, tk.Entry, tk.Listbox)
        for widget in parent.winfo_children():
            if isinstance(widget, plain):
                try:
                    if not hasattr(widget, "_ui_base_font"):
                        actual = tkfont.Font(root=self.root, font=widget.cget("font")).actual()
                        widget._ui_base_font = (actual.get("family", UI_FONT), abs(int(actual.get("size", 9))),
                                                actual.get("weight", "normal"), actual.get("slant", "roman"))
                    family, points, weight, slant = widget._ui_base_font
                    widget.configure(font=(family, max(7, int(round(points * ratio))), weight, slant))
                    if isinstance(widget, tk.Button):
                        if not hasattr(widget, "_ui_base_padding"):
                            widget._ui_base_padding = (int(float(widget.cget("padx"))),
                                                       int(float(widget.cget("pady"))))
                        padx, pady = widget._ui_base_padding
                        widget.configure(padx=max(2, int(round(padx * ratio))),
                                         pady=max(1, int(round(pady * ratio))))
                except (tk.TclError, ValueError, TypeError):
                    pass
            self._rescale_plain_widgets(widget, ratio)

    # ---------------- 右側欄寬度、分頁名稱自動調整 ----------------
    SIDE_MIN, SIDE_MAX, LEFT_MIN = 210, 480, 400
    TAB_SHORT = {"settings": "設定", "map": "地圖", "alarm": "警報", "yolo": "AI", "adv": "校正", "setup": "首設"}

    def _side_target(self, total):
        """依視窗寬度決定右側欄寬：不超過使用者拖曳的寬度，窄視窗時自動收窄，左邊至少保留 LEFT_MIN"""
        want = self._side_pref
        if total < px(960):   # 視窗不寬時才自動收窄；夠寬就照使用者拖曳的寬度
            want = min(want, max(px(self.SIDE_MIN), int(total * 0.34)))
        return max(px(self.SIDE_MIN), min(want, total - px(self.LEFT_MIN)))

    def _apply_side_width(self):
        if not hasattr(self, "body_pane"):
            return
        total = self.body_pane.winfo_width()
        if total < 50:
            return
        try:
            self.body_pane.sashpos(0, max(px(self.LEFT_MIN), total - self._side_target(total)))
        except tk.TclError:
            pass

    def _on_sash_drag(self, _e=None):
        """使用者拖曳中間分隔線：記住右側寬度"""
        try:
            w = self.body_pane.winfo_width() - int(self.body_pane.sashpos(0))
        except (tk.TclError, ValueError):
            return
        w = max(px(self.SIDE_MIN), min(px(self.SIDE_MAX), w))
        if abs(w - self._side_pref) > 2:
            self._side_pref = w
            self.cfg["side_width"] = w
            save_config(self.cfg)
        self._apply_side_width()

    def _on_side_resize(self, e):
        """右側欄寬度改變：文字換行寬度、按鈕文字跟著調整"""
        w = e.width
        wrap = max(px(120), w - px(34))
        for lb in (self.lbl_win, self.lbl_status, self.lbl_map_profile):
            lb.config(wraplength=wrap)
        compact = w < px(268)
        if compact == self._side_compact:
            return
        self._side_compact = compact
        for key, lb in self.chips.items():
            full, short = self._chip_text[key]
            lb.config(text=short if compact else full, padx=3 if compact else 5)
        for btn, full, short in self.profile_btns:
            btn.config(text=short if compact else full)
        self.lbl_hover.config(style="Hint.TLabel")
        if compact:
            self.lbl_hover.pack_forget()
        elif not self.lbl_hover.winfo_ismapped():
            self.lbl_hover.pack(side="right", anchor="s")

    def _autowrap_hints(self, parent):
        """左側分頁裡的說明／狀態文字：依實際寬度自動換行，視窗變窄也不會被截斷"""
        for w in parent.winfo_children():
            self._autowrap_hints(w)
            if not isinstance(w, ttk.Label) or str(w.cget("wraplength")) not in ("", "0"):
                continue
            if str(w.cget("style")) != "Hint.TLabel" or w.winfo_manager() != "pack":
                continue
            info = w.pack_info()
            if info.get("side") in ("left", "right"):
                w.pack_configure(fill="x", expand=True)
            else:
                w.pack_configure(fill="x")
            w.configure(justify="left")
            autowrap(w)

    def _fit_tab_titles(self, _e=None):
        """分頁列放不下時改用短名稱"""
        try:
            f = tkfont.Font(root=self.root, font=self._style.lookup("TNotebook.Tab", "font") or (UI_FONT, 9))
        except tk.TclError:
            f = tkfont.nametofont("TkDefaultFont")
        need = sum(f.measure(f" {t} ") + px(26) for t in self._tab_titles.values())
        short = self.nb.winfo_width() < need
        if short == self._tabs_short:
            return
        self._tabs_short = short
        for key, tab in self.tabs.items():
            self.nb.tab(tab, text=f" {self.TAB_SHORT[key] if short else self._tab_titles[key]} ")

    def _on_root_resize(self, event):
        if event.widget is not self.root:
            return
        if event.width != self._last_root_w:
            self._last_root_w = event.width
            self.root.after_idle(self._apply_side_width)
        # 以緊湊預設寬度為基準；拉大不放大，縮小才等比例收斂。
        self._apply_ui_ratio(event.width / max(1, px(820)))

    # ---------------- 上方橫幅（必要設定未完成、警報） ----------------
    def build_banners(self, root):
        host = ttk.Frame(root, padding=(px(6), px(4), px(6), 0))
        host.pack(fill="x")
        self.setup_frame = tk.Frame(host, bg="#fff4e5")
        self.lbl_setup = tk.Label(self.setup_frame, text="", bg="#fff4e5", fg=C_WARN, font=(UI_FONT, 10, "bold"))
        self.lbl_setup.pack(side="left", padx=8, pady=4)
        ttk.Button(self.setup_frame, text="前往首次設定 →",
                   command=lambda: self.nb.select(self.tab_setup)).pack(side="right", padx=6, pady=3)
        self.alarm_frame = tk.Frame(host, bg=C_BAD)
        self.lbl_alarm = tk.Label(self.alarm_frame, text="", bg=C_BAD, fg="white", justify="left",
                                  wraplength=px(560), font=(UI_FONT, 11, "bold"))
        self.lbl_alarm.pack(side="left", padx=8, pady=6)
        tk.Button(self.alarm_frame, text="我處理好了", command=self.dismiss_alarm).pack(side="right", padx=8)

    # ---------------- 右側：狀態、配置保存、開始／停止、日誌 ----------------
    def build_side(self, f):
        f.columnconfigure(0, weight=1)
        f.rowconfigure(4, weight=1)
        st = ttk.LabelFrame(f, text=" 狀態 ", padding=(8, 4))
        st.grid(row=0, column=0, sticky="we")
        pos_row = ttk.Frame(st)
        pos_row.pack(fill="x")
        self.lbl_pos = ttk.Label(pos_row, text="座標 --", style="Pos.TLabel")
        self.lbl_pos.pack(side="left")
        self.lbl_hover = ttk.Label(pos_row, text="游標座標 --", style="Hint.TLabel")
        self.lbl_hover.pack(side="right", anchor="s")
        chips = ttk.Frame(st)
        chips.pack(anchor="w", pady=(2, 0))
        self.chips = {}
        self._chip_text = {}
        for key, text, short in (("game", "遊戲", "遊戲"), ("map", "小地圖", "地圖"), ("dot", "角色點", "角色"),
                                 ("tag", "名牌", "名牌")):
            self._chip_text[key] = ("● " + text, short)
            lb = tk.Label(chips, text="● " + text, font=(UI_FONT, 9), padx=5, pady=1, bg="#eef2f7")
            lb.pack(side="left", padx=(0, 3))
            self.chips[key] = lb
        self.lbl_win = ttk.Label(st, text="", style="Hint.TLabel", justify="left", wraplength=px(240))
        self.lbl_win.pack(anchor="w", pady=(2, 0))
        self.lbl_status = ttk.Label(st, text="", style="Status.TLabel", justify="left", wraplength=px(240))
        self.lbl_status.pack(anchor="w", pady=(2, 0))

        self.build_map_memory(f)

        run = ttk.Frame(f)
        run.grid(row=2, column=0, sticky="we", pady=(6, 0))
        run.columnconfigure(0, weight=1, uniform="run")
        run.columnconfigure(1, weight=1, uniform="run")
        # Windows 的 vista ttk 主題會強制保留大按鈕的最小高度；改用原生 Tk 按鈕才能跟著縮放。
        self.btn_run = tk.Button(run, text="▶ 開始掛機", font=(UI_FONT, 10, "bold"), padx=6, pady=5, width=1,
                                 relief="groove", bd=1, bg="#e8f1ff", activebackground="#d6e6ff",
                                 command=self.toggle_run)
        self.btn_run.grid(row=0, column=0, sticky="we", padx=(0, 3))
        self.btn_stop = tk.Button(run, text="■ 停止掛機", font=(UI_FONT, 10, "bold"), padx=6, pady=5, width=1,
                                  relief="groove", bd=1, bg="#f4f4f5", activebackground="#e5e7eb",
                                  command=self.stop)
        self.btn_stop.grid(row=0, column=1, sticky="we", padx=(3, 0))
        # 操作結果會寫進下方日誌；這一行只顯示最新一則（錯誤為紅字）
        self.lbl_note = ttk.Label(f, text="設定改完會自動儲存", style="Hint.TLabel", anchor="w", width=1)
        self.lbl_note.grid(row=3, column=0, sticky="we", pady=(3, 0))

        lg = ttk.LabelFrame(f, text=" 日誌 ", padding=(6, 4))
        lg.grid(row=4, column=0, sticky="nsew", pady=(6, 0))
        bar = ttk.Frame(lg)
        bar.pack(side="bottom", fill="x", pady=(4, 0))
        ttk.Button(bar, text="清空", command=self.clear_log, width=6).pack(side="left")
        ttk.Button(bar, text="開啟資料夾", command=self.open_log_dir).pack(side="left", padx=(6, 0))
        body = ttk.Frame(lg)
        body.pack(fill="both", expand=True)
        self.txt_log = tk.Text(body, height=3, width=20, wrap="char", relief="flat", bd=0,
                               bg="#fbfbfc", fg="#1f2937", font=(UI_FONT, 9), state="disabled",
                               padx=4, pady=2, cursor="arrow")
        sb = ttk.Scrollbar(body, orient="vertical", command=self.txt_log.yview)
        self.txt_log.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        self.txt_log.pack(side="left", fill="both", expand=True)
        self.txt_log.tag_configure("error", foreground=C_BAD)
        self.txt_log.tag_configure("warn", foreground=C_WARN)
        self.txt_log.tag_configure("time", foreground=C_MUTED)

    # ---------------- 日誌 ----------------
    LOG_MAX_LINES = 500

    def _on_log(self, line, level):
        """EventLog 的監聽者：任何執行緒呼叫都安全"""
        self.ui(lambda: self._append_log(line, level))

    def _append_log(self, line, level="info"):
        if not hasattr(self, "txt_log"):
            return
        t = self.txt_log
        at_end = t.yview()[1] >= 0.999
        t.configure(state="normal")
        stamp, _, msg = line.partition("] ")
        t.insert("end", stamp + "] ", ("time",))
        t.insert("end", msg + "\n", (level,) if level in ("error", "warn") else ())
        lines = int(t.index("end-1c").split(".")[0])
        if lines > self.LOG_MAX_LINES:
            t.delete("1.0", f"{lines - self.LOG_MAX_LINES}.0")
        t.configure(state="disabled")
        if at_end:
            t.see("end")

    def clear_log(self):
        self.txt_log.configure(state="normal")
        self.txt_log.delete("1.0", "end")
        self.txt_log.configure(state="disabled")

    def open_log_dir(self):
        os.makedirs(LOG_DIR, exist_ok=True)
        if IS_WIN:
            os.startfile(LOG_DIR)
        else:
            self.notify(f"日誌資料夾：{LOG_DIR}")

    def _log_status(self, status):
        """把自動執行的狀態變化寫進日誌：數字不同但內容相同的狀態視為同一種，同一種 20 秒內只記一次"""
        if not status:
            self._status_norm = None
            return
        norm = re.sub(r"[-+]?\d+(?:\.\d+)?", "#", status)
        if norm == self._status_norm:
            return
        self._status_norm = norm
        now = time.time()
        if now - self._status_logged.get(norm, 0) < 20:
            return
        self._status_logged[norm] = now
        if len(self._status_logged) > 200:
            self._status_logged = {k: v for k, v in self._status_logged.items() if now - v < 20}
        log(status, "error" if status.startswith("錯誤") else "info")

    def notify(self, msg, error=False):
        """在右側顯示訊息並寫入日誌（取代大部分彈出視窗）"""
        log(msg, "error" if error else "info")
        if not hasattr(self, "lbl_note"):
            return
        short = msg.replace("\n", " ")
        short = short if len(short) <= 24 else short[:23] + "…"
        self.lbl_note.config(text=("✘ " if error else "✔ ") + short, foreground=C_BAD if error else C_OK)
        if self._note_job:
            self.root.after_cancel(self._note_job)
        self._note_job = self.root.after(6000, lambda: self.lbl_note.config(
            text="設定改完會自動儲存", foreground=C_MUTED))
        if error:
            self.root.bell()

    # ---------------- 配置保存（每張地圖一組：小地圖框選、角色點、定點、路線…） ----------------
    def build_map_memory(self, parent):
        box = ttk.LabelFrame(parent, text=" 配置保存 ", padding=(8, 4))
        box.grid(row=1, column=0, sticky="we", pady=(6, 0))
        row = ttk.Frame(box)
        row.pack(fill="x")
        ttk.Label(row, text="配置名").pack(side="left")
        self.var_profile_name = tk.StringVar()
        ent = ttk.Entry(row, textvariable=self.var_profile_name, width=6)
        ent.pack(side="left", fill="x", expand=True, padx=(4, 4))
        ent.bind("<Return>", lambda _e: self.add_map_profile())
        ttk.Button(row, text="新增", width=5, command=self.add_map_profile).pack(side="left")
        ttk.Button(row, text="改名", width=5, command=self.rename_map_profile).pack(side="left", padx=(3, 0))
        lst = ttk.Frame(box)
        lst.pack(fill="x", pady=(4, 0))
        self.lb_profiles = tk.Listbox(lst, height=4, width=10, exportselection=False, activestyle="none",
                                      font=(UI_FONT, 9), relief="solid", bd=1, highlightthickness=0,
                                      selectbackground="#dbeafe", selectforeground="#111827")
        sb = ttk.Scrollbar(lst, orient="vertical", command=self.lb_profiles.yview)
        self.lb_profiles.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        self.lb_profiles.pack(side="left", fill="x", expand=True)
        self.lb_profiles.bind("<<ListboxSelect>>", self._on_profile_pick)
        self.lb_profiles.bind("<Double-1>", lambda _e: self.load_map_profile())
        self.lbl_map_profile = ttk.Label(box, text="", style="Hint.TLabel", justify="left", wraplength=px(240))
        self.lbl_map_profile.pack(fill="x", pady=(3, 0))
        btns = ttk.Frame(box)
        btns.pack(fill="x", pady=(3, 0))
        self.profile_btns = []
        for i, (text, short, cmd) in enumerate((("讀取選取配置", "讀取", self.load_map_profile),
                                                ("保存並應用當前配置", "保存並應用", self.save_map_profile),
                                                ("刪除", "刪除", self.delete_map_profile),
                                                ("重載清單", "重載", self.refresh_map_profiles))):
            b = ttk.Button(btns, text=text, command=cmd, width=1)
            b.grid(row=i // 2, column=i % 2, sticky="we", padx=(0 if i % 2 == 0 else 3, 0), pady=1)
            self.profile_btns.append((b, text, short))
        btns.columnconfigure(0, weight=1, uniform="pb")
        btns.columnconfigure(1, weight=1, uniform="pb")
        self._map_profiles = {}
        self.refresh_map_profiles()

    def selected_profile(self):
        sel = self.lb_profiles.curselection()
        return self.lb_profiles.get(sel[0]) if sel else None

    def _on_profile_pick(self, _e=None):
        name = self.selected_profile()
        if name:
            self.var_profile_name.set(name)

    def refresh_map_profiles(self):
        keep = self.selected_profile() or self.cfg.get("active_profile")
        self._map_profiles = {name: path for name, path in list_map_profiles()}
        names = list(self._map_profiles)
        self.lb_profiles.delete(0, "end")
        for n in names:
            self.lb_profiles.insert("end", n)
        if keep in self._map_profiles:
            i = names.index(keep)
            self.lb_profiles.selection_set(i)
            self.lb_profiles.see(i)
            self.var_profile_name.set(keep)
        active = self.cfg.get("active_profile")
        if active and active not in self._map_profiles:
            active = None
        self.lbl_map_profile.config(text=(f"目前套用：{active}" if active else "目前沒有套用配置")
                                    + f"（共 {len(names)} 組）")

    def _write_profile(self, name, path):
        os.makedirs(MAPS_DIR, exist_ok=True)
        profile = {"version": 1, "name": name, "saved_at": time.strftime("%Y-%m-%d %H:%M:%S"),
                   "map": map_snapshot(self.cfg)}
        tmp = path + ".tmp"
        try:
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(profile, f, ensure_ascii=False, indent=2)
            os.replace(tmp, path)
        except OSError as e:
            self.notify(f"儲存配置失敗：{e}", error=True)
            return False
        return True

    def add_map_profile(self):
        """新增：用「配置名」把目前設定存成一組新配置"""
        name = self.var_profile_name.get().strip()
        if not name:
            self.notify("請先在「配置名」輸入名稱。", error=True)
            return
        path = map_profile_path(name)
        if (name in self._map_profiles or os.path.exists(path)) and \
                not messagebox.askyesno("覆寫配置", f"「{name}」已存在，要用目前設定覆寫嗎？", parent=self.root):
            return
        if not self._write_profile(name, path):
            return
        self.cfg["active_profile"] = name
        save_config(self.cfg)
        self.refresh_map_profiles()
        self._select_profile(name)
        self.notify(f"已新增配置：{name}")

    def _select_profile(self, name):
        names = list(self._map_profiles)
        if name in names:
            self.lb_profiles.selection_clear(0, "end")
            self.lb_profiles.selection_set(names.index(name))
            self.lb_profiles.see(names.index(name))
            self.var_profile_name.set(name)

    def rename_map_profile(self):
        old = self.selected_profile()
        new = self.var_profile_name.get().strip()
        if not old:
            self.notify("請先在清單選取要改名的配置。", error=True)
            return
        if not new or new == old:
            self.notify("請在「配置名」輸入新的名稱。", error=True)
            return
        if new in self._map_profiles:
            self.notify(f"「{new}」已存在，請換一個名稱。", error=True)
            return
        old_path, new_path = self._map_profiles[old], map_profile_path(new)
        try:
            with open(old_path, "r", encoding="utf-8-sig") as f:
                data = json.load(f)
            data["name"] = new
            with open(new_path + ".tmp", "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
            os.replace(new_path + ".tmp", new_path)
            if os.path.abspath(new_path) != os.path.abspath(old_path):
                os.remove(old_path)
        except (OSError, ValueError) as e:
            self.notify(f"改名失敗：{e}", error=True)
            return
        if self.cfg.get("active_profile") == old:
            self.cfg["active_profile"] = new
            save_config(self.cfg)
        self.refresh_map_profiles()
        self._select_profile(new)
        self.notify(f"配置「{old}」已改名為「{new}」")

    def save_map_profile(self):
        """保存並應用：把目前設定寫進選取的配置（沒有選取就用配置名新增）"""
        name = self.selected_profile()
        if not name:
            self.add_map_profile()
            return
        save_config(self.cfg)
        if not self._write_profile(name, self._map_profiles.get(name) or map_profile_path(name)):
            return
        self.cfg["active_profile"] = name
        save_config(self.cfg)
        self.refresh_map_profiles()
        self.notify(f"已保存並應用配置：{name}")

    def load_map_profile(self):
        name = self.selected_profile()
        path = self._map_profiles.get(name) if name else None
        if not path:
            self.notify("請先在清單選取要讀取的配置。", error=True)
            return
        try:
            with open(path, "r", encoding="utf-8-sig") as f:
                profile = json.load(f)
            data = profile.get("map")
            if not isinstance(data, dict):
                raise ValueError("配置檔格式不正確")
        except (OSError, ValueError, TypeError) as e:
            self.notify(f"讀取配置失敗：{e}", error=True)
            return
        self.stop()
        for key in MAP_PROFILE_KEYS:
            if key in data:
                self.cfg[key] = data[key]
        self.cfg = migrate_config(self.cfg)
        self.cfg["active_profile"] = name
        self.kb.repeat = self.cfg.get("key_repeat", True)
        self.vision.hwnd = None
        self.vision.tracker = PlayerTracker()
        self.bot.last_target = None
        self.bot.anchor_dwell = None
        self.bot.step_idx = 0
        save_config(self.cfg)
        self._sync_loaded_map_ui()
        self.refresh_map_profiles()
        self.notify(f"配置加載：{name}")

    def delete_map_profile(self):
        name = self.selected_profile()
        path = self._map_profiles.get(name) if name else None
        if not path:
            self.notify("請先在清單選取要刪除的配置。", error=True)
            return
        if not messagebox.askyesno("刪除配置", f"確定刪除「{name}」？此動作無法復原。", parent=self.root):
            return
        try:
            os.remove(path)
        except OSError as e:
            self.notify(f"刪除配置失敗：{e}", error=True)
            return
        if self.cfg.get("active_profile") == name:
            self.cfg["active_profile"] = None
            save_config(self.cfg)
        self.var_profile_name.set("")
        self.refresh_map_profiles()
        self.notify(f"已刪除配置：{name}")

    def _sync_loaded_map_ui(self):
        """載入地圖後同步可見控制項，無須重開程式。"""
        if hasattr(self, "var_mode"):
            self.var_mode.set(self.cfg.get("mode", "anchor"))
        for key, value in {
            "min_dot_area": self.cfg.get("min_dot_area"),
            "hsv_low": ",".join(map(str, self.cfg.get("player_hsv_low", []))),
            "hsv_high": ",".join(map(str, self.cfg.get("player_hsv_high", []))),
            "goto_tolerance": self.cfg.get("goto_tolerance"),
            "rope_tolerance": self.cfg.get("rope_tolerance"),
        }.items():
            if hasattr(self, "set_vars") and key in self.set_vars:
                self.set_vars[key].set(str(value))
        if hasattr(self, "var_loop"):
            self.var_loop.set(self.cfg.get("route_loop", True))
        if hasattr(self, "anchor_vars"):
            for key, var in self.anchor_vars.items():
                if key in self.cfg["anchor"]:
                    var.set(str(self.cfg["anchor"][key]))
            self.var_anchor_rand.set(self.cfg["anchor"].get("random_order", True))
            self.var_anchor_rep.set(self.cfg["anchor"].get("repeat", True))
            self.var_anchor_buff.set(self.cfg["anchor"].get("release_for_buff", True))
        if hasattr(self, "patrol_vars"):
            for key, var in self.patrol_vars.items():
                if key in self.cfg["patrol_opt"]:
                    var.set(str(self.cfg["patrol_opt"][key]))
            self.var_rope_target.set(self.cfg["patrol_opt"].get("rope_as_target", True))
        if hasattr(self, "combat_vars"):
            for (sub, key), var in self.combat_vars.items():
                src = self.cfg["combat"].get(sub, {}) if sub else self.cfg["combat"]
                if key in src:
                    var.set(str(src[key]))
            self.var_cb.set(self.cfg["combat"].get("enabled", True))
            if hasattr(self, "var_cb_auto"):
                self.var_cb_auto.set(self.cfg["combat"].get("auto_detect", True))
            self.var_cb_appr.set(self.cfg["combat"].get("approach", True))
            self.var_cb_face.set(self.cfg["combat"].get("always_face", False))
            self.var_cb_blind.set(self.cfg["combat"].get("fallback_blind", True))
        if hasattr(self, "loot_vars"):
            for key, var in self.loot_vars.items():
                if key in self.cfg["loot"]:
                    var.set(str(self.cfg["loot"][key]))
            self.var_loot_tap.set(self.cfg["loot"].get("auto_tap", True))
            if hasattr(self, "var_loot_on"):
                self.var_loot_on.set(self.cfg["loot"].get("enabled", True))
        if hasattr(self, "var_map_play_mode"):
            opts = self.cfg.get("map_macro_options", {})
            self.var_map_play_mode.set(opts.get("play_mode", "record"))
        self.update_map_macro_label()
        if hasattr(self, "tv_route"):
            self.reload_route()
        if hasattr(self, "tv_patrol"):
            self.reload_patrol()
        if hasattr(self, "lbl_anchor"):
            self.update_anchor_label()
        self.show_mode_panel()
        if hasattr(self, "wiz_rows"):
            self.rebuild_wizard()

    # ---------------- 掛機地圖 ----------------
    def build_home(self, f):
        top = ttk.Frame(f)
        top.pack(fill="x")
        ttk.Label(top, text="掛機模式", font=(UI_FONT, 10, "bold")).pack(side="left")
        self.var_mode = tk.StringVar(value=self.cfg.get("mode", "anchor"))
        spec = choice_spec(MODE_ORDER, {k: MODE_INFO[k][0] for k in MODE_ORDER})
        self.cmb_mode = make_choice(top, self.var_mode, spec, width=14,
                                    on_change=lambda: self.set_mode(self.var_mode.get()))
        self.cmb_mode.pack(side="left", padx=(8, 10))
        self.lbl_mode_desc = autowrap(ttk.Label(top, text="", style="Hint.TLabel", justify="left"))
        self.lbl_mode_desc.pack(side="left", fill="x", expand=True)

        mm = ttk.LabelFrame(f, text=" 小地圖 ", padding=(6, 4))
        mm.pack(fill="x", pady=(6, 6))
        self.canvas = tk.Canvas(mm, height=px(130), bg="#1f2328", highlightthickness=0)
        self.canvas.pack(fill="x")
        self.canvas.bind("<Motion>", self.on_minimap_motion)
        self.canvas.bind("<Leave>", lambda _e: self.lbl_hover.config(text="游標座標 --"))
        self._tkimg = None
        self._minimap_view = None
        self.lbl_legend = autowrap(ttk.Label(mm, text="", style="Hint.TLabel", justify="left"))
        self.lbl_legend.pack(fill="x", pady=(2, 0))

        self.mode_scroll = ScrollFrame(f)
        self.mode_scroll.pack(fill="both", expand=True)
        host = self.mode_scroll.inner
        self.pn = {
            "anchor": self.build_anchor(host),
            "buff": self.build_loot(host),
        }
        # 繩下定點／爬繩／跳台：兩種模式共用，放在模式設定下面
        self.pn_patrol = self.build_patrol(host)
        self.patrol_box.config(text=" 繩下定點（爬繩／跳台） ")

    def set_mode(self, key):
        if key != self.cfg.get("mode"):
            log(f"切換模式：{MODE_INFO.get(key, (key,))[0]}")
        self.cfg["mode"] = key
        self.var_mode.set(key)
        self.bot.last_target = None
        self.bot.anchor_dwell = None
        save_config(self.cfg)
        self.show_mode_panel()
        if hasattr(self, "wiz_rows"):
            self.update_wizard()   # 首次設定頁的步驟跟著模式立即更新

    def set_mode_by_name(self, name):   # 相容舊程式
        for k, v in MODE_NAMES.items():
            if v == name:
                self.set_mode(k)

    def show_mode_panel(self):
        mode = self.cfg.get("mode", "anchor")
        if mode not in MODE_INFO:
            mode = "anchor"
            self.cfg["mode"] = mode
        self.lbl_mode_desc.config(text=MODE_INFO[mode][1])
        for p in self.pn.values():
            p.pack_forget()
        self.pn_patrol.pack_forget()
        self.pn[mode].pack(fill="x")
        if mode == "buff":                    # 定點掛機不爬繩，不顯示繩下定點區
            self.pn_patrol.pack(fill="x")
        if mode == "buff":
            self.lbl_patrol_hint.config(text="一組＝「繩下定點」＋「繩上定點」（＋可選的下跳點）：站在繩子正下方按「＋ 繩下定點」，爬上去走到要停的位置，"
                                             "按「＋ 繩上定點」（會配給清單選取的繩子，沒選就配給最後記錄的繩子）。"
                                             "要從那裡跳下去，就站在要跳的位置按「＋ 下跳點」，跳下去後還要再跳就繼續按，會依序接在這一組後面。"
                                             "沒有錄製全圖路線時，BUFF 機只在這些繩組之間隨機移動：走到繩下 → 爬上去 → 走到繩上定點，不攻擊。"
                                             "要往下層時，有「下跳點」就優先在那裡下跳（比沿繩子爬下來快）。")
            if not self.btn_rec_point.winfo_manager():
                self.btn_rec_point.pack(side="left", padx=(0, 6), before=self.btn_rec_rope)
        else:
            self.lbl_patrol_hint.config(text="被怪撞下去時，會用這裡記錄的繩子／跳台爬回定點。站在繩子正下方按「＋ 繩下定點」；"
                                             "爬不穩就用「● 錄製爬繩」親手爬一次；跳上浮空平台用「● 錄製跳台」。往下會自動下跳。")
            self.btn_rec_point.pack_forget()
        legend = "黃十字＝角色　灰虛圈＝已忽略的同色圖示　紅圈＝其他玩家"
        legend += "　青框＝定點"
        if mode == "buff":
            legend += "　青線＝錄製路徑　綠圈＝起點　粉圈＝終點　橘線＝自動讀取的繩子"
        self.lbl_legend.config(text="小地圖：" + legend)
        self.mode_scroll.to_top()

    # ---------------- 定點掛機 ----------------
    def build_anchor(self, host):
        f = ttk.Frame(host)
        a = self.cfg["anchor"]
        box = section(f, "定點", "站到想掛機的位置按「新增定點」，可記多個，會依停留時間輪流換點。")
        self.tv_anchor = make_tree(box, [("n", "#", 50), ("x", "X", 90), ("y", "Y", 90)], height=4)
        self.tv_anchor.pack(fill="x")
        r = button_row(box, [("＋ 新增定點（目前位置）", self.record_anchor), ("刪除", self.del_anchor),
                             ("清空", self.clear_anchor)])
        self.lbl_anchor = ttk.Label(r, text="", style="Hint.TLabel")
        self.lbl_anchor.pack(side="left", padx=6)

        box2 = section(f, "攻擊")
        self.anchor_vars = {}
        g = ttk.Frame(box2)
        g.pack(fill="x")
        form_grid(g, [("hold_key", "按住的鍵（範圍技）", KEY_SPEC)], a, self.anchor_vars, self.save_anchor, width=8, cols=1)
        g1 = ttk.Frame(box2)
        g1.pack(fill="x")
        form_grid(g1, [("rotate_min", "每點停留 最少(秒)"), ("rotate_max", "最多(秒)")], a, self.anchor_vars,
                  self.save_anchor, width=8)
        self.var_anchor_rand = tk.BooleanVar(value=a.get("random_order", True))
        ttk.Checkbutton(box2, text="隨機挑下一個定點（取消＝依序輪流）", variable=self.var_anchor_rand,
                        command=self.save_anchor).pack(anchor="w", pady=(4, 0))
        adv = Collapsible(box2, "進階：偏離判定、轉身、按鍵細節")
        adv.pack(fill="x", pady=(4, 0))
        g2 = ttk.Frame(adv.body)
        g2.pack(fill="x")
        form_grid(g2, [("tol_x", "左右偏離容許(px)"), ("drift_sec", "離開多久才回去(秒)"),
                       ("turn_sec", "每幾秒轉身(0=不轉)")], a, self.anchor_vars, self.save_anchor, width=6)
        self.var_anchor_rep = tk.BooleanVar(value=a.get("repeat", True))
        self.var_anchor_buff = tk.BooleanVar(value=a.get("release_for_buff", True))
        ttk.Checkbutton(adv.body, text="按住期間持續送出按鍵訊號（像真的一直按著）",
                        variable=self.var_anchor_rep, command=self.save_anchor).pack(anchor="w")
        ttk.Checkbutton(adv.body, text="放 Buff 時先放開，放完再按回去",
                        variable=self.var_anchor_buff, command=self.save_anchor).pack(anchor="w")
        self.update_anchor_label()
        return f

    # ---------------- 全自動戰鬥 ----------------
    def build_combat(self, host):
        f = ttk.Frame(host)
        cb = self.cfg["combat"]
        box = section(f, "自動戰鬥", "勾選即可啟用自動尋怪／追擊／攻擊。內部動態偵測不需怪物範本；範本可提高準確度。")
        self.var_cb = tk.BooleanVar(value=cb.get("enabled", True))
        self.var_cb_auto = tk.BooleanVar(value=cb.get("auto_detect", True))
        ttk.Checkbutton(box, text="啟用自動尋怪與打怪", variable=self.var_cb,
                        command=self.save_combat).pack(anchor="w")
        ttk.Checkbutton(box, text="內部自動偵測活動怪物（不需怪物範本）", variable=self.var_cb_auto,
                        command=self.save_combat).pack(anchor="w", pady=(2, 4))
        button_row(box, [("框選角色名牌", self.set_nametag), ("＋ 新增怪物範本", self.add_monster_template),
                         ("範本資料夾", self.open_monster_dir), ("顯示偵測結果", self.preview_combat)])
        self.lbl_cb = ttk.Label(box, text="", style="Hint.TLabel")
        self.lbl_cb.pack(anchor="w", pady=(4, 0))
        self.combat_vars = {}
        box2 = section(f, "技能")
        g = ttk.Frame(box2)
        g.pack(fill="x")
        ttk.Label(g, text="範圍技", font=(UI_FONT, 10, "bold")).grid(row=0, column=0, sticky="w")
        ga = ttk.Frame(g)
        ga.grid(row=1, column=0, sticky="w", pady=(0, 6))
        form_grid(ga, [("key", "按鍵", key_spec("（不用範圍技）")), ("min_count", "幾隻以上才放"), ("range", "範圍(px)"),
                       ("cooldown", "冷卻(秒)")], cb["aoe"], self.combat_vars, self.save_combat, width=7,
                  key_prefix="aoe")
        ttk.Label(g, text="單體技", font=(UI_FONT, 10, "bold")).grid(row=2, column=0, sticky="w")
        gs = ttk.Frame(g)
        gs.grid(row=3, column=0, sticky="w")
        form_grid(gs, [("key", "按鍵", key_spec("（用一般攻擊鍵）")), ("range", "攻擊距離(px)"), ("interval", "間隔(秒)")],
                  cb["single"], self.combat_vars, self.save_combat, width=7, key_prefix="single")
        adv = Collapsible(box2, "進階：辨識門檻、追擊、交戰時間")
        adv.pack(fill="x", pady=(6, 0))
        g3 = ttk.Frame(adv.body)
        g3.pack(fill="x")
        form_grid(g3, [("threshold", "怪物相似度門檻"), ("tag_threshold", "名牌相似度門檻"),
                       ("y_range", "同一層高度差(px)"), ("char_offset_y", "名牌→身體位移Y"),
                       ("scale", "辨識縮小比例"), ("scan_interval", "掃描間隔(秒)"),
                       ("approach_max_sec", "每隻怪追擊最多(秒)"), ("search_sec", "無巡邏點時左右巡查(秒)"),
                       ("engage_max_sec", "單次交戰最長(秒)")],
                  cb, self.combat_vars, self.save_combat, width=6, key_prefix=None)
        # 對應舊的 combat_vars 鍵格式 (sub, k)
        for k in list(self.combat_vars):
            if not isinstance(k, tuple):
                self.combat_vars[(None, k)] = self.combat_vars.pop(k)
        g4 = ttk.Frame(adv.body)
        g4.pack(fill="x")
        form_grid(g4, [("delay", "範圍技施放後等待(秒)")], cb["aoe"], self.combat_vars, self.save_combat,
                  width=6, key_prefix="aoe")
        self.var_cb_appr = tk.BooleanVar(value=cb.get("approach", True))
        self.var_cb_face = tk.BooleanVar(value=cb.get("always_face", False))
        self.var_cb_blind = tk.BooleanVar(value=cb.get("fallback_blind", True))
        for text, var in (("怪太遠就走過去", self.var_cb_appr), ("每次攻擊前都按方向", self.var_cb_face),
                          ("攻擊點沒看到怪時照舊盲打（路線／隨機巡邏模式）", self.var_cb_blind)):
            ttk.Checkbutton(adv.body, text=text, variable=var, command=self.save_combat).pack(anchor="w")
        self.update_combat_label()
        return f

    # ---------------- BUFF機 ----------------
    def build_loot(self, host):
        f = ttk.Frame(host)
        macro = section(f, "整張地圖錄製", "錄下鍵盤、遊戲視窗內的滑鼠點擊，以及小地圖座標路徑。開始後會先放 Buff，再循環播放。")
        button_row(macro, [("＋ 錄製隨機路線", self.record_map_macro), ("清除全部路線", self.clear_map_macro)])
        opts = self.cfg.get("map_macro_options", {})
        self.var_map_play_mode = tk.StringVar(value=opts.get("play_mode", "record"))
        play = ttk.Frame(macro)
        play.pack(anchor="w", pady=(5, 0))
        ttk.Label(play, text="播放方式：").pack(side="left")
        ttk.Radiobutton(play, text="照錄製操作（建議）", value="record", variable=self.var_map_play_mode,
                        command=self.save_map_macro_options).pack(side="left")
        ttk.Radiobutton(play, text="座標監看，偏離時暫停", value="guarded", variable=self.var_map_play_mode,
                        command=self.save_map_macro_options).pack(side="left", padx=(8, 0))
        self.lbl_map_macro = ttk.Label(macro, text="", style="Hint.TLabel")
        self.lbl_map_macro.pack(anchor="w", pady=(3, 0))
        self.update_map_macro_label()

        lt = self.cfg["loot"]
        box = section(f, "撿物", "移動時會一直連點撿物鍵；框選物品範本後，看到地上的物品會走過去撿。Buff 在「共用設定」設定。")
        self.loot_vars = {}
        self.var_loot_on = tk.BooleanVar(value=lt.get("enabled", True))
        ttk.Checkbutton(box, text="啟用撿物（取消＝BUFF 機只移動、放 Buff）", variable=self.var_loot_on,
                        command=self.save_loot).pack(anchor="w", pady=(0, 4))
        g = ttk.Frame(box)
        g.pack(fill="x")
        form_grid(g, [("key", "撿物鍵", KEY_SPEC), ("sweep_sec", "到點掃地秒數(0=不掃)")], lt, self.loot_vars,
                  self.save_loot, width=7)
        self.var_loot_tap = tk.BooleanVar(value=lt.get("auto_tap", True))
        ttk.Checkbutton(box, text="移動時持續連點撿物鍵", variable=self.var_loot_tap,
                        command=self.save_loot).pack(anchor="w", pady=(4, 0))
        button_row(box, [("框選角色名牌", self.set_nametag_loot), ("＋ 新增物品範本", self.add_item_template),
                         ("範本資料夾", self.open_item_dir), ("顯示偵測結果", self.preview_combat)], pady=(8, 0))
        self.lbl_loot = ttk.Label(box, text="", style="Hint.TLabel")
        self.lbl_loot.pack(anchor="w", pady=(4, 0))
        adv = Collapsible(box, "進階：辨識門檻、撿物距離、重試")
        adv.pack(fill="x", pady=(4, 0))
        g2 = ttk.Frame(adv.body)
        g2.pack(fill="x")
        form_grid(g2, [("threshold", "物品相似度門檻"), ("tap_interval", "連點間隔(秒)"),
                       ("y_range", "同一層高度差(px)"), ("range", "多遠內去撿(px)"),
                       ("pick_radius", "站上物品判定(px)"), ("max_tries", "撿不起來重試次數")],
                  lt, self.loot_vars, self.save_loot, width=6)
        self.update_loot_label()
        return f

    # ---------------- 隨機巡邏（攻擊參數） ----------------
    def build_random(self, host):
        f = ttk.Frame(host)
        po = self.cfg["patrol_opt"]
        box = section(f, "每個攻擊點")
        self.patrol_vars = getattr(self, "patrol_vars", {})
        g = ttk.Frame(box)
        g.pack(fill="x")
        form_grid(g, [("attack_min", "攻擊次數 最少"), ("attack_max", "最多")], po, self.patrol_vars,
                  self.save_patrol_opt, width=6)
        hint(box, "攻擊鍵在「共用設定 → 按鍵與熱鍵」。若已設定怪物範本，攻擊點會改用鎖定攻擊。", pady=(4, 0))
        return f

    # ---------------- 巡邏點／繩子（多個模式共用） ----------------
    def build_patrol(self, host):
        f = ttk.Frame(host)
        po = self.cfg["patrol_opt"]
        self.patrol_box = ttk.LabelFrame(f, text=" 巡邏點 ", padding=(10, 6))
        self.patrol_box.pack(fill="x", pady=(0, 8))
        self.lbl_patrol_hint = hint(self.patrol_box, "", pady=(0, 4))
        self.tv_patrol = make_tree(self.patrol_box, [("n", "#", 40), ("type", "類型", 70), ("x", "X", 60),
                                                     ("y", "Y", 60), ("info", "備註", 240)], height=5)
        self.tv_patrol.pack(fill="x")
        r = ttk.Frame(self.patrol_box)
        r.pack(fill="x", pady=(4, 0))
        self.btn_rec_point = ttk.Button(r, text="＋ 巡邏點", command=lambda: self.record_patrol("point"))
        self.btn_rec_point.pack(side="left", padx=(0, 6))
        self.btn_rec_rope = ttk.Button(r, text="＋ 繩下定點", command=lambda: self.record_patrol("rope"))
        self.btn_rec_rope.pack(side="left", padx=(0, 6))
        ttk.Button(r, text="● 錄製爬繩", command=self.record_rope_macro).pack(side="left", padx=(0, 6))
        ttk.Button(r, text="● 錄製跳台", command=self.record_jump_macro).pack(side="left")
        self.btn_rec_top = ttk.Button(r, text="＋ 繩上定點", command=self.record_rope_top)
        self.btn_rec_top.pack(side="left", padx=(6, 0), after=self.btn_rec_rope)
        r2 = ttk.Frame(self.patrol_box)
        r2.pack(fill="x", pady=(4, 0))
        ttk.Button(r2, text="＋ 下跳點", command=self.record_drop).pack(side="left", padx=(0, 6))
        ttk.Button(r2, text="校準精準位置", command=self.calibrate_rope).pack(side="left", padx=(0, 6))
        ttk.Button(r2, text="繩子設定", command=self.edit_patrol_rope).pack(side="left", padx=(0, 6))
        ttk.Button(r2, text="刪除", command=self.del_patrol).pack(side="left", padx=(0, 6))
        ttk.Button(r2, text="清空", command=self.clear_patrol).pack(side="left")
        adv = Collapsible(self.patrol_box, "進階：停留時間、位置偏移、繩子落點")
        adv.pack(fill="x", pady=(4, 0))
        self.patrol_vars = getattr(self, "patrol_vars", {})
        g = ttk.Frame(adv.body)
        g.pack(fill="x")
        form_grid(g, [("stay_min", "停留秒數 最少"), ("stay_max", "最多"), ("x_jitter", "位置隨機偏移(px)")],
                  po, self.patrol_vars, self.save_patrol_opt, width=6)
        self.var_rope_target = tk.BooleanVar(value=po.get("rope_as_target", True))
        ttk.Checkbutton(adv.body, text="繩子也可以當隨機目標（爬上去）", variable=self.var_rope_target,
                        command=self.save_patrol_opt).pack(anchor="w")
        ttk.Button(adv.body, text="重設繩子落點（地圖改了或落點記錯時）", command=self.reset_lands).pack(anchor="w", pady=(4, 0))
        ttk.Button(adv.body, text="重設所有繩子的 YOLO 偏移（之後會重新學）", command=self.reset_rope_dx).pack(anchor="w", pady=(4, 0))
        self.reload_patrol()
        return f

    # ---------------- 路線 ----------------
    def build_route(self, host):
        f = ttk.Frame(host)
        box = section(f, "路線步驟", "站到位置後按「＋走到這裡／這裡有繩子」記錄；其他步驟用下方按鈕加入，雙擊可編輯。")
        self.tv_route = make_tree(box, [("n", "#", 40), ("desc", "步驟", 460)], height=8)
        self.tv_route.pack(fill="x")
        self.tv_route.bind("<Double-1>", lambda _: self.edit_step())
        button_row(box, [("＋ 走到這裡", lambda: self.record("goto")), ("＋ 這裡有繩子", lambda: self.record("rope")),
                         ("設定繩頂＝目前Y", self.set_rope_top), ("● 錄製動作", self.record_route_macro)])
        r2 = ttk.Frame(box)
        r2.pack(fill="x", pady=(4, 0))
        for t in ("jump", "downjump", "attack", "key", "wait"):
            ttk.Button(r2, text="＋" + STEP_TYPES[t], command=lambda t=t: self.add_step(t)).pack(side="left", padx=(0, 4))
        r3 = ttk.Frame(box)
        r3.pack(fill="x", pady=(4, 0))
        for text, cmd in (("↑", lambda: self.move_step(-1)), ("↓", lambda: self.move_step(1)),
                          ("編輯", self.edit_step), ("刪除", self.del_step), ("清空", self.clear_route),
                          ("從選取處開始", self.start_from_sel)):
            ttk.Button(r3, text=text, command=cmd, width=len(text) * 2 + 2 if len(text) > 1 else 3).pack(side="left", padx=(0, 4))
        self.var_loop = tk.BooleanVar(value=self.cfg.get("route_loop", True))
        ttk.Checkbutton(r3, text="循環", variable=self.var_loop,
                        command=lambda: (self.cfg.__setitem__("route_loop", self.var_loop.get()),
                                         save_config(self.cfg))).pack(side="right")
        self.reload_route()
        return f

    # ---------------- 設定分頁 ----------------
    def build_settings(self, f):
        cols = ttk.Frame(f)
        cols.pack(fill="both", expand=True)
        c0, c1 = ttk.Frame(cols), ttk.Frame(cols)
        self._settings_wide = None

        def layout(_e=None):
            wide = cols.winfo_width() >= px(620)
            if wide == self._settings_wide:
                return
            self._settings_wide = wide
            c0.grid_forget()
            c1.grid_forget()
            if wide:
                cols.columnconfigure(0, weight=1, uniform="setcol")
                cols.columnconfigure(1, weight=1, uniform="setcol")
                c0.grid(row=0, column=0, sticky="new", padx=(0, 4))
                c1.grid(row=0, column=1, sticky="new", padx=(4, 0))
            else:
                cols.columnconfigure(0, weight=1, uniform="")
                cols.columnconfigure(1, weight=0, uniform="")
                c0.grid(row=0, column=0, sticky="new")
                c1.grid(row=1, column=0, sticky="new")
        cols.bind("<Configure>", layout, add="+")
        layout()
        self.build_keys(c0)
        self.build_skill(c1)
        self.build_options(c1)

    def open_shared(self, key):
        tab = {"skill": "settings", "keys": "settings"}.get(key, key)
        self.nb.select(self.tabs.get(tab, self.tabs["settings"]))

    # ---------------- YOLO 資料收集 ----------------
    def _ensure_yolo_dirs(self):
        os.makedirs(YOLO_IMAGES_DIR, exist_ok=True)
        os.makedirs(YOLO_LABELS_DIR, exist_ok=True)

    def _yolo_image_files(self):
        self._ensure_yolo_dirs()
        return sorted((n for n in os.listdir(YOLO_IMAGES_DIR) if n.lower().endswith(".png")), reverse=True)

    def build_yolo_dataset(self, f):
        box = section(f, "怪物資料收集（實驗）",
                      "開始後會定時保存遊戲完整畫面。先收集怪物；之後選取圖片、框住每一隻怪物，即可產生 YOLO 訓練標註。")
        row = ttk.Frame(box)
        row.pack(fill="x")
        self.var_yolo_interval = tk.StringVar(value=str(self.cfg.get("yolo_dataset", {}).get("interval_sec", 2.0)))
        ttk.Label(row, text="每隔（秒）").pack(side="left")
        interval = ttk.Entry(row, textvariable=self.var_yolo_interval, width=6)
        interval.pack(side="left", padx=(6, 12))
        interval.bind("<FocusOut>", lambda _: self.save_yolo_dataset_options())
        interval.bind("<Return>", lambda _: self.save_yolo_dataset_options())
        self.btn_yolo_collect = ttk.Button(row, text="開始收集", command=self.toggle_yolo_collection)
        self.btn_yolo_collect.pack(side="left")
        ttk.Button(row, text="立即截圖", command=self.capture_yolo_image).pack(side="left", padx=(6, 0))
        ttk.Button(row, text="開啟資料夾", command=self.open_yolo_dir).pack(side="left", padx=(6, 0))
        row_b = ttk.Frame(box)
        row_b.pack(fill="x", pady=(6, 0))
        ttk.Button(row_b, text="匯入「把圖片丟這裡」", command=self.import_yolo_inbox).pack(side="left")
        ttk.Button(row_b, text="開啟該資料夾", command=self.open_yolo_inbox).pack(side="left", padx=(6, 0))
        ttk.Button(row_b, text="從影片擷取…", command=self.import_yolo_video).pack(side="left", padx=(6, 0))
        hint(box, "更快的收集方式：① 用任何截圖工具截好的圖（png／jpg）丟進「把圖片丟這裡」資料夾，按匯入；"
                  "② 用 OBS／顯示卡錄一段遊戲影片，按「從影片擷取」每隔幾秒取一張，畫面幾乎沒變的會自動略過。"
                  "重複的圖片不會匯入兩次。", pady=(4, 0))
        self.lbl_yolo_dataset = ttk.Label(box, text="", style="Hint.TLabel")
        self.lbl_yolo_dataset.pack(anchor="w", pady=(5, 0))

        runtime = section(f, "YOLO 怪物辨識", "這張地圖的模型會優先用於怪物辨識；沒有模型或 YOLO 環境時會保留舊範本辨識。全自動戰鬥仍維持關閉。")
        yc = self.cfg.get("yolo", {})
        self.var_yolo_enabled = tk.BooleanVar(value=yc.get("enabled", True))
        self.var_yolo_rope_assist = tk.BooleanVar(value=yc.get("rope_assist", True))
        cc = dict(YOLO_CLASS_CONF_DEFAULT, **(yc.get("class_conf") or {}))
        self.var_yolo_class_conf = {k: tk.StringVar(value=f"{float(cc[k]):g}") for k in YOLO_CLASS_NAMES}
        row2 = ttk.Frame(runtime)
        row2.pack(fill="x")
        ttk.Checkbutton(row2, text="啟用此地圖 YOLO 模型", variable=self.var_yolo_enabled,
                        command=self.save_yolo_runtime).pack(side="left")
        ttk.Checkbutton(row2, text="爬繩時畫面對位", variable=self.var_yolo_rope_assist,
                        command=self.save_yolo_runtime).pack(side="left", padx=(10, 0))
        ttk.Button(row2, text="測試目前畫面", command=self.preview_yolo).pack(side="left", padx=(10, 0))
        ttk.Button(row2, text="更新內建模型", command=self.update_builtin_model).pack(side="left", padx=(6, 0))
        row3 = ttk.Frame(runtime)
        row3.pack(fill="x", pady=(4, 0))
        ttk.Label(row3, text="信心門檻").pack(side="left", padx=(0, 6))
        for k, label in zip(YOLO_CLASS_NAMES, YOLO_CLASS_LABELS):
            ttk.Label(row3, text=label).pack(side="left", padx=(6, 2))
            e = ttk.Entry(row3, textvariable=self.var_yolo_class_conf[k], width=5)
            e.pack(side="left")
            e.bind("<FocusOut>", lambda _: self.save_yolo_runtime())
            e.bind("<Return>", lambda _: self.save_yolo_runtime())
        hint(runtime, "道具、繩子比較小或比較細，模型的信心本來就比較低；看不到時先調低它們的門檻（例如 0.2），"
                      "誤判太多再調高。", pady=(3, 0))
        self.lbl_yolo_model = ttk.Label(runtime, text="", style="Hint.TLabel")
        self.lbl_yolo_model.pack(anchor="w", pady=(4, 0))

        labels = section(f, "框選標註", "選類別後框選圖片中的目標；同一張可先標怪物，再切換類別重開標註補道具、繩子或人物。"
                                       "Enter 儲存，Backspace 復原最後一框，在框上按右鍵刪除那一框。"
                                       "「用模型自動標註」會先幫沒標過的圖畫好框（清單顯示 ◐），你只要打開檢查、刪掉錯的、補上漏的再存檔。")
        category = ttk.Frame(labels)
        category.pack(fill="x", pady=(0, 5))
        ttk.Label(category, text="要標註：").pack(side="left")
        self.var_yolo_label_class = tk.StringVar(value=YOLO_CLASS_LABELS[0])
        ttk.Combobox(category, textvariable=self.var_yolo_label_class, values=YOLO_CLASS_LABELS,
                     state="readonly", width=8).pack(side="left")
        body = ttk.Frame(labels)
        body.pack(fill="both", expand=True)
        self.lb_yolo_images = tk.Listbox(body, height=9, exportselection=False)
        self.lb_yolo_images.pack(side="left", fill="both", expand=True)
        side = ttk.Frame(body)
        side.pack(side="left", fill="y", padx=(8, 0))
        ttk.Button(side, text="重新整理", command=self.refresh_yolo_dataset).pack(fill="x")
        ttk.Button(side, text="開始框選", command=self.annotate_yolo_image).pack(fill="x", pady=(6, 0))
        ttk.Button(side, text="下一張未標註", command=self.select_next_yolo_unlabeled).pack(fill="x", pady=(6, 0))
        ttk.Button(side, text="用模型自動標註", command=self.auto_label_yolo).pack(fill="x", pady=(12, 0))
        ttk.Button(side, text="下一張待確認", command=self.select_next_yolo_auto).pack(fill="x", pady=(6, 0))
        self.refresh_yolo_dataset()
        self.update_yolo_model_label()

    def save_yolo_runtime(self):
        try:
            class_conf = {k: float(v.get()) for k, v in self.var_yolo_class_conf.items()}
            if not all(0.05 <= v <= 0.95 for v in class_conf.values()):
                raise ValueError
        except ValueError:
            self.notify("YOLO 信心門檻請填 0.05～0.95", error=True)
            return False
        yc = self.cfg.setdefault("yolo", {})
        yc["enabled"] = self.var_yolo_enabled.get()
        yc["rope_assist"] = self.var_yolo_rope_assist.get()
        yc["class_conf"] = class_conf
        yc["confidence"] = class_conf["monster"]
        yc.setdefault("model", "yolo_data/models/monster_current_map_v2.pt")
        yc.setdefault("imgsz", 960)
        self.scanner.yolo.invalidate()
        save_config(self.cfg)
        self.update_yolo_model_label()
        return True

    def offer_model_update(self, reason):
        """詢問是否更新成內建模型（每次開啟只問一次）"""
        if getattr(self, "_model_offer_done", False) or not self.alive_ui:
            return
        self._model_offer_done = True
        if messagebox.askyesno("更新 YOLO 模型", f"{reason}\n\n要下載內建的四類模型（怪物／道具／繩子／人物）嗎？\n"
                               "原本的模型會備份成 .bak 檔。", parent=self.root):
            self.update_builtin_model()

    def update_builtin_model(self):
        """下載內建模型、比對 SHA-256，舊模型備份後換上；在背景執行"""
        dest = os.path.join(YOLO_DATA_DIR, "models", BUILTIN_MODEL["file"])
        try:
            if os.path.isfile(dest) and file_sha256(dest) == BUILTIN_MODEL["sha256"]:
                self.notify(f"已經是最新的內建模型（{BUILTIN_MODEL['version']}）。")
                return
        except OSError:
            pass
        self.notify("正在下載內建 YOLO 模型…")

        def worker():
            tmp = dest + ".download"
            try:
                os.makedirs(os.path.dirname(dest), exist_ok=True)
                req = urllib.request.Request(BUILTIN_MODEL["url"], headers={"User-Agent": f"MapleHelper/{APP_VERSION}"})
                with urllib.request.urlopen(req, timeout=60) as r, open(tmp, "wb") as out:
                    shutil.copyfileobj(r, out)
                if file_sha256(tmp) != BUILTIN_MODEL["sha256"]:
                    raise ValueError("模型檔校驗碼不符（下載不完整），已取消")
                backup = ""
                if os.path.isfile(dest):
                    backup = dest + time.strftime(".bak-%Y%m%d-%H%M%S")
                    os.replace(dest, backup)
                os.replace(tmp, dest)
                yc = self.cfg.setdefault("yolo", {})
                yc["model"] = "yolo_data/models/" + BUILTIN_MODEL["file"]
                self.scanner.yolo.invalidate()
                save_config(self.cfg)
                msg = f"已更新內建 YOLO 模型（{BUILTIN_MODEL['version']}）" + (
                    f"，舊模型備份為 {os.path.basename(backup)}" if backup else "")
                self.ui(lambda: (self.notify(msg), self.update_yolo_model_label()))
            except Exception as e:
                try:
                    os.remove(tmp)
                except OSError:
                    pass
                err = f"下載內建模型失敗：{e}"
                log_exception("下載內建模型失敗", e)
                self.ui(lambda: self.notify(err, error=True))
        threading.Thread(target=worker, daemon=True).start()

    def check_model_present(self):
        """開啟時：YOLO 已啟用但模型檔不在（例如新電腦），詢問是否下載內建模型"""
        yc = self.cfg.get("yolo", {})
        path = self.scanner.yolo.model_path()
        if yc.get("enabled", True) and not os.path.isfile(path) \
                and os.path.basename(path) == BUILTIN_MODEL["file"]:
            self.offer_model_update("這台電腦還沒有 YOLO 模型檔。")

    def update_yolo_model_label(self):
        if not hasattr(self, "lbl_yolo_model"):
            return
        detector = self.scanner.yolo
        path = detector.model_path()
        if not os.path.isfile(path):
            text = "✘ 找不到模型：請先在此電腦完成訓練或放入模型檔。"
        elif not self.cfg.get("yolo", {}).get("enabled", True):
            text = "○ 模型已找到，目前未啟用。"
        elif detector.error:
            text = f"✘ {detector.error}"
        else:
            text = "✔ 已找到此地圖模型；按「測試目前畫面」可確認框選結果。"
            names = detector.class_names.get(path)
            if names is not None and not {"item", "rope"} <= names:
                text = "△ 這個模型沒有道具／繩子類別（較舊的模型），可按「更新內建模型」。"
        self.lbl_yolo_model.config(text=text)

    def save_yolo_dataset_options(self):
        try:
            interval = float(self.var_yolo_interval.get())
            if interval < 0.5 or interval > 60:
                raise ValueError
        except ValueError:
            self.notify("資料截圖間隔請填 0.5～60 秒", error=True)
            return False
        self.cfg.setdefault("yolo_dataset", {})["interval_sec"] = interval
        save_config(self.cfg)
        return True

    def refresh_yolo_dataset(self):
        if not hasattr(self, "lb_yolo_images"):
            return
        names = self._yolo_image_files()
        previous = self.selected_yolo_image()
        auto = self._yolo_auto_set()
        self.lb_yolo_images.delete(0, "end")
        labeled = 0
        class_counts = [0] * len(YOLO_CLASS_NAMES)
        for name in names:
            stem = os.path.splitext(name)[0]
            label_path = os.path.join(YOLO_LABELS_DIR, stem + ".txt")
            done = os.path.isfile(label_path)
            labeled += int(done)
            if done:
                try:
                    with open(label_path, "r", encoding="utf-8") as f:
                        for line in f:
                            fields = line.split()
                            if len(fields) == 5 and fields[0].isdigit() and int(fields[0]) < len(class_counts):
                                class_counts[int(fields[0])] += 1
                except OSError:
                    pass
            mark = ("◐ " if name in auto else "✓ ") if done else "○ "
            self.lb_yolo_images.insert("end", mark + name)
        if names:
            target = next((i for i, name in enumerate(names) if name == previous), 0)
            self.lb_yolo_images.selection_set(target)
            self.lb_yolo_images.see(target)
        state = "收集中" if self.yolo_collecting else "已停止"
        details = "、".join(f"{YOLO_CLASS_LABELS[i]} {n}" for i, n in enumerate(class_counts))
        pending = sum(1 for n in names if n in auto)
        self.lbl_yolo_dataset.config(text=f"{state}｜已收集 {len(names)} 張，已標註 {labeled} 張（{details}）"
                                     + (f"，其中 {pending} 張是自動標註待確認" if pending else "")
                                     + "。資料只保存在本機 yolo_data 資料夾。")

    def selected_yolo_image(self):
        if not hasattr(self, "lb_yolo_images"):
            return None
        picked = self.lb_yolo_images.curselection()
        if not picked:
            return None
        text = self.lb_yolo_images.get(picked[0])
        return text[2:] if len(text) > 2 else text

    def capture_yolo_image(self, quiet=False):
        img = self.vision.grab_client() if IS_WIN else None
        if img is None:
            if not quiet:
                self.notify("找不到遊戲視窗，無法截圖。", error=True)
            return False
        self._ensure_yolo_dirs()
        name = f"maple_{time.strftime('%Y%m%d_%H%M%S')}_{time.time_ns() % 1_000_000_000:09d}.png"
        path = os.path.join(YOLO_IMAGES_DIR, name)
        if not imwrite_unicode(path, img):
            self.notify("儲存資料圖片失敗。", error=True)
            return False
        self.refresh_yolo_dataset()
        if not quiet:
            self.notify(f"已收集圖片：{name}")
        return True

    def toggle_yolo_collection(self):
        if self.yolo_collecting:
            self.yolo_collecting = False
            if self._yolo_capture_job:
                self.root.after_cancel(self._yolo_capture_job)
                self._yolo_capture_job = None
            self.btn_yolo_collect.config(text="開始收集")
            self.refresh_yolo_dataset()
            return
        if not self.save_yolo_dataset_options():
            return
        if not self.vision.hwnd:
            self.notify("請先開啟並選取遊戲視窗。", error=True)
            return
        self.yolo_collecting = True
        self.btn_yolo_collect.config(text="停止收集")
        self._yolo_capture_tick()
        # 資料收集開始後不遮住遊戲；需要停止時從工作列點回本工具即可。
        self.root.iconify()
        self.root.after(150, lambda: activate_window(self.vision.hwnd))

    def _yolo_capture_tick(self):
        if not self.yolo_collecting or not self.alive_ui:
            return
        self.capture_yolo_image(quiet=True)
        interval_ms = int(float(self.cfg.get("yolo_dataset", {}).get("interval_sec", 2.0)) * 1000)
        self._yolo_capture_job = self.root.after(max(500, interval_ms), self._yolo_capture_tick)

    def select_next_yolo_unlabeled(self):
        names = self._yolo_image_files()
        for i, name in enumerate(names):
            if not os.path.isfile(os.path.join(YOLO_LABELS_DIR, os.path.splitext(name)[0] + ".txt")):
                self.lb_yolo_images.selection_clear(0, "end")
                self.lb_yolo_images.selection_set(i)
                self.lb_yolo_images.see(i)
                return
        self.notify("目前所有收集到的圖片都已標註。")

    def annotate_yolo_image(self):
        name = self.selected_yolo_image()
        if not name:
            self.notify("請先從清單選一張圖片。", error=True)
            return
        image_path = os.path.join(YOLO_IMAGES_DIR, name)
        img = imread_unicode(image_path)
        if img is None:
            self.notify("讀取圖片失敗。", error=True)
            return
        label_path = os.path.join(YOLO_LABELS_DIR, os.path.splitext(name)[0] + ".txt")
        selected = self.var_yolo_label_class.get()
        class_id = YOLO_CLASS_LABELS.index(selected) if selected in YOLO_CLASS_LABELS else 0

        def saved(count):
            auto = self._yolo_auto_set()
            if name in auto:                       # 人工確認過了
                auto.discard(name)
                self._save_yolo_auto_set(auto)
            self.refresh_yolo_dataset()
            self.notify(f"已儲存 {count} 個標註。")
        YoloBoxAnnotator(self.root, img, label_path, class_id, saved)

    # ---- 自動標註清單 ----
    def _yolo_auto_set(self):
        try:
            with open(YOLO_AUTO_LIST, "r", encoding="utf-8") as f:
                return {ln.strip() for ln in f if ln.strip()}
        except OSError:
            return set()

    def _save_yolo_auto_set(self, names):
        try:
            with open(YOLO_AUTO_LIST, "w", encoding="utf-8") as f:
                f.write("".join(n + "\n" for n in sorted(names)))
        except OSError as e:
            log(f"儲存自動標註清單失敗：{e}", "warn")

    def select_next_yolo_auto(self):
        auto = self._yolo_auto_set()
        names = self._yolo_image_files()
        for i, name in enumerate(names):
            if name in auto:
                self.lb_yolo_images.selection_clear(0, "end")
                self.lb_yolo_images.selection_set(i)
                self.lb_yolo_images.see(i)
                return
        self.notify("沒有待確認的自動標註圖片。")

    # ---- 匯入圖片／影片 ----
    def open_yolo_inbox(self):
        os.makedirs(YOLO_INBOX_DIR, exist_ok=True)
        if IS_WIN:
            os.startfile(YOLO_INBOX_DIR)
        else:
            self.notify(f"匯入資料夾：{YOLO_INBOX_DIR}")

    def _save_dataset_image(self, img, prefix, known):
        """存成 yolo_data/images 的 png；內容一樣的圖（雜湊相同）不重複存。回傳是否新增"""
        ok, buf = cv2.imencode(".png", img)
        if not ok:
            return False
        digest = hashlib.sha1(buf.tobytes()).hexdigest()[:16]
        if digest in known:
            return False
        known.add(digest)
        path = os.path.join(YOLO_IMAGES_DIR, f"{prefix}_{digest}.png")
        with open(path, "wb") as f:
            f.write(buf.tobytes())
        return True

    def _known_image_digests(self):
        out = set()
        for n in self._yolo_image_files():
            m = re.search(r"_([0-9a-f]{16})\.png$", n)
            if m:
                out.add(m.group(1))
        return out

    def import_yolo_inbox(self):
        """匯入「把圖片丟這裡」裡的所有圖片（含子資料夾）；匯入完的原檔移到「已匯入」"""
        os.makedirs(YOLO_INBOX_DIR, exist_ok=True)
        done_dir = os.path.join(YOLO_INBOX_DIR, "已匯入")
        files = []
        for base, dirs, names in os.walk(YOLO_INBOX_DIR):
            if os.path.abspath(base).startswith(os.path.abspath(done_dir)):
                continue
            files += [os.path.join(base, n) for n in names if n.lower().endswith(IMAGE_EXTS)]
        if not files:
            self.notify("「把圖片丟這裡」資料夾是空的：先把截圖（png／jpg）放進去再按匯入。")
            self.open_yolo_inbox()
            return
        self.notify(f"正在匯入 {len(files)} 張圖片…")

        def worker():
            self._ensure_yolo_dirs()
            os.makedirs(done_dir, exist_ok=True)
            known = self._known_image_digests()
            added = dup = bad = 0
            for path in files:
                img = imread_unicode(path)
                if img is None:
                    bad += 1
                    continue
                if img.ndim == 3 and img.shape[2] == 4:
                    img = cv2.cvtColor(img, cv2.COLOR_BGRA2BGR)
                if self._save_dataset_image(img, "import", known):
                    added += 1
                else:
                    dup += 1
                try:
                    target = os.path.join(done_dir, os.path.basename(path))
                    if os.path.exists(target):
                        stem, ext = os.path.splitext(target)
                        target = f"{stem}_{time.time_ns() % 1_000_000:06d}{ext}"
                    shutil.move(path, target)
                except OSError:
                    pass
            msg = f"匯入完成：新增 {added} 張" + (f"，重複略過 {dup} 張" if dup else "") + \
                  (f"，無法讀取 {bad} 張" if bad else "") + "。原檔已移到「已匯入」。"
            self.ui(lambda: (self.refresh_yolo_dataset(), self.notify(msg)))
        threading.Thread(target=worker, daemon=True).start()

    def import_yolo_video(self):
        """從遊戲錄影每隔幾秒擷取一張；和上一張幾乎一樣的畫面略過"""
        path = filedialog.askopenfilename(parent=self.root, title="選擇遊戲錄影",
                                          filetypes=[("影片", " ".join("*" + e for e in VIDEO_EXTS)), ("全部檔案", "*.*")])
        if not path:
            return
        d = FormDialog(self.root, "從影片擷取", [("sec", "每隔幾秒取一張", "1.0"), ("max", "最多幾張", "300")])
        if not d.result:
            return
        try:
            every, limit = max(0.2, float(d.result["sec"])), max(1, int(d.result["max"]))
        except ValueError:
            self.notify("秒數與張數請填數字。", error=True)
            return
        self.notify(f"正在從影片擷取：{os.path.basename(path)}…")

        def worker():
            self._ensure_yolo_dirs()
            cap = cv2.VideoCapture(path)
            if not cap.isOpened():
                self.ui(lambda: self.notify("無法開啟這個影片檔（格式不支援或檔案損毀）。", error=True))
                return
            fps = cap.get(cv2.CAP_PROP_FPS) or 30.0
            step = max(1, int(round(fps * every)))
            known = self._known_image_digests()
            added = skipped = idx = 0
            last_small = None
            while added < limit:
                ok = cap.grab()
                if not ok:
                    break
                if idx % step == 0:
                    ok, frame = cap.retrieve()
                    if ok and frame is not None:
                        small = cv2.resize(cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY), (160, 90))
                        if last_small is not None and float(cv2.absdiff(small, last_small).mean()) < 2.5:
                            skipped += 1               # 和上一張幾乎一樣（站著不動、選單畫面）
                        else:
                            last_small = small
                            if self._save_dataset_image(frame, "video", known):
                                added += 1
                                if added % 25 == 0:
                                    n = added
                                    self.ui(lambda: self.notify(f"影片擷取中…已存 {n} 張"))
                idx += 1
            cap.release()
            msg = f"影片擷取完成：新增 {added} 張" + (f"，畫面太像略過 {skipped} 張" if skipped else "") + "。"
            self.ui(lambda: (self.refresh_yolo_dataset(), self.notify(msg)))
        threading.Thread(target=worker, daemon=True).start()

    # ---- 模型自動標註 ----
    def auto_label_yolo(self):
        """用目前的模型替「還沒標註」的圖片先畫好框（之後人工檢查），標成 ◐ 待確認"""
        det = self.scanner.yolo
        if not det.available():
            self.notify("目前沒有可用的 YOLO 模型（或未啟用），無法自動標註。", error=True)
            return
        names = [n for n in self._yolo_image_files()
                 if not os.path.isfile(os.path.join(YOLO_LABELS_DIR, os.path.splitext(n)[0] + ".txt"))]
        if not names:
            self.notify("所有圖片都已經有標註了。")
            return
        if not messagebox.askyesno("用模型自動標註", f"要用目前的模型替 {len(names)} 張還沒標註的圖片先畫框嗎？\n"
                                   "畫好的圖會標成 ◐（待確認），請再逐張打開檢查。", parent=self.root):
            return
        self.notify(f"自動標註中（{len(names)} 張）…")

        def worker():
            auto = self._yolo_auto_set()
            done = boxes_total = 0
            for i, name in enumerate(names):
                img = imread_unicode(os.path.join(YOLO_IMAGES_DIR, name))
                if img is None:
                    continue
                boxes = det.detect_boxes(img)
                if boxes is None:
                    err = det.error or "模型無法使用"
                    self.ui(lambda: self.notify(f"自動標註中斷：{err}", error=True))
                    break
                h, w = img.shape[:2]
                lines = []
                for x1, y1, x2, y2, conf, cls in boxes:
                    if cls not in YOLO_CLASS_NAMES:
                        continue
                    bw, bh = max(1, x2 - x1), max(1, y2 - y1)
                    lines.append(f"{YOLO_CLASS_NAMES.index(cls)} {(x1 + bw / 2) / w:.6f} {(y1 + bh / 2) / h:.6f} "
                                 f"{bw / w:.6f} {bh / h:.6f}")
                with open(os.path.join(YOLO_LABELS_DIR, os.path.splitext(name)[0] + ".txt"), "w",
                          encoding="utf-8", newline="\n") as f:
                    f.write("\n".join(lines) + ("\n" if lines else ""))
                auto.add(name)
                done += 1
                boxes_total += len(lines)
                if done % 20 == 0:
                    self._save_yolo_auto_set(auto)
                    n = done
                    self.ui(lambda: (self.refresh_yolo_dataset(), self.notify(f"自動標註中…{n}/{len(names)}")))
            self._save_yolo_auto_set(auto)
            msg = f"自動標註完成：{done} 張、共 {boxes_total} 個框；清單中 ◐ 的圖請逐張檢查後存檔。"
            self.ui(lambda: (self.refresh_yolo_dataset(), self.notify(msg)))
        threading.Thread(target=worker, daemon=True).start()

    def open_yolo_dir(self):
        self._ensure_yolo_dirs()
        if IS_WIN:
            os.startfile(YOLO_DATA_DIR)

    def preview_yolo(self):
        img = self.vision.grab_client() if IS_WIN else None
        if img is None:
            self.notify("找不到遊戲視窗，無法測試 YOLO。", error=True)
            return
        if not self.save_yolo_runtime():
            return
        t0 = time.time()
        boxes = self.scanner.yolo.detect_boxes(img)
        elapsed = (time.time() - t0) * 1000
        self.update_yolo_model_label()
        if boxes is None:
            self.notify(self.scanner.yolo.error or "YOLO 模型目前無法使用。", error=True)
            return
        out = yolo_preview_image(img, boxes)
        model_names = self.scanner.yolo.class_names.get(self.scanner.yolo.model_path(), set())
        counts = {k: sum(1 for b in boxes if b[5] == k) for k in YOLO_CLASS_NAMES}
        th = self.scanner.yolo.class_conf()
        parts = []
        for k, label in zip(YOLO_CLASS_NAMES, YOLO_CLASS_LABELS):
            if model_names and k not in model_names:
                parts.append(f"{label}：模型沒有這個類別")
            else:
                parts.append(f"{label} {counts[k]}" + ("" if counts[k] else f"（門檻 {th[k]:g}）"))
        summary = "、".join(parts)
        log(f"YOLO 測試：{summary}，{elapsed:.0f} ms")
        win = tk.Toplevel(self.root)
        win.title(f"YOLO 偵測：{summary}（{elapsed:.0f} ms）")
        win.attributes("-topmost", True)
        scale = min(1.0, (self.root.winfo_screenwidth() - 80) / out.shape[1],
                    (self.root.winfo_screenheight() - 120) / out.shape[0])
        disp = cv2.resize(out, (int(out.shape[1] * scale), int(out.shape[0] * scale)))
        win._image = ImageTk.PhotoImage(Image.fromarray(cv2.cvtColor(disp, cv2.COLOR_BGR2RGB)))
        tk.Label(win, image=win._image).pack()

    def build_skill(self, f):
        box = section(f, "Buff／定時技能", "勾選即啟用；每隔設定秒數自動施放，按開始時會先各放一次。直接修改，自動儲存。")
        self.skill_grid = ttk.Frame(box)
        self.skill_grid.pack(fill="x")
        button_row(box, [("＋ 新增技能", self.add_skill)])
        wait_row = ttk.Frame(box)
        wait_row.pack(fill="x", pady=(6, 0))
        ttk.Label(wait_row, text="開始時放完 Buff 後再等").pack(side="left")
        self.var_buff_wait = tk.StringVar(value=f"{float(self.cfg.get('buff_start_wait', 1.0)):g}")
        ew = ttk.Entry(wait_row, textvariable=self.var_buff_wait, width=5)
        ew.pack(side="left", padx=4)
        ttk.Label(wait_row, text="秒才開始移動").pack(side="left")
        ew.bind("<FocusOut>", lambda _e: self.save_buff_wait())
        ew.bind("<Return>", lambda _e: self.save_buff_wait())
        box2 = section(f, "持續攻擊", "路線的「等待」步驟中，依間隔一直按攻擊鍵。")
        r = ttk.Frame(box2)
        r.pack(fill="x")
        self.var_atk = tk.BooleanVar(value=self.cfg["attack"]["enabled"])
        ttk.Checkbutton(r, text="啟用", variable=self.var_atk, command=self.save_attack).pack(side="left")
        ttk.Label(r, text="間隔(秒)").pack(side="left", padx=(16, 6))
        self.var_atk_int = tk.StringVar(value=str(self.cfg["attack"]["interval"]))
        e = ttk.Entry(r, textvariable=self.var_atk_int, width=6)
        e.pack(side="left")
        e.bind("<FocusOut>", lambda _: self.save_attack())
        e.bind("<Return>", lambda _: self.save_attack())
        self.reload_skills()

    def build_elite(self, f):
        el = self.cfg["elite"]
        box = section(f, "偵測", "菁英怪出現時，框選畫面上每次都一樣的特徵（例如菁英血條的圖示或邊框，不要框到血量）。")
        r = ttk.Frame(box)
        r.pack(fill="x")
        self.var_el = tk.BooleanVar(value=el.get("enabled", True))
        ttk.Checkbutton(r, text="啟用菁英偵測", variable=self.var_el, command=self.save_elite).pack(side="left")
        self.var_el_beep = tk.BooleanVar(value=el.get("beep", False))
        ttk.Checkbutton(r, text="切換時嗶一聲", variable=self.var_el_beep, command=self.save_elite).pack(side="left", padx=12)
        button_row(box, [("＋ 新增範本（框選畫面）", self.add_elite_template), ("範本資料夾", self.open_elite_dir),
                         ("測試：假裝菁英出現 10 秒", self.test_elite)])
        self.lbl_el = ttk.Label(box, text="", style="Hint.TLabel")
        self.lbl_el.pack(anchor="w", pady=(4, 0))

        box2 = section(f, "菁英模式攻擊", "菁英技能依冷卻輪流施放；其餘時間用主攻擊鍵。")
        self.elite_vars = {}
        g = ttk.Frame(box2)
        g.pack(fill="x")
        form_grid(g, [("attack_key", "主攻擊鍵", key_spec("（用一般攻擊鍵）")), ("attack_interval", "主攻擊間隔(秒)")],
                  el, self.elite_vars, self.save_elite, width=7)
        self.var_el_hold = tk.BooleanVar(value=el.get("hold_attack", False))
        ttk.Checkbutton(box2, text="按住主攻擊鍵（不連點）— 定點掛機建議勾選，主攻擊鍵填範圍技",
                        variable=self.var_el_hold, command=self.save_elite).pack(anchor="w", pady=(4, 4))
        self.tv_elite = make_tree(box2, [("on", "啟用", 50), ("name", "名稱", 160), ("key", "按鍵", 80),
                                         ("cd", "冷卻(秒)", 80), ("delay", "施放後等待", 90)], height=4)
        self.tv_elite.pack(fill="x")
        self.tv_elite.bind("<Double-1>", lambda _: self.edit_elite_skill())
        button_row(box2, [("＋ 新增菁英技能", lambda: self.edit_elite_skill(new=True)), ("編輯", self.edit_elite_skill),
                          ("啟用／停用", self.toggle_elite_skill), ("刪除", self.del_elite_skill)])
        adv = Collapsible(box2, "進階：門檻、結束判定、轉身")
        adv.pack(fill="x", pady=(6, 0))
        g2 = ttk.Frame(adv.body)
        g2.pack(fill="x")
        form_grid(g2, [("threshold", "相似度門檻"), ("end_sec", "消失幾秒算結束"),
                       ("turn_sec", "每幾秒轉身(0=不轉)"), ("max_sec", "最長持續(秒)")],
                  el, self.elite_vars, self.save_elite, width=6)
        self.reload_elite()

    def build_alarm(self, f):
        ld = self.cfg["lie_detector"]
        lf = section(f, "測謊偵測", "偵測到就暫停並響警報，需要你自己回遊戲作答。測謊出現時框選視窗中固定不變的部分當範本。")
        self.var_ld = tk.BooleanVar(value=ld.get("enabled", True))
        self.var_ld_beep = tk.BooleanVar(value=ld.get("beep", True))
        self.var_ld_th = tk.StringVar(value=str(ld.get("threshold", 0.8)))

        def save_ld(*_):
            try:
                ld["threshold"] = float(self.var_ld_th.get())
            except ValueError:
                self.notify("測謊門檻必須是數字", error=True)
                return
            ld["enabled"], ld["beep"] = self.var_ld.get(), self.var_ld_beep.get()
            save_config(self.cfg)

        r = ttk.Frame(lf)
        r.pack(fill="x")
        ttk.Checkbutton(r, text="啟用", variable=self.var_ld, command=save_ld).pack(side="left")
        ttk.Checkbutton(r, text="嗶嗶警報", variable=self.var_ld_beep, command=save_ld).pack(side="left", padx=12)
        button_row(lf, [("＋ 新增範本（框選畫面）", self.add_ld_template), ("範本資料夾", self.open_template_dir),
                        ("測試警報", lambda: self.trigger_alarm("lie", "測試：偵測到測謊", beep=self.var_ld_beep.get()))])
        self.lbl_tpl = ttk.Label(lf, text="", style="Hint.TLabel")
        self.lbl_tpl.pack(anchor="w", pady=(4, 0))
        adv = Collapsible(lf, "進階：相似度門檻")
        adv.pack(fill="x")
        e = ttk.Entry(adv.body, textvariable=self.var_ld_th, width=6)
        ttk.Label(adv.body, text="相似度門檻").pack(side="left", padx=(0, 6))
        e.pack(side="left")
        e.bind("<FocusOut>", save_ld)
        e.bind("<Return>", save_ld)
        self.update_tpl_label()

        rd = self.cfg["red_dot"]
        rf = section(f, "紅點警報（小地圖出現其他玩家）")
        self.var_rd = tk.BooleanVar(value=rd.get("enabled", True))
        self.var_rd_pause = tk.BooleanVar(value=rd.get("pause", True))
        self.var_rd_beep = tk.BooleanVar(value=rd.get("beep", True))
        self.var_rd_area = tk.StringVar(value=str(rd.get("min_area", 2)))
        self.var_rd_max_area = tk.StringVar(value=str(rd.get("max_area", 12)))
        self.var_rd_max_size = tk.StringVar(value=str(rd.get("max_size", 5)))
        self.var_rd_sec = tk.StringVar(value=str(rd.get("confirm_sec", 0.3)))

        def save_rd(*_):
            try:
                min_area = int(self.var_rd_area.get())
                max_area = int(self.var_rd_max_area.get())
                max_size = int(self.var_rd_max_size.get())
                if min_area < 1 or max_area < min_area or max_size < 1:
                    raise ValueError
                rd["min_area"] = min_area
                rd["max_area"] = max_area
                rd["max_size"] = max_size
                rd["confirm_sec"] = float(self.var_rd_sec.get())
            except ValueError:
                self.notify("紅點大小需為正數，且最大面積不能小於最小面積", error=True)
                return
            rd["enabled"], rd["pause"], rd["beep"] = self.var_rd.get(), self.var_rd_pause.get(), self.var_rd_beep.get()
            save_config(self.cfg)

        r = ttk.Frame(rf)
        r.pack(fill="x")
        ttk.Checkbutton(r, text="啟用", variable=self.var_rd, command=save_rd).pack(side="left")
        ttk.Checkbutton(r, text="出現時暫停", variable=self.var_rd_pause, command=save_rd).pack(side="left", padx=12)
        ttk.Checkbutton(r, text="嗶嗶警報", variable=self.var_rd_beep, command=save_rd).pack(side="left")
        button_row(rf, [("點選紅點取色", self.pick_red_color),
                        ("測試警報", lambda: self.trigger_alarm("red", "測試：小地圖出現紅點", pause=False,
                                                            beep=self.var_rd_beep.get()))])
        adv2 = Collapsible(rf, "進階：紅點大小過濾、持續時間")
        adv2.pack(fill="x")
        for i, (label, var) in enumerate((("最小面積(px)", self.var_rd_area),
                                           ("最大面積(px)", self.var_rd_max_area),
                                           ("最大寬/高(px)", self.var_rd_max_size),
                                           ("持續幾秒才警報", self.var_rd_sec))):
            ttk.Label(adv2.body, text=label).grid(row=0, column=i * 2, sticky="w", padx=(0 if i == 0 else 16, 6))
            e = ttk.Entry(adv2.body, textvariable=var, width=6)
            e.grid(row=0, column=i * 2 + 1)
            e.bind("<FocusOut>", save_rd)
            e.bind("<Return>", save_rd)
        ttk.Label(rf, text="同一批紅點只警報一次；紅點消失 3 秒以上才會再次警報。",
                  style="Hint.TLabel").pack(anchor="w", pady=(4, 0))

    def build_keys(self, f):
        self.set_vars = getattr(self, "set_vars", {})
        box = section(f, "按鍵", "從選單選擇，要和遊戲內的按鍵設定一致。")
        g = ttk.Frame(box)
        g.pack(fill="x")
        src = {"key_" + k: v for k, v in self.cfg["keys"].items()}
        form_grid(g, [("key_jump", "跳躍", KEY_SPEC), ("key_attack", "攻擊", KEY_SPEC), ("key_left", "左", KEY_SPEC),
                      ("key_right", "右", KEY_SPEC), ("key_up", "上（爬繩）", KEY_SPEC), ("key_down", "下", KEY_SPEC)],
                  src, self.set_vars, self.save_settings, width=8, label_min=40, choice_min=8)
        button_row(box, [("測試：3 秒後按一下跳躍", self.test_jump)], pady=(8, 0))

        box2 = section(f, "熱鍵與遊戲視窗")
        g2 = ttk.Frame(box2)
        g2.pack(fill="x")
        src2 = {"hk_toggle": self.cfg["hotkeys"].get("toggle", "f10"), "hk_stop": self.cfg["hotkeys"].get("stop", "f12"),
                "hk_record": self.cfg["hotkeys"].get("record", "f8"),
                "window_title": self.cfg["window_title"]}
        form_grid(g2, [("hk_toggle", "開始／暫停", FKEY_SPEC), ("hk_stop", "緊急停止", FKEY_SPEC),
                       ("hk_record", "錄製結束", FKEY_SPEC)], src2,
                  self.set_vars, self.save_settings, width=6, label_min=60, choice_min=6)
        g3 = ttk.Frame(box2)
        g3.pack(fill="x", pady=(6, 0))
        ttk.Label(g3, text="視窗標題").pack(side="left")
        self.set_vars["window_title"] = tk.StringVar(value=str(src2["window_title"]))
        et = ttk.Entry(g3, textvariable=self.set_vars["window_title"], width=16)
        et.pack(side="left", fill="x", expand=True, padx=(6, 0))
        et.bind("<FocusOut>", lambda _e: self.save_settings())
        et.bind("<Return>", lambda _e: self.save_settings())
        pick = ttk.Frame(box2)
        pick.pack(fill="x", pady=(4, 0))
        self.var_window_pick = tk.StringVar()
        self.cmb_window_pick = ttk.Combobox(pick, textvariable=self.var_window_pick, state="readonly", width=16)
        self.cmb_window_pick.pack(side="left", fill="x", expand=True)
        ttk.Button(pick, text="掃描", width=5, command=self.refresh_window_list).pack(side="left", padx=(4, 0))
        ttk.Button(pick, text="使用", width=5, command=self.use_selected_window).pack(side="left", padx=(4, 0))
        hint(box2, "標題只要包含部分文字即可；找不到遊戲時，從下拉清單選取遊戲視窗按「使用」。", pady=(3, 0))
        self.refresh_window_list()

    def build_options(self, f):
        box2 = section(f, "基礎")
        self.var_focus = tk.BooleanVar(value=self.cfg.get("only_when_focused", True))
        self.var_top = tk.BooleanVar(value=False)
        ttk.Checkbutton(box2, text="只在遊戲視窗為前景時送出按鍵（建議開啟）", variable=self.var_focus,
                        command=self.save_settings).pack(anchor="w", pady=(4, 0))
        ttk.Checkbutton(box2, text="暫時置頂（開始掛機或重開後自動取消）", variable=self.var_top,
                        command=self.save_settings).pack(anchor="w")
        self.var_key_repeat = tk.BooleanVar(value=self.cfg.get("key_repeat", True))
        ttk.Checkbutton(box2, text="按住的鍵持續送出訊號（像實體鍵盤按住）",
                        variable=self.var_key_repeat, command=self.save_settings).pack(anchor="w")
        self.var_min_start = tk.BooleanVar(value=self.cfg.get("minimize_on_start", True))
        self.var_restore = tk.BooleanVar(value=self.cfg.get("restore_on_pause", True))
        ttk.Checkbutton(box2, text="按開始時自動縮小本工具，並切到遊戲", variable=self.var_min_start,
                        command=self.save_settings).pack(anchor="w")
        ttk.Checkbutton(box2, text="暫停／停止時自動還原本工具視窗", variable=self.var_restore,
                        command=self.save_settings).pack(anchor="w")
        self.var_prehold = tk.BooleanVar(value=self.cfg.get("rope_prehold", True))
        pre = ttk.Frame(box2)
        pre.pack(anchor="w", fill="x")
        ttk.Checkbutton(pre, text="接近繩子時先按住上，距離", variable=self.var_prehold,
                        command=self.save_settings).pack(side="left")
        self.var_prehold_dist = tk.StringVar(value=str(self.cfg.get("rope_prehold_dist", 4)))
        e = ttk.Entry(pre, textvariable=self.var_prehold_dist, width=3)
        e.pack(side="left", padx=3)
        e.bind("<FocusOut>", lambda _e: self.save_settings())
        e.bind("<Return>", lambda _e: self.save_settings())
        ttk.Label(pre, text="格內").pack(side="left")
        hint(box2, "開始／暫停熱鍵只在遊戲或本工具在前景時有效；緊急停止隨時有效。", pady=(4, 0))

    def open_diag_dir(self):
        os.makedirs(DIAG_DIR, exist_ok=True)
        if IS_WIN:
            os.startfile(DIAG_DIR)

    def refresh_window_list(self):
        """更新可手動選取的視窗清單；排除本工具自己的視窗。"""
        if not IS_WIN:
            return
        mine = self.root.winfo_id()
        titles = []
        seen = set()
        for hwnd, title in list_visible_windows():
            if hwnd == mine or title in seen:
                continue
            seen.add(title)
            titles.append(title)
        titles.sort(key=str.casefold)
        self.cmb_window_pick["values"] = titles
        current = self.set_vars["window_title"].get().strip()
        if current in titles:
            self.var_window_pick.set(current)
        elif titles:
            self.var_window_pick.set(titles[0])
        else:
            self.var_window_pick.set("")
            self.notify("找不到可選取的視窗；請先開啟遊戲後再重新掃描。", error=True)

    def use_selected_window(self):
        title = self.var_window_pick.get().strip()
        if not title:
            self.notify("請先從清單選取遊戲視窗。", error=True)
            return
        self.set_vars["window_title"].set(title)
        self.cfg["window_title"] = title
        self.vision.hwnd = None  # 讓背景辨識立即依新標題重新搜尋
        save_config(self.cfg)
        if hasattr(self, "wiz_rows"):
            self.rebuild_wizard()
        self.notify(f"已選取遊戲視窗：{title}")

    def build_detect_adv(self, f):
        self.set_vars = getattr(self, "set_vars", {})
        box = section(f, "小地圖與角色點", "通常用「首次設定」的框選和取色即可，不需要手動調整。")
        button_row(box, [("重新框選小地圖", self.calibrate_minimap), ("重新取色", self.pick_color)], pady=(0, 6))
        g = ttk.Frame(box)
        g.pack(fill="x")
        src = {"min_dot_area": self.cfg["min_dot_area"],
               "hsv_low": ",".join(map(str, self.cfg["player_hsv_low"])),
               "hsv_high": ",".join(map(str, self.cfg["player_hsv_high"]))}
        form_grid(g, [("hsv_low", "角色點 HSV 下限"), ("hsv_high", "角色點 HSV 上限"),
                      ("min_dot_area", "角色點最小面積(px)")], src, self.set_vars, self.save_settings,
                  width=12, cols=1)
        box2 = section(f, "移動精準度")
        g2 = ttk.Frame(box2)
        g2.pack(fill="x")
        src2 = {"goto_tolerance": self.cfg["goto_tolerance"], "rope_tolerance": self.cfg["rope_tolerance"]}
        form_grid(g2, [("goto_tolerance", "走到定點容許誤差(px)"), ("rope_tolerance", "對準繩子容許誤差(px)")],
                  src2, self.set_vars, self.save_settings, width=6, cols=1)
        self.patrol_vars = getattr(self, "patrol_vars", {})
        g3 = ttk.Frame(box2)
        g3.pack(fill="x")
        form_grid(g3, [("plat_tol", "同一層判定誤差(px)")], self.cfg["patrol_opt"], self.patrol_vars,
                  self.save_patrol_opt, width=6, cols=1)
        ttk.Label(box2, text="走過頭來回晃 → 調大「走到定點容許誤差」；爬繩對不準 → 調小「對準繩子容許誤差」。",
                  style="Hint.TLabel").pack(anchor="w", pady=(4, 0))

        box3 = section(f, "診斷記錄", "遇到問題時勾選，按開始跑一次再停止。會在工具資料夾的 diag 裡留下小地圖影片、"
                                     "座標與按鍵紀錄、遊戲畫面截圖，方便找出原因。每次開始都會覆蓋上一次的紀錄。")
        self.var_diag = tk.BooleanVar(value=self.cfg.get("diagnostics", False))

        def save_diag():
            self.cfg["diagnostics"] = self.var_diag.get()
            save_config(self.cfg)
        ttk.Checkbutton(box3, text="記錄診斷資料", variable=self.var_diag, command=save_diag).pack(anchor="w")
        button_row(box3, [("開啟診斷資料夾", self.open_diag_dir)])

    # ---------------- 首次設定 ----------------
    def setup_steps(self):
        """(id, 標題, 說明, 檢查函式, [(按鈕, 指令)], 需要此步驟的模式, 選用的模式)"""
        sc, v, c = self.scanner, self.vision, self.cfg
        mode_pts = {
            "anchor": ("記錄定點", "到「掛機地圖」站到掛機位置，按「新增定點」。",
                       lambda: bool(self.bot.anchor_points())),
            "combat": ("記錄巡邏點", "到主控台記錄幾個巡邏點，以及上樓用的繩子。", lambda: bool(c["patrol"])),
            "buff": ("錄製整張地圖", "到「掛機地圖」選 BUFF機，按「錄製隨機路線」，自己跑完一輪後按錄製結束熱鍵。",
                     lambda: bool((c.get("map_macro") or {}).get("events"))),
            "random": ("記錄攻擊點", "到主控台記錄攻擊點，以及上樓用的繩子。", lambda: bool(c["patrol"])),
            "route": ("排好路線", "到主控台用「記錄」與「＋」按鈕排出路線步驟。", lambda: bool(c["route"])),
        }
        mode = c.get("mode", "anchor")
        pt = mode_pts.get(mode, mode_pts["anchor"])
        ALL = set(MODE_ORDER)
        return [
            ("game", "選取遊戲視窗", f"目前目標：「{c['window_title']}」。找不到時可到「設定」頁，從已開啟視窗清單手動選取。",
             lambda: bool(v.hwnd), [("選擇視窗", lambda: self.open_shared("keys")),
                                    ("重新尋找", lambda: setattr(v, "hwnd", None))], ALL, set()),
            ("map", "框選小地圖", "在遊戲截圖上拖曳框住小地圖本體（不含標題列），按 Enter。換地圖或縮放小地圖後要重框。",
             lambda: bool(c.get("minimap")), [("框選小地圖", self.calibrate_minimap)], ALL, set()),
            ("dot", "角色點取色", "在放大的小地圖上點一下你的黃點；上方座標會跟著角色移動就成功了。",
             lambda: v.get_pos() is not None, [("點選取色", self.pick_color)], ALL, set()),
            ("keys", "確認遊戲按鍵", "跳躍、攻擊、方向鍵要和遊戲內一致，按「測試跳躍」確認。",
             lambda: bool(c.get("setup_keys_ok")),
             [("按鍵設定", lambda: self.open_shared("keys")), ("測試跳躍", self.test_jump)], ALL, set()),
            ("points", pt[0], pt[1], pt[2], [("到掛機地圖", lambda: self.nb.select(self.tab_home))], ALL, set()),
            ("tag", "框選角色名牌", "框選自己角色腳下的名牌（不要框到角色）。設定物品範本後，撿物功能才需要它。",
             lambda: sc.tag_template is not None, [("框選名牌", self.set_nametag)], set(), {"buff"}),
            ("mob", "框選怪物範本", "框選這張地圖的怪物，不同動作可多存幾張。",
             lambda: bool(sc.mon_templates), [("新增怪物範本", self.add_monster_template)], {"combat"}, {"random", "route"}),
            ("item", "框選物品範本", "框選地上的楓幣、常掉的道具；沒有範本時只會連點撿物＋掃地。",
             lambda: bool(sc.item_templates), [("新增物品範本", self.add_item_template)], set(), {"buff"}),
            ("buffs", "設定 Buff", "在「設定」頁的 Buff／定時技能表新增要定時施放的技能。",
             lambda: any(s.get("enabled") for s in c["skills"]), [("前往設定", lambda: self.open_shared("skill"))],
             set(), ALL),
            ("lie", "測謊範本", "測謊出現時框選視窗特徵，之後偵測到會暫停並警報。",
             lambda: bool(v.templates), [("前往設定", lambda: self.open_shared("alarm"))], set(), ALL),
        ]

    def missing_required(self, skip=()):
        mode = self.cfg.get("mode", "anchor")
        out = []
        for sid, title, _d, chk, _a, req, _o in self.setup_steps():
            if sid in skip:
                continue
            try:
                ok = chk()
            except Exception:
                ok = False
            if mode in req and not ok:
                out.append(title)
        return out

    def build_wizard(self, f):
        top = ttk.Frame(f)
        top.pack(fill="x")
        self.lbl_wiz_title = ttk.Label(top, text="", font=(UI_FONT, 12, "bold"))
        self.lbl_wiz_title.pack(anchor="w")
        ttk.Label(top, text="照順序完成「必要」步驟即可開始；「選用」的做了會更好用。完成的步驟會自動打勾。",
                  style="Hint.TLabel").pack(anchor="w", pady=(2, 8))
        self.wiz_scroll = ScrollFrame(f)
        self.wiz_scroll.pack(fill="both", expand=True)
        self.wiz_host = self.wiz_scroll.inner
        self.wiz_rows = {}
        self._wiz_mode = None
        self.rebuild_wizard()

    def rebuild_wizard(self):
        for w in self.wiz_host.winfo_children():
            w.destroy()
        self.wiz_rows = {}
        mode = self.cfg.get("mode", "anchor")
        self._wiz_mode = mode
        self.lbl_wiz_title.config(text=f"目前模式：{MODE_INFO.get(mode, MODE_INFO['anchor'])[0]}")
        n = 0
        for sid, title, desc, chk, actions, req, opt in self.setup_steps():
            if mode not in req and mode not in opt:
                continue
            n += 1
            row = ttk.Frame(self.wiz_host, padding=(4, 6))
            row.pack(fill="x")
            dot = tk.Label(row, text="○", font=(UI_FONT, 14, "bold"), width=2, fg=C_MUTED)
            dot.grid(row=0, column=0, rowspan=2, sticky="n")
            tag = "必要" if mode in req else "選用"
            ttk.Label(row, text=f"{n}. {title}", font=(UI_FONT, 10, "bold")).grid(row=0, column=1, sticky="w")
            ttk.Label(row, text=tag, style="Hint.TLabel").grid(row=0, column=2, sticky="w", padx=6)
            autowrap(ttk.Label(row, text=desc, style="Hint.TLabel", justify="left")).grid(
                row=1, column=1, columnspan=2, sticky="we")
            bf = ttk.Frame(row)
            bf.grid(row=0, column=3, rowspan=2, sticky="e")
            for text, cmd in actions:
                ttk.Button(bf, text=text, command=cmd).pack(side="left", padx=(4, 0))
            row.columnconfigure(2, weight=1)
            ttk.Separator(self.wiz_host).pack(fill="x")
            self.wiz_rows[sid] = (dot, chk, mode in req)
        self.update_wizard()

    def update_wizard(self):
        if self._wiz_mode != self.cfg.get("mode"):
            self.rebuild_wizard()
            return
        for sid, (dot, chk, required) in self.wiz_rows.items():
            try:
                ok = chk()
            except Exception:
                ok = False
            if ok:
                dot.config(text="✔", fg=C_OK)
            else:
                dot.config(text="●" if required else "○", fg=C_BAD if required else C_MUTED)

    # ---------------- 定期更新 ----------------
    def refresh(self):
        if not self.alive_ui:
            return
        v, b = self.vision, self.bot
        hk_t = self.cfg["hotkeys"].get("toggle", "f10").upper()
        hk_s = self.cfg["hotkeys"].get("stop", "f12").upper()
        p = v.get_pos()
        self.lbl_pos.config(text=f"座標  X {p[0]}   Y {p[1]}" if p else "座標 --")

        def chip(key, ok, warn=False):
            self.chips[key].config(fg="white" if ok or warn else "#4b5563",
                                   bg=C_OK if ok else (C_WARN if warn else "#e5e7eb"))
        chip("game", bool(v.hwnd))
        chip("map", bool(self.cfg.get("minimap")))
        chip("dot", p is not None, warn=bool(self.cfg.get("minimap")) and p is None)
        need_tag = self.cfg.get("mode") == "buff" and bool(self.scanner.item_templates)
        chip("tag", self.scanner.tag_template is not None, warn=need_tag and self.scanner.tag_template is None)
        info = ""
        if v.hwnd and v.rect:
            info = f"{v.rect[2]}×{v.rect[3]}　{v.fps:.0f} fps"
        sn = self.scanner.snap
        if (self.scanner.scan_ready() or self.scanner.loot_ready()) and sn and time.time() - sn[0] < 1.5:
            info += f"　怪 {len(sn[2])}　物品 {len(sn[3]) if len(sn) > 3 else 0}　{self.scanner.ms:.0f}ms"
        warn = self.overlap_warning()
        if warn:
            self.lbl_win.config(text=warn, foreground=C_BAD)
        else:
            self.lbl_win.config(text=info if v.hwnd else f"找不到「{self.cfg['window_title']}」視窗",
                                foreground=C_MUTED)

        mode_name = MODE_INFO.get(self.cfg.get("mode"), ("", ""))[0]
        if b.active.is_set():
            self.lbl_status.config(text=f"{mode_name}　▶ {b.status}")
            self._log_status(b.status)
        else:
            self.lbl_status.config(text=f"{mode_name}　暫停中（按 {hk_t} 或「開始掛機」）")
            self._log_status(None)
        elite_on = (v.elite_templates and self.cfg["elite"].get("enabled")
                    and time.time() - v.elite_seen_at < float(self.cfg["elite"].get("end_sec", 3)))
        self.lbl_status.config(foreground=C_BAD if elite_on else C_ACCENT)
        word = "" if self._side_compact else "掛機"
        run_text = f"⏸ 暫停 ({hk_t})" if b.active.is_set() else f"▶ 開始{word} ({hk_t})"
        if self.btn_run.cget("text") != run_text:
            self.btn_run.config(text=run_text)
        if self.btn_stop.cget("text") != f"■ 停止{word} ({hk_s})":
            self.btn_stop.config(text=f"■ 停止{word} ({hk_s})")
        self.draw_minimap()

        self._tick += 1
        if self._tick % 10 == 1:   # 約每秒更新一次較耗時的部分
            miss = self.missing_required()
            if miss:
                self.lbl_setup.config(text=f"還有 {len(miss)} 個必要設定沒完成：{'、'.join(miss[:3])}"
                                      + ("…" if len(miss) > 3 else ""))
                if not self.setup_frame.winfo_ismapped():
                    self.setup_frame.pack(fill="x", pady=(6, 0))
            elif self.setup_frame.winfo_ismapped():
                self.setup_frame.pack_forget()
            self.update_wizard()
        self.root.after(100, self.refresh)

    def overlap_warning(self):
        """本工具視窗蓋住遊戲的小地圖時，截到的會是本工具 → 座標不會更新"""
        v, mm = self.vision, self.cfg.get("minimap")
        if not (mm and v.hwnd and v.rect) or self.root.state() == "iconic":
            return ""
        try:
            L, T = v.rect[0] + mm[0], v.rect[1] + mm[1]
            R, B = L + mm[2], T + mm[3]
            x, y = self.root.winfo_rootx(), self.root.winfo_rooty()
            r, b = x + self.root.winfo_width(), y + self.root.winfo_height()
        except Exception:
            return ""
        if x < R and r > L and y < B and b > T:
            return "⚠ 本工具視窗蓋住了小地圖，座標會不準，請把工具移開"
        return ""

    def draw_minimap(self):
        with self.vision.lock:
            img = None if self.vision.minimap is None else self.vision.minimap.copy()
            p = self.vision.pos
            reds = list(self.vision.red_dots)
        self.canvas.delete("all")
        cw = max(self.canvas.winfo_width(), 100)
        if img is None:
            msg = "尚未框選小地圖（到「首次設定」框選）" if not self.cfg.get("minimap") else "等待遊戲畫面…"
            if self.canvas.winfo_height() > px(80):
                self.canvas.config(height=px(60))
            self.canvas.create_text(cw // 2, px(30), text=msg, fill="#9ca3af", font=(UI_FONT, 10))
            self._minimap_view = None
            return
        h, w = img.shape[:2]
        max_h = max(px(70), min(px(130), int(self.root.winfo_height() * 0.16)))   # 視窗矮時小地圖跟著縮
        scale = min(cw / w, max_h / h)
        disp = cv2.resize(img, (max(1, int(w * scale)), max(1, int(h * scale))), interpolation=cv2.INTER_NEAREST)
        self.canvas.config(height=disp.shape[0])
        self._tkimg = ImageTk.PhotoImage(Image.fromarray(cv2.cvtColor(disp, cv2.COLOR_BGR2RGB)))
        ox = (cw - disp.shape[1]) // 2
        self._minimap_view = (ox, scale, w, h)
        self.canvas.create_image(ox, 0, anchor="nw", image=self._tkimg)
        mode = self.cfg.get("mode")
        if mode in ("random", "combat", "buff", "anchor"):
            for i, t in enumerate(self.cfg["patrol"]):
                x, y = ox + t["x"] * scale, t["y"] * scale
                if t["type"] == "drop":
                    bottom = t.get("lands_y", t["y"] + 12) * scale
                    self.canvas.create_line(x, y, x, bottom, fill="#e040fb", width=2, arrow="last", dash=(4, 2))
                    continue
                if t["type"] == "jump":
                    end = (t.get("macro") or {}).get("end")
                    if end:
                        self.canvas.create_line(x, y, ox + end[0] * scale, end[1] * scale, fill="#e040fb",
                                                width=2, arrow="last")
                    continue
                if t["type"] == "rope":
                    top = t.get("lands_y", t["y"] - 15) * scale
                    self.canvas.create_line(x, y, x, top, fill="#ff9800", width=2)
                    if t.get("top"):
                        tx_, ty_ = ox + t["top"][0] * scale, t["top"][1] * scale
                        self.canvas.create_line(x, top, tx_, ty_, fill="#69f0ae", dash=(3, 2))
                        self.canvas.create_oval(tx_ - 4, ty_ - 4, tx_ + 4, ty_ + 4, outline="#69f0ae", width=2)
                        for d in t.get("chain") or []:
                            dx_, dy_ = ox + d["x"] * scale, d["y"] * scale
                            self.canvas.create_line(dx_, dy_, dx_, d.get("lands_y", d["y"] + 12) * scale,
                                                    fill="#e040fb", width=2, arrow="last", dash=(4, 2))
                elif mode != "anchor":
                    self.canvas.create_oval(x - 4, y - 4, x + 4, y + 4, outline="#4caf50", width=2)
                    self.canvas.create_text(x + 7, y - 7, text=str(i + 1), fill="white", font=("Arial", 8))
        if mode == "route":
            for s in self.cfg["route"]:
                if s["type"] in ("goto", "rope"):
                    x = ox + s["x"] * scale
                    color = "#ff9800" if s["type"] == "rope" else "#4caf50"
                    self.canvas.create_line(x, 0, x, disp.shape[0], fill=color, dash=(3, 2))
        if mode == "anchor":
            for i, (px_, py_) in enumerate(self.bot.anchor_points()):
                ax, ay = ox + px_ * scale, py_ * scale
                cur = i == self.bot.anchor_idx
                self.canvas.create_rectangle(ax - 6, ay - 6, ax + 6, ay + 6,
                                             outline="#00e5ff" if cur else "#4dd0e1", width=3 if cur else 1)
                self.canvas.create_text(ax + 9, ay - 9, text=str(i + 1), fill="#00e5ff", font=("Arial", 8))
        if mode == "buff":
            recorded = self.cfg.get("map_macro") or {}
            path = recorded.get("path") or []
            pts = [(ox + int(row[1]) * scale, int(row[2]) * scale)
                   for row in path if isinstance(row, (list, tuple)) and len(row) >= 3
                   and 0 <= int(row[1]) < w and 0 <= int(row[2]) < h]
            if len(pts) >= 2:
                self.canvas.create_line(*[v for pt in pts for v in pt], fill="#00e5ff", width=2)
                for px_, py_, color in ((pts[0][0], pts[0][1], "#69f0ae"), (pts[-1][0], pts[-1][1], "#ff80ab")):
                    self.canvas.create_oval(px_ - 4, py_ - 4, px_ + 4, py_ + 4, outline=color, width=2)
            for rope in recorded.get("ropes") or []:
                x, bottom, top = int(rope.get("x", -1)), int(rope.get("bottom_y", -1)), int(rope.get("top_y", -1))
                if 0 <= x < w and 0 <= top < h and 0 <= bottom < h:
                    self.canvas.create_line(ox + x * scale, top * scale, ox + x * scale, bottom * scale,
                                            fill="#ff9800", width=3)
        for cx_, cy_, _a in list(self.vision.tracker.candidates):
            if p and (cx_, cy_) == tuple(p):
                continue
            x, y = ox + cx_ * scale, cy_ * scale
            self.canvas.create_oval(x - 5, y - 5, x + 5, y + 5, outline="#9ca3af", width=1, dash=(2, 2))
        for rx, ry in reds:
            x, y = ox + rx * scale, ry * scale
            self.canvas.create_oval(x - 7, y - 7, x + 7, y + 7, outline="#ff1744", width=2)
        if p:
            x, y = ox + p[0] * scale, p[1] * scale
            self.canvas.create_line(x - 8, y, x + 8, y, fill="yellow", width=2)
            self.canvas.create_line(x, y - 8, x, y + 8, fill="yellow", width=2)

    def on_minimap_motion(self, event):
        """主控台小地圖上移動游標時，即時顯示對應的小地圖座標。"""
        view = self._minimap_view
        if not view:
            return
        ox, scale, width, height = view
        x, y = int((event.x - ox) / scale), int(event.y / scale)
        if 0 <= x < width and 0 <= y < height:
            self.lbl_hover.config(text=f"游標座標  X {x}   Y {y}")
        else:
            self.lbl_hover.config(text="游標座標 --")


    # ---------------- 狀態 ----------------
    def ui(self, fn):
        """可從任何執行緒呼叫：把介面操作交給主執行緒"""
        self._ui_queue.put(fn)

    def _drain_ui(self):
        try:
            while True:
                fn = self._ui_queue.get_nowait()
                try:
                    fn()
                except Exception as e:
                    log_exception("介面更新錯誤", e)
        except queue.Empty:
            pass
        if self.alive_ui:
            self.root.after(50, self._drain_ui)

    # ---------------- 技能 ----------------
    def save_attack(self):
        try:
            self.cfg["attack"]["interval"] = float(self.var_atk_int.get())
        except ValueError:
            pass
        self.cfg["attack"]["enabled"] = self.var_atk.get()
        save_config(self.cfg)

    def reload_skills(self):
        g = self.skill_grid
        for w in g.winfo_children():
            w.destroy()
        for c, t in enumerate(("啟用", "名稱", "按鍵", "每隔(秒)", "施放後等待", "")):
            ttk.Label(g, text=t, style="Hint.TLabel").grid(row=0, column=c, sticky="w", padx=2)
        g.columnconfigure(1, weight=1)
        self.skill_rows = []
        num = lambda v: (f"{float(v):g}" if isinstance(v, (int, float)) else str(v))
        for i, sk in enumerate(self.cfg["skills"]):
            r = i + 1
            on = tk.BooleanVar(value=bool(sk.get("enabled")))
            name = tk.StringVar(value=str(sk.get("name", "")))
            key = tk.StringVar(value=str(sk.get("key", "")))
            itv = tk.StringVar(value=num(sk.get("interval", 60)))
            dly = tk.StringVar(value=num(sk.get("delay", 0.6)))
            save = (lambda i=i: self.save_skill_row(i))
            ttk.Checkbutton(g, variable=on, command=save).grid(row=r, column=0, padx=(6, 2))
            entries = []
            e = ttk.Entry(g, textvariable=name, width=9)
            e.grid(row=r, column=1, sticky="we", padx=2, pady=1)
            entries.append(e)
            make_choice(g, key, KEY_SPEC, width=7, on_change=save).grid(row=r, column=2, padx=2, pady=1)
            for col, var in ((3, itv), (4, dly)):
                e = ttk.Entry(g, textvariable=var, width=6)
                e.grid(row=r, column=col, padx=2, pady=1)
                entries.append(e)
            for e in entries:
                e.bind("<FocusOut>", lambda _e, sv=save: sv())
                e.bind("<Return>", lambda _e, sv=save: sv())
            ttk.Button(g, text="✕", width=3, command=lambda i=i: self.del_skill(i)).grid(row=r, column=5, padx=(2, 0))
            self.skill_rows.append((on, name, key, itv, dly))
        if not self.cfg["skills"]:
            ttk.Label(g, text="尚未新增技能", style="Hint.TLabel").grid(row=1, column=0, columnspan=6, sticky="w")

    def save_buff_wait(self):
        try:
            v = float(self.var_buff_wait.get())
            if not 0 <= v <= 30:
                raise ValueError
        except ValueError:
            self.notify("放完 Buff 後等待請填 0～30 秒", error=True)
            return
        if v != self.cfg.get("buff_start_wait"):
            self.cfg["buff_start_wait"] = v
            save_config(self.cfg)

    def save_skill_row(self, i):
        if i >= len(self.cfg["skills"]) or i >= len(self.skill_rows):
            return
        on, name, key, itv, dly = self.skill_rows[i]
        sk = self.cfg["skills"][i]
        try:
            interval, delay = float(itv.get()), float(dly.get())
            if interval <= 0 or delay < 0:
                raise ValueError
        except ValueError:
            self.notify(f"技能「{name.get()}」的秒數要填正數", error=True)
            return
        k = key.get().strip().lower()
        if k not in SCANCODES:
            self.notify(f"不支援的按鍵：{k}", error=True)
            return
        new = dict(sk, enabled=on.get(), name=name.get().strip() or f"技能{i + 1}", key=k,
                   interval=interval, delay=delay)
        if new != sk:
            if new["enabled"] != sk.get("enabled"):
                log(f"技能「{new['name']}」{'啟用' if new['enabled'] else '停用'}")
            self.cfg["skills"][i] = new
            save_config(self.cfg)

    def add_skill(self):
        n = len(self.cfg["skills"]) + 1
        self.cfg["skills"].append({"name": f"技能{n}", "key": "q", "interval": 60.0, "enabled": True, "delay": 0.6})
        save_config(self.cfg)
        self.reload_skills()
        self.notify(f"已新增技能{n}：請選擇按鍵並設定秒數。")

    def del_skill(self, i):
        if 0 <= i < len(self.cfg["skills"]):
            name = self.cfg["skills"][i].get("name", "")
            del self.cfg["skills"][i]
            self.bot.skill_last = {}
            save_config(self.cfg)
            self.reload_skills()
            self.notify(f"已刪除技能：{name}")

    def sel_index(self, tv):
        sel = tv.selection()
        return int(sel[0]) if sel else None

    # ---------------- 定點掛機 ----------------
    def update_anchor_label(self):
        pts = self.cfg["anchor"].get("points") or []
        self.tv_anchor.delete(*self.tv_anchor.get_children())
        for i, (x, y) in enumerate(pts):
            self.tv_anchor.insert("", "end", iid=str(i), values=(i + 1, x, y))
        self.lbl_anchor.config(text="尚未記錄定點" if not pts else
                               f"共 {len(pts)} 個定點" + ("（只有 1 個點不會換點）" if len(pts) == 1 else ""))

    def highlight_anchor(self, i):
        def f():
            if self.tv_anchor.exists(str(i)):
                self.tv_anchor.selection_set(str(i))
        self.ui(f)

    def record_anchor(self):
        p = self.vision.get_pos()
        if not p:
            self.notify("目前偵測不到角色座標，請先框選小地圖並確認取色。", error=True)
            return
        self.cfg["anchor"].setdefault("points", []).append([p[0], p[1]])
        self.cfg["anchor"]["x"] = self.cfg["anchor"]["y"] = None
        save_config(self.cfg)
        self.update_anchor_label()

    def del_anchor(self):
        idx = self.sel_index(self.tv_anchor)
        if idx is not None:
            del self.cfg["anchor"]["points"][idx]
            self.bot.anchor_idx = 0
            self.bot.anchor_dwell = None
            save_config(self.cfg)
            self.update_anchor_label()

    def clear_anchor(self):
        if messagebox.askyesno("清空", "確定清空所有定點？"):
            self.cfg["anchor"]["points"] = []
            self.cfg["anchor"]["x"] = self.cfg["anchor"]["y"] = None
            self.bot.anchor_idx = 0
            self.bot.anchor_dwell = None
            save_config(self.cfg)
            self.update_anchor_label()

    def save_anchor(self):
        a = self.cfg["anchor"]
        try:
            for k, v in self.anchor_vars.items():
                val = v.get().strip()
                if k == "hold_key":
                    if val.lower() not in SCANCODES:
                        raise ValueError(f"不支援的按鍵：{val}")
                    a[k] = val.lower()
                elif k == "tol_x":
                    a[k] = int(float(val))
                else:
                    a[k] = float(val)
        except ValueError as e:
            self.notify(str(e), error=True)
            return
        self.bot.anchor_dwell = None
        a["repeat"] = self.var_anchor_rep.get()
        a["random_order"] = self.var_anchor_rand.get()
        a["release_for_buff"] = self.var_anchor_buff.get()
        save_config(self.cfg)

    # ---------------- 路線 ----------------
    def reload_route(self):
        self.tv_route.delete(*self.tv_route.get_children())
        for i, s in enumerate(self.cfg["route"]):
            self.tv_route.insert("", "end", iid=str(i), values=(i + 1, describe_step(s)))

    def highlight_step(self, i):
        def f():
            if self.tv_route.exists(str(i)):
                self.tv_route.selection_set(str(i))
                self.tv_route.see(str(i))
        self.ui(f)

    def insert_step(self, s):
        idx = self.sel_index(self.tv_route)
        pos = len(self.cfg["route"]) if idx is None else idx + 1
        self.cfg["route"].insert(pos, s)
        save_config(self.cfg)
        self.reload_route()
        self.tv_route.selection_set(str(pos))

    def record(self, typ):
        p = self.vision.get_pos()
        if not p:
            self.notify("目前偵測不到角色座標，請先框選小地圖並確認取色。", error=True)
            return
        self.insert_step({"type": typ, "x": p[0]})

    def set_rope_top(self):
        idx = self.sel_index(self.tv_route)
        p = self.vision.get_pos()
        if idx is None or self.cfg["route"][idx]["type"] != "rope":
            self.notify("請先選取一個「爬繩」步驟，再把角色爬到想停的高度後按此鈕。\n"
                                       "（不設定也可以：會一直爬到繩頂不再上升為止）")
            return
        if p:
            self.cfg["route"][idx]["top_y"] = p[1]
            save_config(self.cfg)
            self.reload_route()

    def step_fields(self, s):
        t = s["type"]
        yn = lambda v: 1 if v else 0
        if t == "macro":
            return [("align", "先走到錄製起點", yn(s.get("align", True)), YESNO_SPEC)]
        if t in ("goto",):
            return [("x", "X 座標", s.get("x", 0))]
        if t == "rope":
            return [("x", "繩子 X 座標", s.get("x", 0)),
                    ("top_y", "爬到 Y ≤（空白＝爬到頂）", "" if s.get("top_y") is None else s["top_y"]),
                    ("jump_to_grab", "先跳躍抓繩", yn(s.get("jump_to_grab")), YESNO_SPEC)]
        if t == "jump":
            return [("dir", "方向", s.get("dir", ""), choice_spec(["left", "right"], {"left": "← 往左", "right": "→ 往右"},
                                                                 empty="（原地跳）")),
                    ("times", "次數", s.get("times", 1)),
                    ("double", "二段跳", yn(s.get("double")), YESNO_SPEC),
                    ("after", "每次跳後等待(秒)", s.get("after", 0.5))]
        if t == "downjump":
            return [("after", "下跳後等待(秒)", s.get("after", 0.8))]
        if t == "attack":
            return [("times", "攻擊次數", s.get("times", 5)), ("interval", "間隔(秒)", s.get("interval", 0.6)),
                    ("dir", "先轉向", s.get("dir", ""), DIR_SPEC)]
        if t == "key":
            return [("key", "按鍵", s.get("key", "z"), KEY_SPEC), ("hold", "按住(秒)", s.get("hold", 0.05)),
                    ("after", "按後等待(秒)", s.get("after", 0.3))]
        if t == "wait":
            return [("sec", "秒數", s.get("sec", 3))]
        return []

    def parse_step(self, t, r):
        s = {"type": t}
        num = lambda v, f=float: f(v) if str(v).strip() != "" else None
        for k, v in r.items():
            if k in ("x", "times"):
                s[k] = int(float(v))
            elif k == "top_y":
                val = num(v, lambda z: int(float(z)))
                if val is not None:
                    s[k] = val
            elif k in ("after", "interval", "hold", "sec"):
                s[k] = float(v)
            elif k in ("double", "jump_to_grab", "align"):
                s[k] = str(v).strip() in ("1", "true", "是", "y")
            elif k == "dir":
                s[k] = str(v).strip().lower()
            elif k == "key":
                if str(v).lower() not in SCANCODES:
                    raise ValueError(f"不支援的按鍵：{v}")
                s[k] = str(v).lower()
        return s

    def add_step(self, t):
        if t == "downjump":
            self.insert_step({"type": t, "after": 0.8})
            return
        d = FormDialog(self.root, STEP_TYPES[t], self.step_fields({"type": t}))
        if d.result:
            try:
                self.insert_step(self.parse_step(t, d.result))
            except Exception as e:
                self.notify(str(e), error=True)

    def edit_step(self):
        idx = self.sel_index(self.tv_route)
        if idx is None:
            return
        s = self.cfg["route"][idx]
        d = FormDialog(self.root, STEP_TYPES[s["type"]], self.step_fields(s))
        if d.result:
            try:
                new = self.parse_step(s["type"], d.result)
                for k in ("events", "start", "end", "duration", "macro"):   # 保留錄製資料
                    if k in s:
                        new[k] = s[k]
                self.cfg["route"][idx] = new
                save_config(self.cfg)
                self.reload_route()
            except Exception as e:
                self.notify(str(e), error=True)

    def move_step(self, delta):
        idx = self.sel_index(self.tv_route)
        r = self.cfg["route"]
        if idx is None or not (0 <= idx + delta < len(r)):
            return
        r[idx], r[idx + delta] = r[idx + delta], r[idx]
        save_config(self.cfg)
        self.reload_route()
        self.tv_route.selection_set(str(idx + delta))

    def del_step(self):
        idx = self.sel_index(self.tv_route)
        if idx is not None:
            del self.cfg["route"][idx]
            save_config(self.cfg)
            self.reload_route()

    def clear_route(self):
        if messagebox.askyesno("清空", "確定清空整條路線？"):
            self.cfg["route"] = []
            self.bot.step_idx = 0
            save_config(self.cfg)
            self.reload_route()

    def start_from_sel(self):
        idx = self.sel_index(self.tv_route)
        self.bot.step_idx = idx or 0

    # ---------------- 隨機巡邏 ----------------
    def save_patrol_opt(self):
        try:
            po = self.cfg["patrol_opt"]
            for k, v in self.patrol_vars.items():
                po[k] = float(v.get()) if k.startswith("stay") else int(float(v.get()))
            po["rope_as_target"] = self.var_rope_target.get()
            save_config(self.cfg)
        except ValueError as e:
            self.notify(f"數值格式錯誤：{e}", error=True)

    def reload_patrol(self):
        self.tv_patrol.delete(*self.tv_patrol.get_children())
        for i, t in enumerate(self.cfg["patrol"]):
            if t["type"] == "rope":
                climb = ("● 錄製動作（" + macro_summary(t["macro"]) + "）") if t.get("macro") else \
                    "⚠ 之前的錄製沒爬上去，請重錄" if t.get("macro_invalid") else \
                    ("先跳抓繩" if t.get("jump_to_grab") else "直接上爬")
                info = (f"{climb}；落在 Y={t['lands_y']}" if t.get("lands_y") is not None
                        else f"{climb}；尚未爬過（第一次會自動記住）")
                info = ("◎精準 " if t.get("screen_anchor") else "△未校準 ") + info
                if t.get("top"):
                    chain = t.get("chain") or []
                    drops = "".join(f" → 下跳 ({d['x']},{d['y']})" for d in chain)
                    info = f"繩組｜繩上 ({t['top'][0]},{t['top'][1]}){drops}；" + info
            elif t["type"] == "drop":
                info = (f"下跳後落在 Y={t['lands_y']}" if t.get("lands_y") is not None
                        else "尚未跳過（第一次需要往下時會在這裡跳，並記住落點）")
            elif t["type"] == "jump":
                end = (t.get("macro") or {}).get("end") or ["?", "?"]
                info = ("◎精準 " if t.get("screen_anchor") else "△未校準 ") + \
                    f"跳到 ({end[0]},{end[1]})；● 錄製動作（{macro_summary(t.get('macro'))}）"
            else:
                info = "停留（BUFF 機有繩組時不使用）" if self.cfg.get("mode") == "buff" else "隨機攻擊、停留"
            kind = {"rope": "繩組" if t.get("top") else "繩子", "jump": "跳台", "drop": "下跳點"}.get(t["type"], "巡邏點")
            self.tv_patrol.insert("", "end", iid=str(i), values=(i + 1, kind, t["x"], t["y"], info))

    def highlight_patrol(self, i):
        def f():
            if self.tv_patrol.exists(str(i)):
                self.tv_patrol.selection_set(str(i))
                self.tv_patrol.see(str(i))
        self.ui(f)

    def save_rope_anchor(self, rope, img=None):
        """以目前（或指定）畫面為繩子截取精準對位地標。回傳說明文字"""
        if self.scanner.tag_template is None:
            return "（沒有框選名牌，無法精準對位）"
        if img is None:
            try:
                img = self.vision.grab_client()
            except Exception:
                img = None
        if img is None:
            return "（擷取不到遊戲畫面）"
        try:   # 角色正站在抓得到繩子的位置：記下這根繩子的 YOLO 偏移（有模型時；呼叫端會存檔）
            self.bot.learn_rope_dx(rope, self.bot.yolo_rope_delta(img), save=False)
        except Exception as e:
            log(f"記錄 YOLO 繩子偏移失敗：{e}", "warn")
        crop, meta = make_rope_anchor(img, self.scanner.tag_template)
        if crop is None:
            return f"（無法精準對位：{meta}）"
        old = (rope.get("screen_anchor") or {}).get("file")
        path = new_template_path(ROPE_DIR, "rope")
        imwrite_unicode(path, cv2.cvtColor(crop, cv2.COLOR_GRAY2BGR))
        meta["file"] = os.path.basename(path)
        rope["screen_anchor"] = meta
        if old and old != meta["file"]:
            try:
                os.remove(os.path.join(ROPE_DIR, old))
            except OSError:
                pass
        self.bot.__dict__.pop("_anchor_cache", None)
        return "，已記下精準位置"

    def record_patrol(self, typ):
        p = self.vision.get_pos()
        if not p:
            self.notify("目前偵測不到角色座標，請先框選小地圖並確認取色。", error=True)
            return
        item = {"type": typ, "x": p[0], "y": p[1]}
        extra = ""
        if typ == "rope":
            extra = self.save_rope_anchor(item)
        self.cfg["patrol"].append(item)
        save_config(self.cfg)
        self.reload_patrol()
        if typ == "rope":
            self.notify(f"已記錄繩子 #{len(self.cfg['patrol'])}（X={p[0]} Y={p[1]}）{extra}",
                        error="無法" in extra or "沒有" in extra)
        elif typ == "drop":
            self.notify(f"已記錄下跳點 #{len(self.cfg['patrol'])}（X={p[0]} Y={p[1]}）；第一次用到時會記住落在哪一層。")

    def record_drop(self):
        """下跳點：清單選了繩組（沒選時看最後記錄的是不是繩組）就依序接在那一組後面；否則是獨立的下跳點"""
        p = self.vision.get_pos()
        if not p:
            self.notify("目前偵測不到角色座標，請先框選小地圖並確認取色。", error=True)
            return
        pts = self.cfg["patrol"]
        idx = self.sel_index(self.tv_patrol)
        if idx is None and pts and pts[-1].get("type") == "rope" and pts[-1].get("top"):
            idx = len(pts) - 1
        if idx is not None and pts[idx].get("type") == "rope" and pts[idx].get("top"):
            r = pts[idx]
            chain = r.setdefault("chain", [])
            chain.append({"x": p[0], "y": p[1]})
            save_config(self.cfg)
            self.reload_patrol()
            self.tv_patrol.selection_set(str(idx))
            self.notify(f"繩組 #{idx + 1}：第 {len(chain)} 個下跳點 ({p[0]},{p[1]})。之後跳下去到下一層，"
                        "可以再走到下一個要跳的位置按「＋ 下跳點」。")
            return
        self.record_patrol("drop")

    def record_rope_top(self):
        """記錄「繩上定點」，和選取的（或最後記錄的）繩子配成一組"""
        p = self.vision.get_pos()
        if not p:
            self.notify("目前偵測不到角色座標，請先框選小地圖並確認取色。", error=True)
            return
        idx = self.sel_index(self.tv_patrol)
        ropes = [i for i, t in enumerate(self.cfg["patrol"]) if t.get("type") == "rope"]
        if idx is None or self.cfg["patrol"][idx].get("type") != "rope":
            if not ropes:
                self.notify("請先站在繩子下方按「＋ 繩下定點」，再爬上去按「＋ 繩上定點」。", error=True)
                return
            idx = ropes[-1]
        r = self.cfg["patrol"][idx]
        tol = int(self.cfg["patrol_opt"]["plat_tol"])
        if p[1] >= r["y"] - tol:
            self.notify(f"繩上定點要在繩子上面那一層（繩下 Y={r['y']}，目前 Y={p[1]}）；請先爬上去再按。", error=True)
            return
        r["top"] = [p[0], p[1]]
        r.pop("chain", None)                  # 重設繩上定點時，後面的下跳點一起清掉重記
        if r.get("lands_y") is None:
            r["lands_y"] = p[1]
        save_config(self.cfg)
        self.reload_patrol()
        self.tv_patrol.selection_set(str(idx))
        self.notify(f"繩組 #{idx + 1}：繩下 ({r['x']},{r['y']}) ↔ 繩上 ({p[0]},{p[1]})")

    def calibrate_rope(self):
        """角色站在「按↑就抓得到繩子」的位置時，重新記下所選繩子的精準位置"""
        idx = self.sel_index(self.tv_patrol)
        if idx is None or self.cfg["patrol"][idx].get("type") not in ("rope", "jump"):
            self.notify("請先選取一條繩子或跳台，並讓角色站在起跳／按↑就抓得到的位置。", error=True)
            return
        r = self.cfg["patrol"][idx]
        p = self.vision.get_pos()
        if p and abs(p[1] - r["y"]) > int(self.cfg["patrol_opt"]["plat_tol"]):
            self.notify(f"角色不在這條繩子那一層（繩子 Y={r['y']}，角色 Y={p[1]}）。", error=True)
            return
        if p:
            r["x"] = p[0]
            if r.get("macro") and r["macro"].get("start"):   # 錄製動作的起點也一起更新，重播前才會對到這裡
                r["macro"]["start"] = [p[0], r["macro"]["start"][1]]
        msg = self.save_rope_anchor(r)
        save_config(self.cfg)
        self.reload_patrol()
        self.notify(f"繩子 #{idx + 1}{msg}", error="無法" in msg or "沒有" in msg or "擷取" in msg)

    def edit_patrol_rope(self):
        idx = self.sel_index(self.tv_patrol)
        if idx is None or self.cfg["patrol"][idx].get("type") != "rope":
            self.notify("請先選取一條繩子，再按「繩子設定」。", error=True)
            return
        rope = self.cfg["patrol"][idx]
        d = FormDialog(self.root, "繩子設定", [
            ("jump_to_grab", "先跳躍抓繩", 1 if rope.get("jump_to_grab") else 0, YESNO_SPEC)])
        if not d.result:
            return
        rope["jump_to_grab"] = str(d.result["jump_to_grab"]).strip().lower() in ("1", "true", "是", "y")
        save_config(self.cfg)
        self.reload_patrol()

    def del_patrol(self):
        idx = self.sel_index(self.tv_patrol)
        if idx is not None:
            del self.cfg["patrol"][idx]
            self.bot.last_target = None
            save_config(self.cfg)
            self.reload_patrol()

    def clear_patrol(self):
        if messagebox.askyesno("清空", "確定清空所有巡邏點？"):
            self.cfg["patrol"] = []
            self.bot.last_target = None
            save_config(self.cfg)
            self.reload_patrol()

    def reset_rope_dx(self):
        n = 0
        for t in self.cfg["patrol"]:
            if t.pop("yolo_dx", None) is not None:
                n += 1
        self.cfg.get("yolo", {}).pop("rope_dx", None)
        save_config(self.cfg)
        self.reload_patrol()
        self.notify(f"已重設 {n} 條繩子的 YOLO 偏移；之後精準對位成功或重新記錄時會再學。")

    def schedule_save(self, delay_ms=1500):
        """背景學到新資料時呼叫：合併 1.5 秒內的多次變更，只存一次檔"""
        if getattr(self, "_save_job", None):
            try:
                self.root.after_cancel(self._save_job)
            except tk.TclError:
                pass

        def go():
            self._save_job = None
            save_config(self.cfg)
        self._save_job = self.root.after(delay_ms, go)

    def reset_lands(self):
        for t in self.cfg["patrol"]:
            t.pop("lands_y", None)
        save_config(self.cfg)
        self.reload_patrol()

    # ---------------- 測謊偵測 ----------------
    def update_tpl_label(self):
        n = len(self.vision.templates)
        self.lbl_tpl.config(text=f"目前範本：{n} 個" + ("（請在測謊出現時按「新增範本」框選測謊視窗中固定不變的部分）" if n == 0 else ""))

    def add_ld_template(self):
        img = self.vision.grab_client() if IS_WIN else None
        if img is None:
            self.notify("找不到遊戲視窗。", error=True)
            return

        def done(rect):
            x, y, w, h = rect
            path = new_template_path(TEMPLATE_DIR, "lie")
            imwrite_unicode(path, img[y:y + h, x:x + w])
            self.vision.templates = load_templates()
            self.update_tpl_label()
            self.notify(f"已儲存範本：{os.path.basename(path)}")

        RectSelector(self.root, img, done,
                     title="框選測謊視窗中「固定不變」的部分（例如標題文字、外框），按 Enter 確認")

    def open_template_dir(self):
        os.makedirs(TEMPLATE_DIR, exist_ok=True)
        if IS_WIN:
            os.startfile(TEMPLATE_DIR)
        self.vision.templates = load_templates()
        self.update_tpl_label()

    def trigger_alarm(self, kind, text, pause=True, beep=True):
        """可從背景執行緒呼叫。kind: "lie" 測謊 / "red" 紅點"""
        if self.alarm_kind == "lie" or self.alarm_kind == kind:
            return
        self.alarm_kind = kind
        if pause:
            self.bot.active.clear()
            self.kb.release_all()
        log(f"警報：{text}", "warn")
        tail = "已自動暫停，請回遊戲自己作答" if kind == "lie" else ("已自動暫停" if pause else "自動仍在執行")
        msg = f"⚠ {text}\n{tail}"
        self.ui(lambda: self._show_alarm(msg))
        if beep:
            threading.Thread(target=self._beep_loop, args=(kind,), daemon=True).start()

    def _show_alarm(self, msg):
        self.lbl_alarm.config(text=msg)
        if not self.alarm_frame.winfo_ismapped():
            self.alarm_frame.pack(fill="x", pady=(6, 0))
        self.root.deiconify()
        self.root.lift()
        if IS_WIN:
            try:
                user32.FlashWindow(self.vision.hwnd, True)
            except Exception:
                pass

    def _beep_loop(self, kind):
        import winsound
        end = time.time() + 120  # 最多響 2 分鐘
        while self.alarm_kind == kind and time.time() < end:
            if kind == "lie":      # 測謊：高低交替
                winsound.Beep(1800, 250); time.sleep(0.15)
                winsound.Beep(1200, 250); time.sleep(0.6)
            else:                  # 紅點：三短音，間隔較長
                for _ in range(3):
                    winsound.Beep(2200, 90); time.sleep(0.08)
                time.sleep(1.5)

    def red_cleared(self):
        """紅點消失 3 秒：若目前是紅點警報且沒暫停，自動收起提示"""
        if self.alarm_kind == "red" and not self.cfg["red_dot"].get("pause", True):
            self.ui(self.dismiss_alarm)

    def dismiss_alarm(self):
        if self.alarm_kind:
            log("警報已解除")
        if self.alarm_kind == "lie":
            self.vision.last_ld_check = time.time() + 5  # 給測謊視窗 5 秒時間關閉
        self.alarm_kind = None
        self.alarm_frame.pack_forget()

    # ---------------- 警報頁 ----------------
    def save_settings(self):
        """先檢查全部欄位，全部正確才一起寫入，避免只存一半"""
        v = self.set_vars
        try:
            keys = {k: v["key_" + k].get().strip().lower() for k in self.cfg["keys"]}
            bad = [x for x in keys.values() if x not in SCANCODES]
            if bad:
                raise ValueError(f"不支援的按鍵：{', '.join(bad)}")
            hkt, hks = v["hk_toggle"].get().strip().lower(), v["hk_stop"].get().strip().lower()
            hkr = v["hk_record"].get().strip().lower()
            if any(k not in VK_FKEYS for k in (hkt, hks, hkr)) or len({hkt, hks, hkr}) < 3:
                raise ValueError("熱鍵必須是 F1～F12，且開始、停止、錄製結束三個要不同")
            new = {
                "keys": keys,
                "hotkeys": {"toggle": hkt, "stop": hks, "record": hkr},
                "window_title": v["window_title"].get().strip() or "MapleStory",
                "goto_tolerance": int(v["goto_tolerance"].get()),
                "rope_tolerance": int(v["rope_tolerance"].get()),
                "min_dot_area": int(v["min_dot_area"].get()),
                "player_hsv_low": [int(x) for x in v["hsv_low"].get().split(",")],
                "player_hsv_high": [int(x) for x in v["hsv_high"].get().split(",")],
            }
            if len(new["player_hsv_low"]) != 3 or len(new["player_hsv_high"]) != 3:
                raise ValueError("HSV 要填三個數字，用逗號分隔")
        except ValueError as e:
            msg = str(e)
            if "invalid literal" in msg:
                msg = "數值格式錯誤，請填數字"
            self.notify(msg, error=True)
            return
        if new["window_title"] != self.cfg["window_title"]:
            self.vision.hwnd = None
        self.cfg.update(new)
        self.cfg["only_when_focused"] = self.var_focus.get()
        self.cfg["topmost"] = False              # 置頂只是暫時的，不寫進設定
        self.cfg["minimize_on_start"] = self.var_min_start.get()
        self.cfg["key_repeat"] = self.var_key_repeat.get()
        self.kb.repeat = self.cfg["key_repeat"]
        self.cfg["restore_on_pause"] = self.var_restore.get()
        if hasattr(self, "var_prehold"):
            self.cfg["rope_prehold"] = self.var_prehold.get()
            try:
                d = int(self.var_prehold_dist.get())
                if not 1 <= d <= 20:
                    raise ValueError
                self.cfg["rope_prehold_dist"] = d
            except ValueError:
                self.notify("先按住上的距離請填 1～20 格", error=True)
        self.root.attributes("-topmost", bool(self.var_top.get()))
        save_config(self.cfg)

    def test_jump(self):
        def go():
            time.sleep(3)
            try:
                self.kb.tap(self.cfg["keys"]["jump"])
            except InputSendError as e:
                msg = str(e)
                self.ui(lambda m=msg: self.notify(m, error=True))
                return
            self.cfg["setup_keys_ok"] = True
            save_config(self.cfg)
            self.ui(lambda: self.notify("按鍵已送出；請確認角色是否有跳一下。"))
        threading.Thread(target=go, daemon=True).start()
        self.notify("請在 3 秒內切換到遊戲視窗，角色應該會跳一下。")

    # ---------------- 菁英怪 ----------------
    def save_elite(self):
        el = self.cfg["elite"]
        el["enabled"], el["beep"] = self.var_el.get(), self.var_el_beep.get()
        el["hold_attack"] = self.var_el_hold.get()
        for k, v in self.elite_vars.items():
            val = v.get().strip()
            try:
                if k == "attack_key":
                    if val and val.lower() not in SCANCODES:
                        raise ValueError(f"不支援的按鍵：{val}")
                    el[k] = val.lower()
                elif k == "max_sec":
                    el[k] = int(float(val))
                else:
                    el[k] = float(val)
            except ValueError as e:
                self.notify(f"{k}：{e}", error=True)
                return
        save_config(self.cfg)

    def reload_elite(self):
        self.tv_elite.delete(*self.tv_elite.get_children())
        for i, sk in enumerate(self.cfg["elite"]["skills"]):
            self.tv_elite.insert("", "end", iid=str(i), values=(
                "✔" if sk.get("enabled", True) else "", sk["name"], sk["key"], sk["cooldown"], sk.get("delay", 0.6)))
        n = len(self.vision.elite_templates)
        self.lbl_el.config(text=f"目前範本：{n} 個" + ("（尚未建立，菁英偵測不會作用）" if n == 0 else ""))

    def edit_elite_skill(self, new=False):
        idx = None if new else self.sel_index(self.tv_elite)
        if not new and idx is None:
            return
        sk = {"name": "大招", "key": "r", "cooldown": 30, "delay": 0.8, "enabled": True} if new \
            else dict(self.cfg["elite"]["skills"][idx])
        d = FormDialog(self.root, "菁英技能", [
            ("name", "名稱", sk["name"]), ("key", "按鍵", sk["key"], KEY_SPEC),
            ("cooldown", "冷卻(秒)", sk["cooldown"]), ("delay", "施放後等待(秒)", sk.get("delay", 0.6))])
        if not d.result:
            return
        r = d.result
        if r["key"].lower() not in SCANCODES:
            self.notify(f"不支援的按鍵：{r['key']}", error=True)
            return
        try:
            sk.update(name=r["name"], key=r["key"].lower(), cooldown=float(r["cooldown"]), delay=float(r["delay"]))
        except ValueError as e:
            self.notify(str(e), error=True)
            return
        if new:
            self.cfg["elite"]["skills"].append(sk)
        else:
            self.cfg["elite"]["skills"][idx] = sk
        save_config(self.cfg)
        self.reload_elite()

    def toggle_elite_skill(self):
        idx = self.sel_index(self.tv_elite)
        if idx is not None:
            sk = self.cfg["elite"]["skills"][idx]
            sk["enabled"] = not sk.get("enabled", True)
            save_config(self.cfg)
            self.reload_elite()

    def del_elite_skill(self):
        idx = self.sel_index(self.tv_elite)
        if idx is not None:
            del self.cfg["elite"]["skills"][idx]
            save_config(self.cfg)
            self.reload_elite()

    def add_elite_template(self):
        img = self.vision.grab_client() if IS_WIN else None
        if img is None:
            self.notify("找不到遊戲視窗。", error=True)
            return

        def done(rect):
            x, y, w, h = rect
            path = new_template_path(ELITE_DIR, "elite")
            imwrite_unicode(path, img[y:y + h, x:x + w])
            self.vision.elite_templates = load_templates(ELITE_DIR)
            self.reload_elite()
            self.notify(f"已儲存菁英範本：{os.path.basename(path)}")

        RectSelector(self.root, img, done,
                     title="框選菁英怪出現時「固定不變」的特徵（例如菁英血條的圖示/邊框），按 Enter 確認")

    def open_elite_dir(self):
        os.makedirs(ELITE_DIR, exist_ok=True)
        if IS_WIN:
            os.startfile(ELITE_DIR)
        self.vision.elite_templates = load_templates(ELITE_DIR)
        self.reload_elite()

    def test_elite(self):
        if not self.bot.active.is_set():
            self.notify("請先按「開始」執行，再按這個測試鈕。", error=True)
            return
        end = time.time() + 10 - float(self.cfg["elite"].get("end_sec", 3))

        def keep():
            while time.time() < end:
                self.vision.elite_seen_at = time.time()
                time.sleep(0.2)
        threading.Thread(target=keep, daemon=True).start()

    # ---------------- 自動戰鬥 ----------------
    def update_combat_label(self):
        if not hasattr(self, "lbl_cb"):
            return
        n = len(self.scanner.mon_templates) // 2
        tag = "✔ 已設定" if self.scanner.tag_template is not None else "✘ 尚未設定"
        auto = "開" if self.cfg["combat"].get("auto_detect", True) else "關"
        self.lbl_cb.config(text=f"角色名牌：{tag}　｜　怪物範本：{n} 張　｜　內部自動偵測：{auto}")

    def save_combat(self, show=False):
        cb = self.cfg["combat"]
        try:
            for (sub, k), v in self.combat_vars.items():
                tgt = cb[sub] if sub else cb
                val = v.get().strip()
                if k == "key":
                    if val and val.lower() not in SCANCODES:
                        raise ValueError(f"不支援的按鍵：{val}")
                    tgt[k] = val.lower()
                elif k in ("range", "min_count", "y_range", "char_offset_y"):
                    tgt[k] = int(float(val))
                else:
                    tgt[k] = float(val)
        except ValueError as e:
            self.notify(str(e), error=True)
            return
        cb["enabled"] = self.var_cb.get()
        cb["auto_detect"] = self.var_cb_auto.get()
        cb["approach"] = self.var_cb_appr.get()
        cb["always_face"] = self.var_cb_face.get()
        cb["fallback_blind"] = self.var_cb_blind.get()
        save_config(self.cfg)

    def set_nametag(self):
        img = self.vision.grab_client() if IS_WIN else None
        if img is None:
            self.notify("找不到遊戲視窗。", error=True)
            return

        def done(rect):
            x, y, w, h = rect
            os.makedirs(TAG_DIR, exist_ok=True)
            imwrite_unicode(TAG_PATH, img[y:y + h, x:x + w])
            self.scanner.reload()
            self.update_combat_label()
            self.update_loot_label()
            self.notify("角色名牌已設定")

        RectSelector(self.root, img, done, title="框選「自己角色腳下的名牌」（只框名牌，不要框到角色本身），按 Enter 確認")

    def add_monster_template(self):
        img = self.vision.grab_client() if IS_WIN else None
        if img is None:
            self.notify("找不到遊戲視窗。", error=True)
            return

        def done(rect):
            x, y, w, h = rect
            path = new_template_path(MON_DIR, "mob")
            imwrite_unicode(path, img[y:y + h, x:x + w])
            self.scanner.reload()
            self.update_combat_label()
            self.notify(f"已新增怪物範本：{os.path.basename(path)}")

        RectSelector(self.root, img, done,
                     title="框選一隻怪物（框緊一點，盡量少框背景），按 Enter 確認；不同動作可多存幾張")

    def open_monster_dir(self):
        os.makedirs(MON_DIR, exist_ok=True)
        if IS_WIN:
            os.startfile(MON_DIR)
        self.scanner.reload()
        self.update_combat_label()

    def preview_combat(self):
        img = self.vision.grab_client() if IS_WIN else None
        if img is None:
            self.notify("找不到遊戲視窗。", error=True)
            return
        cb = self.cfg["combat"]
        t0 = time.time()
        char, mons = analyze_combat(img, cb, self.scanner.mon_templates, self.scanner.tag_template)
        items = analyze_items(img, self.cfg["loot"], cb, self.scanner.item_templates, self.scanner.yolo)
        ms = (time.time() - t0) * 1000
        out = img.copy()
        if char:
            yr = int(cb["y_range"])
            cv2.rectangle(out, (0, char[1] - yr), (out.shape[1] - 1, char[1] + yr), (255, 200, 0), 1)
            for r, col in ((int(cb["single"]["range"]), (0, 255, 0)), (int(cb["aoe"]["range"]), (0, 165, 255))):
                cv2.line(out, (char[0] - r, char[1]), (char[0] + r, char[1]), col, 2)
                for xx in (char[0] - r, char[0] + r):
                    cv2.line(out, (xx, char[1] - 10), (xx, char[1] + 10), col, 2)
            cv2.circle(out, char, 8, (0, 255, 255), 2)
        for x, y, v, name in mons:
            same = char and abs(y - char[1]) <= int(cb["y_range"])
            cv2.circle(out, (x, y), 14, (0, 0, 255) if same else (128, 128, 255), 2)
            cv2.putText(out, f"{v:.2f}", (x - 14, y - 18), cv2.FONT_HERSHEY_SIMPLEX, 0.4, (255, 255, 255), 1)
        for x, y, v, name in items:
            same = char and abs(y - char[1]) <= int(self.cfg["loot"]["y_range"])
            col = (255, 0, 255) if same else (255, 180, 255)
            cv2.rectangle(out, (x - 10, y - 10), (x + 10, y + 10), col, 2)
            cv2.putText(out, f"{v:.2f}", (x - 12, y + 24), cv2.FONT_HERSHEY_SIMPLEX, 0.4, (255, 255, 255), 1)
        win = tk.Toplevel(self.root)
        win.title(f"偵測結果：角色 {'有' if char else '找不到'}，怪物 {len(mons)} 隻，物品 {len(items)} 個（{ms:.0f} ms）"
                  "　黃圈=角色 紅圈=同層怪 紫框=同層物品 淡色=其他層 綠線=單體距離 橘線=範圍")
        win.attributes("-topmost", True)
        sc = min(1.0, (self.root.winfo_screenwidth() - 80) / out.shape[1],
                 (self.root.winfo_screenheight() - 120) / out.shape[0])
        disp = cv2.resize(out, (int(out.shape[1] * sc), int(out.shape[0] * sc)))
        win._img = ImageTk.PhotoImage(Image.fromarray(cv2.cvtColor(disp, cv2.COLOR_BGR2RGB)))
        tk.Label(win, image=win._img).pack()

    # ---------------- BUFF機 ----------------
    def update_loot_label(self):
        tag = "✔ 已設定" if self.scanner.tag_template is not None else "✘ 尚未設定"
        self.lbl_loot.config(text=f"角色名牌：{tag}　｜　物品範本：{len(self.scanner.item_templates)} 張"
                             + ("（沒有範本時只會連點＋掃地）" if not self.scanner.item_templates else ""))

    def save_loot(self):
        lt = self.cfg["loot"]
        try:
            for k, v in self.loot_vars.items():
                val = v.get().strip()
                if k == "key":
                    if val.lower() not in SCANCODES:
                        raise ValueError(f"不支援的按鍵：{val}")
                    lt[k] = val.lower()
                elif k in ("y_range", "range", "pick_radius", "max_tries"):
                    lt[k] = int(float(val))
                else:
                    lt[k] = float(val)
        except ValueError as e:
            self.notify(str(e), error=True)
            return
        lt["auto_tap"] = self.var_loot_tap.get()
        if hasattr(self, "var_loot_on") and lt.get("enabled", True) != self.var_loot_on.get():
            lt["enabled"] = self.var_loot_on.get()
            log("撿物：" + ("開啟" if lt["enabled"] else "關閉（BUFF 機只移動）"))
        save_config(self.cfg)

    def set_nametag_loot(self):
        self.set_nametag()

    def add_item_template(self):
        img = self.vision.grab_client() if IS_WIN else None
        if img is None:
            self.notify("找不到遊戲視窗。", error=True)
            return

        def done(rect):
            x, y, w, h = rect
            path = new_template_path(ITEM_DIR, "item")
            imwrite_unicode(path, img[y:y + h, x:x + w])
            self.scanner.reload()
            self.update_loot_label()
            self.notify(f"已新增物品範本：{os.path.basename(path)}")

        RectSelector(self.root, img, done,
                     title="框選地上的一個物品（例如楓幣、常掉的道具），框緊一點，按 Enter 確認")

    def open_item_dir(self):
        os.makedirs(ITEM_DIR, exist_ok=True)
        if IS_WIN:
            os.startfile(ITEM_DIR)
        self.scanner.reload()
        self.update_loot_label()

    # ---------------- 校正 ----------------
    def calibrate_minimap(self):
        img = self.vision.grab_client() if IS_WIN else None
        if img is None:
            self.notify("找不到遊戲視窗，請確認遊戲已開啟、標題設定正確。", error=True)
            return
        RectSelector(self.root, img, self.on_minimap_selected)

    def on_minimap_selected(self, rect):
        self.cfg["minimap"] = list(rect)
        save_config(self.cfg)

    def pick_color(self):
        with self.vision.lock:
            img = None if self.vision.minimap is None else self.vision.minimap.copy()
        if img is None:
            self.notify("請先框選小地圖。", error=True)
            return
        ColorPicker(self.root, img, self.on_color_picked, with_pos=True)

    def on_color_picked(self, hsv, pos=None, img=None):
        h, s, v = (int(x) for x in hsv)
        self.cfg["player_hsv_low"] = [max(0, h - 8), max(0, s - 70), max(0, v - 70)]
        self.cfg["player_hsv_high"] = [min(179, h + 8), 255, 255]
        self.set_vars["hsv_low"].set(",".join(map(str, self.cfg["player_hsv_low"])))
        self.set_vars["hsv_high"].set(",".join(map(str, self.cfg["player_hsv_high"])))
        msg = "已更新角色點顏色"
        if pos is not None and img is not None:
            cands = player_candidates(img, self.cfg["player_hsv_low"], self.cfg["player_hsv_high"],
                                      self.cfg["min_dot_area"])
            if cands:
                c = min(cands, key=lambda c: (c[0] - pos[0]) ** 2 + (c[1] - pos[1]) ** 2)
                if max(abs(c[0] - pos[0]), abs(c[1] - pos[1])) <= 6:
                    self.cfg["player_area_ref"] = c[2]
                    with self.vision.lock:
                        self.vision.tracker.seed(c[0], c[1])
                    msg = f"已鎖定角色點（大小 {c[2]} px）"
                    if len(cands) > 1:
                        msg += f"；小地圖上另有 {len(cands) - 1} 個同色色塊，會自動忽略不動的那些"
        save_config(self.cfg)
        self.notify(msg)

    def pick_red_color(self):
        with self.vision.lock:
            img = None if self.vision.minimap is None else self.vision.minimap.copy()
        if img is None:
            self.notify("請先框選小地圖。", error=True)
            return
        ColorPicker(self.root, img, self.on_red_picked, title="點一下其他玩家的紅點")

    def on_red_picked(self, hsv):
        h, s, v = (int(x) for x in hsv)
        sl, vl = max(0, s - 70), max(0, v - 70)
        lo, hi = h - 8, h + 8
        ranges = []
        if lo < 0:  # 紅色色相會跨過 0/179
            ranges += [[[0, sl, vl], [hi, 255, 255]], [[180 + lo, sl, vl], [179, 255, 255]]]
        elif hi > 179:
            ranges += [[[lo, sl, vl], [179, 255, 255]], [[0, sl, vl], [hi - 180, 255, 255]]]
        else:
            ranges.append([[lo, sl, vl], [hi, 255, 255]])
        self.cfg["red_dot"]["ranges"] = ranges
        save_config(self.cfg)
        self.notify(f"紅點顏色已更新（HSV {h},{s},{v}）")

    # ---------------- 控制 ----------------
    # ---------------- 錄製 ----------------
    def start_recording(self, what, on_saved, max_sec=60):
        """縮小本工具、切到遊戲，錄製到使用者按「錄製結束」熱鍵為止。"""
        if self.bot.active.is_set():
            self.notify("請先暫停，再開始錄製。", error=True)
            return
        if getattr(self, "recorder", None) is not None and self.recorder.active:
            return
        if not self.vision.hwnd:
            self.notify("找不到遊戲視窗，無法錄製。", error=True)
            return
        # 預設跳躍鍵可能是 Alt；錄製前一定釋放殘留按鍵，避免下一個 Z 觸發 NVIDIA 的 Alt+Z 覆蓋介面。
        self.kb.release_all()
        hk = self.cfg["hotkeys"]
        self._rec_pill = tk.Toplevel(self.root)
        self._rec_pill.overrideredirect(True)
        self._rec_pill.attributes("-topmost", True)
        tk.Label(self._rec_pill, text=f"● 錄製{what}中…　做完按 {hk.get('record', 'f8').upper()} 結束、"
                                       f"{hk.get('stop', 'f12').upper()} 取消",
                 bg=C_BAD, fg="white", font=(UI_FONT, 10, "bold"), padx=10, pady=4).pack()
        wl, wt, ww, wh = work_area(self.root)
        self._rec_pill.update_idletasks()
        self._rec_pill.geometry(f"+{wl + ww - self._rec_pill.winfo_width() - 20}+{wt + wh - self._rec_pill.winfo_height() - 20}")

        def done(rec, cancelled):
            self.hotkey_quiet_until = time.time() + 1.0   # 錄製剛結束：1 秒內熱鍵不作用，避免誤觸開始
            try:
                self._rec_pill.destroy()
            except Exception:
                pass
            self.root.deiconify()
            self.root.lift()
            if cancelled:
                self.notify("已取消錄製。")
            elif not rec:
                self.notify("沒有錄到任何按鍵。", error=True)
            else:
                on_saved(rec)

        log(f"開始錄製{what}（{hk.get('record', 'f8').upper()} 結束）")
        self.recorder = KeyRecorder(self, done, max_sec=max_sec)
        self.root.iconify()
        self.root.after(150, lambda: activate_window(self.vision.hwnd))
        self.recorder.start()

    def record_rope_macro(self):
        """錄製爬繩：有選取繩子就重錄那條，沒選就新增一條（位置＝錄製起點）"""
        idx = self.sel_index(self.tv_patrol)
        target = idx if idx is not None and self.cfg["patrol"][idx].get("type") == "rope" else None

        def saved(rec):
            if not rec.get("start"):
                self.notify("錄製時偵測不到角色座標，請先確認小地圖與取色。", error=True)
                return
            tol = int(self.cfg["patrol_opt"]["plat_tol"])
            if not rec.get("end") or rec["end"][1] >= rec["start"][1] - tol:
                self.notify(f"這次錄製結束時角色沒有在上一層（起點 Y={rec['start'][1]}，結束 Y="
                            f"{rec['end'][1] if rec.get('end') else '?'}），可能被撞下來或太早按結束，請重錄。",
                            error=True)
                return
            if target is None:
                self.cfg["patrol"].append({"type": "rope", "x": rec["start"][0], "y": rec["start"][1]})
                i = len(self.cfg["patrol"]) - 1
            else:
                i = target
            r = self.cfg["patrol"][i]
            r["x"], r["y"] = rec["start"][0], rec["start"][1]
            start_img = rec.pop("start_img", None)
            r["macro"] = rec
            r.pop("macro_invalid", None)
            anchor_msg = self.save_rope_anchor(r, start_img) if start_img is not None else ""
            if rec.get("end"):
                r["lands_y"] = rec["end"][1]
            save_config(self.cfg)
            self.reload_patrol()
            end = rec.get("end")
            moved = f"，從 Y={rec['start'][1]} 到 Y={end[1]}" if end else ""
            self.notify(f"已錄製爬繩 #{i + 1}（{macro_summary(rec)}{moved}）{anchor_msg}")

        self.start_recording("爬繩", saved)

    def record_jump_macro(self):
        """錄製跳台：從一個平台跳到另一個平台。選取既有跳台＝重錄"""
        idx = self.sel_index(self.tv_patrol)
        target = idx if idx is not None and self.cfg["patrol"][idx].get("type") == "jump" else None

        def saved(rec):
            start_img = rec.pop("start_img", None)
            if not rec.get("start") or not rec.get("end"):
                self.notify("錄製時偵測不到角色座標，請先確認小地圖與取色。", error=True)
                return
            (sx, sy), (ex, ey) = rec["start"], rec["end"]
            tol = int(self.cfg["patrol_opt"]["plat_tol"])
            if abs(ey - sy) <= tol and abs(ex - sx) < 4:
                self.notify("錄製結束時角色還在原地附近，沒有跳到別的平台，請重錄。", error=True)
                return
            item = {"type": "jump", "x": sx, "y": sy, "macro": rec}
            if target is None:
                self.cfg["patrol"].append(item)
                i = len(self.cfg["patrol"]) - 1
            else:
                old = self.cfg["patrol"][target].get("screen_anchor")
                if old:
                    item["screen_anchor"] = old
                self.cfg["patrol"][target] = item
                i = target
            msg = self.save_rope_anchor(self.cfg["patrol"][i], start_img) if start_img is not None else ""
            save_config(self.cfg)
            self.reload_patrol()
            self.notify(f"已錄製跳台 #{i + 1}：({sx},{sy}) → ({ex},{ey})（{macro_summary(rec)}）{msg}")

        self.start_recording("跳台", saved)

    def record_route_macro(self):
        def saved(rec):
            rec = dict(rec, type="macro", align=True)
            rec.pop("start_img", None)
            idx = self.sel_index(self.tv_route)
            pos = len(self.cfg["route"]) if idx is None else idx + 1
            self.cfg["route"].insert(pos, rec)
            save_config(self.cfg)
            self.reload_route()
            self.notify(f"已加入錄製動作（{macro_summary(rec)}）")

        self.start_recording("動作", saved)

    def update_map_macro_label(self):
        if not hasattr(self, "lbl_map_macro"):
            return
        routes = self.map_macro_routes()
        if routes:
            mode = routes[0].get("play_mode", self.cfg.get("map_macro_options", {}).get("play_mode", "record"))
            suffix = "座標監看已啟用，偏離會自動暫停。" if mode == "guarded" else "會照錄製操作循環播放。"
            summaries = "；".join(f"#{i + 1} {macro_summary(rec)}" for i, rec in enumerate(routes))
            self.lbl_map_macro.config(text=f"已錄製 {len(routes)} 條路線，BUFF 機每輪隨機選一條：{summaries}。{suffix}")
        else:
            self.lbl_map_macro.config(text="尚未錄製；BUFF 機仍可原地放 Buff／撿物。")

    def map_macro_routes(self):
        routes = [r for r in self.cfg.get("map_macros", []) if isinstance(r, dict) and r.get("events")]
        if not routes:
            legacy = self.cfg.get("map_macro")
            if isinstance(legacy, dict) and legacy.get("events"):
                routes = [legacy]
        return routes

    def save_map_macro_options(self):
        mode = self.var_map_play_mode.get() if hasattr(self, "var_map_play_mode") else "record"
        self.cfg.setdefault("map_macro_options", {})["play_mode"] = mode
        for rec in self.map_macro_routes():
            rec["play_mode"] = mode
            rec.setdefault("position_tolerance", 10)
        save_config(self.cfg)
        self.update_map_macro_label()

    def record_map_macro(self):
        def saved(rec):
            rec.pop("start_img", None)
            options = self.cfg.get("map_macro_options", {})
            rec["play_mode"] = options.get("play_mode", "record")
            rec["position_tolerance"] = int(options.get("position_tolerance", 10))
            routes = self.map_macro_routes()
            routes.append(rec)
            self.cfg["map_macros"] = routes
            self.cfg["map_macro"] = routes[0]  # 兼容已有地圖檔與舊版資料
            save_config(self.cfg)
            self.update_map_macro_label()
            self.notify(f"已加入第 {len(routes)} 條隨機路線（{macro_summary(rec)}）。")

        # 全圖跑法通常較長，最多可錄十分鐘；按設定的「錄製結束」熱鍵可隨時完成。
        self.start_recording("整張地圖", saved, max_sec=600)

    def clear_map_macro(self):
        if not self.map_macro_routes():
            return
        if not messagebox.askyesno("清除錄製", "確定清除這張地圖的全部隨機路線？"):
            return
        self.cfg["map_macro"] = None
        self.cfg["map_macros"] = []
        self.bot.last_map_macro_index = None
        save_config(self.cfg)
        self.update_map_macro_label()
        self.notify("已清除全部隨機路線。")

    def _after_start(self):
        """開始後：取消暫時置頂、縮小本工具、把遊戲切到前景"""
        if getattr(self, "var_top", None) is not None and self.var_top.get():
            self.var_top.set(False)
            self.root.attributes("-topmost", False)
        if not self.cfg.get("minimize_on_start", True):
            return
        self.root.iconify()
        self.root.after(150, lambda: activate_window(self.vision.hwnd))

    def _after_pause(self):
        if self.cfg.get("restore_on_pause", True) and self.root.state() == "iconic":
            self.root.deiconify()

    def toggle_run(self):
        if self.bot.active.is_set():
            self.bot.active.clear()
            log("暫停掛機")
            self._after_pause()
        else:
            if self.alarm_kind == "lie":
                self.notify("請先處理測謊，再按「我處理好了」。", error=True)
                return
            if self.alarm_kind == "red":
                self.dismiss_alarm()
            mode = self.cfg.get("mode")
            # BUFF 機的全圖錄製只重播鍵盤操作，不依賴小地圖；定點掛機才需要定位。
            needs_map = bool(self.bot.anchor_points()) if mode == "anchor" else False
            if not self.cfg.get("minimap") and needs_map:
                self.notify("請先到「首次設定」框選小地圖。", error=True)
                self.nb.select(self.tab_setup)
                return
            self.bot.skill_last = {}
            self.bot.startup_buffs_pending = True
            self.bot.nav_fail = 0
            self.bot.anchor_dwell = None
            self.bot.active.set()
            n_buff = sum(1 for sk in self.cfg["skills"] if sk.get("enabled"))
            log(f"開始掛機：{MODE_INFO.get(mode, (mode,))[0]}（Buff {n_buff} 個）")
            self._after_start()

    def stop(self):
        was_running = self.bot.active.is_set()
        self.bot.active.clear()
        self.bot.step_idx = 0
        self.kb.release_all()
        if was_running:
            log("停止掛機")
            self._after_pause()

    def _hotkey_focus_ok(self):
        """熱鍵只在遊戲視窗或本工具視窗在前景時作用，避免在其他程式誤觸"""
        fg = user32.GetForegroundWindow()
        if not fg:
            return False
        if self.vision.hwnd and fg == self.vision.hwnd:
            return True
        try:
            mine = int(self.root.wm_frame(), 16)
        except Exception:
            mine = self.root.winfo_id()
        GA_ROOT = 2
        return fg == mine or user32.GetAncestor(fg, GA_ROOT) in (mine, user32.GetAncestor(mine, GA_ROOT))

    def poll_hotkeys(self):
        if not self.alive_ui:
            return
        rec = getattr(self, "recorder", None)
        quiet = (rec is not None and rec.active) or time.time() < getattr(self, "hotkey_quiet_until", 0)
        if quiet:   # 錄製中或剛結束：熱鍵交給錄製器，只更新按鍵狀態、不觸發
            if IS_WIN:
                for vk in VK_FKEYS.values():
                    self._hotkey_state[vk] = bool(user32.GetAsyncKeyState(vk) & 0x8000)
            self.root.after(50, self.poll_hotkeys)
            return
        if IS_WIN:
            hk = self.cfg.get("hotkeys", {})
            pairs = ((hk.get("toggle", "f10"), self.toggle_run), (hk.get("stop", "f12"), self.stop))
            for name, fn in pairs:
                vk = VK_FKEYS.get(str(name).lower())
                if vk is None:
                    continue
                down = bool(user32.GetAsyncKeyState(vk) & 0x8000)
                # 工具自己剛送出同一個鍵（例如技能設成 F10）時不算熱鍵
                injected = time.time() - self.kb.last_sent.get(str(name).lower(), 0) < 0.6
                if down and not self._hotkey_state.get(vk) and not injected:
                    # 停止鍵任何時候都有效（安全）；開始/暫停只在遊戲或本工具在前景時有效
                    if fn == self.stop or self._hotkey_focus_ok():
                        fn()
                self._hotkey_state[vk] = down
        self.root.after(50, self.poll_hotkeys)

    # ---------------- GitHub 一鍵更新 ----------------
    def check_for_updates(self):
        """背景檢查公開 GitHub Release，避免網路延遲卡住介面。"""
        def worker():
            release = latest_github_release()
            if not release or version_key(release.get("tag_name", "")) <= version_key(APP_VERSION):
                return
            assets = release.get("assets") or []
            asset = next((a for a in assets if str(a.get("name", "")).lower().endswith(".zip")), None)
            if asset and asset.get("browser_download_url"):
                self.ui(lambda: self.offer_update(release, asset))
        threading.Thread(target=worker, daemon=True).start()

    def offer_update(self, release, asset):
        if not self.alive_ui:
            return
        tag = release.get("tag_name", "新版")
        notes = str(release.get("body") or "").strip()
        text = f"發現新版 {tag}（目前 {APP_VERSION}）。\n\n要下載並更新嗎？"
        if notes:
            text += "\n\n更新內容：\n" + notes[:700]
        log(f"發現新版 {tag}")
        if messagebox.askyesno("有新版本", text, parent=self.root):
            threading.Thread(target=self.download_and_apply_update, args=(asset,), daemon=True).start()

    def download_and_apply_update(self, asset):
        """下載 Release ZIP、解壓到暫存區，再由關閉後的批次檔覆寫程式檔案。"""
        try:
            stage = tempfile.mkdtemp(prefix="maple-helper-update-")
            archive = os.path.join(stage, "update.zip")
            req = urllib.request.Request(asset["browser_download_url"], headers={"User-Agent": f"MapleHelper/{APP_VERSION}"})
            with urllib.request.urlopen(req, timeout=30) as response, open(archive, "wb") as out:
                shutil.copyfileobj(response, out)
            digest = str(asset.get("digest") or "")
            if digest.lower().startswith("sha256:"):
                h = hashlib.sha256()
                with open(archive, "rb") as f:
                    for chunk in iter(lambda: f.read(1 << 20), b""):
                        h.update(chunk)
                if h.hexdigest().lower() != digest.split(":", 1)[1].strip().lower():
                    raise ValueError("更新檔校驗碼不符（下載不完整或檔案被竄改），已取消更新")
                log("更新檔 SHA-256 校驗通過")
            unpacked = os.path.join(stage, "unpacked")
            os.makedirs(unpacked, exist_ok=True)
            with zipfile.ZipFile(archive) as zf:
                root = os.path.abspath(unpacked) + os.sep
                for member in zf.infolist():
                    target = os.path.abspath(os.path.join(unpacked, member.filename))
                    if not target.startswith(root):
                        raise ValueError("更新檔包含不安全路徑")
                zf.extractall(unpacked)
            candidates = []
            for base, _dirs, files in os.walk(unpacked):
                if "maple_helper.py" in files:
                    candidates.append(base)
            if not candidates:
                raise ValueError("更新檔中找不到 maple_helper.py")
            payload = candidates[0]
            names = [n for n in ("maple_helper.py", "啟動.bat", "打包成exe.bat", "requirements.txt", "使用說明.md")
                     if os.path.isfile(os.path.join(payload, n))]
            model_rel = os.path.join("yolo_data", "models", "monster_current_map_v2.pt")
            if os.path.isfile(os.path.join(payload, model_rel)):
                names.append(model_rel)
            if "maple_helper.py" not in names:
                raise ValueError("更新檔不完整")
            self.ui(lambda: self.finish_update(payload, names))
        except Exception as e:
            msg = f"下載更新失敗：{e}"
            log_exception("下載更新失敗", e)
            self.ui(lambda m=msg: self.notify(m, error=True))

    def finish_update(self, payload, names):
        if not self.alive_ui:
            return
        self.notify("下載完成，正在更新並重新開啟…")
        log(f"套用更新：{', '.join(names)}")
        # 不使用 .cmd：cmd 對中文資料夾／檔名的編碼常會變成亂碼。
        # 以 Unicode 參數直接啟動短暫的 Python 更新助手，保留使用者的設定與地圖資料。
        # 由本程式自己的「--apply-update」模式當更新助手（Python 版與 EXE 版都適用）：
        # 等本視窗關閉 → 複製新檔 → 重新開啟。EXE 版會在啟動時改跑資料夾內較新的 maple_helper.py。
        args = ["--apply-update", payload, APP_DIR, json.dumps(names, ensure_ascii=False)]
        if getattr(sys, "frozen", False):
            cmd = [sys.executable] + args
        else:
            cmd = [sys.executable, os.path.abspath(__file__)] + args
        subprocess.Popen(cmd, creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        self.root.after(300, self.on_close)

    def on_close(self):
        log("關閉工具")
        if self._on_log in EVENT_LOG.listeners:
            EVENT_LOG.listeners.remove(self._on_log)
        self.alive_ui = False
        self.yolo_collecting = False
        if self._yolo_capture_job:
            try:
                self.root.after_cancel(self._yolo_capture_job)
            except tk.TclError:
                pass
        if hasattr(self, "diag"):
            self.diag.running = False
        self.scanner.running = False
        self.bot.alive = False
        self.bot.active.clear()
        self.vision.running = False
        self.kb.release_all()
        save_config(self.cfg)
        self.root.destroy()


# --------------------------------------------------------------------------
# 對話框
# --------------------------------------------------------------------------
class FormDialog(simpledialog.Dialog):
    def __init__(self, parent, title, fields):
        self.fields = fields
        self.vars = {}
        self.result = None
        super().__init__(parent, title)

    def body(self, master):
        first = None
        for i, f in enumerate(self.fields):
            k, label, val = f[0], f[1], f[2]
            spec = f[3] if len(f) > 3 else None
            ttk.Label(master, text=label).grid(row=i, column=0, sticky="w", pady=2)
            v = tk.StringVar(value=str(val))
            e = make_choice(master, v, spec, width=20) if spec else ttk.Entry(master, textvariable=v, width=22)
            e.grid(row=i, column=1, padx=6, sticky="w")
            self.vars[k] = v
            first = first or e
        return first

    def apply(self):
        self.result = {k: v.get() for k, v in self.vars.items()}


class RectSelector(tk.Toplevel):
    """在遊戲截圖上拖曳框選小地圖"""

    def __init__(self, parent, img_bgr, callback, title=None):
        super().__init__(parent)
        self.title(title or "用滑鼠拖曳框選小地圖範圍（只框地圖本體，不含標題列），放開後按 Enter 確認")
        self.attributes("-topmost", True)
        self.callback = callback
        h, w = img_bgr.shape[:2]
        sw, sh = self.winfo_screenwidth() - 80, self.winfo_screenheight() - 120
        self.scale = min(1.0, sw / w, sh / h)
        disp = cv2.resize(img_bgr, (int(w * self.scale), int(h * self.scale)))
        self.tkimg = ImageTk.PhotoImage(Image.fromarray(cv2.cvtColor(disp, cv2.COLOR_BGR2RGB)))
        self.cv = tk.Canvas(self, width=disp.shape[1], height=disp.shape[0], cursor="cross")
        self.cv.pack()
        self.cv.create_image(0, 0, anchor="nw", image=self.tkimg)
        self.start = None
        self.rect_id = None
        self.sel = None
        self.cv.bind("<ButtonPress-1>", self.on_down)
        self.cv.bind("<B1-Motion>", self.on_drag)
        self.bind("<Return>", self.on_ok)
        self.bind("<Escape>", lambda _: self.destroy())
        self.focus_force()

    def on_down(self, e):
        self.start = (e.x, e.y)
        if self.rect_id:
            self.cv.delete(self.rect_id)
        self.rect_id = self.cv.create_rectangle(e.x, e.y, e.x, e.y, outline="red", width=2)

    def on_drag(self, e):
        x0, y0 = self.start
        self.cv.coords(self.rect_id, x0, y0, e.x, e.y)
        x1, x2 = sorted((x0, e.x))
        y1, y2 = sorted((y0, e.y))
        s = self.scale
        self.sel = (int(x1 / s), int(y1 / s), int((x2 - x1) / s), int((y2 - y1) / s))

    def on_ok(self, _):
        if self.sel and self.sel[2] > 5 and self.sel[3] > 5:
            self.callback(self.sel)
            self.destroy()


class YoloBoxAnnotator(tk.Toplevel):
    """簡化的 YOLO 標註器：可在同一張圖片標記多個類別。"""

    def __init__(self, parent, img_bgr, label_path, class_id, callback):
        super().__init__(parent)
        label = YOLO_CLASS_LABELS[class_id] if 0 <= class_id < len(YOLO_CLASS_LABELS) else "怪物"
        self.title(f"框選{label}：拖曳可新增多個框，Enter 儲存，Backspace 復原")
        self.attributes("-topmost", True)
        self.img = img_bgr
        self.label_path = label_path
        self.class_id = class_id
        self.callback = callback
        self.h, self.w = img_bgr.shape[:2]
        sw, sh = self.winfo_screenwidth() - 80, self.winfo_screenheight() - 180
        self.scale = min(1.0, sw / self.w, sh / self.h)
        disp = cv2.resize(img_bgr, (max(1, int(self.w * self.scale)), max(1, int(self.h * self.scale))))
        self.tkimg = ImageTk.PhotoImage(Image.fromarray(cv2.cvtColor(disp, cv2.COLOR_BGR2RGB)))
        self.cv = tk.Canvas(self, width=disp.shape[1], height=disp.shape[0], cursor="cross")
        self.cv.pack()
        self.cv.create_image(0, 0, anchor="nw", image=self.tkimg)
        self.boxes = self._load_existing()
        self.start = None
        self.preview = None
        self._draw_boxes()
        controls = ttk.Frame(self)
        controls.pack(fill="x", padx=6, pady=6)
        ttk.Label(controls, text=f"目前新增類別：{label}").pack(side="left")
        ttk.Button(controls, text="復原最後一框", command=self.undo).pack(side="right")
        ttk.Button(controls, text="儲存標註", command=self.save).pack(side="right", padx=(0, 6))
        self.cv.bind("<ButtonPress-1>", self.on_down)
        self.cv.bind("<B1-Motion>", self.on_drag)
        self.cv.bind("<ButtonRelease-1>", self.on_up)
        self.cv.bind("<Button-3>", self.on_right_click)
        self.bind("<Return>", self.save)
        self.bind("<BackSpace>", lambda _: self.undo())
        self.bind("<Escape>", lambda _: self.destroy())
        self.focus_force()

    def _load_existing(self):
        boxes = []
        if not os.path.isfile(self.label_path):
            return boxes
        try:
            with open(self.label_path, "r", encoding="utf-8") as f:
                for line in f:
                    parts = line.split()
                    if len(parts) != 5 or not parts[0].isdigit() or int(parts[0]) >= len(YOLO_CLASS_NAMES):
                        continue
                    class_id = int(parts[0])
                    cx, cy, bw, bh = (float(v) for v in parts[1:])
                    w, h = bw * self.w, bh * self.h
                    boxes.append((class_id, max(0, cx * self.w - w / 2), max(0, cy * self.h - h / 2), w, h))
        except (OSError, ValueError):
            pass
        return boxes

    def _draw_boxes(self):
        self.cv.delete("yolo_box")
        for class_id, x, y, w, h in self.boxes:
            color = YOLO_CLASS_COLORS[class_id] if class_id < len(YOLO_CLASS_COLORS) else "#ffffff"
            self.cv.create_rectangle(x * self.scale, y * self.scale, (x + w) * self.scale, (y + h) * self.scale,
                                     outline=color, width=2, tags="yolo_box")
            self.cv.create_text(x * self.scale + 3, y * self.scale + 3,
                                text=YOLO_CLASS_LABELS[class_id], fill=color, anchor="nw", tags="yolo_box")

    def on_down(self, event):
        self.start = (event.x, event.y)
        if self.preview:
            self.cv.delete(self.preview)
        self.preview = self.cv.create_rectangle(event.x, event.y, event.x, event.y, outline="#ffcc00", width=2)

    def on_drag(self, event):
        if self.start and self.preview:
            self.cv.coords(self.preview, self.start[0], self.start[1], event.x, event.y)

    def on_up(self, event):
        if not self.start:
            return
        x0, x1 = sorted((self.start[0], event.x))
        y0, y1 = sorted((self.start[1], event.y))
        self.start = None
        if self.preview:
            self.cv.delete(self.preview)
            self.preview = None
        if x1 - x0 < 4 or y1 - y0 < 4:
            return
        s = self.scale
        self.boxes.append((self.class_id, x0 / s, y0 / s, (x1 - x0) / s, (y1 - y0) / s))
        self._draw_boxes()

    def undo(self):
        if self.boxes:
            self.boxes.pop()
            self._draw_boxes()

    def on_right_click(self, event):
        """右鍵：刪除游標所在的框（重疊時刪最小的那個）"""
        x, y = event.x / self.scale, event.y / self.scale
        hits = [(w * h, i) for i, (_c, bx, by, w, h) in enumerate(self.boxes)
                if bx <= x <= bx + w and by <= y <= by + h]
        if hits:
            del self.boxes[min(hits)[1]]
            self._draw_boxes()

    def save(self, _event=None):
        os.makedirs(os.path.dirname(self.label_path), exist_ok=True)
        lines = []
        for class_id, x, y, w, h in self.boxes:
            x, y = max(0, min(x, self.w)), max(0, min(y, self.h))
            w, h = min(w, self.w - x), min(h, self.h - y)
            if w < 2 or h < 2:
                continue
            lines.append(f"{class_id} {(x + w / 2) / self.w:.6f} {(y + h / 2) / self.h:.6f} {w / self.w:.6f} {h / self.h:.6f}")
        with open(self.label_path, "w", encoding="utf-8", newline="\n") as f:
            f.write("\n".join(lines) + ("\n" if lines else ""))
        self.callback(len(lines))
        self.destroy()


class ColorPicker(tk.Toplevel):
    """放大顯示小地圖，點擊角色黃點取色"""

    def __init__(self, parent, img_bgr, callback, title=None, with_pos=False):
        super().__init__(parent)
        self.with_pos = with_pos
        self.title(title or "點一下你的角色點（通常是黃色）")
        self.attributes("-topmost", True)
        self.img = img_bgr
        self.callback = callback
        h, w = img_bgr.shape[:2]
        self.z = max(1, min(6, 900 // max(w, 1)))
        disp = cv2.resize(img_bgr, (w * self.z, h * self.z), interpolation=cv2.INTER_NEAREST)
        self.tkimg = ImageTk.PhotoImage(Image.fromarray(cv2.cvtColor(disp, cv2.COLOR_BGR2RGB)))
        cv = tk.Canvas(self, width=disp.shape[1], height=disp.shape[0], cursor="tcross")
        cv.pack()
        cv.create_image(0, 0, anchor="nw", image=self.tkimg)
        cv.bind("<Button-1>", self.on_click)

    def on_click(self, e):
        x, y = e.x // self.z, e.y // self.z
        h, w = self.img.shape[:2]
        x0, x1, y0, y1 = max(0, x - 1), min(w, x + 2), max(0, y - 1), min(h, y + 2)
        patch = cv2.cvtColor(self.img[y0:y1, x0:x1], cv2.COLOR_BGR2HSV).reshape(-1, 3)
        hsv = patch[np.argmax(patch[:, 1].astype(int) + patch[:, 2])]  # 取最鮮豔的像素
        if self.with_pos:
            self.callback(hsv, (x, y), self.img)
        else:
            self.callback(hsv)
        self.destroy()


def apply_update_cli(argv):
    """更新助手：python maple_helper.py --apply-update <來源> <目的> <檔名清單JSON>（EXE 版同參數）。
    等舊視窗關閉後複製新檔（已存在的 yolo_data 模型不覆蓋），再重新開啟工具。"""
    src, dst, names = argv[0], argv[1], json.loads(argv[2])
    time.sleep(1.5)
    copied = []
    for n in names:
        s_path, d_path = os.path.join(src, n), os.path.join(dst, n)
        if not os.path.isfile(s_path) or (n.startswith("yolo_data") and os.path.exists(d_path)):
            continue
        for _ in range(10):          # 舊程式可能還沒完全結束：最多重試 5 秒
            try:
                os.makedirs(os.path.dirname(d_path), exist_ok=True)
                shutil.copy2(s_path, d_path)
                copied.append(n)
                break
            except OSError:
                time.sleep(0.5)
    try:
        os.makedirs(LOG_DIR, exist_ok=True)
        with open(os.path.join(LOG_DIR, time.strftime("%Y-%m-%d") + ".log"), "a", encoding="utf-8") as f:
            f.write(f"{EventLog.stamp()} 更新助手：已複製 {', '.join(copied) or '（無）'}\n")
    except OSError:
        pass
    if getattr(sys, "frozen", False):
        subprocess.Popen([sys.executable], cwd=dst)
    else:
        subprocess.Popen([sys.executable, os.path.join(dst, "maple_helper.py")], cwd=dst)


def run_newer_source():
    """EXE 版：資料夾裡有比執行檔內建版本更新的 maple_helper.py（一鍵更新下載的）就改跑它。
    執行檔已內含所有套件，新的原始碼可以直接用；載入失敗時退回內建版本。回傳是否已執行新版。"""
    if not getattr(sys, "frozen", False) or os.environ.get("MAPLE_HELPER_SOURCE"):
        return False
    path = os.path.join(APP_DIR, "maple_helper.py")
    try:
        with open(path, "r", encoding="utf-8-sig") as f:
            head = f.read(20000)
    except OSError:
        return False
    m = re.search(r'^APP_VERSION = "([^"]+)"', head, re.M)
    if not m or version_key(m.group(1)) <= version_key(APP_VERSION):
        return False
    os.environ["MAPLE_HELPER_SOURCE"] = path
    try:
        import runpy
        runpy.run_path(path, run_name="__main__")
        return True
    except (ImportError, SyntaxError) as e:
        log(f"執行新版原始碼失敗，改用執行檔內建的 {APP_VERSION}：{e}", "error")
        return False


def main():
    if len(sys.argv) >= 5 and sys.argv[1] == "--apply-update":
        apply_update_cli(sys.argv[2:5])
        return
    if run_newer_source():
        return
    if not IS_WIN:
        print("此工具僅支援 Windows。")
        return
    if not ctypes.windll.shell32.IsUserAnAdmin():
        print("提示：若遊戲以系統管理員身分執行，本工具也必須以系統管理員身分執行，否則按鍵送不進去。")
    root = tk.Tk()
    try:
        ttk.Style().theme_use("vista")
    except Exception:
        pass
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
