@echo off
chcp 65001 >nul
cd /d "%~dp0"

rem ---- 找 Python：優先用 py -3（Python 官方啟動器），沒有再用 python ----
set "PY="
py -3 --version >nul 2>&1 && set "PY=py -3"
if not defined PY (
    python --version >nul 2>&1 && set "PY=python"
)
if not defined PY (
    echo [錯誤] 找不到 Python。請到 https://www.python.org 安裝 Python 3.10 以上，
    echo        安裝時勾選「Add Python to PATH」。
    pause
    exit /b 1
)

rem ---- 只有缺少套件時才安裝 ----
%PY% -c "import mss, numpy, cv2, PIL" >nul 2>&1
if errorlevel 1 (
    echo 第一次執行，正在安裝需要的套件...
    %PY% -m pip install -r requirements.txt
    if errorlevel 1 (
        echo [錯誤] 套件安裝失敗，請確認網路連線後再試一次。
        pause
        exit /b 1
    )
)

%PY% maple_helper.py
if errorlevel 1 pause
