@echo off
chcp 65001 >nul
cd /d "%~dp0"
set "PY="
py -3 --version >nul 2>&1 && set "PY=py -3"
if not defined PY (
    python --version >nul 2>&1 && set "PY=python"
)
if not defined PY (
    echo [錯誤] 找不到 Python。
    pause
    exit /b 1
)
%PY% -m pip install -r requirements.txt pyinstaller
%PY% -m PyInstaller --noconfirm --onefile --windowed --uac-admin --name MapleHelper maple_helper.py
echo.
echo 完成！執行檔在 dist\MapleHelper.exe
pause
