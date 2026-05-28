#!/bin/bash

# --- 設定項目 ---
# 書き込みたいイメージファイル
IMAGE="x86_64_uefi.img"
# ターゲットデバイス (例: /dev/sdb)
TARGET="/dev/sdb"
# USBメモリの最大想定サイズ (GB)。これより大きい場合はSSDとみなして停止。
MAX_SIZE_GB=65
# ----------------

# 1. そもそもデバイスファイルが存在するか
if [ ! -b "$TARGET" ]; then
    echo "Error: デバイス $TARGET が見つかりません。USBは挿さっていますか？"
    exit 1
fi

# 2. USB接続かどうかをチェック (ID_BUSを確認)
IS_USB=$(udevadm info --query=property --name="$TARGET" | grep "ID_BUS=usb")
if [ -z "$IS_USB" ]; then
    echo "Error: $TARGET はUSBデバイスではないようです！内蔵SSDへの書き込みを阻止しました。"
    exit 1
fi

# 3. サイズチェック (巨大なドライブへの誤爆防止)
SIZE_BYTE=$(blockdev --getsize64 "$TARGET")
SIZE_GB=$((SIZE_BYTE / 1024 / 1024 / 1024))

if [ "$SIZE_GB" -gt "$MAX_SIZE_GB" ]; then
    echo "Error: $TARGET のサイズが ${SIZE_GB}GB です。設定（${MAX_SIZE_GB}GB）を超えているため、実行を中止します。"
    exit 1
fi

# 4. 最終確認
echo "書き込み対象: $TARGET (USB接続, ${SIZE_GB}GB)"
echo "イメージ: $IMAGE"
read -p "本当に書き込みますか？ (y/N): " -n 1 -r
echo
if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    echo "中止しました。"
    exit 1
fi

# 5. 実行
echo "書き込み中..."
sudo dd if="$IMAGE" of="$TARGET" bs=4M status=progress conv=fsync
echo "完了しました！"