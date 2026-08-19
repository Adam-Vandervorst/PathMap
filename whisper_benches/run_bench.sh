#!/usr/bin/bash
set -o errexit
set -o nounset
set -o pipefail
set -o xtrace
set -o errtrace

WHISPER_PATH=${WHISPER_PATH:-/var/data/whisper/demo}
THIS_DIR=$(dirname "${BASH_SOURCE[0]}")
CROSS_LIBC_PATH=${CROSS_LIBC_PATH:-/usr/riscv64-linux-gnu/lib}

check_env() {
    RED="\033[31m"
    RESET="\033[0m"
    if ! test -e "$CROSS_LIBC_PATH/libc.so.6"; then
        echo "${RED}Missing libc in '$CROSS_LIBC_PATH'${RESET}"
        echo "Need to 'sudo apt-get install libc6-riscv64-cross',"
        echo "or equivalent package in your linux distribution."
        echo "Alternatively, provide path to riscv64 libc directory as CROSS_LIBC_PATH env var."
        exit 1
    fi
    for file in bin/whisper \
        bin/whisper.json \
        bin/fw_jump.elf \
        bin/wb.dtb \
        bin/Image \
        bin/initramfs.cpio; do
        if ! test -e "$WHISPER_PATH/$file"; then
            echo "${RED}Missing whisper installation in '$WHISPER_PATH'${RESET}"
            echo "You can use the demo archive to get all the necessary files,"
            echo "and provide path to the directory as WHISPER_PATH env var."
            exit 1
        fi
    done
}

prepare_base_fs() {
    echo "creating base-fs"
    rm -fr "$THIS_DIR/base-fs"
    mkdir "$THIS_DIR/base-fs"
    cp "$THIS_DIR/app" -t "$THIS_DIR/base-fs"
    mkdir "$THIS_DIR/base-fs/lib"
    for file in ld-linux-riscv64-lp64d.so.1 \
        libc.so.6 \
        libgcc_s.so.1 \
        libm.so.6 \
        libpthread.so.0; do
        cp "$CROSS_LIBC_PATH/$file" -t "$THIS_DIR/base-fs/lib"
    done
    mkdir "$THIS_DIR/base-fs/data"
    for file in "$THIS_DIR/../benches"/*.{txt,laz,paths}; do
        cp "$file" -t "$THIS_DIR/base-fs/data"
    done
    cp "$1" "$THIS_DIR/base-fs/current_bench"

    echo "creating disk image"
    rm -f "$THIS_DIR/base-fs.img.tmp"
    mke2fs -d "$THIS_DIR/base-fs" -t ext2 "$THIS_DIR/base-fs.img.tmp" 128M
    mv "$THIS_DIR/base-fs.img.tmp" "$THIS_DIR/base-fs.img"
}

run_whisper() {
    mkdir -p "$THIS_DIR/logs"
    BENCH_NAME="$(basename "$1")"
    "$WHISPER_PATH/bin/whisper" \
        --logfile "$THIS_DIR/logs/$BENCH_NAME.log" \
        --hart 1 --quitany \
        --configfile "$WHISPER_PATH/bin/whisper.json" \
        --target "$WHISPER_PATH/bin/fw_jump.elf" \
        --fromhost 0x70000000 \
        --tohost 0x70000008 \
        --memorysize 0x380000000 \
        --setreg a1=0x830ab000 \
        -b "$WHISPER_PATH/bin/wb.dtb:0x830ab000" \
        -b "$WHISPER_PATH/bin/Image:0x80200000" \
        -b "$WHISPER_PATH/bin/initramfs.cpio:0x83000000" \
        -b "$THIS_DIR/base-fs.img:0x280000000"
}
cleanup() {
    rm -fr "$THIS_DIR/base-fs" "$THIS_DIR/base-fs.img"
}

check_env
prepare_base_fs "$1"
run_whisper "$1"
cleanup
