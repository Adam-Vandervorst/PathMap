#!/usr/bin/bash
set -o errexit
set -o nounset
set -o pipefail
set -o xtrace
set -o errtrace

THIS_DIR=$(dirname "${BASH_SOURCE[0]}")
export CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_GNU_RUNNER="$THIS_DIR/run_bench.sh"

cargo bench --target riscv64gc-unknown-linux-gnu
