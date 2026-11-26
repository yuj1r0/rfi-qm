#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
local_bin="$PWD/.toolchain/lean-4.35.0-darwin_aarch64/bin"
if [[ -x "$local_bin/lake" ]]; then
  export PATH="$local_bin:$PATH"
fi
exec "$@"
