#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"

need() { command -v "$1" >/dev/null 2>&1 || return 0; return 1; }

if ! command -v lake >/dev/null 2>&1; then
  if ! command -v elan >/dev/null 2>&1; then
    echo "[i] Installing elan (Lean toolchain manager)"
    curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | bash -s -- -y
    export PATH="$HOME/.elan/bin:$PATH"
  else
    echo "[ok] elan present"
  fi
fi

export PATH="$HOME/.elan/bin:$PATH"
echo "[i] Updating Lake dependencies"
cd "$ROOT_DIR/lean"
lake update || true
echo "[i] Building unified_demo"
lake build --wfail unified_demo || lake build --wfail HeytingLean.CLI.UnifiedDemo
echo "[ok] Bootstrap complete"
