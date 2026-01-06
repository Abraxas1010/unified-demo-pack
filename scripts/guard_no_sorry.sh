#!/usr/bin/env bash
set -euo pipefail

# Fast guard: fail early if Lean sources contain proof escapes.
# This intentionally scans only the workspace `lean/` tree and excludes `.lake/`.

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
PATTERN='\b(sorry|admit)\b'

if rg -n --type lean -S --glob '!.lake/**' "$PATTERN" "$ROOT_DIR/lean" >/dev/null 2>&1; then
  echo "E: forbidden token found in Lean sources (sorry/admit)."
  rg -n --type lean -S --glob '!.lake/**' "$PATTERN" "$ROOT_DIR/lean" | head -n 80
  exit 1
fi

exit 0
