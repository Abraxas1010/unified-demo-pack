#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"

"$ROOT_DIR/scripts/guard_no_sorry.sh"
(cd "$ROOT_DIR/lean" && lake build --wfail unified_demo) || (cd "$ROOT_DIR/lean" && lake build --wfail HeytingLean.CLI.UnifiedDemo)

if [[ -x "$ROOT_DIR/lean/.lake/build/bin/unified_demo" ]]; then
  (cd "$ROOT_DIR/lean" && .lake/build/bin/unified_demo --quick)
else
  (cd "$ROOT_DIR/lean" && lake env lean --run HeytingLean/CLI/UnifiedDemo.lean -- --quick)
fi

echo '{"demo_quick_all":"ok"}'
