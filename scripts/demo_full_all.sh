#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
ART_DIR="$ROOT_DIR/.artifacts"
SENTINEL="$ART_DIR/pqc_verify_all.ok"

mkdir -p "$ART_DIR"

"$ROOT_DIR/scripts/guard_no_sorry.sh"
(cd "$ROOT_DIR/lean" && lake build --wfail unified_demo) || (cd "$ROOT_DIR/lean" && lake build --wfail HeytingLean.CLI.UnifiedDemo)

# Run PQC verification and capture output
OUT_STD="$ART_DIR/pqc_verify_all.stdout"
bash "$ROOT_DIR/WIP/pqc_lattice/scripts/pqc_verify_all.sh" | tee "$OUT_STD"

# Compute hardened sentinel
hash_cmd() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

TS="$(date -Iseconds)"
COMMIT="$(git -C "$ROOT_DIR" rev-parse --short=12 HEAD 2>/dev/null || echo unknown)"
STD_SHA="$(hash_cmd "$OUT_STD")"

# Hash all verifier scripts as a combined digest
SCR_LIST="$ART_DIR/pqc_scripts.sha256list"
find "$ROOT_DIR/WIP/pqc_lattice/scripts" -type f -maxdepth 1 -print0 | xargs -0 -I{} bash -c 'if command -v sha256sum >/dev/null 2>&1; then sha256sum "$0"; else shasum -a 256 "$0"; fi' {} > "$SCR_LIST"
if command -v sha256sum >/dev/null 2>&1; then
  SCRIPTS_SHA="$(sha256sum "$SCR_LIST" | awk '{print $1}')"
else
  SCRIPTS_SHA="$(shasum -a 256 "$SCR_LIST" | awk '{print $1}')"
fi

EVID_SRC="$ART_DIR/pqc_evidence.src"
{
  echo "$TS"
  echo "$COMMIT"
  echo "$STD_SHA"
  echo "$SCRIPTS_SHA"
} > "$EVID_SRC"
EVID_SHA="$(hash_cmd "$EVID_SRC")"

# Write JSON sentinel
cat > "$SENTINEL" <<JSON
{
  "verified": true,
  "ts": "$TS",
  "commit": "$COMMIT",
  "stdout_sha256": "$STD_SHA",
  "scripts_sha256": "$SCRIPTS_SHA",
  "evidence_hash": "$EVID_SHA"
}
JSON

if [[ -x "$ROOT_DIR/lean/.lake/build/bin/unified_demo" ]]; then
  (cd "$ROOT_DIR/lean" && .lake/build/bin/unified_demo --full)
else
  (cd "$ROOT_DIR/lean" && lake env lean --run HeytingLean/CLI/UnifiedDemo.lean -- --full)
fi

echo '{"demo_full_all":"ok"}'
