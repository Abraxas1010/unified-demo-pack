#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
ART_DIR="$ROOT_DIR/.artifacts"
SENTINEL="$ART_DIR/pqc_verify_all.ok"

mkdir -p "$ART_DIR"

"$ROOT_DIR/scripts/guard_no_sorry.sh"
(cd "$ROOT_DIR/lean" && lake build --wfail HeytingLean.CLI.UnifiedDemo)

# Run PQC verification and capture output
OUT_STD="$ART_DIR/pqc_verify_all.stdout"
# Ensure deterministic locale for hashing/sorting
export LC_ALL=C
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
# Deterministic combined hash of verifier scripts: sort paths, hash contents, hash the list
SCRIPTS_SHA=$( \
  find "$ROOT_DIR/WIP/pqc_lattice/scripts" -maxdepth 1 -type f -print0 \
  | tr '\0' '\n' \
  | LC_ALL=C sort \
  | while IFS= read -r f; do \
      [ -n "$f" ] && sha256sum "$f"; \
    done \
  | sha256sum | awk '{print $1}' \
)

# Dirty state + diff hash for audit clarity
if git -C "$ROOT_DIR" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  if git -C "$ROOT_DIR" diff --no-ext-diff --quiet --exit-code; then
    DIRTY=false
    DIFF_SHA=""
  else
    DIRTY=true
    DIFF_TMP="$ART_DIR/pqc_git_diff.patch"
    git -C "$ROOT_DIR" diff --no-ext-diff --binary HEAD > "$DIFF_TMP" || true
    DIFF_SHA="$(hash_cmd "$DIFF_TMP")"
  fi
else
  DIRTY=false
  DIFF_SHA=""
fi

# Evidence hash over core fields
EVID_SRC="$ART_DIR/pqc_evidence.src"
{
  echo "$TS"
  echo "$COMMIT"
  echo "$STD_SHA"
  echo "$SCRIPTS_SHA"
  echo "$DIRTY"
  echo "$DIFF_SHA"
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
  "dirty": $DIRTY,
  "diff_sha256": "${DIFF_SHA}",
  "evidence_hash": "$EVID_SHA"
}
JSON

if [[ -x "$ROOT_DIR/lean/.lake/build/bin/unified_demo" ]]; then
  (cd "$ROOT_DIR/lean" && .lake/build/bin/unified_demo --full)
else
  (cd "$ROOT_DIR/lean" && lake env lean --run HeytingLean/CLI/UnifiedDemo.lean -- --full)
fi

echo '{"demo_full_all":"ok"}'
