# Unified Demo Pack (Lean + PQC Evidence)

This pack provides a coherent, auditable demonstration that ties together four strands:

1. CryptoSheaf contextuality witness (triangle)
2. Valuation proxy (finite support cardinalities; no entropy claims)
3. FHE/ZK hooks (spec-level homomorphic addition; SIS PoK boolean verifier)
4. PQC corpora verification as external evidence (sentinel gating)

## Quick Start

```bash
cd artifacts/unified_demo_pack
make bootstrap   # installs elan if needed; fetches deps; builds
make run-quick   # Lean-only JSON: contextuality+valuation+fhe/zk, pqc=false
make run-quick-robust  # run with a minimal env to catch accidental dependencies
```

```bash
# With ACVP/KAT corpora and verifier deps available
make run-full    # runs corpora verification, sets sentinel, unified JSON with pqc=true
```

## What’s Implemented (Mathematical)

### Contextuality (Triangle Witness)

We formalize a three-context cover over Meas := Fin 3 with contexts C_ab, C_bc, C_ac and Bool outcomes. The empirical model uses possibilistic supports:

- supportAB := { s | s a_in_ab = s b_in_ab }
- supportBC := { s | s b_in_bc = s c_in_bc }
- supportAC := { s | s a_in_ac ≠ s c_in_ac }

`triangle_no_global` is a Lean proof artifact showing no global section. The unified demo emits a JSON witness with cover_size=3; the proof remains compile-checked and separate from runtime.

### Valuation Proxy (Finite Cardinalities)

We avoid Real-valued “entropy” claims and instead instrument finite support sizes. For any context C, `supportSize S := Fintype.card {s // s ∈ S}`. In the triangle model, each context’s support is finite and nonempty, and we prove exact cardinalities:

- AB: |supportAB| = 2 (bijection via constant assignments; in the primary bridge)
- BC: |supportBC| = 2 (idem)
- AC: |supportAC| = 2 (bijection via flip-at-a; proved in `UnifiedPack.ContextualityAC`)

### FHE Hook (Noise-Aware Homomorphic Addition)

We expose a spec-level relation `EncRel P β ct m` that ties ciphertext structure (MLWE-shaped) to a message with bounded noise. A Lean theorem `homAdd_correct` shows that `addCt` preserves the relation with noise growth β₁+β₂. Runtime only performs a tiny smoke (construct two toy ciphertexts and run addCt) — the proof is a compile artifact.

### ZK Hook (SIS PoK Boolean Verifier)

We instantiate a trivial PoK interface over SIS: the verifier is a Boolean function `sisVerify` proving soundness (`sisVerify_sound`). Runtime checks a toy instance (x=0) and returns sis_pok_demo=true. No cryptographic guarantees are claimed; this is a checked bridge for end-to-end wiring.

## What’s Implemented (Computational)

- Unified CLI: `lean/HeytingLean/CLI/UnifiedDemo.lean` outputs a single quiet JSON combining the four strands.
- Lean-only quick mode: does not touch corpora; proves build integrity and runs small smokes.
- Full mode: runs corpora verification (via `WIP/pqc_lattice/scripts/pqc_verify_all.sh`), writes `.artifacts/pqc_verify_all.ok` (hardened; see below); the CLI sets `pqc.verified=true` and includes `pqc.evidence_hash` when the sentinel is present.
- Strict builds: we use `lake build --wfail` and keep no `sorry`/`admit` in sources (guarded by `scripts/guard_no_sorry.sh`).

## JSON Contract

```json
{
  "demo": "unified",
  "contextuality": { "contextual": true, "cover_size": 3 },
  "valuation": {
    "supports": [
      { "context": "ab", "size": 2 },
      { "context": "bc", "size": 2 },
      { "context": "ac", "size": 2 }
    ]
  },
  "fhe": { "hom_add_demo": true },
  "zk": { "sis_pok_demo": true },
  "pqc": { "verified": false }
}
```

In full mode, `pqc.verified` becomes `true` iff `.artifacts/pqc_verify_all.ok` exists. When present, the CLI reads the sentinel and includes `pqc.evidence_hash`.

### Hardened Sentinel (Full Mode)

The sentinel JSON contains:

- `ts` (ISO timestamp), `commit` (short repo hash)
- `stdout_sha256` (hash of verifier stdout)
- `scripts_sha256` (combined hash of verifier scripts)
- `evidence_hash` (sha256 over the above fields)

This makes `pqc.verified` auditable rather than a bare flag.

### Versions / Pinning

- Lean toolchain is pinned by `./lean-toolchain`.
- mathlib revision is pinned in `lean/lakefile.lean` (v4.24.0).
- PQC verifier scripts are checksummed into the sentinel.

## Structure and Sources

- `lean/HeytingLean/LoF/CryptoSheaf/Quantum/**` — site, contexts, empirical model, bridge
- `lean/UnifiedPack/ContextualityAC.lean` — AC exact cardinality proof (separate namespace)
- `lean/HeytingLean/Crypto/FHE/**` — spec-level homomorphic addition hook
- `lean/HeytingLean/Crypto/ZK/**`  — SIS PoK boolean verifier
- `lean/HeytingLean/Crypto/Lattice/**` — lattice prerequisites

### Diagrams (Optional)

Generate UMAP embeddings of the proof graph (requires python packages `umap-learn`, `numpy`, `matplotlib`, `plotly`):

```bash
make diagrams
# outputs docs/proof_graph.json, docs/umap2d.png, docs/umap3d.html
```

## Security/Portability

- Lean code does not perform network activity.
- No file writes except PQC sentinel (`.artifacts/`) by the full script.
- External PQC validators should be audited independently.

## Repack to a New Repo

```bash
git init
git add .
git commit -m "unified demo pack"
git remote add origin <new_repo>
git push -u origin main
```
