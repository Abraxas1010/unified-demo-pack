import Lean.Data.Json
import HeytingLean.Bridges.Emergence
import HeytingLean.Exec.Emergence.SelectMain

/-
# Emergence certificates (semantics-first)

This module provides a small, semantics-level certificate format for
the Emergence Selector.  It is intentionally simple and does **not**
encode any R1CS or SNARK backend; instead it:

* reuses the selector report shape from `Exec.Emergence.SelectMain`,
* checks that candidate partitions are well-formed and that the
  chosen index is in-bounds (delegating to the existing validator),
* packages the report together with a version tag and a simple
  textual digest.

The goal is to make Emergence selection **proof-carrying** at the
JSON/TCB boundary, while leaving any heavy ZK/R1CS encoding to
future layers that can build on this honest, structural core.
-/

namespace HeytingLean
namespace Crypto
namespace ZK
namespace EmergenceCert

open Lean
open Lean.Json
open HeytingLean.Bridges
open HeytingLean.Bridges.Emergence
open HeytingLean.Exec.Emergence

/-- Reuse the selector report type from the executable. -/
abbrev SelectorReport :=
  HeytingLean.Exec.Emergence.SelectMain.Report

/-- A minimal emergence certificate: selector report plus a human-
readable version tag and a simple digest string.  The `digest` is
currently a plain hash of the JSON payload computed outside Lean;
this keeps the format flexible while remaining honest about what
is and is not checked here. -/
structure Cert where
  version : String
  report  : SelectorReport
  digest  : String
  deriving Repr

/-- Encode a selector report back to JSON.  This mirrors the schema
emitted by `tools/emergence/selector.py` so that certificates can
round-trip cleanly. -/
def reportToJson (r : SelectorReport) : Json :=
  let mkNum (n : Nat) : Json := Json.num (n : Nat)
  let mkFloat (f : Float) : Json := Json.str (toString f)
  let candJson : Json :=
    Json.arr <|
      (r.candidates.map fun π =>
        Json.arr <|
          (π.map fun block =>
            Json.arr ((block.map fun i => mkNum i).toArray)
          ).toArray
      ).toArray
  Json.mkObj
    [ ("version", Json.str "EmergenceSelector.v1")
    , ("n", mkNum r.n)
    , ("candidates", candJson)
    , ("chosen", mkNum r.chosen)
    , ("deltaCP",
        Json.arr (r.deltaCP.map (fun f => mkFloat f)).toArray)
    , ("S_path", mkFloat r.S_path)
    , ("S_row", mkFloat r.S_row)
    , ("regime", Json.str r.regime)
    ]

/-- Encode an emergence certificate as JSON.  The certificate nests the
selector report under a `report` field and carries a separate digest
string so that external systems can bind additional integrity checks. -/
def toJson (c : Cert) : Json :=
  Json.mkObj
    [ ("version", Json.str c.version)
    , ("digest", Json.str c.digest)
    , ("report", reportToJson c.report)
    ]

/-- Decode an emergence certificate from JSON, reusing the selector
report parser from `Exec.Emergence.SelectMain`. -/
def fromJson (j : Json) : Except String Cert := do
  let obj ←
    match j.getObj? with
    | .ok _ => pure j
    | .error _ => .error "expected object"
  let version ←
    match obj.getObjVal? "version" with
    | .ok v =>
        match v.getStr? with
        | .ok s => pure s
        | .error _ => .error "field 'version' not a String"
    | .error _ => .error "missing field 'version'"
  let digest ←
    match obj.getObjVal? "digest" with
    | .ok v =>
        match v.getStr? with
        | .ok s => pure s
        | .error _ => .error "field 'digest' not a String"
    | .error _ => .error "missing field 'digest'"
  let reportJson ←
    match obj.getObjVal? "report" with
    | .ok v => pure v
    | .error _ => .error "missing field 'report'"
  let report ←
    match Exec.Emergence.SelectMain.parseReport reportJson with
    | .ok r => pure r
    | .error msg => .error s!"invalid report: {msg}"
  pure { version, report, digest }

/-- Structural validation of an emergence certificate.  This checks
only that the embedded report passes the selector's internal
partition/choice validation; any external digest or ZK checks are
left to higher layers. -/
def valid (c : Cert) : Bool :=
  match Exec.Emergence.SelectMain.validate c.report with
  | .ok => true
  | .error _ => false

/-- Convenience: emit a JSON certificate to stdout from an already
parsed selector report and an arbitrary digest string.  The digest
is treated opaquely here and can be bound by external systems
to whatever hash or commitment they require. -/
def emitEmergenceCert (version : String) (digest : String)
    (r : SelectorReport) : IO Unit := do
  let cert : Cert := { version, report := r, digest := digest }
  IO.println (toJson cert).compress

/-- Check a JSON certificate string for structural validity.  Returns
`true` exactly when the embedded selector report passes the same
partition checks as `emergence_select_check`. -/
def verifyEmergenceCert (raw : String) : IO Bool := do
  match Json.parse raw with
  | .error _ => pure false
  | .ok j =>
      match fromJson j with
      | .error _ => pure false
      | .ok cert => pure (valid cert)

end EmergenceCert
end ZK
end Crypto
end HeytingLean
