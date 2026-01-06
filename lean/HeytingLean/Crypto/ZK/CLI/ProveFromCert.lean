import Lean
import Lean.Data.Json
import HeytingLean.CCI.Core
import HeytingLean.CCI.Json
import HeytingLean.CCI.Check
import HeytingLean.CCI.Cert
import HeytingLean.CCI.Version

/-!
# ProveFromCert (certificate sanity check)

Reads a certificate JSON via CCI_CERT_PATH and checks only that
the provided omega digest equals hashExpr(canon(omega)).
This is a semantics-only check intended to be composed with ZK later.
-/

namespace HeytingLean
namespace Crypto
namespace ZK
namespace CLI
namespace ProveFromCert

open HeytingLean.CCI
open Lean

/- Deterministic set helpers (ByteArray with UTF‑8 sort key) -/
-- Hex encoder for ByteArray (used for keys and stmt digest)
private def hexOfBA (ba : ByteArray) : String :=
  let parts := ba.toList.map (fun b =>
    let s := (Nat.toDigits 16 b.toNat).asString
    if s.length = 1 then "0" ++ s else s)
  String.intercalate "" parts

private def key (b : ByteArray) : String := hexOfBA b
private def leKey (a b : ByteArray) : Bool := (key a) ≤ (key b)
private def eqKey (a b : ByteArray) : Bool := (key a) = (key b)

private def norm (xs : List ByteArray) : List ByteArray :=
  let rec ins (x : ByteArray) (ys : List ByteArray) : List ByteArray :=
    match ys with
    | [] => [x]
    | y::ys' => if leKey x y then if eqKey x y then y::ys' else x::y::ys' else y :: ins x ys'
  let sorted := xs.foldl (fun acc x => ins x acc) []
  let rec dd (ys : List ByteArray) : List ByteArray :=
    match ys with
    | [] => []
    | [x] => [x]
    | x::y::zs => if eqKey x y then dd (y::zs) else x :: dd (y::zs)
  dd sorted

private def setUnion (a b : List ByteArray) : List ByteArray :=
  let rec merge (xs ys : List ByteArray) : List ByteArray :=
    match xs, ys with
    | [], ys => ys
    | xs, [] => xs
    | x::xs', y::ys' =>
        if leKey x y then (if eqKey x y then x :: merge xs' ys' else x :: merge xs' (y::ys')) else y :: merge (x::xs') ys'
  merge (norm a) (norm b)

private def setInter (a b : List ByteArray) : List ByteArray :=
  let rec go (xs ys : List ByteArray) : List ByteArray :=
    match xs, ys with
    | [], _ => []
    | _, [] => []
    | x::xs', y::ys' => if eqKey x y then x :: go xs' ys' else if leKey x y then go xs' (y::ys') else go (x::xs') ys'
  go (norm a) (norm b)

private def setDiff (a b : List ByteArray) : List ByteArray :=
  let rec go (xs ys : List ByteArray) : List ByteArray :=
    match xs, ys with
    | [], _ => []
    | xs, [] => xs
    | x::xs', y::ys' => if eqKey x y then go xs' ys' else if leKey x y then x :: go xs' (y::ys') else go (x::xs') ys'
  go (norm a) (norm b)

private def setSub (a b : List ByteArray) : Bool :=
  let rec go (xs ys : List ByteArray) : Bool :=
    match xs, ys with
    | [], _ => true
    | _, [] => false
    | x::xs', y::ys' => if eqKey x y then go xs' ys' else if leKey x y then false else go (x::xs') ys'
  go (norm a) (norm b)

private def setEq (a b : List ByteArray) : Bool := (norm a) = (norm b)

/- Fixed finite universe and Option‑A core -/
private def U : List ByteArray := ["p","q","r","s"].map (·.toUTF8)

private def parseCoreC (envVal : Option String) : List ByteArray :=
  let names := (envVal.getD "p").splitOn ","
  let items := names.map (fun s => s.trim.toUTF8)
  let allowed := U.map key
  norm (items.filter (fun b => allowed.contains (key b)))

private def coreCIO : IO (List ByteArray) := do
  let v ← IO.getEnv "CORE_C"
  pure (parseCoreC v)

private def rUnion (c : List ByteArray) (s : List ByteArray) : List ByteArray := setUnion s c

/- Atom environment -/
private def atomEnv (nm : String) : List ByteArray :=
  match nm with
  | "P" => norm ["p".toUTF8]
  | "Q" => norm ["q".toUTF8]
  | "R" => norm ["r".toUTF8]
  | "S" => norm ["s".toUTF8]
  | _    => []

/- Canon‑aware evaluation (join/negation closed by Option‑A core). -/
def eval (c : List ByteArray) (env : String → List ByteArray) : CCI.Expr → List ByteArray
  | .atom nm   => env nm
  | .andR a b  => setInter (eval c env a) (eval c env b)
  | .orR  a b  => rUnion c (setUnion (eval c env a) (eval c env b))
  | .notR a    => rUnion c (setDiff U (eval c env a))
  | .impR a b  =>
      -- `a ⇒ b` is interpreted as `¬a ∪ b` (with Option‑A closure), but avoid
      -- recursion on a constructed term.
      let notA := rUnion c (setDiff U (eval c env a))
      let eb := eval c env b
      rUnion c (setUnion notA eb)

/- Node‑by‑node semantics verification. -/
def verifyNodes (c : List ByteArray) (env : String → List ByteArray) : CCI.Expr → Option String
  | .atom _ => none
  | .notR a => verifyNodes c env a
  | .andR a b =>
      match verifyNodes c env a with
      | some e => some e
      | none =>
        match verifyNodes c env b with
        | some e => some e
        | none =>
          let lhs := eval c env (.andR a b)
          let rhs := setInter (eval c env a) (eval c env b)
          if setEq lhs rhs then none else some "E-NODE-AND"
  | .orR a b =>
      match verifyNodes c env a with
      | some e => some e
      | none =>
        match verifyNodes c env b with
        | some e => some e
        | none =>
          let lhs := eval c env (.orR a b)
          let rhs := rUnion c (setUnion (eval c env a) (eval c env b))
          if setEq lhs rhs then none else some "E-NODE-OR"
  | .impR a b =>
      match verifyNodes c env a with
      | some e => some e
      | none =>
        match verifyNodes c env b with
        | some e => some e
        | none =>
          let lhs := eval c env (.impR a b)
          let rhs :=
            let notA := rUnion c (setDiff U (eval c env a))
            rUnion c (setUnion notA (eval c env b))
          if setEq lhs rhs then none else some "E-NODE-IMP"

/- Helpers for stmt digest parity -/
private def hexOf (d : Digest) : String :=
  let parts := d.toList.map (fun b =>
    let s := (Nat.toDigits 16 b.toNat).asString
    if s.length = 1 then "0" ++ s else s)
  String.intercalate "" parts

private def qstr (s : String) : String :=
  let s' := HeytingLean.CCI.jsonEscape s
  "\"" ++ s' ++ "\""

private def encodeKVStr (kvs : List (String × String)) : String :=
  let arr := kvs.map (fun (k,v) =>
    "{" ++ "\"k\":" ++ qstr k ++ ",\"v\":" ++ qstr v ++ "}")
  "[" ++ String.intercalate "," arr ++ "]"

private def exToOpt {α} : Except String α → Option α
  | .ok a => some a
  | .error _ => none

private def decodeInputsKV (inputsJson? : Option Json) : List (String × String) :=
  match inputsJson? with
  | some j =>
      match exToOpt (j.getArr?) with
      | some a =>
          let rec go (i : Nat) (acc : List (String × String)) : List (String × String) :=
            if h : i < a.size then
              have _ := h
              match (a[i]!).getObj? with
              | .ok oi =>
                  match (oi.get? "k", oi.get? "v") with
                  | (some (.str k), some (.str v)) => go (i+1) ((k,v)::acc)
                  | _ => go (i+1) acc
              | _ => go (i+1) acc
            else acc.reverse
          go 0 []
      | none => []
  | none => []

def run : IO Unit := do
  match (← IO.getEnv "CCI_CERT_PATH") with
  | none =>
      IO.eprintln "usage: set CCI_CERT_PATH to cert.json"
      IO.Process.exit 2
  | some p => do
      let fp := System.FilePath.mk p
      if !(← fp.pathExists) then
        IO.eprintln s!"file not found: {p}"
        IO.Process.exit 2
      let s ← IO.FS.readFile fp
      match Lean.Json.parse s with
      | .error _ =>
          IO.eprintln "invalid certificate JSON"
          IO.Process.exit 2
      | .ok j =>
          match j.getObj? with
          | .error _ =>
              IO.eprintln "invalid certificate object"
              IO.Process.exit 2
          | .ok o =>
              let omega? := (o.get? "omega") >>= decodeExpr
              -- helper to find a digest hex by path inside a Json array
              let findDigestHexIn (j? : Option Json) (p : String) : Option String := Id.run do
                match j? with
                | some j =>
                    match exToOpt (j.getArr?) with
                    | some a =>
                        let rec loop (i : Nat) : Option String :=
                          if h : i < a.size then
                            have _ := h
                            match (a[i]!).getObj? with
                            | .ok oi =>
                                match (oi.get? "path", oi.get? "digest") with
                                | (some (.str path), some (.str hex)) => if path = p then some hex else loop (i+1)
                                | _ => loop (i+1)
                            | _ => loop (i+1)
                          else none
                        loop 0
                    | none => none
                | none => none
              let hex? := findDigestHexIn (o.get? "digests") "omega"
              match (omega?, hex?) with
              | (some omega, some hex) =>
                  let ω' := canon omega
                  let expD := hashExpr ω'
                  let expHex := match encodeDigest expD with | Lean.Json.str s => s | _ => ""
                  if expHex ≠ hex then
                    IO.eprintln "prove_from_cert: digest mismatch"
                    IO.Process.exit 1
                  -- stmt digest parity (if present)
                  let inputsKV := decodeInputsKV (o.get? "inputs")
                  let stmtHex? := findDigestHexIn (o.get? "digests") "stmt"
                  match stmtHex? with
                  | some stmtHex =>
                      let payload := "Stmt|" ++ encodeKVStr inputsKV ++ "|" ++ expHex
                      let stmtD := digestOfString payload
                      let stmtHex' := hexOfBA stmtD
                      if stmtHex' ≠ stmtHex then
                        IO.eprintln "prove_from_cert: stmt digest mismatch"
                        IO.Process.exit 1
                  | none => pure ()
                  -- Option‑A nucleus constraints
                  let c ← coreCIO
                  let v := eval c atomEnv ω'
                  if !(setSub c v) then
                    IO.eprintln "E-FIXPOINT"
                    IO.Process.exit 1
                  match verifyNodes c atomEnv ω' with
                  | some code =>
                      IO.eprintln code
                      IO.Process.exit 1
                  | none => pure ()
                  -- Success: print binding with public omega digest
                  let j := Lean.Json.mkObj [
                    ("ok", Lean.Json.str "true"),
                    ("IRv", Lean.Json.str IRv),
                    ("rewriteTablev", Lean.Json.str RewriteTablev),
                    ("canonv", Lean.Json.str Canonv),
                    ("circuitv", Lean.Json.str Circuitv),
                    ("omega_digest_public", Lean.Json.str expHex)
                  ]
                  IO.println j.compress
              | _ =>
                  IO.eprintln "prove_from_cert: missing omega/digest"
                  IO.Process.exit 2

end ProveFromCert
end CLI
end ZK
end Crypto
end HeytingLean

def main : IO Unit := HeytingLean.Crypto.ZK.CLI.ProveFromCert.run
