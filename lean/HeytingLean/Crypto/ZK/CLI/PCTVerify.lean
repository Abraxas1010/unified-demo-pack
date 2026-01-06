import Lean
import Lean.Data.Json
import HeytingLean.Crypto.Form
import HeytingLean.Crypto.ZK.R1CS
import HeytingLean.Crypto.ZK.Support
import HeytingLean.Crypto.ZK.Export
import HeytingLean.Crypto.ZK.R1CSBool
import HeytingLean.Crypto.BoolLens
import HeytingLean.Crypto.ZK.CLI.PCTR1CS

namespace HeytingLean
namespace Crypto
namespace ZK
namespace CLI
namespace PCTVerify

open IO
open Lean
open BoolLens
open R1CSBool

/-- Try to read a file, returning an explanatory error string on failure. -/
def readFileE (path : System.FilePath) : IO (Except String String) := do
  try
    let s ← FS.readFile path
    pure (.ok s)
  catch e =>
    pure (.error s!"read error at {path}: {e}")

def main (args : List String) : IO UInt32 := do
  match args with
  | [formPath, envPath, r1csPath, witnessPath] =>
      let formRaw ← match (← readFileE formPath) with | .ok s => pure s | .error msg => eprintln msg; return 1
      let envRaw  ← match (← readFileE envPath) with | .ok s => pure s | .error msg => eprintln msg; return 1
      let r1csRaw ← match (← readFileE r1csPath) with | .ok s => pure s | .error msg => eprintln msg; return 1
      let witRaw  ← match (← readFileE witnessPath) with | .ok s => pure s | .error msg => eprintln msg; return 1
      let formJson ← match Json.parse formRaw with | .ok j => pure j | .error err => eprintln err; return 1
      let envJson  ← match Json.parse envRaw  with | .ok j => pure j | .error err => eprintln err; return 1
      let sysJson  ← match Json.parse r1csRaw with | .ok j => pure j | .error err => eprintln err; return 1
      let asJson   ← match Json.parse witRaw  with | .ok j => pure j | .error err => eprintln err; return 1
      let n := match envJson.getArr? with | .ok a => a.size | .error _ => 0
      let formJ ← match CLI.PCTR1CS.FormJ.fromJsonE formJson with | .ok f => pure f | .error err => eprintln err; return 1
      let some φ := CLI.PCTR1CS.FormJ.toForm? n formJ | do eprintln s!"Form contains var ≥ n={n}"; return 1
      let ρ ← match CLI.PCTR1CS.parseEnvE n envJson with | .ok r => pure r | .error err => eprintln err; return 1
      let some sys := Export.jsonToSystem sysJson | do eprintln "Bad system"; return 1
      let some arr := Export.jsonToAssignment asJson | do eprintln "Bad assignment"; return 1
      -- domain check: ensure assignment covers all vars in system
      -- compute maxVar by scanning constraints (Boolean-friendly)
      let maxVar := sys.constraints.foldl (init := 0) (fun m c =>
        let step := fun acc (ts : List (ZK.Var × ℚ)) => ts.foldl (fun a p => Nat.max a p.fst) acc
        let m1 := step 0 c.A.terms
        let m2 := step m1 c.B.terms
        let m3 := step m2 c.C.terms
        Nat.max m m3)
      if arr.size ≤ maxVar then
        eprintln s!"Witness too small, needs ≥ {maxVar+1}, got {arr.size}"
        return 1
      let assign := Export.assignmentOfArray arr
      -- Check satisfaction (Boolean check over constraints)
      let okSat : Bool :=
        sys.constraints.all (fun c =>
          ((c.A.eval assign) * (c.B.eval assign)) == (c.C.eval assign))
      if ¬ okSat then
        eprintln "R1CS not satisfied by witness"
        return 1
      -- Check output alignment against recomputed compiled output
      let compiled := R1CSBool.compile φ ρ
      let expected := compiled.output
      let actual := assign expected
      let want := if BoolLens.eval φ ρ then (1 : ℚ) else 0
      if actual ≠ want then
        eprintln s!"Output mismatch: witness[{expected}]={actual}, expected {want}"
        return 1
      println "ok"
      return 0
  | [formPath, envPath, r1csPath, witnessPath, metaPath] =>
      let formRaw ← match (← readFileE formPath) with | .ok s => pure s | .error msg => eprintln msg; return 1
      let envRaw  ← match (← readFileE envPath) with | .ok s => pure s | .error msg => eprintln msg; return 1
      let r1csRaw ← match (← readFileE r1csPath) with | .ok s => pure s | .error msg => eprintln msg; return 1
      let witRaw  ← match (← readFileE witnessPath) with | .ok s => pure s | .error msg => eprintln msg; return 1
      let metaRaw ← match (← readFileE metaPath) with | .ok s => pure s | .error msg => eprintln msg; return 1
      let formJson ← match Json.parse formRaw with | .ok j => pure j | .error err => eprintln err; return 1
      let envJson  ← match Json.parse envRaw  with | .ok j => pure j | .error err => eprintln err; return 1
      let sysJson  ← match Json.parse r1csRaw with | .ok j => pure j | .error err => eprintln err; return 1
      let asJson   ← match Json.parse witRaw  with | .ok j => pure j | .error err => eprintln err; return 1
      let metaJson ← match Json.parse metaRaw with | .ok j => pure j | .error err => eprintln err; return 1
      let n := match envJson.getArr? with | .ok a => a.size | .error _ => 0
      let formJ ← match CLI.PCTR1CS.FormJ.fromJsonE formJson with | .ok f => pure f | .error err => eprintln err; return 1
      let some φ := CLI.PCTR1CS.FormJ.toForm? n formJ | do eprintln s!"Form contains var ≥ n={n}"; return 1
      let ρ ← match CLI.PCTR1CS.parseEnvE n envJson with | .ok r => pure r | .error err => eprintln err; return 1
      let some sys := Export.jsonToSystem sysJson | do eprintln "Bad system"; return 1
      let some arr := Export.jsonToAssignment asJson | do eprintln "Bad assignment"; return 1
      -- Check satisfaction and output alignment (reuse 4-arg branch logic)
      let maxVar := sys.constraints.foldl (init := 0) (fun m c =>
        let step := fun acc (ts : List (ZK.Var × ℚ)) => ts.foldl (fun a p => Nat.max a p.fst) acc
        let m1 := step 0 c.A.terms
        let m2 := step m1 c.B.terms
        let m3 := step m2 c.C.terms
        Nat.max m m3)
      if arr.size ≤ maxVar then
        eprintln s!"Witness too small, needs ≥ {maxVar+1}, got {arr.size}"
        return 1
      let assign := Export.assignmentOfArray arr
      let okSat : Bool :=
        sys.constraints.all (fun c =>
          ((c.A.eval assign) * (c.B.eval assign)) == (c.C.eval assign))
      if ¬ okSat then
        eprintln "R1CS not satisfied by witness"
        return 1
      let compiled := R1CSBool.compile φ ρ
      let expected := compiled.output
      let actual := assign expected
      let want := if BoolLens.eval φ ρ then (1 : ℚ) else 0
      if actual ≠ want then
        eprintln s!"Output mismatch: witness[{expected}]={actual}, expected {want}"
        return 1
      -- Enforce policy hash if present in meta
      -- Rebuild canonical form string and simple hash (same as PCTProve)
      let canonString : CLI.PCTR1CS.FormJ → String :=
        let rec go (f : CLI.PCTR1CS.FormJ) : String :=
          match f with
          | .top => "top"
          | .bot => "bot"
          | .var i => s!"v:{i}"
          | .and a b => s!"and({go a},{go b})"
          | .or a b  => s!"or({go a},{go b})"
          | .imp a b => s!"imp({go a},{go b})"
        go
      let m : Nat := Nat.pow 2 64
      let simpleHash64 (s : String) : String :=
        let h := s.data.foldl (fun acc ch => (acc * 1315423911 + ch.toNat) % m) 1469598103934665603
        toString h
      let canon := canonString formJ
      let wantHash := simpleHash64 canon
      match metaJson.getObjVal? "policyHash" with
      | .ok j =>
          match j.getStr? with
          | .ok s =>
              if s ≠ wantHash then
                eprintln s!"policyHash mismatch: meta={s}, expected={wantHash}"; return 1
              else pure ()
          | .error _ => pure ()
      | .error _ => pure ()
      println "ok"
      return 0
  | _ =>
      eprintln "Usage: lake exe pct_verify <form.json> <env.json> <r1cs.json> <witness.json>"
      return 1

end PCTVerify
end CLI
end ZK
end Crypto
end HeytingLean

-- Provide a top-level main alias for the executable linker
open HeytingLean.Crypto.ZK.CLI.PCTVerify in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Crypto.ZK.CLI.PCTVerify.main args
