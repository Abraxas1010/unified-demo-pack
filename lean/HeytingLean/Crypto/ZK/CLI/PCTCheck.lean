import Lean
import Lean.Data.Json
import HeytingLean.Crypto.BoolLens
import HeytingLean.Crypto.ZK.R1CSBool
-- import HeytingLean.Crypto.ZK.PlonkIR -- temporarily disabled in CLI
import HeytingLean.Crypto.ZK.AirIR
import HeytingLean.Crypto.ZK.CLI.PCTR1CS

namespace HeytingLean
namespace Crypto
namespace ZK
namespace CLI
namespace PCTCheck

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

private def findOpt (opts : List String) (pref : String) : Option String :=
  match opts.find? (fun s => s.startsWith pref) with
  | none => none
  | some s =>
      let parts := s.splitOn "="
      if parts.length = 2 then some (parts[1]!) else none

def main (args : List String) : IO UInt32 := do
  match args with
  | backend :: formPath :: envPath :: _opts =>
      let formRaw ← match (← readFileE formPath) with | .ok s => pure s | .error msg => eprintln msg; return 1
      let envRaw  ← match (← readFileE envPath) with | .ok s => pure s | .error msg => eprintln msg; return 1
      let formJson ← match Json.parse formRaw with | .ok j => pure j | .error err => eprintln err; return 1
      let envJson  ← match Json.parse envRaw  with | .ok j => pure j | .error err => eprintln err; return 1
      let n := match envJson.getArr? with | .ok a => a.size | .error _ => 0
      let formJ ← match CLI.PCTR1CS.FormJ.fromJsonE formJson with | .ok f => pure f | .error err => eprintln err; return 1
      let some φ := CLI.PCTR1CS.FormJ.toForm? n formJ | do eprintln s!"Form contains var ≥ n={n}"; return 1
      let ρ ← match CLI.PCTR1CS.parseEnvE n envJson with | .ok r => pure r | .error err => eprintln err; return 1
      let compiled := R1CSBool.compile φ ρ
      match backend with
      | "plonk" =>
          eprintln "plonk backend currently disabled in this CLI"
          return 2
      | "air" =>
          -- Build TransitionSet.auto and check satisfiability under compiled assignment (Boolean run)
          let cs := compiled.system.constraints
          let tset := ZK.AIR.TransitionSet.ofSystemAuto cs
          -- Compute booleans for eqs and muls
          let assign := compiled.assignment
          let eqsOk := tset.eqs.all (fun eqp => (eqp.1.eval assign) == (eqp.2.eval assign))
          let mulsOk := tset.muls.all (fun tr => ((tr.1.eval assign) * (tr.2.1.eval assign)) == (tr.2.2.eval assign))
          let r1csOk := cs.all (fun c => ((c.A.eval assign) * (c.B.eval assign)) == (c.C.eval assign))
          let report := Json.mkObj
            [ ("backend", Json.str "air-check")
            , ("eqsCount", Json.num tset.eqs.length)
            , ("mulsCount", Json.num tset.muls.length)
            , ("eqsSatisfied", Json.bool eqsOk)
            , ("mulsSatisfied", Json.bool mulsOk)
            , ("r1csSatisfied", Json.bool r1csOk)
            , ("implicationHint", Json.str "ofSystemAuto_imply_r1cs applies when TransitionSet.satisfied holds")
            ] |>.compress
          println report
          return 0
      | _ =>
          eprintln "Usage: lake exe pct_check (plonk|air) <form.json> <env.json>"
          return 2
  | _ =>
      eprintln "Usage: lake exe pct_check (plonk|air) <form.json> <env.json>"
      return 1

end PCTCheck
end CLI
end ZK
end Crypto
end HeytingLean

-- Provide a top-level main alias for the executable linker
open HeytingLean.Crypto.ZK.CLI.PCTCheck in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Crypto.ZK.CLI.PCTCheck.main args
