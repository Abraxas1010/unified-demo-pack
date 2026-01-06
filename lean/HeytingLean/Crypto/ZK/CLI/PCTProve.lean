import Lean
import Lean.Data.Json
import HeytingLean.Crypto.Form
import HeytingLean.Crypto.ZK.R1CSBool
import HeytingLean.Crypto.ZK.Export
import HeytingLean.Crypto.BoolLens
import HeytingLean.Crypto.ZK.CLI.PCTR1CS

namespace HeytingLean
namespace Crypto
namespace ZK
namespace CLI
namespace PCTProve

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

def writeFile (path : System.FilePath) (content : String) : IO Unit := do
  FS.writeFile path content

private def findOpt (opts : List String) (pref : String) : Option String :=
  match opts.find? (fun s => s.startsWith pref) with
  | none => none
  | some s =>
      let parts := s.splitOn "="
      if parts.length = 2 then some (parts[1]!) else none

def canonString (f : CLI.PCTR1CS.FormJ) : String :=
  match f with
  | .top => "top"
  | .bot => "bot"
  | .var i => s!"v:{i}"
  | .and a b => s!"and({canonString a},{canonString b})"
  | .or a b  => s!"or({canonString a},{canonString b})"
  | .imp a b => s!"imp({canonString a},{canonString b})"

def simpleHash64 (s : String) : String :=
  let m : Nat := Nat.pow 2 64
  let h := s.data.foldl (fun acc ch => (acc * 1315423911 + ch.toNat) % m) 1469598103934665603
  toString h

def main (args : List String) : IO UInt32 := do
  match args with
  | formPath :: envPath :: outDir :: opts =>
      let formRaw ← match (← readFileE formPath) with
        | .ok s => pure s
        | .error msg => eprintln msg; return 1
      let envRaw  ← match (← readFileE envPath) with
        | .ok s => pure s
        | .error msg => eprintln msg; return 1
      let formJson ← match Json.parse formRaw with
        | .ok j => pure j
        | .error err => eprintln err; return 1
      let envJson ← match Json.parse envRaw with
        | .ok j => pure j
        | .error err => eprintln err; return 1
      -- infer n
      let n := match envJson.getArr? with | .ok a => a.size | .error _ => 0
      let formJ ← match CLI.PCTR1CS.FormJ.fromJsonE formJson with
        | .ok f => pure f
        | .error err => eprintln err; return 1
      let some φ := CLI.PCTR1CS.FormJ.toForm? n formJ | do eprintln s!"Form contains var ≥ n={n}"; return 1
      let ρ ← match CLI.PCTR1CS.parseEnvE n envJson with
        | .ok r => pure r
        | .error err => eprintln err; return 1
      let compiled := R1CSBool.compile φ ρ
      -- Write R1CS and witness
      let r1csJson := Export.systemToJson compiled.system |>.compress
      -- compute maximum var index referenced in the system
      let maxVar := compiled.system.constraints.foldl (init := 0) (fun m c =>
        let step := fun acc (ts : List (Var × ℚ)) => ts.foldl (fun a p => Nat.max a p.fst) acc
        let m1 := step 0 c.A.terms
        let m2 := step m1 c.B.terms
        let m3 := step m2 c.C.terms
        Nat.max m m3)
      let numVars := maxVar + 1
      let witnessJson := Export.assignmentToJson compiled.assignment numVars |>.compress
      -- policy metadata (optional flags)
      let policyName := (findOpt opts "--policy-name=").getD "unknown"
      let policyVersion := (findOpt opts "--policy-version=").getD "0"
      let canon := canonString formJ
      let policyHash := (findOpt opts "--policy-hash=").getD (simpleHash64 canon)
      let metaJ := Json.mkObj
        [ ("outputVar", Json.num compiled.output)
        , ("eval", Json.str (toString (BoolLens.eval φ ρ)))
        , ("backend", Json.str "r1cs")
        , ("field", Json.str "prime")
        , ("modulus", Json.str "21888242871839275222246405745257275088548364400416034343698204186575808495617")
        , ("policyName", Json.str policyName)
        , ("policyVersion", Json.str policyVersion)
        , ("policyHash", Json.str policyHash)
        ] |>.compress
      let outR1cs := System.FilePath.mk outDir / "r1cs.json"
      let outWitness := System.FilePath.mk outDir / "witness.json"
      let outMeta := System.FilePath.mk outDir / "meta.json"
      FS.createDirAll (System.FilePath.mk outDir)
      writeFile outR1cs r1csJson
      writeFile outWitness witnessJson
      writeFile outMeta metaJ
      println s!"wrote {outR1cs} {outWitness} {outMeta}"
      return 0
  | _ =>
      eprintln "Usage: lake exe pct_prove <form.json> <env.json> <outdir>"
      return 1

end PCTProve
end CLI
end ZK
end Crypto
end HeytingLean

-- Provide a top-level main alias for the executable linker
open HeytingLean.Crypto.ZK.CLI.PCTProve in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Crypto.ZK.CLI.PCTProve.main args
