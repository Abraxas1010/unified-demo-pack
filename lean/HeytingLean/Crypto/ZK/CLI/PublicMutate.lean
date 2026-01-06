import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args

namespace HeytingLean
namespace Crypto
namespace ZK
namespace CLI

open Lean

private def readFileE (p : System.FilePath) : IO (Except String String) := do
  try let s ← IO.FS.readFile p; pure (.ok s) catch e => pure (.error s!"read error at {p}: {e}")

def setOutputIndex (pubPath outPath : System.FilePath) (idx : Nat) : IO UInt32 := do
  let raw ← match (← readFileE pubPath) with | .ok s => pure s | .error m => IO.eprintln m; return 1
  let j ← match Json.parse raw with | .ok j => pure j | .error e => IO.eprintln e; return 1
  match j with
  | .obj kv =>
      let kv' := kv.insert "output_index" (Json.num idx)
      IO.FS.writeFile outPath (Json.obj kv' |>.compress); return 0
  | _ => IO.eprintln "public not object"; return 1

def setEnvIndices (pubPath outPath : System.FilePath) (idxs : List Nat) : IO UInt32 := do
  let raw ← match (← readFileE pubPath) with | .ok s => pure s | .error m => IO.eprintln m; return 1
  let j ← match Json.parse raw with | .ok j => pure j | .error e => IO.eprintln e; return 1
  match j with
  | .obj kv =>
      let ja : Array Json := (idxs.map (fun (n : Nat) => Json.num n)).toArray
      let arrJ : Json := Json.arr ja
      let kv' := kv.insert "env_indices" arrJ
      IO.FS.writeFile outPath (Json.obj kv' |>.compress); return 0
  | _ => IO.eprintln "public not object"; return 1

def delEnvIndices (pubPath outPath : System.FilePath) : IO UInt32 := do
  let raw ← match (← readFileE pubPath) with | .ok s => pure s | .error m => IO.eprintln m; return 1
  let j ← match Json.parse raw with | .ok j => pure j | .error e => IO.eprintln e; return 1
  match j with
  | .obj kv =>
      let kv' := kv.erase "env_indices"
      IO.FS.writeFile outPath (Json.obj kv' |>.compress); return 0
  | _ => IO.eprintln "public not object"; return 1

def main (args : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs args
  match args with
  | ["--set-output-index", idxStr, pub, out] =>
      match idxStr.toNat? with
      | some i => setOutputIndex (System.FilePath.mk pub) (System.FilePath.mk out) i
      | none => IO.eprintln "bad index"; return 2
  | ["--set-env", a, b, c, d, pub, out] =>
      let parse := fun s => s.toNat?.getD 0
      setEnvIndices (System.FilePath.mk pub) (System.FilePath.mk out) [parse a, parse b, parse c, parse d]
  | ["--del-env", pub, out] => delEnvIndices (System.FilePath.mk pub) (System.FilePath.mk out)
  | _ => IO.eprintln "usage: public_mutate --set-output-index <idx> <public.json> <out.json> | --set-env <i0> <i1> <i2> <i3> <public.json> <out.json> | --del-env <public.json> <out.json>"; return 2

end CLI
end ZK
end Crypto
end HeytingLean

def main (args : List String) : IO UInt32 := HeytingLean.Crypto.ZK.CLI.main args
