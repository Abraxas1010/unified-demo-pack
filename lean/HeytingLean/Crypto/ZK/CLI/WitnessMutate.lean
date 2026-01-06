import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.Crypto.ZK.Export

namespace HeytingLean
namespace Crypto
namespace ZK
namespace CLI

open Lean

private def readFileE (p : System.FilePath) : IO (Except String String) := do
  try let s ← IO.FS.readFile p; pure (.ok s) catch e => pure (.error s!"read error at {p}: {e}")

def setIndex (arr : Array Json) (i : Nat) (val : String) : Array Json :=
  if i < arr.size then arr.set! i (Json.str val) else arr

def mutateSet (witPath outPath : System.FilePath) (idx : Nat) (val : String) : IO UInt32 := do
  let raw ← match (← readFileE witPath) with | .ok s => pure s | .error m => IO.eprintln m; return 1
  let j ← match Json.parse raw with | .ok j => pure j | .error e => IO.eprintln e; return 1
  let arr ← match j.getArr? with | .ok a => pure a | .error _ => IO.eprintln "witness not array"; return 1
  let arr' := setIndex arr idx val
  IO.FS.writeFile outPath (Json.arr arr' |>.compress)
  return 0

def mutateSwapEnv (witPath pubPath outPath : System.FilePath) : IO UInt32 := do
  let wraw ← match (← readFileE witPath) with | .ok s => pure s | .error m => IO.eprintln m; return 1
  let praw ← match (← readFileE pubPath) with | .ok s => pure s | .error m => IO.eprintln m; return 1
  let wJ ← match Json.parse wraw with | .ok j => pure j | .error e => IO.eprintln e; return 1
  let pJ ← match Json.parse praw with | .ok j => pure j | .error e => IO.eprintln e; return 1
  let arr ← match wJ.getArr? with | .ok a => pure a | .error _ => IO.eprintln "witness not array"; return 1
  let envIdxs : List Nat :=
    match pJ.getObjVal? "env_indices" with
    | .ok (.arr a) => a.toList.map (fun jj => match jj.getNat? with | .ok n => n | .error _ => 0)
    | _ => []
  match envIdxs with
  | i0 :: i1 :: _ =>
      if i0 < arr.size then
        if i1 < arr.size then
          let v0 := arr[i0]!
          let v1 := arr[i1]!
          let arr1 := arr.set! i0 v1
          let arr2 := arr1.set! i1 v0
          IO.FS.writeFile outPath (Json.arr arr2 |>.compress); return 0
        else IO.eprintln "env index 1 out of bounds"; return 1
      else IO.eprintln "env index 0 out of bounds"; return 1
  | _ => IO.eprintln "not enough env_indices"; return 1

def main (args : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs args
  match args with
  | ["--set", idxStr, val, wit, out] =>
      match idxStr.toNat? with
      | some i => mutateSet (System.FilePath.mk wit) (System.FilePath.mk out) i val
      | none => IO.eprintln "bad index"; return 2
  | ["--swap-env", wit, pub, out] =>
      mutateSwapEnv (System.FilePath.mk wit) (System.FilePath.mk pub) (System.FilePath.mk out)
  | _ => IO.eprintln "usage: mutate_witness --set <idx> <val> <witness.json> <out.json> | --swap-env <witness.json> <public.json> <out.json>"; return 2

end CLI
end ZK
end Crypto
end HeytingLean

def main (args : List String) : IO UInt32 := HeytingLean.Crypto.ZK.CLI.main args
