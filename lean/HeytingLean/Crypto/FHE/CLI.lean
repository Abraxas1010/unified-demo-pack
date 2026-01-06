import Lean
import HeytingLean.Crypto.FHE.API

open Lean (Json)

open IO

open HeytingLean.Crypto.FHE.API

def main (args : List String) : IO UInt32 := do
  let useStdin := args.contains "--stdin"
  let inFile := Id.run <|
    match args with
    | _ :: "--input" :: f :: _ => some f
    | _ => none
  let input ← match inFile with
    | some f => do IO.FS.readFile f
    | none => if useStdin then readAllStdin else pure "{}"
  match Json.parse input with
  | .ok j =>
      let out ← handle j
      IO.println (out.compress)
      pure 0
  | .error e =>
      IO.eprintln s!"json error: {e}"
      pure 1
