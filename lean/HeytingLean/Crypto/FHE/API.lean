import Lean
import HeytingLean.Crypto.FHE.Params
import HeytingLean.Crypto.FHE.Ciphertext
import HeytingLean.Crypto.FHE.Core

namespace HeytingLean.Crypto.FHE.API

open Lean (Json)
open HeytingLean.Crypto.FHE

structure KeyJson where
  p : Nat
deriving Repr

namespace KeyJson
def toJson (k : KeyJson) : Json := Json.mkObj [ ("p", Json.num (Int.ofNat k.p)) ]
def ofJson (j : Json) : Except String KeyJson := do
  let o ← j.getObj?
  let pj ← match o.get? "p" with | some x => .ok x | none => .error "missing p"
  let p ← pj.getNat?
  pure { p }
end KeyJson

def parseIntish (s : String) : Except String Int :=
  match s.toInt? with | some i => .ok i | none => .error s

def exToIO {α} (e : Except String α) : IO α :=
  match e with | .ok a => pure a | .error e => throw <| IO.userError e

def readAllStdin : IO String := do let h ← IO.getStdin; h.readToEnd

def handle (j : Json) : IO Json := do
  let o ← exToIO (j.getObj?)
  let cmd ← match o.get? "cmd" with | some x => pure x | none => throw <| IO.userError "missing cmd"
  let cmdStr ← exToIO (cmd.getStr?)
  let verbose := match o.get? "verbose" with
                 | some j => (match j.getBool? with | .ok b => b | .error _ => false)
                 | none => false
  match cmdStr with
  | "keygen" =>
      let secBits := match o.get? "secBits" with | some j => (match j.getNat? with | .ok n => n | .error _ => 80) | none => 80
      let key : KeyJson := { p := defaultParams.p }
      pure <| Json.mkObj [ ("key", KeyJson.toJson key), ("secBits", Json.num (Int.ofNat secBits)) ]
  | "enc" =>
      let ptNat := match o.get? "pt" with | some j => (match j.getNat? with | .ok n => n | .error _ => 0) | none => 0
      let some keyJ := o.get? "key" | throw <| IO.userError "missing key"
      let kj ← exToIO (KeyJson.ofJson keyJ)
      let k : Key := { p := kj.p }
      let c := enc k (ptNat ≠ 0)
      let base := #[ ("c", Json.num c.val) ]
      if verbose then
        pure <| Json.mkObj ((base.push ("noise", Json.num c.noise)).push ("pt", Json.bool (dec k c)) |>.toList)
      else
        pure <| Json.mkObj base.toList
  | "add" =>
      let some c1j := o.get? "c1" | throw <| IO.userError "missing c1"
      let some c2j := o.get? "c2" | throw <| IO.userError "missing c2"
      let c1s := match c1j.getStr? with | .ok s => s | .error _ => toString (match c1j.getInt? with | .ok i => i | .error _ => 0)
      let c2s := match c2j.getStr? with | .ok s => s | .error _ => toString (match c2j.getInt? with | .ok i => i | .error _ => 0)
      match parseIntish c1s, parseIntish c2s with
      | .ok i1, .ok i2 =>
          let c := add {val := i1, noise := 0} {val := i2, noise := 0}
          pure <| Json.mkObj [ ("c", Json.num c.val) ]
      | .error s, _ => throw <| IO.userError s
      | _, .error s => throw <| IO.userError s
  | "mul" =>
      let some c1j := o.get? "c1" | throw <| IO.userError "missing c1"
      let some c2j := o.get? "c2" | throw <| IO.userError "missing c2"
      let c1s := match c1j.getStr? with | .ok s => s | .error _ => toString (match c1j.getInt? with | .ok i => i | .error _ => 0)
      let c2s := match c2j.getStr? with | .ok s => s | .error _ => toString (match c2j.getInt? with | .ok i => i | .error _ => 0)
      match parseIntish c1s, parseIntish c2s with
      | .ok i1, .ok i2 =>
          let c := mul {val := i1, noise := 0} {val := i2, noise := 0}
          let base := #[ ("c", Json.num c.val) ]
          if verbose then
            pure <| Json.mkObj (base.push ("noise", Json.num c.noise) |>.toList)
          else
            pure <| Json.mkObj base.toList
      | .error s, _ => throw <| IO.userError s
      | _, .error s => throw <| IO.userError s
  | "dec" =>
      let some cj := o.get? "c" | throw <| IO.userError "missing c"
      let cs := match cj.getStr? with | .ok s => s | .error _ => toString (match cj.getInt? with | .ok i => i | .error _ => 0)
      let some keyJ := o.get? "key" | throw <| IO.userError "missing key"
      let kj ← exToIO (KeyJson.ofJson keyJ)
      match parseIntish cs with
      | .ok i =>
          let k : Key := { p := kj.p }
          let b := dec k { val := i, noise := 0 }
          pure <| Json.mkObj [ ("pt", Json.bool b) ]
      | .error s => throw <| IO.userError s
  | "boot" =>
      let some cj := o.get? "c" | throw <| IO.userError "missing c"
      let cs := match cj.getStr? with | .ok s => s | .error _ => toString (match cj.getInt? with | .ok i => i | .error _ => 0)
      let n0 := match o.get? "noise" with | some j => (match j.getNat? with | .ok n => n | .error _ => 0) | none => 0
      match parseIntish cs with
      | .ok i =>
          let c := boot {p := defaultParams.p} { val := i, noise := n0 }
          let base := #[ ("c", Json.num c.val) ]
          if verbose then
            pure <| Json.mkObj (base.push ("noise", Json.num c.noise) |>.toList)
          else
            pure <| Json.mkObj base.toList
      | .error s => throw <| IO.userError s
  | "info" =>
      let some cj := o.get? "c" | throw <| IO.userError "missing c"
      let cs := match cj.getStr? with | .ok s => s | .error _ => toString (match cj.getInt? with | .ok i => i | .error _ => 0)
      let n0 := match o.get? "noise" with | some j => (match j.getNat? with | .ok n => n | .error _ => 0) | none => 0
      match parseIntish cs with
      | .ok i =>
          let k : Key := { p := defaultParams.p }
          let parity := dec k { val := i, noise := n0 }
          let nref := Nat.min n0 defaultParams.B0
          pure <| Json.mkObj [ ("c", Json.num i), ("noise", Json.num n0), ("pt", Json.bool parity), ("refreshedNoise", Json.num nref) ]
      | .error s => throw <| IO.userError s
  | "addn" =>
      let some c1j := o.get? "c1" | throw <| IO.userError "missing c1"
      let some c2j := o.get? "c2" | throw <| IO.userError "missing c2"
      let c1s := match c1j.getStr? with | .ok s => s | .error _ => toString (match c1j.getInt? with | .ok i => i | .error _ => 0)
      let c2s := match c2j.getStr? with | .ok s => s | .error _ => toString (match c2j.getInt? with | .ok i => i | .error _ => 0)
      let n1 := match o.get? "n1" with | some j => (match j.getNat? with | .ok n => n | .error _ => 0) | none => 0
      let n2 := match o.get? "n2" with | some j => (match j.getNat? with | .ok n => n | .error _ => 0) | none => 0
      match parseIntish c1s, parseIntish c2s with
      | .ok i1, .ok i2 =>
          let c := add {val := i1, noise := n1} {val := i2, noise := n2}
          pure <| Json.mkObj [ ("c", Json.num c.val), ("noise", Json.num c.noise) ]
      | .error s, _ => throw <| IO.userError s
      | _, .error s => throw <| IO.userError s
  | "muln" =>
      let some c1j := o.get? "c1" | throw <| IO.userError "missing c1"
      let some c2j := o.get? "c2" | throw <| IO.userError "missing c2"
      let c1s := match c1j.getStr? with | .ok s => s | .error _ => toString (match c1j.getInt? with | .ok i => i | .error _ => 0)
      let c2s := match c2j.getStr? with | .ok s => s | .error _ => toString (match c2j.getInt? with | .ok i => i | .error _ => 0)
      let n1 := match o.get? "n1" with | some j => (match j.getNat? with | .ok n => n | .error _ => 0) | none => 0
      let n2 := match o.get? "n2" with | some j => (match j.getNat? with | .ok n => n | .error _ => 0) | none => 0
      match parseIntish c1s, parseIntish c2s with
      | .ok i1, .ok i2 =>
          let c := mul {val := i1, noise := n1} {val := i2, noise := n2}
          pure <| Json.mkObj [ ("c", Json.num c.val), ("noise", Json.num c.noise) ]
      | .error s, _ => throw <| IO.userError s
      | _, .error s => throw <| IO.userError s
  | _ => throw <| IO.userError s!"unknown cmd: {cmdStr}"

/-- C-callable: evaluate JSON (bytes) -> JSON (bytes). -/
@[export apmt_fhe_eval_json_lean]
def evalJsonBA (ba : ByteArray) : IO ByteArray := do
  let s := String.fromUTF8! ba
  match Json.parse s with
  | .ok j =>
      let out ← handle j
      pure <| (out.compress).toUTF8
  | .error e =>
      pure <| s!"json error: {e}".toUTF8

/-- C-callable: evaluate JSON (string) -> JSON (string). -/
@[export apmt_fhe_eval_string]
def evalJsonStr (s : String) : IO String := do
  match Json.parse s with
  | .ok j =>
      let out ← handle j
      pure <| out.compress
  | .error e =>
      pure <| s!"json error: {e}"

end HeytingLean.Crypto.FHE.API
