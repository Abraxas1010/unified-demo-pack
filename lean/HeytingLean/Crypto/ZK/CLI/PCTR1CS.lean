import Lean
import Lean.Data.Json
import HeytingLean.Crypto.Form
import HeytingLean.Crypto.ZK.R1CSBool
import HeytingLean.Crypto.ZK.Export
import HeytingLean.Crypto.BoolLens

namespace HeytingLean
namespace Crypto
namespace ZK
namespace CLI
namespace PCTR1CS

open IO
open Lean
open BoolLens
open R1CSBool

/-- JSON-friendly form AST independent of `n`. -/
inductive FormJ where
  | top
  | bot
  | var (idx : Nat)
  | and (lhs rhs : FormJ)
  | or (lhs rhs : FormJ)
  | imp (lhs rhs : FormJ)
  deriving Repr, BEq, Inhabited

namespace FormJ

open Lean (Json)

private def fromJsonEFuel : Nat → Json → Except String FormJ
  | 0, _ => .error "fromJsonE: fuel exhausted"
  | fuel + 1, j => do
      let tag ← (j.getObjVal? "tag") >>= (fun t => t.getStr?)
      match tag with
      | "top" => return top
      | "bot" => return bot
      | "var" =>
          let idx ← (j.getObjVal? "idx") >>= (fun t => t.getNat?)
          return var idx
      | "and" =>
          let lhsJ ← j.getObjVal? "lhs"
          let rhsJ ← j.getObjVal? "rhs"
          let lhs ← fromJsonEFuel fuel lhsJ
          let rhs ← fromJsonEFuel fuel rhsJ
          return and lhs rhs
      | "or" =>
          let lhsJ ← j.getObjVal? "lhs"
          let rhsJ ← j.getObjVal? "rhs"
          let lhs ← fromJsonEFuel fuel lhsJ
          let rhs ← fromJsonEFuel fuel rhsJ
          return or lhs rhs
      | "imp" =>
          let lhsJ ← j.getObjVal? "lhs"
          let rhsJ ← j.getObjVal? "rhs"
          let lhs ← fromJsonEFuel fuel lhsJ
          let rhs ← fromJsonEFuel fuel rhsJ
          return imp lhs rhs
      | _ => .error "unknown tag"

def fromJsonE (j : Json) : Except String FormJ :=
  fromJsonEFuel 256 j

def toForm? (n : Nat) : FormJ → Option (Form n)
  | top => some .top
  | bot => some .bot
  | var i =>
      if h : i < n then
        some (.var ⟨i, h⟩)
      else
        none
  | and a b => do return .and (← toForm? n a) (← toForm? n b)
  | or a b  => do return .or  (← toForm? n a) (← toForm? n b)
  | imp a b => do return .imp (← toForm? n a) (← toForm? n b)

end FormJ

def readFile (path : System.FilePath) : IO String :=
  FS.readFile path

def parseEnvE (n : Nat) (j : Json) : Except String (Env n) := do
  let arr ← j.getArr?
  if arr.size ≠ n then
    .error s!"Env length {arr.size} ≠ n={n}"
  else
    return (fun i =>
      match (arr[i.1]!).getBool? with
      | .ok b => b
      | .error _ => false)

def main (args : List String) : IO UInt32 := do
  match args with
  | [formPath, envPath] =>
      let formRaw ← readFile formPath
      let envRaw  ← readFile envPath
      let formJson ← match Json.parse formRaw with
        | .ok j => pure j
        | .error err => eprintln err; return 1
      let envJson ← match Json.parse envRaw with
        | .ok j => pure j
        | .error err => eprintln err; return 1
      -- infer `n` from env length
      let n :=
        match envJson.getArr? with
        | .ok arr => arr.size
        | .error _ => 0
      let formJ ← match FormJ.fromJsonE formJson with
        | .ok f => pure f
        | .error err => eprintln err; return 1
      match FormJ.toForm? n formJ with
      | none =>
          eprintln s!"Form contains var index ≥ n={n}"
          return 1
      | some φ =>
          let ρ ← match parseEnvE n envJson with
            | .ok r => pure r
            | .error err => eprintln err; return 1
          let compiled := R1CSBool.compile φ ρ
          let out := Export.compiledToJson compiled
          println (Json.compress out)
          return 0
  | _ =>
      eprintln "Usage: lake exe pct_r1cs <form.json> <env.json>"
      return 1

end PCTR1CS
end CLI
end ZK
end Crypto
end HeytingLean
