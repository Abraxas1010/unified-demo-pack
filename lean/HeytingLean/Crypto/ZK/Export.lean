import Lean.Data.Json
import HeytingLean.Crypto.ZK.R1CS
import HeytingLean.Crypto.ZK.Support
import HeytingLean.Crypto.ZK.R1CSBool
-- import HeytingLean.Crypto.ZK.PlonkIR -- avoid heavy PLONK IR dependency in core export
import HeytingLean.Crypto.ZK.AirIR
import HeytingLean.Crypto.ZK.BulletIR

namespace HeytingLean
namespace Crypto
namespace ZK
namespace Export

open Lean
open R1CSBool

private def ratToJson (q : ℚ) : Json :=
  -- Encode rationals as strings to avoid lossy floats (Boolean case: -1|0|1)
  if q = 0 then Json.str "0"
  else if q = 1 then Json.str "1"
  else if q = (-1) then Json.str "-1"
  else Json.str (toString q)

def linCombToJson (lc : LinComb) : Json :=
  let termsJson :=
    lc.terms.map (fun (p : Var × ℚ) =>
      Json.arr #[Json.num p.1, ratToJson p.2])
  Json.mkObj
    [ ("const", ratToJson lc.const)
    , ("terms", Json.arr termsJson.toArray)
    ]

def constraintToJson (c : Constraint) : Json :=
  Json.mkObj
    [ ("A", linCombToJson c.A)
    , ("B", linCombToJson c.B)
    , ("C", linCombToJson c.C)
    ]

def systemToJson (sys : System) : Json :=
  Json.mkObj
    [ ("constraints", Json.arr (sys.constraints.map constraintToJson).toArray) ]

def assignmentToJson (assign : Var → ℚ) (numVars : Nat) : Json :=
  let arr := (List.range numVars).map (fun v => ratToJson (assign v))
  Json.arr arr.toArray

private def maxVarInTerms (acc : Nat) (terms : List (Var × ℚ)) : Nat :=
  terms.foldl (fun m p => Nat.max m p.fst) acc

private def maxVarInConstraint (c : Constraint) : Nat :=
  let m1 := maxVarInTerms 0 c.A.terms
  let m2 := maxVarInTerms m1 c.B.terms
  maxVarInTerms m2 c.C.terms

private def maxVarInSystem (sys : System) : Nat :=
  sys.constraints.foldl (fun m c => Nat.max m (maxVarInConstraint c)) 0

def compiledToJson (c : Compiled) : Json :=
  let maxVar := maxVarInSystem c.system
  let numVars := maxVar + 1
  Json.mkObj
    [ ("system", systemToJson c.system)
    , ("assignment", assignmentToJson c.assignment numVars)
    , ("outputVar", Json.num c.output)
    ]

/-! Minimal decoders for the Boolean setup (coefficients in {-1,0,1}). -/

private def exToOpt {α} : Except String α → Option α
  | .ok a => some a
  | .error _ => none

private def jsonToRatBooly (j : Json) : Option ℚ := do
  let s ← exToOpt (j.getStr?)
  match s with
  | "0" => some 0
  | "1" => some 1
  | "-1" => some (-1)
  | _ => none

def jsonToLinComb (j : Json) : Option LinComb := do
  let obj ← exToOpt (j.getObj?)
  let const ← (obj.get? "const") >>= jsonToRatBooly
  let termsArr ← (obj.get? "terms") >>= (fun t => exToOpt (t.getArr?))
  let rec go (i : Nat) (acc : List (Var × ℚ)) : Option (List (Var × ℚ)) :=
    if h : i < termsArr.size then
      -- mark binder `h` as used to avoid unused-binder lint
      have _ := h
      let e := termsArr[i]!
      match exToOpt (e.getArr?) with
      | none => none
      | some arr =>
          if arr.size = 2 then
            let vJson := arr[0]!
            let cJson := arr[1]!
            match exToOpt (vJson.getNat?), jsonToRatBooly cJson with
            | some v, some coeff => go (i+1) ((v, coeff) :: acc)
            | _, _ => none
          else
            none
    else
      some acc.reverse
  let terms ← go 0 []
  pure ⟨const, terms⟩

def jsonToConstraint (j : Json) : Option Constraint := do
  let obj ← exToOpt (j.getObj?)
  let A ← (obj.get? "A") >>= jsonToLinComb
  let B ← (obj.get? "B") >>= jsonToLinComb
  let C ← (obj.get? "C") >>= jsonToLinComb
  pure { A := A, B := B, C := C }

def jsonToSystem (j : Json) : Option System := do
  let obj ← exToOpt (j.getObj?)
  let csArr ← (obj.get? "constraints") >>= (fun t => exToOpt (t.getArr?))
  let rec go (i : Nat) (acc : List Constraint) : Option (List Constraint) :=
    if h : i < csArr.size then
      have _ := h
      let e := csArr[i]!
      match jsonToConstraint e with
      | none => none
      | some c => go (i+1) (c :: acc)
    else
      some acc.reverse
  let out ← go 0 []
  pure { constraints := out }

def jsonToAssignment (j : Json) : Option (Array ℚ) := do
  let arr ← exToOpt (j.getArr?)
  let rec go (i : Nat) (acc : List ℚ) : Option (List ℚ) :=
    if h : i < arr.size then
      have _ := h
      let e := arr[i]!
      match jsonToRatBooly e with
      | none => none
      | some q => go (i+1) (q :: acc)
    else
      some acc.reverse
  let outList ← go 0 []
  pure outList.toArray

def assignmentOfArray (a : Array ℚ) : Var → ℚ :=
  fun v => a.getD v 0

end Export
end ZK
end Crypto
end HeytingLean

-- Additional exports for non-R1CS backends (minimal JSON shapes)
namespace HeytingLean
namespace Crypto
namespace ZK
namespace Export

open Lean

def linCombToJson' (lc : ZK.LinComb) : Json :=
  let termsJson :=
    lc.terms.map (fun (p : ZK.Var × ℚ) =>
      Json.arr #[Json.num p.1, ratToJson p.2])
  Json.mkObj
    [ ("const", ratToJson lc.const)
    , ("terms", Json.arr termsJson.toArray)
    ]

-- plonkSystemToJson removed for now to keep Export lean and avoid PLONK IR dependency

def airSystemToJson (sys : ZK.AIR.System) : Json :=
  let t := sys.trace
  Json.mkObj [ ("trace", Json.mkObj [("width", Json.num t.width), ("length", Json.num t.length)])
             , ("r1cs", systemToJson sys.r1cs) ]

def bulletSystemToJson (sys : ZK.Bullet.System) : Json :=
  Json.mkObj [ ("commitments", Json.arr (sys.commitments.map (fun c => Json.mkObj [("label", Json.str c.label)])).toArray)
             , ("r1cs", systemToJson sys.r1cs) ]

end Export
end ZK
end Crypto
end HeytingLean
