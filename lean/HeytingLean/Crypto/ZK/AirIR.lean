import HeytingLean.Crypto.ZK.R1CS

namespace HeytingLean
namespace Crypto
namespace ZK
namespace AIR

/-- Minimal AIR (STARK) trace descriptor. -/
structure Trace where
  width : Nat := 0
  length : Nat := 0

/-- AIR system carries a trace descriptor plus a semantics bridge to R1CS. -/
structure System where
  trace : Trace := {}
  r1cs  : ZK.System := { constraints := [] }

/-- A composite AIR transition set: equality transitions and multiplicative transitions. -/
structure TransitionSet where
  eqs  : List (ZK.LinComb × ZK.LinComb) := []
  muls : List (ZK.LinComb × ZK.LinComb × ZK.LinComb) := []

/-- Bool predicate capturing that the B-slot of a constraint is the constant one. -/
def isConstOne (c : ZK.Constraint) : Bool := decide (c.B = ZK.LinComb.ofConst 1)

/-- Auto-encode a mixed TransitionSet by classifying constraints into equalities (B=1)
    and multiplicatives (otherwise). -/
def TransitionSet.ofSystemAuto (cs : List ZK.Constraint) : TransitionSet :=
  { eqs := (cs.filter (fun c => isConstOne c)).map (fun c => (c.A, c.C))
  , muls := (cs.filter (fun c => ! isConstOne c)).map (fun c => (c.A, c.B, c.C)) }

/-! Encoding helpers and equivalences to the embedded R1CS. -/

/-! Minimal interface only; proof-oriented helpers are deferred. -/

end AIR
end ZK
end Crypto
end HeytingLean
