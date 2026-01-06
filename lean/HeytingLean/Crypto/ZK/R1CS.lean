import Mathlib.Data.Rat.Init

namespace HeytingLean
namespace Crypto
namespace ZK

/-- Variables are indexed by natural numbers. -/
abbrev Var := Nat

/-- Linear combinations over `ℚ` as a constant plus explicit terms. -/
structure LinComb where
  const : ℚ
  terms : List (Var × ℚ)
  deriving DecidableEq

namespace LinComb

/-- Evaluate a linear combination for a given assignment. -/
def eval (lc : LinComb) (assign : Var → ℚ) : ℚ :=
  lc.terms.foldl
    (fun acc term => acc + term.2 * assign term.1) lc.const

/-- Constant linear combination. -/
def ofConst (c : ℚ) : LinComb :=
  ⟨c, []⟩

/-- Linear combination consisting of a single `(variable, coefficient)` entry. -/
def single (v : Var) (coeff : ℚ) : LinComb :=
  ⟨0, [(v, coeff)]⟩

end LinComb

/-- A single R1CS constraint `(A, B, C)` meaning `(A·x) * (B·x) = (C·x)`. -/
structure Constraint where
  A : LinComb
  B : LinComb
  C : LinComb
  deriving DecidableEq

/-- Satisfaction of a constraint by an assignment. -/
def Constraint.satisfied (assign : Var → ℚ) (c : Constraint) : Prop :=
  c.A.eval assign * c.B.eval assign = c.C.eval assign

/-- An R1CS system is a finite list of constraints. -/
structure System where
  constraints : List Constraint
  deriving Inhabited

/-- An assignment satisfies the entire system iff it satisfies every constraint. -/
def System.satisfied (assign : Var → ℚ) (sys : System) : Prop :=
  ∀ {c}, c ∈ sys.constraints → Constraint.satisfied assign c

end ZK
end Crypto
end HeytingLean
