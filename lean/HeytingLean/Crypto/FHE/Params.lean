/-!
  Minimal parameters for the FHE V0 scaffold.
  This file intentionally avoids deep arithmetic so it compiles quickly
  under `-Dno_sorry -DwarningAsError=true`.
-/

namespace HeytingLean.Crypto.FHE

structure Params where
  /-- ciphertext modulus (V0 parameter) -/        p  : Nat
  /-- noise threshold (must be < p) -/            T  : Nat
  /-- post-refresh bound (reset target) -/        B0 : Nat
deriving Repr, DecidableEq

def defaultParams : Params := { p := 4093, T := 1024, B0 := 16 }

/-- Basic sanity relation between parameters (kept as a Prop, not enforced). -/
def Params.sane (P : Params) : Prop := 2 ≤ P.p ∧ P.B0 < P.T ∧ P.T * 2 ≤ P.p

/-- The default parameter choice satisfies the basic sanity relation. -/
theorem Params.sane_default : Params.sane defaultParams := by
  -- Reduce to a concrete conjunction of numeric inequalities and discharge
  -- it by computation.
  unfold Params.sane defaultParams
  decide

end HeytingLean.Crypto.FHE
