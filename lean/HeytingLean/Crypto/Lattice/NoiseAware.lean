import HeytingLean.Crypto.Lattice.FaithfulReductions

namespace HeytingLean
namespace Crypto
namespace Lattice

/-!
# Noise-aware lattice views (v1.2)

This module adds **noise-aware** recovery views on top of the concrete, faithful (but noiseless)
carriers in `FaithfulReductions.lean`.

Design notes:
- We remain *statement-first*: no distributions, no PPT, no security loss accounting.
- The key addition is an explicit error term `e` together with a checkable correctness equation.
- We provide a reviewable decode API that always returns a consistent residual error, plus lemmas
  showing that in the **noiseless** case (`e = 0`) the inversion-trapdoor decoder recovers the
  original secret.
-/

open scoped Classical BigOperators

noncomputable section

namespace RingMLWE

/-- Noise-aware ring-MLWE secret: `b = A*s + e`. -/
structure NoisySecret (P : MLWEParams) where
  inst : Instance P
  s : ModVec P
  e : ModVec P
  correct : inst.b = inst.A.mulVec s + e

noncomputable def junkNoisySecret (P : MLWEParams) : NoisySecret P :=
  { inst := { A := 0, b := 0 }
    s := 0
    e := 0
    correct := by simp }

/-- Noise-aware view: the recovery goal is to recover the secret `s` (error is auxiliary). -/
def NoisyView (P : MLWEParams) : RecoveryView (NoisySecret P) where
  Pub := Instance P
  encode := fun sec => sec.inst
  goalEq := fun r s => r.s = s.s

private abbrev residual (P : MLWEParams) (inst : Instance P) (s : ModVec P) : ModVec P :=
  inst.b - inst.A.mulVec s

private theorem add_residual_eq (P : MLWEParams) (inst : Instance P) (s : ModVec P) :
    inst.A.mulVec s + residual P inst s = inst.b := by
  -- `a + (b - a) = b`
  -- Rewrite to `a + b - a` and apply `add_sub_cancel`.
  simp [residual, sub_eq_add_neg]

/-- Build a noise-aware secret by attaching the residual error `e := b - A*s`. -/
noncomputable def withResidual (P : MLWEParams) (inst : Instance P) (s : ModVec P) : NoisySecret P :=
  { inst := inst
    s := s
    e := residual P inst s
    correct := (add_residual_eq P inst s).symm }

/-- Decoder skeleton: given *any* `s` candidate, return a consistent residual error. -/
noncomputable def decodeResidual (P : MLWEParams) (inst : Instance P) (s : ModVec P) : NoisySecret P :=
  withResidual P inst s

/-- Inversion-trapdoor decoder with an explicit `round` stage.

This is an executable *API*; it does not claim that rounding succeeds under any distributional
assumptions. The residual error is always consistent by construction.
-/
noncomputable def decodeByInv (P : MLWEParams) (round : ModVec P → ModVec P) (inst : Instance P)
    (td : InvTrapdoor P) : NoisySecret P :=
  decodeResidual P inst (round (td.invA.mulVec inst.b))

theorem decodeByInv_correct (P : MLWEParams) (round : ModVec P → ModVec P) (inst : Instance P) (td : InvTrapdoor P) :
    (decodeByInv P round inst td).inst = inst := by
  rfl

theorem decodeByInv_residual (P : MLWEParams) (round : ModVec P → ModVec P) (inst : Instance P) (td : InvTrapdoor P) :
    (decodeByInv P round inst td).e = inst.b - inst.A.mulVec (decodeByInv P round inst td).s := by
  rfl

/-- In the noiseless case `b = A*s`, and when the trapdoor matches the instance matrix,
the inversion decoder (with identity rounding) recovers `s`. -/
theorem decodeByInv_recovers_noiseless (P : MLWEParams)
    (inst : Instance P) (td : InvTrapdoor P)
    (hA : td.A = inst.A) (hdet : IsUnit (Matrix.det inst.A))
    (s : ModVec P) (hb : inst.b = inst.A.mulVec s) :
    (decodeByInv P id inst td).s = s := by
  classical
  -- Unfold the decoder.
  simp [decodeByInv, decodeResidual, withResidual]
  -- Reduce to `invA * (A*s) = s`.
  have hdet' : IsUnit (Matrix.det td.A) := by simpa [hA] using hdet
  have hinv : td.invA * inst.A = (1 : ModMat P) := by
    simpa [hA] using td.inv_mul hdet'
  calc
    td.invA.mulVec inst.b = td.invA.mulVec (inst.A.mulVec s) := by simp [hb]
    _ = (td.invA * inst.A).mulVec s := by simp [Matrix.mulVec_mulVec]
    _ = (1 : ModMat P).mulVec s := by simp [hinv]
    _ = s := by simp

/-- In the same noiseless setting, the residual error computed by `decodeByInv` is zero. -/
theorem decodeByInv_error_zero_noiseless (P : MLWEParams)
    (inst : Instance P) (td : InvTrapdoor P)
    (hA : td.A = inst.A) (hdet : IsUnit (Matrix.det inst.A))
    (s : ModVec P) (hb : inst.b = inst.A.mulVec s) :
    (decodeByInv P id inst td).e = 0 := by
  classical
  have hdet' : IsUnit (Matrix.det td.A) := by simpa [hA] using hdet
  have hinv : td.invA * inst.A = (1 : ModMat P) := by
    simpa [hA] using td.inv_mul hdet'
  have hdecode : td.invA.mulVec (inst.A.mulVec s) = s := by
    calc
      td.invA.mulVec (inst.A.mulVec s) = (td.invA * inst.A).mulVec s := by simp [Matrix.mulVec_mulVec]
      _ = (1 : ModMat P).mulVec s := by simp [hinv]
      _ = s := by simp
  -- Unfold the residual error and simplify using the noiseless equation `b = A*s`.
  simp [decodeByInv, decodeResidual, withResidual, residual, hb, hdecode]

end RingMLWE

end

end Lattice
end Crypto
end HeytingLean
