import HeytingLean.Crypto.ZK.BulletIR
import HeytingLean.Crypto.BoolLens
import HeytingLean.Crypto.Form
import HeytingLean.Crypto.ZK.Backends.Bullet

/-
# Crypto.ZK.Spec.Bullet

Specification façade for the simplified Bulletproof-style inner-product IR.

The current model embeds an R1CS system in `Bullet.System.r1cs`; we take
its satisfaction as the spec-level relation `Rel`. This can later be
refined to distinguish commitment and inner-product semantics explicitly.
-/

namespace HeytingLean
namespace Crypto
namespace ZK
namespace Spec
namespace Bullet

open ZK
open Crypto.ZK.Bullet
open Crypto
open Crypto.BoolLens
open Crypto.ZK.Backends

/-- Spec-level satisfaction relation for a Bullet-style system: for now,
    this is just R1CS satisfaction of the embedded system. -/
def Rel (sys : Crypto.ZK.Bullet.System) (a : ZK.Var → ℚ) : Prop :=
  sys.r1cs.satisfied a

/-- In the current model, `Rel` is definitionally equal to
    `System.satisfiedNative`. -/
@[simp] theorem Rel_iff_native (sys : Crypto.ZK.Bullet.System) (a : ZK.Var → ℚ) :
    Rel sys a ↔ sys.satisfiedNative a := by
  rfl

/-- Bundled IR-level constraints-correctness statement for the current
    Bulletproof-style system: the spec-level relation `Rel` coincides
    with R1CS satisfaction of the embedded `r1cs` system for all
    systems and assignments. -/
def ConstraintsCorrectnessStatement : Prop :=
  ∀ (sys : Crypto.ZK.Bullet.System) (a : ZK.Var → ℚ),
    Rel sys a ↔ sys.r1cs.satisfied a

/-- `ConstraintsCorrectnessStatement` holds, witnessed directly by the
    definitional equality between `Rel` and the embedded R1CS
    satisfaction relation. -/
theorem constraintsCorrectnessStatement_holds :
    ConstraintsCorrectnessStatement := by
  intro sys a
  rfl

/-- Backend-level correctness statement for the Bullet backend with
    respect to Boolean `Form` semantics: for every Boolean `Form` `φ`
    and environment `ρ`, the compiled Bullet system admits an assignment
    whose embedded R1CS system is satisfied and whose public output
    encodes the Boolean evaluation `BoolLens.eval φ ρ`. -/
def BackendCorrectnessStatement : Prop :=
  ∀ {n : ℕ} (φ : Crypto.Form n) (ρ : Env n),
    let p := Crypto.Form.compile φ
    let s := Backends.bulletCompile ρ p
    ∃ a, Backends.bulletSatisfies s a ∧
      Backends.bulletPublic s a =
        [if BoolLens.eval φ ρ then 1 else 0]

/-- `BackendCorrectnessStatement` holds, witnessed directly by the
    backend-level completeness theorem `Backends.bullet_complete`. -/
theorem backendCorrectnessStatement_holds :
    BackendCorrectnessStatement := by
  intro n φ ρ
  -- `bullet_complete` already provides the required witness.
  simpa [BackendCorrectnessStatement] using
    (Backends.bullet_complete (φ := φ) (ρ := ρ))

end Bullet
end Spec
end ZK
end Crypto
end HeytingLean
