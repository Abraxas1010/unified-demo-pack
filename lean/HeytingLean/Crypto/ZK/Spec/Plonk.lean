import HeytingLean.Crypto.ZK.PlonkIR
import HeytingLean.Crypto.BoolLens
import HeytingLean.Crypto.Form
import HeytingLean.Crypto.ZK.Backends.Plonk

/-
# Crypto.ZK.Spec.Plonk

Specification façade for the simplified PLONK-style IR.

This module:
* re-exports the `Plonk.System` structure;
* defines a spec-level relation `Rel` as `System.satisfiedNative`; and
* provides thin wrappers around the key equivalence lemmas that relate
  native satisfaction to R1CS satisfaction under copy/permutation and
  gate-bound assumptions.
-/

namespace HeytingLean
namespace Crypto
namespace ZK
namespace Spec
namespace Plonk

open ZK
open Crypto.ZK.Plonk
open Crypto
open Crypto.BoolLens
open Crypto.ZK.Backends

/-- Spec-level satisfaction relation for a PLONK system: we take the
    native semantics as the intended relation for now. -/
def Rel (sys : Plonk.System) (a : ZK.Var → ℚ) : Prop :=
  Plonk.System.satisfiedNative a sys

/-- Bundled IR-level soundness statement for the simplified PLONK-style
    system: under copy-satisfaction and suitable gate-bounds, the native
    semantics `Rel` coincides with the semantics of some renamed R1CS
    system obtained from `System.toR1CS`. -/
def SoundnessStatement : Prop :=
  ∀ (sys : Plonk.System) (a : ZK.Var → ℚ),
    (copyConstraintSystem sys.copyPermutation).satisfied a →
    (∀ g ∈ sys.gates, gateBound g sys.copyPermutation.length) →
    ∃ σ, Rel sys a ↔
      ZK.System.satisfied a (ZK.Rename.system σ (Plonk.System.toR1CS sys))

/-- `SoundnessStatement` holds at the IR level, witnessed directly by
    the core lemma `native_iff_renamed_sigma_of_gateBounds`. -/
theorem soundnessStatement_holds : SoundnessStatement := by
  intro sys a hCopy hBound
  simpa [Rel] using
    (native_iff_renamed_sigma_of_gateBounds
      (sys := sys) (a := a) (hCopy := hCopy) (hBound := hBound))

/-- Under an explicit pair-respect hypothesis, the native relation is
    equivalent to R1CS satisfaction of the converted system. -/
theorem Rel_iff_r1cs_of_pairs (sys : Plonk.System) (a : ZK.Var → ℚ)
    (hPairs : ∀ ij ∈ copyPairs sys.copyPermutation, a ij.1 = a ij.2) :
    Rel sys a ↔ (Plonk.System.toR1CS sys).satisfied a := by
  unfold Rel
  exact satisfiedNative_iff_r1cs_of_pairs (sys := sys) (a := a) (hPairs := hPairs)

/-- If the copy-constraint system is satisfied, the native relation is
    equivalent to R1CS satisfaction of the converted system. -/
theorem Rel_iff_r1cs_of_copySatisfied (sys : Plonk.System) (a : ZK.Var → ℚ)
    (hCopy : (copyConstraintSystem sys.copyPermutation).satisfied a) :
    Rel sys a ↔ (Plonk.System.toR1CS sys).satisfied a := by
  unfold Rel
  exact satisfiedNative_iff_r1cs_of_copySatisfied (sys := sys) (a := a) (hCopy := hCopy)

/-- Under copy-satisfaction and suitable gate-bounds, the native relation
    coincides with the renamed R1CS semantics for some permutation `σ`. -/
theorem Rel_iff_renamed_sigma_of_gateBounds (sys : Plonk.System) (a : ZK.Var → ℚ)
    (hCopy : (copyConstraintSystem sys.copyPermutation).satisfied a)
    (hBound : ∀ g ∈ sys.gates, gateBound g sys.copyPermutation.length) :
    ∃ σ, Rel sys a ↔
      ZK.System.satisfied a (ZK.Rename.system σ (Plonk.System.toR1CS sys)) := by
  unfold Rel
  exact native_iff_renamed_sigma_of_gateBounds
    (sys := sys) (a := a) (hCopy := hCopy) (hBound := hBound)

/-- Abstract PLONK protocol interface over a fixed system.

  * `sys` is the underlying PLONK constraint system.
  * `Proof` is the type of proofs.
  * `Public` is the type of public inputs seen by the verifier
    (commitments, transcript summaries, etc.).
  * `encodePublic` maps an assignment into public inputs; this is where
    concrete encodings will live in later refinements.
  * `verify` is the Boolean verifier for a given public input and proof.
  * `sound` encodes the intended protocol-level soundness property:
    whenever the verifier accepts, there exists an assignment satisfying
    `Rel` whose public encoding is exactly the given input. -/
structure Protocol where
  sys          : Plonk.System
  Proof        : Type
  Public       : Type
  encodePublic : (ZK.Var → ℚ) → Public
  verify       : Public → Proof → Bool
  sound :
    ∀ {pub : Public} {π : Proof},
      verify pub π = true →
      ∃ a : ZK.Var → ℚ, Rel sys a ∧ encodePublic a = pub

/-- Bundled protocol-level PLONK soundness statement: for a given
    abstract protocol instance `P`, whenever the verifier accepts some
    public input and proof, there exists an assignment satisfying `Rel`
    whose public encoding is exactly that input. -/
def ProtocolSoundnessStatement (P : Protocol) : Prop :=
  ∀ {pub : P.Public} {π : P.Proof},
    P.verify pub π = true →
    ∃ a : ZK.Var → ℚ, Rel P.sys a ∧ P.encodePublic a = pub

/-- `ProtocolSoundnessStatement P` holds for any abstract PLONK protocol
    instance `P`, by definition of the `sound` field. Concrete PLONK
    arguments (commitment binding, transcript soundness, etc.) are
    intended to justify particular instances of this field. -/
theorem protocolSoundnessStatement_holds (P : Protocol) :
    ProtocolSoundnessStatement P :=
  P.sound

end Plonk
end Spec
end ZK
end Crypto
end HeytingLean
