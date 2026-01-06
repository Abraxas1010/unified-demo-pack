import HeytingLean.Crypto.ZK.AirIR
import HeytingLean.Crypto.ZK.Spec.AIR

/-
# Crypto.ZK.Spec.STARK

Abstract STARK protocol skeleton over the simplified AIR IR.

At this level we:
* keep the AIR semantics as `Spec.AIR.Rel sys a`;
* introduce an abstract protocol interface `Protocol` over a fixed `AIR.System`;
* package the intended soundness shape as a field `sound` of `Protocol`; and
* expose a bundled `StarkSoundnessStatement` that simply reuses this field.

No cryptographic assumptions (FRI, hash binding, etc.) are encoded here;
these are intended to justify concrete instances of `Protocol.sound` in
future, more detailed developments.
-/

namespace HeytingLean
namespace Crypto
namespace ZK
namespace Spec
namespace STARK

open ZK
open Crypto.ZK.AIR
open Crypto.ZK.Spec.AIR

/-- Abstract STARK protocol over a fixed AIR system.

  * `sys` is the underlying AIR constraint system.
  * `Proof` is the type of STARK proofs.
  * `Public` is the type of public inputs seen by the verifier.
  * `encodePublic` maps an AIR assignment into public inputs; this is the
    place where concrete encodings (trace commitments, boundary constraints,
    etc.) will sit in later refinements.
  * `verify` is the (Boolean) verifier for a given public input and proof.
  * `sound` encodes the intended soundness property: whenever the verifier
    accepts, there exists an assignment satisfying the AIR relation whose
    public encoding is exactly the given input.
-/
structure Protocol where
  sys          : AIR.System
  Proof        : Type
  Public       : Type
  encodePublic : (Var → ℚ) → Public
  verify       : Public → Proof → Bool
  sound :
    ∀ {pub : Public} {π : Proof},
      verify pub π = true →
      ∃ a : Var → ℚ, Rel sys a ∧ encodePublic a = pub

/-- Bundled STARK soundness statement: for a given abstract protocol
    instance `P`, whenever the verifier accepts some public input and
    proof, there exists an assignment satisfying the AIR relation whose
    public encoding is exactly that input. -/
def StarkSoundnessStatement (P : Protocol) : Prop :=
  ∀ {pub : P.Public} {π : P.Proof},
    P.verify pub π = true →
    ∃ a : Var → ℚ, Rel P.sys a ∧ P.encodePublic a = pub

/-- `StarkSoundnessStatement P` holds for any abstract protocol instance
    `P`, by definition of the `sound` field. Concrete cryptographic
    arguments are meant to show that a particular `P` can be constructed
    with this field justified by FRI/commitment assumptions. -/
theorem starkSoundnessStatement_holds (P : Protocol) :
    StarkSoundnessStatement P :=
  P.sound

/-! ## Example STARK instance

As a concrete sanity check (and a bridge to more realistic protocols),
we construct a minimal "example STARK" instance whose verifier always accepts
and whose AIR system has an empty constraint list. This makes the
soundness field `sound` provable purely from the definitions, without
any cryptographic assumptions.
-/

namespace Example

/-- Trivial AIR system with an empty constraint set. -/
def sys : AIR.System :=
  { trace := { width := 0, length := 0 }
  , r1cs  := { constraints := [] } }

/-- Canonical all-zero assignment used in the example protocol. -/
def assign : Var → ℚ := fun _ => 0

/-- A concrete example STARK protocol instance:
  * public inputs and proofs are both `Unit`;
  * the public encoding ignores the assignment; and
  * the verifier always returns `true`.

  Soundness then states that whenever the verifier accepts (which it
  always does), there exists an assignment satisfying the AIR relation
  whose public encoding matches the given (trivial) public input. -/
def protocol : Protocol :=
  { sys := sys
  , Proof := Unit
  , Public := Unit
  , encodePublic := fun _ => ()
  , verify := fun _ _ => true
  , sound := by
      intro pub π h
      refine ⟨assign, ?_, ?_⟩
      · -- AIR relation coincides with R1CS satisfaction for `sys`.
        -- For the empty constraint set, satisfaction is trivial.
        change sys.r1cs.satisfied assign
        intro c hc
        cases hc
      · -- Public encoding is definitionally constant.
        cases pub
        simp }

/-- The example protocol instance satisfies the bundled STARK soundness
    statement. This is a direct corollary of `protocol.sound`. -/
theorem protocol_soundness :
    StarkSoundnessStatement protocol :=
  starkSoundnessStatement_holds protocol

end Example

end STARK
end Spec
end ZK
end Crypto
end HeytingLean
