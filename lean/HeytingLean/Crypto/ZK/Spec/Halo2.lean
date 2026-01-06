/-
# Crypto.ZK.Spec.Halo2

Abstract specification façade for a Halo2-style recursive proof system.

At this level we:
* keep the notion of "statement" and its correctness as abstract data;
* introduce a protocol interface `Protocol` with a composition operator
  on statements; and
* package the intended correctness shape as a field `sound` together
  with a bundled `CorrectnessStatement` including a composition
  preservation lemma.

No concrete circuit, polynomial, or commitment semantics are fixed
here; those are intended to justify specific instances of
`Protocol.sound` and `Protocol.sound_compose` in later developments.
-/

namespace HeytingLean
namespace Crypto
namespace ZK
namespace Spec
namespace Halo2

/-- Abstract Halo2-style recursive proof protocol.

  * `Statement` is the type of statements being proved.
  * `Correct : Statement → Prop` expresses semantic correctness of a
    statement.
  * `Proof` is the type of proofs.
  * `verify s π` is the (Boolean) verifier for a statement `s` and
    proof `π`.
  * `compose s₁ s₂` is an abstract composition operator on statements,
    intended to model recursive proof composition.
  * `sound` encodes basic soundness: whenever the verifier accepts, the
    statement is semantically correct.
  * `sound_compose` states that correctness is preserved by
    composition: composing two correct statements yields a correct
    statement. -/
structure Protocol where
  Statement : Type
  Correct   : Statement → Prop
  Proof     : Type
  verify    : Statement → Proof → Bool
  compose   : Statement → Statement → Statement
  sound :
    ∀ {s : Statement} {π : Proof},
      verify s π = true → Correct s
  sound_compose :
    ∀ {s₁ s₂ : Statement},
      Correct s₁ → Correct s₂ → Correct (compose s₁ s₂)

/-- Bundled Halo2-correctness statement for a fixed protocol instance:
    basic soundness of `verify` together with the fact that semantic
    correctness is preserved by the composition operator. -/
def CorrectnessStatement (P : Protocol) : Prop :=
  (∀ {s : P.Statement} {π : P.Proof},
      P.verify s π = true → P.Correct s) ∧
  (∀ {s₁ s₂ : P.Statement},
      P.Correct s₁ → P.Correct s₂ → P.Correct (P.compose s₁ s₂))

/-- `CorrectnessStatement P` holds for any abstract protocol instance
    `P`, by definition of the `sound` and `sound_compose` fields. -/
theorem correctnessStatement_holds (P : Protocol) :
    CorrectnessStatement P := by
  refine And.intro ?hSound ?hCompose
  · intro s π h
    exact P.sound h
  · intro s₁ s₂ h₁ h₂
    exact P.sound_compose h₁ h₂

/-! ## Example Halo2 instance

As a concrete sanity check (and a bridge to more realistic recursive
protocols), we construct a minimal "example Halo2" instance whose verifier
always accepts and whose correctness predicate is trivially satisfied.
This keeps the abstract interface exercised without committing to any
particular circuit or commitment semantics.
-/

namespace Example

/-- Trivial statement type for the example Halo2 protocol. -/
def Statement := Unit

/-- In the example protocol, every statement is considered correct. -/
def Correct (_ : Statement) : Prop := True

/-- Trivial proof type for the example Halo2 protocol. -/
def Proof := Unit

/-- Verifier for the example protocol: always returns `true`. -/
def verify (_ : Statement) (_ : Proof) : Bool := true

/-- Composition on statements in the example protocol: ignores its inputs
    and returns `()`. -/
def compose (_ : Statement) (_ : Statement) : Statement := ()

/-- Concrete example Halo2 protocol instance satisfying the abstract
    `Protocol` interface. -/
def protocol : Protocol :=
  { Statement := Statement
    , Correct := Correct
    , Proof := Proof
    , verify := verify
    , compose := compose
    , sound := by
        intro s π h
        trivial
    , sound_compose := by
        intro s₁ s₂ h₁ h₂
        trivial }

/-- The example Halo2 protocol instance satisfies the bundled correctness
    statement. This is a direct corollary of `protocol.sound` and
    `protocol.sound_compose`. -/
theorem protocol_correctness :
    CorrectnessStatement protocol :=
  correctnessStatement_holds protocol

end Example

end Halo2
end Spec
end ZK
end Crypto
end HeytingLean
