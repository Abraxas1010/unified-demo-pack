import HeytingLean.Basic

/-
# Crypto.ZK.AnonymousCredentialsExample

Minimal example model backing the `anonymousCredentialsCorrectness` ZK
property.

This model abstracts away cryptographic details and focuses on the
shape of a ZK proof for anonymous credentials:

* correctness: whenever the verifier accepts a proof, the revealed
  attributes correspond to some credential in the registry; and
* anonymity: the verifier's decision depends only on attributes and
  the registry, not on the holder identity.

It is deliberately small and axiom-free, providing a clear target for
the spec-level statement in `Crypto.ZK.Spec`.
-/

namespace HeytingLean
namespace Crypto
namespace ZK
namespace AnonymousCredentialsExample

open Classical

/-- A credential with an identifier and a list of attributes. -/
structure Credential where
  id    : String
  attrs : List String
  deriving Repr, DecidableEq

/-- Example proof object for anonymous credentials: carries the holder
    identity, the attributes being proved, and a registry of issued
    credentials. In a real system, this would also include
    commitments and a zero-knowledge proof; here we model only the
    semantic payload. -/
structure Proof where
  holder   : String
  attrs    : List String
  registry : List Credential
  deriving Repr

/-- Registry membership predicate: the attribute list `attrs` appears
    as the attribute list of some credential in `registry`. -/
def hasAttrsInRegistry (attrs : List String)
    (registry : List Credential) : Prop :=
  ∃ c ∈ registry, c.attrs = attrs

/-- Decidability instance for `hasAttrsInRegistry`, obtained from the
    standard decidability instances for existential quantification and
    list membership (using `DecidableEq` for `Credential`). -/
instance instDecidableHasAttrsInRegistry
    (attrs : List String) (registry : List Credential) :
    Decidable (hasAttrsInRegistry attrs registry) := by
  classical
  unfold hasAttrsInRegistry
  infer_instance

/-- Example verifier: accepts exactly when there exists a credential in
    the registry whose attribute list matches the attributes carried
    in the proof. The decision is independent of the `holder` field. -/
def verify (p : Proof) : Bool :=
  if _ : hasAttrsInRegistry p.attrs p.registry then true else false

/-- Correctness property: whenever the verifier accepts a proof, the
    attributes it carries are those of some credential in the
    registry. -/
def AttributeCorrectness : Prop :=
  ∀ p : Proof, verify p = true →
    ∃ c ∈ p.registry, c.attrs = p.attrs

/-- Anonymity property: the verifier's decision is independent of the
    holder identity when attributes and registry are fixed. -/
def Anonymity : Prop :=
  ∀ (holder₁ holder₂ : String)
    (attrs : List String) (registry : List Credential),
    let p₁ : Proof :=
      { holder := holder₁, attrs := attrs, registry := registry }
    let p₂ : Proof :=
      { holder := holder₂, attrs := attrs, registry := registry }
    verify p₁ = verify p₂

/-- Anonymity holds because `verify` depends only on attributes and
    registry. -/
theorem anonymity_holds : Anonymity := by
  intro holder₁ holder₂ attrs registry
  let p₁ : Proof :=
    { holder := holder₁, attrs := attrs, registry := registry }
  let p₂ : Proof :=
    { holder := holder₂, attrs := attrs, registry := registry }
  -- `verify` depends only on `attrs` and `registry`, so the two calls
  -- coincide definitionally once we rewrite these components.
  simp [verify, hasAttrsInRegistry]

/-- Bundled correctness/anonymity statement for the example anonymous
    credentials verifier. -/
def Statement : Prop :=
  AttributeCorrectness ∧ Anonymity

/-- `Statement` holds: the verifier is both attribute-correct and
    independent of the holder identity. -/
theorem statement_holds : Statement := by
  constructor
  · -- Attribute correctness.
    intro p hAccept
    unfold verify at hAccept
    by_cases h : hasAttrsInRegistry p.attrs p.registry
    · -- In the case where the existential holds, we recover it.
      rcases h with ⟨c, hcIn, hcEq⟩
      exact ⟨c, hcIn, hcEq⟩
    · -- Otherwise the verifier would have returned `false`,
      -- contradicting `hAccept`.
      have : False := by
        have hAccept' := hAccept
        simp [h] at hAccept'
      exact False.elim this
  · -- Anonymity.
    exact anonymity_holds

end AnonymousCredentialsExample
end ZK
end Crypto
end HeytingLean
