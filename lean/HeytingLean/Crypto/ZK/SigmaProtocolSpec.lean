import HeytingLean.Crypto.ZK.ProofOfKnowledgeSpec

/-!
# Sigma-protocol interface (spec-only)

This module provides a small, **interactive** Sigma-protocol interface:

1. Prover sends a commitment `a`
2. Verifier sends a challenge `e`
3. Prover sends a response `z`
4. Verifier checks `verify s a e z`

Scope:
- purely structural (no probability, no PPT/security model);
- **completeness** and a lightweight **special soundness** axiom (two accepting transcripts
  with the same commitment but different challenges imply existence of a witness).

We also provide a trivial, axiom-free constructor where the response simply carries the witness;
this is useful as a scaffolding target for later, nontrivial instances.
-/

namespace HeytingLean.Crypto.ZK

/-!
## Sigma protocol
-/

structure SigmaProtocol (Stmt Wit Rand Comm Chal Resp : Type) (R : Relation Stmt Wit) where
  commit : Stmt → Wit → Rand → Comm
  respond : Stmt → Wit → Rand → Chal → Resp
  verify : Stmt → Comm → Chal → Resp → Bool
  complete :
    ∀ {s w}, R.holds s w → ∀ (r : Rand) (e : Chal),
      verify s (commit s w r) e (respond s w r e) = true
  /-- Special soundness: two accepting transcripts with the same commitment but different challenges
  imply existence of a witness (no extractability algorithm is claimed). -/
  specialSound :
    ∀ (s : Stmt) (a : Comm) (e₁ e₂ : Chal) (z₁ z₂ : Resp),
      e₁ ≠ e₂ →
      verify s a e₁ z₁ = true →
      verify s a e₂ z₂ = true →
      ∃ w : Wit, R.holds s w

namespace SigmaProtocol

variable {Stmt Wit Rand Comm Chal Resp : Type} {R : Relation Stmt Wit}
variable (proto : SigmaProtocol Stmt Wit Rand Comm Chal Resp R)

theorem exists_witness_of_two_accepting
    (s : Stmt) (a : Comm) (e₁ e₂ : Chal) (z₁ z₂ : Resp)
    (hne : e₁ ≠ e₂)
    (h1 : proto.verify s a e₁ z₁ = true)
    (h2 : proto.verify s a e₂ z₂ = true) :
    ∃ w : Wit, R.holds s w :=
  proto.specialSound s a e₁ e₂ z₁ z₂ hne h1 h2

end SigmaProtocol

/-!
## Trivial Sigma protocol: response carries the witness
-/

def witnessSigma {Stmt Wit : Type} (R : Relation Stmt Wit)
    [hdec : ∀ s w, Decidable (R.holds s w)] :
    SigmaProtocol Stmt Wit Unit Unit Bool Wit R := by
  classical
  refine
    { commit := fun _s _w _r => ()
      respond := fun _s w _r _e => w
      verify := fun s _a _e w => decide (R.holds s w)
      complete := ?_
      specialSound := ?_ }
  · intro s w hw r e
    have : decide (R.holds s w) = true := by
      exact (Bool.decide_iff (R.holds s w)).2 hw
    simpa using this
  · intro s a e₁ e₂ z₁ z₂ _hne h1 _h2
    -- Since the verifier checks `R.holds s z₁`, any accepting transcript yields a witness.
    refine ⟨z₁, ?_⟩
    have : decide (R.holds s z₁) = true := by
      simpa using h1
    exact (Bool.decide_iff (R.holds s z₁)).1 this

end HeytingLean.Crypto.ZK
