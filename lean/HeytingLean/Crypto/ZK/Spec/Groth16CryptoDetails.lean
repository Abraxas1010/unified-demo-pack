import Mathlib

/-!
# Groth16CryptoDetails (demo algebraic backend)

This module provides a small, self-contained algebraic "pairing backend"
interface for Groth16-style developments.

It is intentionally **not** a cryptographic implementation. Instead it
offers:

* `PairingBackend`: types for groups `G1`, `G2`, `GT` (as additive commutative
  groups) plus a pairing function `pair : G1 → G2 → GT`.
* `BackendAxioms`: explicit assumptions stating bilinearity and
  non-degeneracy of `pair`.
* `Example`: a concrete instance over `ℚ × ℚ` with pairing given by the
  determinant `x₁y₂ - x₂y₁`, together with proofs of the axioms.
-/

namespace HeytingLean
namespace Crypto
namespace ZK
namespace Spec
namespace Groth16CryptoDetails

open scoped BigOperators

/-! ## Backend interface -/

universe u v w

structure PairingBackend where
  G1 : Type u
  G2 : Type v
  GT : Type w
  instG1 : AddCommGroup G1
  instG2 : AddCommGroup G2
  instGT : AddCommGroup GT
  pair : G1 → G2 → GT

attribute [instance] PairingBackend.instG1 PairingBackend.instG2 PairingBackend.instGT

structure BackendAxioms (B : PairingBackend) : Prop where
  add_left :
    ∀ (a b : B.G1) (c : B.G2),
      B.pair (a + b) c = B.pair a c + B.pair b c
  add_right :
    ∀ (a : B.G1) (b c : B.G2),
      B.pair a (b + c) = B.pair a b + B.pair a c
  nondegenerate :
    ∃ a : B.G1, ∃ b : B.G2, B.pair a b ≠ 0

structure RealBackend where
  backend : PairingBackend
  axioms : BackendAxioms backend

/-! ## Example backend over ℚ × ℚ -/

namespace Example

abbrev Point := ℚ × ℚ

def det : Point → Point → ℚ
  | (x₁, y₁), (x₂, y₂) => x₁ * y₂ - x₂ * y₁

theorem det_add_left (P P' Q : Point) :
    det (P + P') Q = det P Q + det P' Q := by
  rcases P with ⟨x₁, y₁⟩
  rcases P' with ⟨x₂, y₂⟩
  rcases Q with ⟨x₃, y₃⟩
  simp [det]
  ring

theorem det_add_right (P Q Q' : Point) :
    det P (Q + Q') = det P Q + det P Q' := by
  rcases P with ⟨x₁, y₁⟩
  rcases Q with ⟨x₂, y₂⟩
  rcases Q' with ⟨x₃, y₃⟩
  simp [det]
  ring

theorem det_nondegenerate : ∃ P : Point, ∃ Q : Point, det P Q ≠ 0 := by
  refine ⟨(1, 0), (0, 1), ?_⟩
  simp [det]

def backend : PairingBackend :=
  { G1 := Point
    , G2 := Point
    , GT := ℚ
    , instG1 := inferInstance
    , instG2 := inferInstance
    , instGT := inferInstance
    , pair := det }

def axioms : BackendAxioms backend :=
  { add_left := by
      intro a b c
      simpa [backend, PairingBackend.pair] using det_add_left a b c
    , add_right := by
      intro a b c
      simpa [backend, PairingBackend.pair] using det_add_right a b c
    , nondegenerate := by
      rcases det_nondegenerate with ⟨a, b, h⟩
      refine ⟨a, b, ?_⟩
      simpa [backend, PairingBackend.pair] using h }

def realBackend : RealBackend :=
  { backend := backend, axioms := axioms }

theorem axioms_sound : BackendAxioms realBackend.backend := realBackend.axioms

#print axioms det_add_left
#print axioms det_add_right
#print axioms det_nondegenerate

end Example

/-! ## Convenience aliases -/

def demoRealBackend : RealBackend := Example.realBackend

/-- Demo alias for a BN254-style backend.

This repository currently provides only the proved demo backend above.
The intended BN254 instantiation should eventually live in a dedicated
module (likely with an external backend), at which point this alias can
be replaced.
-/
def bn254BackendDemo : RealBackend := demoRealBackend

end Groth16CryptoDetails
end Spec
end ZK
end Crypto
end HeytingLean
