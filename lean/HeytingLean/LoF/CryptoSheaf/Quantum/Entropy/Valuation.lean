import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import HeytingLean.LoF.CryptoSheaf.Quantum.Entropy.Basic

/-
Valuation primitives: conservative numeric proxies (ℕ-valued) over
distributive lattices. We avoid calling these “entropy” and only expose
properties we can prove today (monotonicity, submodularity skeletons).
-/
namespace HeytingLean
namespace LoF
namespace CryptoSheaf
namespace Quantum
namespace Entropy

open Classical

class Valuation (L : Type*) [DistribLattice L] [OrderBot L] where
  v : L → Nat
  mono : Monotone v
  submodular : ∀ x y, v (x ⊔ y) + v (x ⊓ y) ≤ v x + v y
  v_bot : v ⊥ = 0

namespace Valuation

variable {L : Type*} [DistribLattice L] [OrderBot L] (V : Valuation L)

/-- Optional proxies that may be useful later. -/
def gain (x y : L) : Int := (V.v x : Int) + (V.v y : Int) - (V.v (x ⊓ y) : Int)
def overlap (x y : L) : Nat := V.v (x ⊓ y)

end Valuation

/-- A nontrivial valuation instance on finite sets `Finset α` using cardinality.
Submodularity follows from `card_union_add_card_inter`. -/
instance (α : Type*) [DecidableEq α] : Valuation (Finset α) where
  v := fun s => Finset.card s
  mono := by
    intro s t hst
    -- `card_le_card : s ⊆ t → #s ≤ #t`
    simpa using (Finset.card_le_card hst)
  submodular := by
    intro s t
    -- |s ∪ t| + |s ∩ t| = |s| + |t|
    change Finset.card (s ∪ t) + Finset.card (s ∩ t) ≤ Finset.card s + Finset.card t
    simpa using (le_of_eq (Finset.card_union_add_card_inter s t))
  v_bot := by rfl

/-- A trivial-but-safe valuation instance that assigns 0 everywhere.
Useful as a conservative default; nontrivial instances can be added later. -/
instance (L : Type*) [DistribLattice L] [OrderBot L] : Valuation L where
  v := fun _ => 0
  mono := by intro _ _ _; simp
  submodular := by intro _ _; simp
  v_bot := by simp

end Entropy
end Quantum
end CryptoSheaf
end LoF
end HeytingLean
