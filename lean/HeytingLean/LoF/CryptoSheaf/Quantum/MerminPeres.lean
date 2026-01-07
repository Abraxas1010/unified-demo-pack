import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
Mermin–Peres square (combinatorial/parity layer).

This file proves the standard *state-independent* parity obstruction:
there is no assignment of ±1 values to a 3×3 grid satisfying the six
row/column product constraints (five with product +1, one with product -1).

It is independent of any matrix quantum mechanics; the quantum realization
layer lives under `HeytingLean.Quantum.Contextuality`.
-/

namespace HeytingLean
namespace LoF
namespace CryptoSheaf
namespace Quantum

open scoped BigOperators

abbrev MPCell := Fin 3 × Fin 3
abbrev MPVal := Units ℤ

namespace MerminPeres

private def negOne : MPVal :=
  ⟨(-1 : ℤ), (-1 : ℤ), by simp, by simp⟩

variable (v : MPCell → MPVal)

/-- Product of the three values in row `i`. -/
def rowProd (i : Fin 3) : MPVal :=
  ∏ j : Fin 3, v (i, j)

/-- Product of the three values in column `j`. -/
def colProd (j : Fin 3) : MPVal :=
  ∏ i : Fin 3, v (i, j)

theorem no_assignment :
    ¬ ∃ v : MPCell → MPVal,
        (∀ i : Fin 3, rowProd v i = 1) ∧
        (∀ j : Fin 3, colProd v j = (if j = (2 : Fin 3) then negOne else 1)) := by
  classical
  intro h
  rcases h with ⟨v, hrow, hcol⟩

  have hrowAll : (∏ i : Fin 3, rowProd v i) = 1 := by
    simp [hrow]

  have hcolAll : (∏ j : Fin 3, colProd v j) = negOne := by
    -- Expand the product of column-constraints: exactly one column has product `-1`.
    calc
      (∏ j : Fin 3, colProd v j) = ∏ j : Fin 3, (if j = (2 : Fin 3) then negOne else 1) := by
        simp [hcol]
      _ = negOne := by
        -- Evaluate the 3-term product explicitly.
        simp

  -- The product of all row products and the product of all column products are the same:
  -- both are the global product over the 3×3 grid.
  have hswap : (∏ i : Fin 3, rowProd v i) = (∏ j : Fin 3, colProd v j) := by
    -- Rewrite both sides as `∏ p : Fin 3 × Fin 3, v p` using `Fintype.prod_prod_type`.
    have h1 : (∏ i : Fin 3, rowProd v i) = ∏ p : MPCell, v p := by
      simpa [rowProd] using (Fintype.prod_prod_type (f := fun p : MPCell => v p)).symm
    have h2 : (∏ j : Fin 3, colProd v j) = ∏ p : MPCell, v p := by
      -- `prod_prod_type_right` swaps the nesting order.
      simpa [colProd] using (Fintype.prod_prod_type_right (f := fun p : MPCell => v p)).symm
    exact h1.trans h2.symm

  have : (1 : MPVal) = negOne := by
    calc
      (1 : MPVal) = (∏ i : Fin 3, rowProd v i) := by
        simpa using hrowAll.symm
      _ = (∏ j : Fin 3, colProd v j) := hswap
      _ = negOne := hcolAll

  exact (by
    have hne : (1 : MPVal) ≠ negOne := by decide
    exact hne this)

end MerminPeres

end Quantum
end CryptoSheaf
end LoF
end HeytingLean
