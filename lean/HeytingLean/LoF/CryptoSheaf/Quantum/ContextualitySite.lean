import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic

namespace HeytingLean
namespace LoF
namespace CryptoSheaf
namespace Quantum

open Classical

abbrev Meas := Fin 3
abbrev Outcome := Bool
abbrev Context := Finset Meas

def MeasIn (U : Context) := { i : Meas // i ∈ U }
abbrev Assignment (U : Context) := MeasIn U → Outcome

def restrictAssign {V U : Context} (h : V ⊆ U) (s : Assignment U) : Assignment V :=
  fun ⟨i, hiV⟩ => s ⟨i, h hiV⟩

@[simp] theorem restrict_id {U : Context} (s : Assignment U) :
    restrictAssign (by intro i hi; simpa using hi : U ⊆ U) s = s := by
  funext x; cases x with
  | mk i hi => simp [restrictAssign]

@[simp] theorem restrict_comp {W V U : Context}
    (h₁ : W ⊆ V) (h₂ : V ⊆ U) (s : Assignment U) :
    restrictAssign h₁ (restrictAssign h₂ s) =
      (restrictAssign (by intro i hi; exact h₂ (h₁ hi)) s) := by
  funext x; cases x with
  | mk i hi => simp [restrictAssign]

@[simp] theorem inter_subset_left (U V : Context) : U ∩ V ⊆ U := by
  intro i hi
  exact (Finset.mem_of_subset (Finset.inter_subset_left) hi)

@[simp] theorem inter_subset_right (U V : Context) : U ∩ V ⊆ V := by
  intro i hi
  exact (Finset.mem_of_subset (Finset.inter_subset_right) hi)

-- On a self-intersection, left and right restrictions coincide pointwise
@[simp] theorem restrict_inter_self_eq
    (U : Context) (s : Assignment U) :
    restrictAssign (inter_subset_left U U) s =
    restrictAssign (inter_subset_right U U) s := by
  funext x; cases x with
  | mk i hi =>
    -- Both sides apply `s` to the same underlying measurement `i`.
    -- The subtype proofs are irrelevant (proof irrelevance).
    simp [restrictAssign]

-- Canonical measurements a,b,c
@[simp] def a : Meas := 0
@[simp] def b : Meas := 1
@[simp] def c : Meas := 2

-- Concrete contexts
def C_ab : Context := ([a, b] : List Meas).toFinset
def C_bc : Context := ([b, c] : List Meas).toFinset
def C_ac : Context := ([a, c] : List Meas).toFinset
def X_abc : Context := ([a, b, c] : List Meas).toFinset

-- Membership helpers
@[simp] theorem a_mem_ab : a ∈ C_ab := by simp [C_ab]
@[simp] theorem b_mem_ab : b ∈ C_ab := by simp [C_ab]
@[simp] theorem b_mem_bc : b ∈ C_bc := by simp [C_bc]
@[simp] theorem c_mem_bc : c ∈ C_bc := by simp [C_bc]
@[simp] theorem a_mem_ac : a ∈ C_ac := by simp [C_ac]
@[simp] theorem c_mem_ac : c ∈ C_ac := by simp [C_ac]

-- Subset-to-global helpers
@[simp] theorem subset_ab_abc : C_ab ⊆ X_abc := by
  intro i hi; simp [C_ab, X_abc] at *; rcases hi with hi | hi <;> simp [hi]

@[simp] theorem subset_bc_abc : C_bc ⊆ X_abc := by
  intro i hi; simp [C_bc, X_abc] at *; rcases hi with hi | hi <;> simp [hi]

@[simp] theorem subset_ac_abc : C_ac ⊆ X_abc := by
  intro i hi; simp [C_ac, X_abc] at *; rcases hi with hi | hi <;> simp [hi]

-- Overlap singletons (decidable by computation)
@[simp] theorem inter_ab_bc : C_ab ∩ C_bc = ({b} : Finset Meas) := by
  decide

@[simp] theorem inter_ab_ac : C_ab ∩ C_ac = ({a} : Finset Meas) := by
  decide

@[simp] theorem inter_bc_ac : C_bc ∩ C_ac = ({c} : Finset Meas) := by
  decide

@[simp] theorem b_mem_inter_ab_bc : b ∈ C_ab ∩ C_bc := by simp
@[simp] theorem a_mem_inter_ab_ac : a ∈ C_ab ∩ C_ac := by simp
@[simp] theorem c_mem_inter_bc_ac : c ∈ C_bc ∩ C_ac := by simp

-- Any element of a singleton-subtype has the indicated value
@[simp] theorem val_of_mem_singleton {m : Meas} (x : MeasIn ({m} : Context)) : x.1 = m := by
  cases x with
  | mk i hi => simpa using (Finset.mem_singleton.mp hi)

end Quantum
end CryptoSheaf
end LoF
end HeytingLean
