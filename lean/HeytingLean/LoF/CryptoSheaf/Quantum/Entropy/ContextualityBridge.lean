import Mathlib.Data.Fintype.Basic
import HeytingLean.LoF.CryptoSheaf.Quantum.ContextualitySite
import HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel
import HeytingLean.LoF.CryptoSheaf.Quantum.Entropy.Basic

/-
Small bridge from contextuality supports to finite-size proxies. We avoid
any strong “entropy” claims and only expose cardinalities of support sets
in finite cases (e.g., the triangle demo with Bool outcomes).
-/
namespace HeytingLean
namespace LoF
namespace CryptoSheaf
namespace Quantum
namespace Entropy

open Classical

-- Ensure finiteness is visible on the base measurement type `Meas := Fin 3`.
instance finiteMeas : Finite Meas := by infer_instance

-- Finite function spaces: for our `Assignment U := MeasIn U → Bool` we get finiteness.
instance instFiniteMeasIn (U : Context) : Finite (MeasIn U) := by
  classical
  -- Inject into the finite type `Meas` via `.1`
  refine (Finite.of_injective (fun x : MeasIn U => x.1) ?inj)
  intro x y h
  cases x; cases y
  -- `Subtype.ext` will finish after reducing
  cases h
  rfl

noncomputable instance instFintypeMeasIn (U : Context) : Fintype (MeasIn U) := by
  -- `Meas := Fin 3` is finite; `{i // i ∈ U}` is a subtype of a finite type
  classical
  exact Fintype.ofFinite _

noncomputable instance instFintypeAssignment (U : Context) : Fintype (Assignment U) := by
  -- Functions from a finite domain to a finite codomain are finite
  classical
  exact inferInstance

/-- Cardinality of a support set (as a subtype) in the finite assignment space. -/
noncomputable def supportSize {C : Context} (S : Set (Assignment C)) : Nat :=
  Fintype.card { s // s ∈ S }

/-!
  For the triangle demo, supports are definable sets of assignments with
  simple parity constraints. We avoid trying to fully enumerate here; the
  size can be reasoned about in future work or measured in tiny cases.
-/

end Entropy
end Quantum
end CryptoSheaf
end LoF
end HeytingLean
/-!
### Tiny support-size facts for the triangle witness

Using the constructors from `EmpiricalModel.lean`, we show each triangle
support has size 2. Intuitively, each constraint has one free Bool.
-/

open HeytingLean.LoF.CryptoSheaf.Quantum

private lemma mem_C_ab_iff (x : Meas) : x ∈ C_ab ↔ x = a ∨ x = b := by
  classical
  simp [C_ab]

private lemma mem_C_bc_iff (x : Meas) : x ∈ C_bc ↔ x = b ∨ x = c := by
  classical
  simp [C_bc]

noncomputable def equivSupportAB : {s // s ∈ supportAB} ≃ Bool :=
{ toFun := fun p => p.1 a_in_ab,
  invFun := fun v => ⟨(fun _ => v), by simpa [supportAB]⟩,
  left_inv := by
    intro p; cases p with
    | mk s hs =>
      -- s satisfies a=b; show s equals the constant assignment with value s a
      apply Subtype.ext
      funext x; classical
      -- reduce x to either a or b
      have hx : x = a_in_ab ∨ x = b_in_ab := by
        have hx' : x.1 = a ∨ x.1 = b := (mem_C_ab_iff x.1).1 x.2
        rcases hx' with hxa | hxb
        · left; apply Subtype.ext; simpa [hxa]
        · right; apply Subtype.ext; simpa [hxb]
      rcases hx with hxa | hxb
      · simpa [hxa]
      · have hab : s a_in_ab = s b_in_ab := by simpa [supportAB] using hs
        simpa [hxb, hab]
  , right_inv := by intro v; rfl }

noncomputable def equivSupportBC : {s // s ∈ supportBC} ≃ Bool :=
{ toFun := fun p => p.1 b_in_bc,
  invFun := fun v => ⟨(fun _ => v), by simpa [supportBC]⟩,
  left_inv := by
    intro p; cases p with
    | mk s hs =>
      apply Subtype.ext; funext x; classical
      have hx : x = b_in_bc ∨ x = c_in_bc := by
        have hx' : x.1 = b ∨ x.1 = c := (mem_C_bc_iff x.1).1 x.2
        rcases hx' with hxb | hxc
        · left; apply Subtype.ext; simp [hxb, b_in_bc, b]
        · right; apply Subtype.ext; simp [hxc, c_in_bc, c]
      rcases hx with hxb | hxc
      · simpa [hxb]
      · have hbc : s b_in_bc = s c_in_bc := by simpa [supportBC] using hs
        simpa [hxc, hbc]
  , right_inv := by intro v; rfl }

theorem supportAB_size_two :
  Entropy.supportSize (C:=C_ab) (supportAB) = 2 := by
  classical
  have h := Fintype.card_congr (equivSupportAB)
  simpa [Entropy.supportSize] using h

theorem supportBC_size_two :
  Entropy.supportSize (C:=C_bc) (supportBC) = 2 := by
  classical
  have h := Fintype.card_congr (equivSupportBC)
  simpa [Entropy.supportSize] using h
