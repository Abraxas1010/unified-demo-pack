import HeytingLean.Crypto.Lattice.NucleusBridge
import HeytingLean.Crypto.Lattice.Problems
import HeytingLean.Crypto.Lattice.Reductions

namespace HeytingLean
namespace Crypto
namespace Lattice

/-!
# Placeholder Recovery Views for Lattice Problems

This file introduces statement-level `RecoveryView` wrappers for:
- trapdoor recovery (GPV-style, placeholder);
- LWE secret recovery (placeholder); and
- SIS short-solution recovery (placeholder).

These are *interfaces only*: no computational complexity model, no distributions, and no concrete
matrix/ring realizations yet. The goal is to let us state reductions early and refine later.
-/

universe u v

/-- Generic unsolvability (hardness) predicate for a recovery view. -/
def Unsolvable {Secret : Type u} (V : RecoveryView Secret) : Prop :=
  ¬ ∃ recover : V.Pub → Secret, RecoveryView.solves V recover

namespace Unsolvable

variable {α : Type u} [SemilatticeInf α]

@[simp] theorem iff_nra (V : PublicView (α := α)) : Unsolvable V ↔ NRA V := by
  rfl

end Unsolvable

/-!
## LWE Secret Recovery (placeholder)

Model: secret contains a public LWE instance together with a witness for the secret.
-/

structure LWESecret (P : LWEParams) where
  inst : LWEInstance P
  /-- Secret vector. -/
  s : ZVec P.n P.q := 0
  /-- Error vector (witness). -/
  e : ZVec P.m P.q := 0
  deriving Repr, Inhabited

def LWEView (P : LWEParams) : RecoveryView (LWESecret P) where
  Pub := LWEInstance P
  encode := fun s => s.inst

/-!
## Module-LWE Secret Recovery (placeholder)

This matches the “module lattice” assumptions referenced by FIPS 203/204 families.
-/

structure MLWESecret (P : MLWEParams) where
  inst : MLWEInstance P
  /-- Secret module vector. -/
  s : ModVec P.k P.n P.q := 0
  /-- Error module vector (witness). -/
  e : ModVec P.k P.n P.q := 0
  deriving Repr, Inhabited

def MLWEView (P : MLWEParams) : RecoveryView (MLWESecret P) where
  Pub := MLWEInstance P
  encode := fun s => s.inst

/-!
## SIS Short-Solution Recovery (placeholder)

We only record parameters; the concrete matrix/vector types will be added later.
-/

structure SISInstance (_P : SISParams) where
  A : ZMat _P.m _P.n _P.q := 0
  deriving Repr, Inhabited

structure SISSecret (P : SISParams) where
  inst : SISInstance P
  /-- Witness vector (later: short integer vector with a norm bound). -/
  x : ZVec P.n P.q := 0
  deriving Repr, Inhabited

def SISView (P : SISParams) : RecoveryView (SISSecret P) where
  Pub := SISInstance P
  encode := fun s => s.inst

/-!
## Trapdoor Recovery (placeholder)

Model: secret contains a public instance together with a trapdoor witness; the public view exposes
only the instance.
-/

structure TrapdoorParams where
  m : Nat
  n : Nat
  q : Nat
  deriving Repr, DecidableEq

structure TrapdoorInstance (P : TrapdoorParams) where
  A : ZMat P.m P.n P.q := 0
  deriving Repr, Inhabited

structure TrapdoorSecret (P : TrapdoorParams) where
  inst : TrapdoorInstance P
  trapdoor : Unit := ()
  deriving Repr, Inhabited

def TrapdoorView (P : TrapdoorParams) : RecoveryView (TrapdoorSecret P) where
  Pub := TrapdoorInstance P
  encode := fun s => s.inst

/-!
## Hardness Transport (NRA endpoints)
-/

/-- Stage B bridge interface: bundle the data/proofs required to build a reduction
from a nucleus public view to a trapdoor recovery view. -/
abbrev BridgeToTrapdoor {α : Type u} [SemilatticeInf α]
    (Vn : PublicView (α := α)) (P : TrapdoorParams) :=
  Reduction.BridgeData Vn (TrapdoorView P)

theorem nra_of_trapdoor_unsolvable {α : Type u} [SemilatticeInf α]
    (Vn : PublicView (α := α)) (P : TrapdoorParams)
    (R : Reduction Vn (TrapdoorView P)) :
    Unsolvable (TrapdoorView P) → NRA Vn := by
  intro htd
  have hn : Unsolvable Vn := (Reduction.unsolvable_of_unsolvable R) htd
  exact (Unsolvable.iff_nra (α := α) Vn).1 hn

theorem nra_of_trapdoor_unsolvable_of_bridge {α : Type u} [SemilatticeInf α]
    (Vn : PublicView (α := α)) (P : TrapdoorParams)
    (B : BridgeToTrapdoor (Vn := Vn) P) :
    Unsolvable (TrapdoorView P) → NRA Vn := by
  intro htd
  exact nra_of_trapdoor_unsolvable (Vn := Vn) (P := P) (R := B.toReduction) htd

theorem nra_of_unsolvable {α : Type u} [SemilatticeInf α]
    (Vn : PublicView (α := α)) {S₂ : Type v} {V₂ : RecoveryView S₂}
    (R : Reduction Vn V₂) :
    Unsolvable V₂ → NRA Vn := by
  intro h₂
  have hn : Unsolvable Vn := (Reduction.unsolvable_of_unsolvable R) h₂
  exact (Unsolvable.iff_nra (α := α) Vn).1 hn

/-!
## Stage C bridge aliases + chained hardness lemmas
-/

/-- Stage C bridge interface: bundle the data/proofs required to build a reduction
from trapdoor recovery to LWE recovery. -/
abbrev BridgeTrapdoorToLWE (Ptd : TrapdoorParams) (Plwe : LWEParams) : Type :=
  Reduction.BridgeData (TrapdoorView Ptd) (LWEView Plwe)

theorem nra_of_lwe_unsolvable {α : Type u} [SemilatticeInf α]
    (Vn : PublicView (α := α)) (Ptd : TrapdoorParams) (Plwe : LWEParams)
    (R₁ : Reduction Vn (TrapdoorView Ptd))
    (R₂ : Reduction (TrapdoorView Ptd) (LWEView Plwe)) :
    Unsolvable (LWEView Plwe) → NRA Vn := by
  intro hlwe
  exact nra_of_unsolvable (Vn := Vn) (R := Reduction.comp R₁ R₂) hlwe

/-- Stage C bridge interface: bundle the data/proofs required to build a reduction
from trapdoor recovery to module-LWE recovery. -/
abbrev BridgeTrapdoorToMLWE (Ptd : TrapdoorParams) (Pmlwe : MLWEParams) : Type :=
  Reduction.BridgeData (TrapdoorView Ptd) (MLWEView Pmlwe)

theorem nra_of_mlwe_unsolvable {α : Type u} [SemilatticeInf α]
    (Vn : PublicView (α := α)) (Ptd : TrapdoorParams) (Pmlwe : MLWEParams)
    (R₁ : Reduction Vn (TrapdoorView Ptd))
    (R₂ : Reduction (TrapdoorView Ptd) (MLWEView Pmlwe)) :
    Unsolvable (MLWEView Pmlwe) → NRA Vn := by
  intro hmlwe
  exact nra_of_unsolvable (Vn := Vn) (R := Reduction.comp R₁ R₂) hmlwe

/-- Stage C bridge interface: bundle the data/proofs required to build a reduction
from trapdoor recovery to SIS short-solution recovery. -/
abbrev BridgeTrapdoorToSIS (Ptd : TrapdoorParams) (Psis : SISParams) : Type :=
  Reduction.BridgeData (TrapdoorView Ptd) (SISView Psis)

theorem nra_of_sis_unsolvable {α : Type u} [SemilatticeInf α]
    (Vn : PublicView (α := α)) (Ptd : TrapdoorParams) (Psis : SISParams)
    (R₁ : Reduction Vn (TrapdoorView Ptd))
    (R₂ : Reduction (TrapdoorView Ptd) (SISView Psis)) :
    Unsolvable (SISView Psis) → NRA Vn := by
  intro hsis
  exact nra_of_unsolvable (Vn := Vn) (R := Reduction.comp R₁ R₂) hsis

end Lattice
end Crypto
end HeytingLean
