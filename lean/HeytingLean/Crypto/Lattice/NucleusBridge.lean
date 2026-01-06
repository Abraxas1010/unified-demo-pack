import HeytingLean.LoF.Nucleus

namespace HeytingLean
namespace Crypto
namespace Lattice

/-!
# Nucleus Recovery Problem (NRP) and Assumption (NRA)

This module provides a *statement-level* interface for the bridge assumption used by the PQC
work in `WIP/pqc_lattice/`.

Notes:
- We do **not** formalize probabilistic polynomial time here.
- We model the “public view” abstractly as an `encode : Nucleus α → Pub` together with a chosen
  set of instances (e.g. outputs of a generator).
- The recovery goal is parameterized by `goalEq`; by default this is definitional equality of
  nuclei, but the bridge may later use a trapdoor-equivalence relation.
-/

universe u

section

/-- Public view of a (hidden) secret, parameterized by an encoding. -/
structure RecoveryView (Secret : Type u) where
  /-- Public data seen by the adversary (e.g. a public key). -/
  Pub : Type u
  /-- Encoding that hides the secret behind public data. -/
  encode : Secret → Pub
  /-- The set of instances over which recovery is required (e.g. generator support). -/
  instances : Set Secret := Set.univ
  /-- Recovery goal equivalence; defaults to definitional equality. -/
  goalEq : Secret → Secret → Prop := (· = ·)

namespace RecoveryView

variable {Secret : Type u}

/-- A recovery function succeeds on a particular secret instance. -/
def succeedsOn (V : RecoveryView Secret) (recover : V.Pub → Secret) (s : Secret) : Prop :=
  s ∈ V.instances → V.goalEq (recover (V.encode s)) s

/-- The recovery function succeeds on all instances. -/
def solves (V : RecoveryView Secret) (recover : V.Pub → Secret) : Prop :=
  ∀ s, succeedsOn V recover s

end RecoveryView

/-- Public view of a (hidden) nucleus, parameterized by an encoding. -/
abbrev PublicView (α : Type u) [SemilatticeInf α] : Type (u+1) :=
  RecoveryView (Nucleus α)

namespace PublicView

variable {α : Type u} [SemilatticeInf α]

abbrev succeedsOn (V : PublicView (α := α)) (recover : V.Pub → Nucleus α) (R : Nucleus α) : Prop :=
  RecoveryView.succeedsOn V recover R

abbrev solves (V : PublicView (α := α)) (recover : V.Pub → Nucleus α) : Prop :=
  RecoveryView.solves V recover

end PublicView

/-- Nucleus Recovery Problem (NRP): recover the hidden nucleus from its public view. -/
def NRP {α : Type u} [SemilatticeInf α] (V : PublicView α) (recover : V.Pub → Nucleus α) : Prop :=
  PublicView.solves V recover

/-- Nucleus Recovery Assumption (NRA): no single recovery function solves NRP on all instances. -/
def NRA {α : Type u} [SemilatticeInf α] (V : PublicView α) : Prop :=
  ¬ ∃ recover : V.Pub → Nucleus α, NRP V recover

end

end Lattice
end Crypto
end HeytingLean
