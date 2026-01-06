import HeytingLean.Crypto.Lattice.NoiseMLWE
import HeytingLean.Crypto.Lattice.RecoveryViews
import HeytingLean.Crypto.ZK.ProofOfKnowledgeSpec

/-!
# SIS-backed proof-of-knowledge demo (spec connection)

This file instantiates the generic `PoK` interface from `ProofOfKnowledgeSpec` using the
statement-level SIS carrier from `Crypto.Lattice.RecoveryViews`.

Important:
- This is **not** a real ZK protocol.
- The provided PoK instance is the trivial “proof carries the witness” construction.
  Its purpose is to make the PQC lattice ↔ ZK interface connection explicit and compile-checked.
-/

namespace HeytingLean.Crypto.ZK

open HeytingLean.Crypto.Lattice

/-!
## SIS relation: `A*x = 0` with a coefficient-wise shortness predicate

Shortness uses `ZMod.val` (Nat representatives) via `Crypto.Lattice.coeffBound`.
-/

def ShortNatRep (P : SISParams) (β : Nat) (x : ZVec P.n P.q) : Prop :=
  ∀ i, coeffBound (x i) ≤ β

theorem shortNatRep_zero (P : SISParams) (β : Nat) : ShortNatRep P β (0 : ZVec P.n P.q) := by
  intro i
  simp

def SISRel (P : SISParams) (β : Nat) : Relation (SISInstance P) (ZVec P.n P.q) where
  holds := fun inst x => inst.A.mulVec x = 0 ∧ ShortNatRep P β x

/-!
## A stable Boolean verifier for the SIS relation

We avoid `Classical` decidability here so this verifier can be reused in executable-facing code.
-/

def vecEqZeroCheck {n q : Nat} (v : ZVec n q) : Bool :=
  (List.finRange n).all fun i => decide (v i = 0)

theorem vecEqZeroCheck_sound {n q : Nat} {v : ZVec n q} :
    vecEqZeroCheck v = true → v = 0 := by
  intro h
  funext i
  have hall : ∀ x ∈ List.finRange n, decide (v x = 0) = true := (List.all_eq_true).1 h
  have hi : decide (v i = 0) = true := hall i (List.mem_finRange i)
  exact (Bool.decide_iff (v i = 0)).1 hi

def shortNatRepCheck (P : SISParams) (β : Nat) (x : ZVec P.n P.q) : Bool :=
  (List.finRange P.n).all fun i => decide (coeffBound (x i) ≤ β)

theorem shortNatRepCheck_sound {P : SISParams} {β : Nat} {x : ZVec P.n P.q} :
    shortNatRepCheck P β x = true → ShortNatRep P β x := by
  intro h i
  have hall : ∀ j ∈ List.finRange P.n, decide (coeffBound (x j) ≤ β) = true := (List.all_eq_true).1 h
  have hi : decide (coeffBound (x i) ≤ β) = true := hall i (List.mem_finRange i)
  exact (Bool.decide_iff (coeffBound (x i) ≤ β)).1 hi

def sisVerify (P : SISParams) (β : Nat) (inst : SISInstance P) (x : ZVec P.n P.q) : Bool :=
  vecEqZeroCheck (inst.A.mulVec x) && shortNatRepCheck P β x

theorem sisVerify_sound {P : SISParams} {β : Nat} {inst : SISInstance P} {x : ZVec P.n P.q} :
    sisVerify P β inst x = true → (SISRel P β).holds inst x := by
  intro h
  have h' :
      vecEqZeroCheck (inst.A.mulVec x) = true ∧ shortNatRepCheck P β x = true := by
    exact (Eq.mp (Bool.and_eq_true_eq_eq_true_and_eq_true _ _) h)
  refine ⟨?_, shortNatRepCheck_sound (P := P) (β := β) (x := x) h'.2⟩
  exact vecEqZeroCheck_sound (v := inst.A.mulVec x) h'.1

def sisPoK (P : SISParams) (β : Nat) :
    PoK (SISInstance P) (ZVec P.n P.q) (ZVec P.n P.q) (SISRel P β) where
  prove := fun _s w _hw => w
  verify := sisVerify P β
  sound := by
    intro s p hp
    exact ⟨p, sisVerify_sound (P := P) (β := β) (inst := s) (x := p) hp⟩

/-!
## Toy instance: witness `x = 0`
-/

def toyParams : SISParams :=
  { n := 1, m := 1, q := 17 }

def toyStmt : SISInstance toyParams :=
  { A := 0 }

theorem toyRelHolds : (SISRel toyParams 0).holds toyStmt (0 : ZVec toyParams.n toyParams.q) := by
  constructor
  · simp [toyStmt]
  · simpa using shortNatRep_zero toyParams 0

example :
    (sisPoK toyParams 0).verify toyStmt
      ((sisPoK toyParams 0).prove toyStmt (0 : ZVec toyParams.n toyParams.q) toyRelHolds) = true := by
  simp [sisPoK, sisVerify, vecEqZeroCheck, shortNatRepCheck, toyStmt]

end HeytingLean.Crypto.ZK
