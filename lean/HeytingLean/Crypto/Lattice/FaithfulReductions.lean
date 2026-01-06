import HeytingLean.Crypto.Lattice.Reductions
import HeytingLean.Crypto.Lattice.Rings
import HeytingLean.Crypto.Lattice.Problems
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace HeytingLean
namespace Crypto
namespace Lattice

/-!
# “Faithful” lattice reductions (v1.0)

This module upgrades the previous “statement-only / payload-embedding” reductions by introducing:
- explicit algebraic carriers (cyclotomic quotient ring + matrices);
- explicit *equation-level* problem statements; and
- concrete `Reduction.BridgeData` instances whose `decode` functions use actual algebraic
  equalities (matrix inversion / block structure), not auxiliary witness payload fields.

This remains a statement-first development: we do not model PPT, distributions, or tight security
losses here.
-/

open scoped Classical BigOperators

noncomputable section

/-!
## Stage C (MLWE side): inversion trapdoor ⇒ noiseless ring-MLWE recovery

We model a simple “trapdoor” for ring-MLWE as the ability to recover an inverse matrix.
Given an invertible public matrix `A` and `b = A*s`, one can recover `s = A⁻¹*b`.

This is not GPV; it is a concrete, checkable algebraic reduction over the cyclotomic quotient ring.
-/

namespace RingMLWE

def cycloOf (P : MLWEParams) : CycloParams :=
  { n := P.n, q := P.q }

abbrev Rq (P : MLWEParams) : Type :=
  Rings.Rq (cycloOf P)

abbrev ModVec (P : MLWEParams) : Type :=
  Fin P.k → Rq P

abbrev ModMat (P : MLWEParams) : Type :=
  Matrix (Fin P.k) (Fin P.k) (Rq P)

structure Instance (P : MLWEParams) where
  A : ModMat P
  b : ModVec P

structure Secret (P : MLWEParams) where
  inst : Instance P
  s : ModVec P
  correct : inst.b = inst.A.mulVec s

noncomputable def junkSecret (P : MLWEParams) : Secret P :=
  { inst := { A := 0, b := 0 }
    s := 0
    correct := by simp }

def View (P : MLWEParams) : RecoveryView (Secret P) where
  Pub := Instance P
  encode := fun s => s.inst
  -- Restrict to instances with invertible `A` (det is a unit), so the secret is uniquely decodable.
  instances := { s | IsUnit (Matrix.det s.inst.A) }
  goalEq := (· = ·)

structure InvTrapdoor (P : MLWEParams) where
  A : ModMat P
  invA : ModMat P
  mul_inv : IsUnit (Matrix.det A) → A * invA = 1
  inv_mul : IsUnit (Matrix.det A) → invA * A = 1

def InvView (P : MLWEParams) : RecoveryView (InvTrapdoor P) where
  Pub := ModMat P
  encode := fun td => td.A
  instances := { td | IsUnit (Matrix.det td.A) }
  goalEq := (· = ·)

noncomputable def mapSecret (P : MLWEParams) (s : Secret P) : InvTrapdoor P :=
  { A := s.inst.A
    invA := s.inst.A⁻¹
    mul_inv := fun h => by simpa using (Matrix.mul_nonsing_inv s.inst.A h)
    inv_mul := fun h => by simpa using (Matrix.nonsing_inv_mul s.inst.A h) }

noncomputable def decode (P : MLWEParams) (pub : Instance P) (td : InvTrapdoor P) : Secret P := by
  classical
  by_cases hA : td.A = pub.A
  · by_cases hdet : IsUnit (Matrix.det pub.A)
    · refine
        { inst := pub
          s := td.invA.mulVec pub.b
          correct := ?_ }
      have hdet' : IsUnit (Matrix.det td.A) := by simpa [hA] using hdet
      have hmul : pub.A * td.invA = 1 := by
        simpa [hA] using td.mul_inv hdet'
      have hb : pub.A.mulVec (td.invA.mulVec pub.b) = pub.b := by
        calc
          pub.A.mulVec (td.invA.mulVec pub.b) = (pub.A * td.invA).mulVec pub.b := by
            simp [Matrix.mulVec_mulVec]
          _ = (1 : ModMat P).mulVec pub.b := by simp [hmul]
          _ = pub.b := by simp
      exact hb.symm
    · exact junkSecret P
  · exact junkSecret P

@[ext] theorem Secret.ext {P : MLWEParams} (x y : Secret P)
    (hinst : x.inst = y.inst) (hs : x.s = y.s) : x = y := by
  cases x
  cases y
  cases hinst
  cases hs
  simp

/-- Concrete Stage C bridge: inversion trapdoor recovery ⇒ noiseless ring-MLWE recovery. -/
noncomputable def bridgeInvTrapdoorToMLWE (P : MLWEParams) :
    Reduction.BridgeData (InvView P) (View P) where
  mapPub := fun pub => pub.A
  mapSecret := mapSecret P
  decode := fun pub td => decode P pub td
  mapInstances := by
    intro s hs
    simpa [View, InvView, mapSecret] using hs
  encode_comm := by
    intro s
    rfl
  decode_correct := by
    intro s hs r hr
    subst hr
    have hdet : IsUnit (Matrix.det s.inst.A) := by
      simpa [View] using hs
    -- Evaluate the conditionals in `decode` (they are true in the correctness case).
    have hinst' : (decode P s.inst (mapSecret P s)).inst = s.inst := by
      simp [decode, mapSecret, hdet]
    have hs' : (decode P s.inst (mapSecret P s)).s = s.s := by
      -- Reduce to the inverse-cancels property.
      simp [decode, mapSecret, hdet, s.correct, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul]
    -- Now use extensionality to ignore proof fields.
    exact Secret.ext (x := decode P s.inst (mapSecret P s)) (y := s) hinst' hs'

end RingMLWE

/-!
## Stage C (SIS side): gadget-form trapdoor ⇒ SIS witness

We model a concrete, checkable “trapdoor family” for SIS:
- public matrix is `[I | R]` (identity block + free right block);
- given `R`, one can explicitly construct a nonzero kernel vector `(-R*y, y)`.

This is not GPV, but it is a concrete construction and an actual algebraic reduction.
-/

namespace GadgetSIS

structure Params where
  m : Nat
  t : Nat
  q : Nat
  deriving Repr, DecidableEq

abbrev Cols (P : Params) : Type := Fin P.m ⊕ Fin P.t

abbrev Zq (P : Params) : Type := Lattice.Zq P.q

abbrev Mat (P : Params) : Type :=
  Matrix (Fin P.m) (Cols P) (Zq P)

abbrev RBlock (P : Params) : Type :=
  Matrix (Fin P.m) (Fin P.t) (Zq P)

abbrev Vec (P : Params) : Type := Cols P → Zq P

def gadgetMatrix (P : Params) (R : RBlock P) : Mat P :=
  fun i j =>
    match j with
    | Sum.inl jL => if i = jL then 1 else 0
    | Sum.inr jR => R i jR

structure Instance (P : Params) where
  A : Mat P

def TrapdoorView (P : Params) : RecoveryView (RBlock P) where
  Pub := Instance P
  encode := fun R => { A := gadgetMatrix P R }
  goalEq := (· = ·)

structure SISSecret (P : Params) where
  /-- The hidden right block `R` (derivable from the public gadget matrix, but kept explicit). -/
  R : RBlock P
  x : Vec P
  hx : (gadgetMatrix P R).mulVec x = 0
  hne : x ≠ 0

def SISView (P : Params) : RecoveryView (SISSecret P) where
  Pub := Instance P
  encode := fun s => { A := gadgetMatrix P s.R }
  -- Search-SIS: any nonzero kernel vector is acceptable.
  goalEq := fun r s => r.R = s.R

variable {P : Params} (ht : 0 < P.t) [Fact (1 < P.q)]

private def fin0 : Fin P.t := ⟨0, ht⟩

private def basisVec : Fin P.t → Zq P := fun j => if j = fin0 (P := P) ht then 1 else 0

private def sisWitness (P : Params) (R : RBlock P) (ht : 0 < P.t) : Vec P :=
  let y : Fin P.t → Zq P := basisVec (P := P) ht
  Sum.elim (fun i => -(R.mulVec y) i) (fun j => y j)

private theorem gadget_mulVec_witness (P : Params) (R : RBlock P) (ht : 0 < P.t) :
    (gadgetMatrix P R).mulVec (sisWitness P R ht) = 0 := by
  classical
  ext i
  let y : Fin P.t → Zq P := basisVec (P := P) ht
  let xL : Fin P.m → Zq P := fun j => -(R.mulVec y) j
  have hR : (∑ j : Fin P.t, R i j * y j) = (R.mulVec y) i := by
    rfl
  -- Split the sum over `Fin m ⊕ Fin t` and cancel.
  have :
      (gadgetMatrix P R).mulVec (sisWitness P R ht) i =
        (∑ j : Fin P.m, (if i = j then (1 : Zq P) else 0) * xL j) +
          (∑ j : Fin P.t, R i j * y j) := by
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, gadgetMatrix, sisWitness, xL, y]
  -- Finish.
  calc
    (gadgetMatrix P R).mulVec (sisWitness P R ht) i
        = (∑ j : Fin P.m, (if i = j then (1 : Zq P) else 0) * xL j) +
            (∑ j : Fin P.t, R i j * y j) := this
    _ = xL i + (R.mulVec y) i := by simp [hR]
    _ = 0 := by simp [xL]

private theorem witness_ne_zero (P : Params) (R : RBlock P) (ht : 0 < P.t) [Fact (1 < P.q)] :
    sisWitness P R ht ≠ (0 : Vec P) := by
  classical
  intro h
  -- Evaluate on the right block at index `0`; it is `1`.
  have hz : (sisWitness P R ht) (Sum.inr (fin0 (P := P) ht)) = 0 := by
    simp [h]
  simp [sisWitness, basisVec, fin0] at hz

noncomputable def decodeSIS (P : Params) (ht : 0 < P.t) [Fact (1 < P.q)] (R : RBlock P) :
    SISSecret P := by
  classical
  refine
    { R := R
      x := sisWitness P R ht
      hx := gadget_mulVec_witness P R ht
      hne := witness_ne_zero P R ht }

/-- Concrete Stage C bridge: gadget trapdoor recovery ⇒ SIS witness recovery. -/
noncomputable def bridgeTrapdoorToSIS (P : Params) (ht : 0 < P.t) [Fact (1 < P.q)] :
    Reduction.BridgeData (TrapdoorView P) (SISView P) where
  mapPub := fun pub => pub
  mapSecret := fun s => s.R
  decode := fun _pub R => decodeSIS (P := P) ht R
  mapInstances := by
    intro _s _hs
    trivial
  encode_comm := by
    intro _s
    rfl
  decode_correct := by
    intro s _hs r hr
    subst hr
    simp [SISView, decodeSIS]

end GadgetSIS

/-!
## Stage C (SIS side, generalized): invertible left block ⇒ SIS witness

`GadgetSIS` fixes the left block to the identity `[I | R]`. To move beyond that restricted family,
we also provide a *block* family `[L | R]` where the left block `L` is (secretly) invertible.

Given an inverse `L⁻¹`, one can explicitly construct a nonzero kernel vector:
`x = (-L⁻¹ * (R*y), y)` for any nonzero `y`.

This is still statement-first and is not a GPV trapdoor; it is a concrete, checkable algebraic
construction useful for bridging out of abstract trapdoor views.
-/

namespace BlockSIS

structure Params where
  m : Nat
  t : Nat
  q : Nat
  deriving Repr, DecidableEq

abbrev Cols (P : Params) : Type := Fin P.m ⊕ Fin P.t

abbrev Zq (P : Params) : Type := Lattice.Zq P.q

abbrev Mat (P : Params) : Type :=
  Matrix (Fin P.m) (Cols P) (Zq P)

abbrev LBlock (P : Params) : Type :=
  Matrix (Fin P.m) (Fin P.m) (Zq P)

abbrev RBlock (P : Params) : Type :=
  Matrix (Fin P.m) (Fin P.t) (Zq P)

abbrev Vec (P : Params) : Type := Cols P → Zq P

def blockMatrix (P : Params) (L : LBlock P) (R : RBlock P) : Mat P :=
  fun i j =>
    match j with
    | Sum.inl jL => L i jL
    | Sum.inr jR => R i jR

structure Instance (P : Params) where
  A : Mat P

structure Trapdoor (P : Params) where
  L : LBlock P
  R : RBlock P
  invL : LBlock P
  mul_inv : L * invL = 1
  inv_mul : invL * L = 1

def TrapdoorView (P : Params) : RecoveryView (Trapdoor P) where
  Pub := Instance P
  encode := fun td => { A := blockMatrix P td.L td.R }
  goalEq := (· = ·)

structure SISSecret (P : Params) where
  td : Trapdoor P
  x : Vec P
  hx : (blockMatrix P td.L td.R).mulVec x = 0
  hne : x ≠ 0

def SISView (P : Params) : RecoveryView (SISSecret P) where
  Pub := Instance P
  encode := fun s => { A := blockMatrix P s.td.L s.td.R }
  goalEq := fun r s => r.td.L = s.td.L ∧ r.td.R = s.td.R

variable {P : Params} (ht : 0 < P.t) [Fact (1 < P.q)]

private def fin0 : Fin P.t := ⟨0, ht⟩

private def basisVec : Fin P.t → Zq P := fun j => if j = fin0 (P := P) ht then 1 else 0

private def sisWitness (P : Params) (td : Trapdoor P) (ht : 0 < P.t) : Vec P :=
  let y : Fin P.t → Zq P := basisVec (P := P) ht
  let v : Fin P.m → Zq P := td.R.mulVec y
  Sum.elim (fun i => -(td.invL.mulVec v) i) (fun j => y j)

private theorem block_mulVec_witness (P : Params) (td : Trapdoor P) (ht : 0 < P.t) [Fact (1 < P.q)] :
    (blockMatrix P td.L td.R).mulVec (sisWitness P td ht) = 0 := by
  classical
  ext i
  let y : Fin P.t → Zq P := basisVec (P := P) ht
  let v : Fin P.m → Zq P := td.R.mulVec y
  let xL : Fin P.m → Zq P := fun j => -(td.invL.mulVec v) j
  have hsplit :
      (blockMatrix P td.L td.R).mulVec (sisWitness P td ht) i =
        (∑ j : Fin P.m, td.L i j * xL j) + (∑ j : Fin P.t, td.R i j * y j) := by
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, blockMatrix, sisWitness, xL, y, v]
  have hLvec : td.L.mulVec xL = -(td.R.mulVec y) := by
    -- `L *ᵥ (-(invL *ᵥ v)) = -(L * invL) *ᵥ v = -v`
    calc
      td.L.mulVec xL = td.L.mulVec (-(td.invL.mulVec v)) := by rfl
      _ = -(td.L.mulVec (td.invL.mulVec v)) := by
        -- `A *ᵥ (-w) = -(A *ᵥ w)`
        simpa using (Matrix.mulVec_neg (v := td.invL.mulVec v) (A := td.L))
      _ = -((td.L * td.invL).mulVec v) := by
        simp [Matrix.mulVec_mulVec]
      _ = -v := by
        simp [td.mul_inv]
      _ = -(td.R.mulVec y) := by rfl
  have hLidx : (td.L.mulVec xL) i = -(td.R.mulVec y) i := by
    simpa using congrArg (fun f => f i) hLvec
  -- Combine the block split with `L*xL = -(R*y)`.
  calc
    (blockMatrix P td.L td.R).mulVec (sisWitness P td ht) i
        = (td.L.mulVec xL) i + (td.R.mulVec y) i := by
            simpa [Matrix.mulVec, dotProduct] using hsplit
    _ = 0 := by simp [hLidx]

private theorem witness_ne_zero (P : Params) (td : Trapdoor P) (ht : 0 < P.t) [Fact (1 < P.q)] :
    sisWitness P td ht ≠ (0 : Vec P) := by
  classical
  intro h
  have hz : (sisWitness P td ht) (Sum.inr (fin0 (P := P) ht)) = 0 := by
    simp [h]
  simp [sisWitness, basisVec, fin0] at hz

noncomputable def decodeSIS (P : Params) (ht : 0 < P.t) [Fact (1 < P.q)] (td : Trapdoor P) : SISSecret P := by
  classical
  refine
    { td := td
      x := sisWitness P td ht
      hx := block_mulVec_witness P td ht
      hne := witness_ne_zero P td ht }

/-- Concrete Stage C bridge: invertible-left-block trapdoor recovery ⇒ SIS witness recovery. -/
noncomputable def bridgeTrapdoorToSIS (P : Params) (ht : 0 < P.t) [Fact (1 < P.q)] :
    Reduction.BridgeData (TrapdoorView P) (SISView P) where
  mapPub := fun pub => pub
  mapSecret := fun s => s.td
  decode := fun _pub td => decodeSIS (P := P) ht td
  mapInstances := by
    intro _s _hs
    trivial
  encode_comm := by
    intro _s
    rfl
  decode_correct := by
    intro s _hs r hr
    subst hr
    simp [SISView, decodeSIS]

end BlockSIS

end

end Lattice
end Crypto
end HeytingLean
