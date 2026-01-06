import HeytingLean.LoF.Nucleus
import HeytingLean.Crypto.Form
import HeytingLean.Crypto.CoreSemantics
import HeytingLean.Crypto.Lens.Class
import HeytingLean.Crypto.Lens.Semantics
import HeytingLean.Crypto.Lens.Transport
import HeytingLean.Bridges.Tensor
import HeytingLean.Bridges.Graph
import HeytingLean.Bridges.Clifford

/-!
# ZK Lens Proofs — Shadow Commutation and Equivalence

Witness once in the core (Ω_R), then transport to any lens (tensor/graph/clifford).
Lens verifiers are equivalent via `Lens.dec_evalL` and the RoundTrip contract.
-/

namespace HeytingLean
namespace Crypto
namespace ZK

open HeytingLean.LoF
open HeytingLean.Crypto
open HeytingLean.Crypto.Lens

universe u v

variable {α : Type u} [PrimaryAlgebra α]
variable {R : Reentry α}

namespace LensProofs

/-- Core proof for a `Form n`: environment in Ω_R and evaluation to top. -/
structure ProofCore {n : ℕ} (φ : Form n) (R : Reentry α) where
  envΩ : EnvΩ (R := R) n
  soundΩ : Form.evalΩ (R := R) φ envΩ = ⊤

/-- Lens-side proof: lens environment and a soundness certificate decoding to Ω_R top. -/
structure ProofWith (L : Lens (R := R)) {n : ℕ} (φ : Form n) where
  envL : L.EnvL n
  sound : L.dec (Lens.Form.evalL (L := L) φ envL) = (⊤ : R.Omega)

namespace ProofWith

/-- Build a lens proof from a core proof using the RoundTrip encoder. -/
def ofCore {n} (L : Lens (R := R)) {φ : Form n}
    (pc : ProofCore (R := R) φ) : ProofWith (R := R) (L := L) φ :=
  { envL := fun i => L.enc (pc.envΩ i)
    sound := by
      -- dec (evalL φ (enc ∘ ρ)) = evalΩ φ ρ, then rewrite with core soundness
      have htransport := Lens.dec_evalL (L := L)
        (φ := φ) (ρ := fun i => L.enc (pc.envΩ i))
      simpa [htransport, Function.comp, pc.soundΩ] }

end ProofWith

/-- Lens verifier: there exists a lens environment whose decoded evaluation is top. -/
def verifyWith (L : Lens (R := R)) {n} (φ : Form n) : Prop :=
  ∃ (ρL : L.EnvL n), L.dec (Lens.Form.evalL (L := L) φ ρL) = (⊤ : R.Omega)

/-- Core satisfiability: there exists a core environment whose evaluation is top. -/
def holdsCore {n} (φ : Form n) : Prop :=
  ∃ (ρΩ : EnvΩ (R := R) n), Form.evalΩ (R := R) φ ρΩ = ⊤

/-- Shadow commutation: lens verification is equivalent to core satisfiability. -/
theorem verifyWith_iff_holdsCore (L : Lens (R := R)) {n} (φ : Form n) :
    verifyWith (R := R) L φ ↔ holdsCore (R := R) φ := by
  constructor
  · intro h
    rcases h with ⟨ρL, hs⟩
    -- transport lens eval to core eval via dec_evalL
    have htransport := Lens.dec_evalL (L := L) (φ := φ) (ρ := ρL)
    refine ⟨(fun i => L.dec (ρL i)), ?_⟩
    simpa [htransport]
      using hs
  · intro h
    rcases h with ⟨ρΩ, hs⟩
    -- choose lens env as enc ∘ ρΩ, then cancel with RoundTrip
    refine ⟨(fun i => L.enc (ρΩ i)), ?_⟩
    have htransport := Lens.dec_evalL (L := L)
      (φ := φ) (ρ := fun i => L.enc (ρΩ i))
    -- dec (evalL φ (enc ∘ ρΩ)) = evalΩ φ ρΩ
    simpa [htransport, Function.comp, hs]

/-- Build a lens verifier witness directly from a core proof. -/
theorem verifyWith_ofCore (L : Lens (R := R)) {n} {φ : Form n}
    (pc : ProofCore (R := R) φ) :
    verifyWith (R := R) L φ := by
  refine ⟨(fun i => L.enc (pc.envΩ i)), ?_⟩
  have htransport := Lens.dec_evalL (L := L)
      (φ := φ) (ρ := fun i => L.enc (pc.envΩ i))
  simpa [htransport, Function.comp, pc.soundΩ]

/-- Tensor/Graph/Clifford specialisations. -/
def verifyTensor {n} (M : Bridges.Tensor.Model α) (φ : Form n) : Prop :=
  verifyWith (R := R) (Lens.Instances.tensor (α := α) M) φ

def verifyGraph {n} (M : Bridges.Graph.Model α) (φ : Form n) : Prop :=
  verifyWith (R := R) (Lens.Instances.graph (α := α) M) φ

def verifyClifford {n} (M : Bridges.Clifford.Model α) (φ : Form n) : Prop :=
  verifyWith (R := R) (Lens.Instances.clifford (α := α) M) φ

/-- Cross-lens equivalence via shadow commutation. -/
theorem tensor_iff_graph {n}
    (MT : Bridges.Tensor.Model α) (MG : Bridges.Graph.Model α)
    (φ : Form n) :
    verifyTensor (R := R) MT φ ↔ verifyGraph (R := R) MG φ := by
  have ht := verifyWith_iff_holdsCore (R := R)
    (L := Lens.Instances.tensor (α := α) MT) φ
  have hg := verifyWith_iff_holdsCore (R := R)
    (L := Lens.Instances.graph (α := α) MG) φ
  exact Iff.trans ht (Iff.symm hg)

theorem tensor_iff_clifford {n}
    (MT : Bridges.Tensor.Model α) (MC : Bridges.Clifford.Model α)
    (φ : Form n) :
    verifyTensor (R := R) MT φ ↔ verifyClifford (R := R) MC φ := by
  have ht := verifyWith_iff_holdsCore (R := R)
    (L := Lens.Instances.tensor (α := α) MT) φ
  have hc := verifyWith_iff_holdsCore (R := R)
    (L := Lens.Instances.clifford (α := α) MC) φ
  exact Iff.trans ht (Iff.symm hc)

theorem graph_iff_clifford {n}
    (MG : Bridges.Graph.Model α) (MC : Bridges.Clifford.Model α)
    (φ : Form n) :
    verifyGraph (R := R) MG φ ↔ verifyClifford (R := R) MC φ := by
  have hg := verifyWith_iff_holdsCore (R := R)
    (L := Lens.Instances.graph (α := α) MG) φ
  have hc := verifyWith_iff_holdsCore (R := R)
    (L := Lens.Instances.clifford (α := α) MC) φ
  exact Iff.trans hg (Iff.symm hc)

/-- Per-lens proof structures wrapping a lens environment with a soundness certificate. -/
structure ProofTensor {n} (M : Bridges.Tensor.Model α) (φ : Form n) where
  envL : (Lens.Instances.tensor (α := α) M).EnvL n
  sound : (Lens.Instances.tensor (α := α) M).dec
    (Lens.Form.evalL (L := Lens.Instances.tensor (α := α) M) φ envL)
    = (⊤ : R.Omega)

structure ProofGraph {n} (M : Bridges.Graph.Model α) (φ : Form n) where
  envL : (Lens.Instances.graph (α := α) M).EnvL n
  sound : (Lens.Instances.graph (α := α) M).dec
    (Lens.Form.evalL (L := Lens.Instances.graph (α := α) M) φ envL)
    = (⊤ : R.Omega)

structure ProofClifford {n} (M : Bridges.Clifford.Model α) (φ : Form n) where
  envL : (Lens.Instances.clifford (α := α) M).EnvL n
  sound : (Lens.Instances.clifford (α := α) M).dec
    (Lens.Form.evalL (L := Lens.Instances.clifford (α := α) M) φ envL)
    = (⊤ : R.Omega)

namespace ProofTensor

def ofCore {n} (M : Bridges.Tensor.Model α) {φ : Form n}
    (pc : ProofCore (R := R) φ) : ProofTensor (R := R) (M := M) φ :=
  { envL := fun i => (Lens.Instances.tensor (α := α) M).enc (pc.envΩ i)
    sound := by
      have htransport := Lens.dec_evalL
        (L := Lens.Instances.tensor (α := α) M)
        (φ := φ) (ρ := fun i => (Lens.Instances.tensor (α := α) M).enc (pc.envΩ i))
      simpa [htransport, Function.comp, pc.soundΩ] }

end ProofTensor

namespace ProofGraph

def ofCore {n} (M : Bridges.Graph.Model α) {φ : Form n}
    (pc : ProofCore (R := R) φ) : ProofGraph (R := R) (M := M) φ :=
  { envL := fun i => (Lens.Instances.graph (α := α) M).enc (pc.envΩ i)
    sound := by
      have htransport := Lens.dec_evalL
        (L := Lens.Instances.graph (α := α) M)
        (φ := φ) (ρ := fun i => (Lens.Instances.graph (α := α) M).enc (pc.envΩ i))
      simpa [htransport, Function.comp, pc.soundΩ] }

end ProofGraph

namespace ProofClifford

def ofCore {n} (M : Bridges.Clifford.Model α) {φ : Form n}
    (pc : ProofCore (R := R) φ) : ProofClifford (R := R) (M := M) φ :=
  { envL := fun i => (Lens.Instances.clifford (α := α) M).enc (pc.envΩ i)
    sound := by
      have htransport := Lens.dec_evalL
        (L := Lens.Instances.clifford (α := α) M)
        (φ := φ) (ρ := fun i => (Lens.Instances.clifford (α := α) M).enc (pc.envΩ i))
      simpa [htransport, Function.comp, pc.soundΩ] }

end ProofClifford

/-- Convenience: top is always verifiable on any lens. -/
@[simp] theorem verifyWith_top (L : Lens (R := R)) :
    verifyWith (R := R) L (Form.top) := by
  -- trivial core witness exists
  have hcore : holdsCore (R := R) (Form.top) := by
    refine ⟨(fun i => (⊤ : R.Omega)), ?_⟩
    simp
  have := (verifyWith_iff_holdsCore (R := R) (L := L) (Form.top)).2 hcore
  simpa using this

@[simp] theorem verifyTensor_top (M : Bridges.Tensor.Model α) :
    verifyTensor (R := R) M (Form.top) := by
  simpa [verifyTensor] using verifyWith_top (R := R)
    (L := Lens.Instances.tensor (α := α) M)

@[simp] theorem verifyGraph_top (M : Bridges.Graph.Model α) :
    verifyGraph (R := R) M (Form.top) := by
  simpa [verifyGraph] using verifyWith_top (R := R)
    (L := Lens.Instances.graph (α := α) M)

@[simp] theorem verifyClifford_top (M : Bridges.Clifford.Model α) :
    verifyClifford (R := R) M (Form.top) := by
  simpa [verifyClifford] using verifyWith_top (R := R)
    (L := Lens.Instances.clifford (α := α) M)

/-! ## Examples: simple 2-variable conjunction and bottom -/

namespace Examples

@[simp] def φAnd2 : Form 2 :=
  Form.and (Form.var ⟨0, by decide⟩) (Form.var ⟨1, by decide⟩)

def coreAnd2 (R : Reentry α) : ProofCore (R := R) φAnd2 :=
  { envΩ := fun _ => (⊤ : R.Omega)
    soundΩ := by simp [φAnd2, Form.evalΩ_and, Form.evalΩ_var] }

@[simp] theorem verifyTensor_and2 (R : Reentry α)
    (M : Bridges.Tensor.Model α) :
    verifyTensor (R := R) M φAnd2 :=
  verifyWith_ofCore (R := R)
    (L := Lens.Instances.tensor (α := α) M) (pc := coreAnd2 (R := R))

@[simp] theorem verifyGraph_and2 (R : Reentry α)
    (M : Bridges.Graph.Model α) :
    verifyGraph (R := R) M φAnd2 :=
  verifyWith_ofCore (R := R)
    (L := Lens.Instances.graph (α := α) M) (pc := coreAnd2 (R := R))

@[simp] theorem verifyClifford_and2 (R : Reentry α)
    (M : Bridges.Clifford.Model α) :
    verifyClifford (R := R) M φAnd2 :=
  verifyWith_ofCore (R := R)
    (L := Lens.Instances.clifford (α := α) M) (pc := coreAnd2 (R := R))

@[simp] theorem not_holdsCore_bot (R : Reentry α) :
    ¬ holdsCore (R := R) (Form.bot) := by
  intro h
  rcases h with ⟨ρΩ, htop⟩
  simp at htop

@[simp] theorem not_verifyTensor_bot (R : Reentry α)
    (M : Bridges.Tensor.Model α) :
    ¬ verifyTensor (R := R) M (Form.bot) := by
  have h := (verifyWith_iff_holdsCore (R := R)
    (L := Lens.Instances.tensor (α := α) M) (Form.bot)).not
  simpa [not_holdsCore_bot (R := R), verifyTensor] using h

@[simp] theorem not_verifyGraph_bot (R : Reentry α)
    (M : Bridges.Graph.Model α) :
    ¬ verifyGraph (R := R) M (Form.bot) := by
  have h := (verifyWith_iff_holdsCore (R := R)
    (L := Lens.Instances.graph (α := α) M) (Form.bot)).not
  simpa [not_holdsCore_bot (R := R), verifyGraph] using h

@[simp] theorem not_verifyClifford_bot (R : Reentry α)
    (M : Bridges.Clifford.Model α) :
    ¬ verifyClifford (R := R) M (Form.bot) := by
  have h := (verifyWith_iff_holdsCore (R := R)
    (L := Lens.Instances.clifford (α := α) M) (Form.bot)).not
  simpa [not_holdsCore_bot (R := R), verifyClifford] using h

end Examples

end LensProofs

end ZK
end Crypto
end HeytingLean
