import HeytingLean.Crypto.ZK.Spec.Plonk
import Mathlib.Data.Bool.Basic

/-!
# Minimal PLONK example protocol and soundness

A tiny PLONK-style protocol with one gate enforcing `x₀ + x₁ = x₂`.
The verifier checks the addition and that `x₂` matches the public value;
soundness then produces an assignment satisfying the PLONK semantics.
-/

open HeytingLean.Crypto.ZK.Spec.Plonk
open HeytingLean.Crypto.ZK
open Bool

/-- Witness for the example circuit. -/
structure AddProof where
  witness₀ : ℚ
  witness₁ : ℚ
  witness₂ : ℚ

/-- Public input: the expected value of `x₂`. -/
structure AddPublic where
  out : ℚ

/-- Single addition gate `x₀ + x₁ - x₂ = 0`. -/
def addGate : Plonk.Gate :=
  { A := { const := 0, terms := [(0, 1), (1, 1), (2, -1)] }
    , B := LinComb.ofConst 1
    , C := LinComb.ofConst 0 }

/-- PLONK system with the addition gate and no copy constraints. -/
def addSystem : Plonk.System :=
  { gates := [addGate], copyPermutation := [] }

/-- Boolean verifier for the example protocol. -/
def addVerify (pub : AddPublic) (π : AddProof) : Bool :=
  decide (π.witness₀ + π.witness₁ = π.witness₂ ∧ π.witness₂ = pub.out)

/-- Encode an assignment into public data (just `x₂`). -/
def addEncode (a : Var → ℚ) : AddPublic :=
  { out := a 2 }

/-- Concrete PLONK protocol instance for the example system. -/
def minimalPlonkProtocol : Protocol :=
  { sys := addSystem
    Proof := AddProof
    Public := AddPublic
    encodePublic := addEncode
    verify := addVerify
    sound := by
      intro pub π hVerify
      -- Extract conjunction from the verifier result.
      have hTrue :
          π.witness₀ + π.witness₁ = π.witness₂ ∧
            π.witness₂ = pub.out := by
        simpa [addVerify, Bool.decide_iff] using hVerify
      rcases hTrue with ⟨h_add, h_out⟩
      -- Build an assignment from the proof.
      let a : Var → ℚ := fun
        | 0 => π.witness₀
        | 1 => π.witness₁
        | 2 => π.witness₂
        | _ => 0
      refine ⟨a, ?hRel, ?hPub⟩
      · -- Show the assignment satisfies the PLONK relation.
        refine And.intro ?hR1CS ?hCopy
        · -- R1CS part: the single gate encodes `x₀ + x₁ - x₂ = 0`.
          intro c hc
          classical
          have hc' :
              c = { A := addGate.A, B := addGate.B, C := addGate.C } := by
            simpa [Plonk.System.toR1CS, addSystem] using hc
          subst hc'
          simp [addGate, Constraint.satisfied, LinComb.eval, LinComb.ofConst, a, h_add]
        · -- Copy constraints: permutation is empty, so trivially satisfied.
          intro c hc; cases hc
      · -- Public encoding matches.
        simp [addEncode, h_out, a] }

/-- Protocol-level soundness for the minimal PLONK example instance. -/
theorem minimalPlonk_soundness :
    ProtocolSoundnessStatement minimalPlonkProtocol :=
  protocolSoundnessStatement_holds _

/-- QA: ensure no proof-hole/axiom leakage. -/
#print axioms minimalPlonk_soundness
