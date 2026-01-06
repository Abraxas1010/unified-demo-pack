import HeytingLean.Crypto.ZK.Spec.Groth16
import HeytingLean.Crypto.ZK.Spec.Groth16CryptoDetails

/-!
# Groth16PairingToy

Minimal example showing how to instantiate the abstract
`HeytingLean.Crypto.ZK.Spec.Groth16.Protocol` skeleton using the
pairing-backend interface in `Groth16CryptoDetails`.

This is **not** a real Groth16 implementation. It is a tiny “pairing
preimage” demo protocol whose soundness statement is a genuine
existential witness property (not merely a public-input validity check).
-/

namespace HeytingLean
namespace Crypto
namespace ZK
namespace Spec
namespace Groth16PairingToy

open HeytingLean.Crypto.ZK.Spec.Groth16CryptoDetails

/-! ## Pairing-preimage demo protocol -/

/-- Public instance for the demo protocol: a fixed `b : G2` and a target `y : GT`. -/
structure PairingInstance (B : PairingBackend) where
  b : B.G2
  y : B.GT

/-- Proofs are single `G1` elements. -/
abbrev Proof (B : PairingBackend) := B.G1

/-- Verifier: accept iff `pair π b = y`. -/
noncomputable def verify (B : PairingBackend) (inst : PairingInstance B) (π : Proof B) : Bool := by
  classical
  exact decide (B.pair π inst.b = inst.y)

/-- Soundness statement (witness existence): if the verifier accepts, then there exists
some witness `w : G1` whose pairing with `b` equals `y`. -/
def Statement (B : PairingBackend) (inst : PairingInstance B) (_π : Proof B) : Prop :=
  ∃ w : B.G1, B.pair w inst.b = inst.y

/-- Protocol instance for the demo pairing-preimage system.

We include `BackendAxioms` in the explicit assumptions to demonstrate how protocol-level
soundness statements can be parameterised by nontrivial algebraic hypotheses, even though
this particular verifier does not need bilinearity to justify its soundness lemma.
-/
noncomputable def pairingProtocol (B : PairingBackend) :
    Groth16.Protocol (Inst := PairingInstance B) :=
  { assumptions := BackendAxioms B
    Proof := Proof B
    Statement := fun inst π => Statement B inst π
    verify := fun inst π => verify B inst π
    sound := by
      intro _hAx inst π h
      classical
      have hDec : decide (B.pair π inst.b = inst.y) = true := by
        simpa [verify] using h
      have hEq :
          B.pair π inst.b = inst.y := by
        have hDecEq :
            (decide (B.pair π inst.b = inst.y) = true) =
              (B.pair π inst.b = inst.y) := by
          simpa using (decide_eq_true_eq (p := B.pair π inst.b = inst.y))
        exact (Eq.mp hDecEq hDec)
      exact ⟨π, hEq⟩ }

/-- Generic soundness wrapper for `pairingProtocol`. -/
theorem pairingProtocol_soundness (B : PairingBackend) :
    Groth16.ProtocolSoundnessStatement (pairingProtocol B) :=
  Groth16.protocolSoundnessStatement_holds (pairingProtocol B)

/-! ## Concrete instantiation using the proved demo backend -/

noncomputable def demoProtocol : Groth16.Protocol (Inst := PairingInstance Example.backend) :=
  pairingProtocol Example.backend

/-- Soundness specialised to the demo backend, discharging the explicit backend axioms. -/
theorem demoProtocol_soundness_applied :
    ∀ (inst : PairingInstance Example.backend) (π : Proof Example.backend),
      demoProtocol.verify inst π = true →
        demoProtocol.Statement inst π := by
  intro inst π h
  have hSound := pairingProtocol_soundness (B := Example.backend)
  exact hSound Example.axioms_sound inst π h

end Groth16PairingToy
end Spec
end ZK
end Crypto
end HeytingLean
