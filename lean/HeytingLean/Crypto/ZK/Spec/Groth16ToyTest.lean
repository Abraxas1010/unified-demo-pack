import HeytingLean.Crypto.ZK.Spec.Groth16MinimalTest

/-!
Lightweight wrapper reusing the minimal Groth16 protocol instance to keep
the example test compiling and axiom-audited.
-/

open HeytingLean.Crypto.ZK.Spec.Groth16

def groth16ToyProtocol : Protocol := minimalGroth16Protocol

theorem groth16Toy_sound : ProtocolSoundnessStatement groth16ToyProtocol :=
  minimalGroth16_soundness

#print axioms groth16Toy_sound
