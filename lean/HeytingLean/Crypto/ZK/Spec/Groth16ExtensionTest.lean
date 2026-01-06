import HeytingLean.Crypto.ZK.Spec.Groth16MinimalTest

/-!
Extension baseline reusing the minimal Groth16 protocol. This keeps the
extension test compiling while we build richer constraint/public-private
cases in subsequent steps.
-/

open HeytingLean.Crypto.ZK.Spec.Groth16

def groth16ExtendedProtocol : Protocol := minimalGroth16Protocol

theorem groth16Extended_sound :
    ProtocolSoundnessStatement groth16ExtendedProtocol :=
  minimalGroth16_soundness

#print axioms groth16Extended_sound
