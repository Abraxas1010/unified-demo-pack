import HeytingLean.Crypto.ZK.Spec.Groth16

namespace HeytingLean
namespace Crypto
namespace ZK
namespace Spec
namespace Groth16

/-!
Paper-facing aliases for the assumption-scoped Groth16 interface results.

This module exists to provide a stable, non-`Stub` namespace path for citations,
without changing the underlying definitions/proofs.
-/

namespace Abstract

abbrev knowledgeProtocol : Crypto.ZK.Spec.Groth16.Protocol :=
  Crypto.ZK.Spec.Groth16.Stub.knowledgeProtocol

theorem knowledgeProtocol_soundness :
    Crypto.ZK.Spec.Groth16.ProtocolSoundnessStatement knowledgeProtocol :=
  Crypto.ZK.Spec.Groth16.Stub.knowledgeProtocol_soundness

end Abstract

end Groth16
end Spec
end ZK
end Crypto
end HeytingLean

