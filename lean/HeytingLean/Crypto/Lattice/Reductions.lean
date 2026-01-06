import HeytingLean.Crypto.Lattice.NucleusBridge

namespace HeytingLean
namespace Crypto
namespace Lattice

universe u v

/-- A statement-level reduction between recovery views, as an algorithm transformer. -/
structure Reduction {S₁ : Type u} {S₂ : Type v} (V₁ : RecoveryView S₁) (V₂ : RecoveryView S₂) where
  mapPub : V₂.Pub → V₁.Pub
  mapSecret : S₂ → S₁
  lift : (V₁.Pub → S₁) → (V₂.Pub → S₂)
  sound : ∀ recover₁, RecoveryView.solves V₁ recover₁ → RecoveryView.solves V₂ (lift recover₁)

namespace Reduction

universe u₁ u₂ u₃

variable {S₁ : Type u₁} {S₂ : Type u₂} {S₃ : Type u₃}
variable {V₁ : RecoveryView S₁} {V₂ : RecoveryView S₂} {V₃ : RecoveryView S₃}

/-- Identity reduction. -/
def id (V : RecoveryView S₁) : Reduction V V where
  mapPub := fun x => x
  mapSecret := fun x => x
  lift := fun recover => recover
  sound := by intro recover h; exact h

/-- Composition of reductions. -/
def comp (R₁₂ : Reduction V₁ V₂) (R₂₃ : Reduction V₂ V₃) : Reduction V₁ V₃ where
  mapPub := fun pub₃ => R₁₂.mapPub (R₂₃.mapPub pub₃)
  mapSecret := fun s₃ => R₁₂.mapSecret (R₂₃.mapSecret s₃)
  lift := fun recover₁ => R₂₃.lift (R₁₂.lift recover₁)
  sound := by
    intro recover₁ h₁
    have h₂ : RecoveryView.solves V₂ (R₁₂.lift recover₁) := R₁₂.sound recover₁ h₁
    exact R₂₃.sound (R₁₂.lift recover₁) h₂

/-- Hardness transport: if `V₂` is unsolvable and `V₂` reduces to `V₁`, then `V₁` is unsolvable. -/
theorem unsolvable_of_unsolvable (R : Reduction V₁ V₂) :
    (¬ ∃ recover₂ : V₂.Pub → S₂, RecoveryView.solves V₂ recover₂) →
      (¬ ∃ recover₁ : V₁.Pub → S₁, RecoveryView.solves V₁ recover₁) := by
  intro h₂ h₁
  rcases h₁ with ⟨recover₁, h₁solves⟩
  have : ∃ recover₂ : V₂.Pub → S₂, RecoveryView.solves V₂ recover₂ :=
    ⟨R.lift recover₁, R.sound recover₁ h₁solves⟩
  exact h₂ this

/-- Bridge data for building a `Reduction` by decoding a recovered secret. -/
structure BridgeData {S₁ : Type u₁} {S₂ : Type u₂} (V₁ : RecoveryView S₁) (V₂ : RecoveryView S₂) where
  /-- Public-instance map (challenge translation). -/
  mapPub : V₂.Pub → V₁.Pub
  /-- Secret-instance map (witness embedding). -/
  mapSecret : S₂ → S₁
  /-- Decode a candidate `S₁` solution back into an `S₂` solution. -/
  decode : V₂.Pub → S₁ → S₂
  /-- `V₂` instances map into `V₁` instances. -/
  mapInstances : ∀ s, s ∈ V₂.instances → mapSecret s ∈ V₁.instances
  /-- Public encoding commutes with `mapPub`/`mapSecret` on instances. -/
  encode_comm : ∀ s, mapPub (V₂.encode s) = V₁.encode (mapSecret s)
  /-- If the recovered `S₁` is correct (up to `V₁.goalEq`), decoding yields a correct `S₂`. -/
  decode_correct :
    ∀ s, s ∈ V₂.instances → ∀ r, V₁.goalEq r (mapSecret s) → V₂.goalEq (decode (V₂.encode s) r) s

namespace BridgeData

variable {S₁ : Type u₁} {S₂ : Type u₂}
variable {V₁ : RecoveryView S₁} {V₂ : RecoveryView S₂}

/-- Build a `Reduction` from bridge data (standard decode-based construction). -/
def toReduction (B : BridgeData (V₁ := V₁) (V₂ := V₂)) : Reduction V₁ V₂ where
  mapPub := B.mapPub
  mapSecret := B.mapSecret
  lift := fun recover₁ pub₂ => B.decode pub₂ (recover₁ (B.mapPub pub₂))
  sound := by
    intro recover₁ hsolve
    intro s hs
    have hs1 : B.mapSecret s ∈ V₁.instances := B.mapInstances s hs
    have h1 : V₁.goalEq (recover₁ (V₁.encode (B.mapSecret s))) (B.mapSecret s) := by
      have h := hsolve (B.mapSecret s)
      exact h hs1
    have h1' : V₁.goalEq (recover₁ (B.mapPub (V₂.encode s))) (B.mapSecret s) := by
      simpa [B.encode_comm s] using h1
    exact B.decode_correct s hs (recover₁ (B.mapPub (V₂.encode s))) h1'

end BridgeData

end Reduction

end Lattice
end Crypto
end HeytingLean
