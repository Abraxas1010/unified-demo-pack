import HeytingLean.LoF.CryptoSheaf.Quantum.Entropy.Valuation
import HeytingLean.LoF.CryptoSheaf.Quantum.Entropy.ContextualityBridge
import HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel

/-
Tiny tests to ensure the new Entropy modules compile and surface their
core interfaces safely.
-/
namespace HeytingLean
namespace LoF
namespace CryptoSheaf
namespace Quantum
namespace Entropy

open Classical

#check Valuation
#check HeytingLean.LoF.CryptoSheaf.Quantum.triangle_no_global

section
  -- Check the concrete Finset valuation instance compiles.
  #check (inferInstance : Valuation Bool)
end

section
  -- Sanity: supportSize is available on triangle supports.
  open HeytingLean.LoF.CryptoSheaf.Quantum

  noncomputable example :
      0 < Entropy.supportSize
        (HeytingLean.LoF.CryptoSheaf.Quantum.supportAB) := by
    -- `supportAB_nonempty` exists; cardinal of a nonempty finite subtype is > 0.
    classical
    have hne := HeytingLean.LoF.CryptoSheaf.Quantum.supportAB_nonempty
    -- Convert to a witness in the subtype `{s // s ∈ supportAB}`
    rcases hne with ⟨s, hs⟩
    let S : Set (Assignment HeytingLean.LoF.CryptoSheaf.Quantum.C_ab) :=
      HeytingLean.LoF.CryptoSheaf.Quantum.supportAB
    have : Nonempty {t // t ∈ S} := ⟨⟨s, hs⟩⟩
    -- cardinality of a finite nonempty type is positive
    simpa [Entropy.supportSize] using Fintype.card_pos_iff.mpr this
end

end Entropy
end Quantum
end CryptoSheaf
end LoF
end HeytingLean
