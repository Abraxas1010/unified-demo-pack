import HeytingLean.Crypto.Lattice.RecoveryViews
import HeytingLean.Crypto.Lattice.FaithfulReductions

namespace HeytingLean
namespace Crypto
namespace Lattice

/-!
# Stage B/C Concrete Bridge Constructions (v0.9 → v1.1)

This module provides *concrete* `Reduction.BridgeData` instances with proofs, to instantiate:
- Stage B: a specific NRA/PublicView → trapdoor reduction; and
- Stage C: restricted-family trapdoor → MLWE / SIS reductions.

These are statement-level constructions intended to eliminate “interface-only” placeholders without
introducing axioms. They are not claims about cryptographic hardness.
-/

open scoped Classical

namespace StageBC

/-!
## Stage B: Build a `PublicView` of nuclei that encodes trapdoor secrets

We encode a trapdoor secret `s` as the nucleus on `Set Secret` that closes any set by adding `s`.
The public encoding extracts the trapdoor instance from the unique element of `n ⊥`.
-/

universe u

variable {Secret : Type u}

/-- The “singleton-closure” nucleus: close a set by adding a fixed element `s`. -/
def nucleusOfSecret (s : Secret) : Nucleus (Set Secret) :=
  let f : InfHom (Set Secret) (Set Secret) :=
    { toFun := fun X => X ∪ {s}
      map_inf' := by
        intro X Y
        ext x
        by_cases hx : x = s <;> simp [hx] }
  Nucleus.mk f
    (by
      intro X
      -- idempotence is equality here; we use `le_of_eq` for the required `≤`.
      refine le_of_eq ?_
      ext x
      simp [f])
    (by
      intro X
      exact Set.subset_union_left)

@[simp] theorem nucleusOfSecret_apply (s : Secret) (X : Set Secret) :
    nucleusOfSecret (Secret := Secret) s X = X ∪ {s} :=
  rfl

@[simp] theorem nucleusOfSecret_bot (s : Secret) :
    nucleusOfSecret (Secret := Secret) s (⊥ : Set Secret) = {s} := by
  ext x
  simp [Set.bot_eq_empty]

private theorem choose_eq_of_singleton (s : Secret) (h : ({s} : Set Secret).Nonempty) :
    Classical.choose h = s := by
  exact Set.mem_singleton_iff.mp (Classical.choose_spec h)

/-!
### Stage B specialization: NRA→Trapdoor

We define a concrete nucleus public view whose secrets are nuclei that encode trapdoor secrets.
-/

noncomputable def stageBPublicView (P : TrapdoorParams) :
    PublicView (α := Set (TrapdoorSecret P)) :=
  { Pub := TrapdoorInstance P
    encode := fun n =>
      if h : (n (⊥ : Set (TrapdoorSecret P))).Nonempty then
        (Classical.choose h).inst
      else
        default
    instances := { n | ∃ s : TrapdoorSecret P, n = nucleusOfSecret (Secret := TrapdoorSecret P) s }
    goalEq := (· = ·) }

noncomputable def stageBBridgeToTrapdoor (P : TrapdoorParams) :
    BridgeToTrapdoor (Vn := stageBPublicView P) P where
  mapPub := fun x => x
  mapSecret := fun s => nucleusOfSecret (Secret := TrapdoorSecret P) s
  decode := fun pub n =>
    if h : (n (⊥ : Set (TrapdoorSecret P))).Nonempty then
      Classical.choose h
    else
      { inst := pub }
  mapInstances := by
    intro s _hs
    exact ⟨s, rfl⟩
  encode_comm := by
    intro s
    simp [stageBPublicView, TrapdoorView]
  decode_correct := by
    intro s _hs r hr
    subst hr
    simp [TrapdoorView]

/-!
## Stage C: Faithful restricted-family bridges (v1.1)

The earlier v0.9 Stage C instantiations used explicit witness payload embedding inside
`TrapdoorSecret`. In v1.0+ we instead provide “faithful” reductions where solutions are derived
from algebraic structure:
- MLWE: inversion trapdoor ⇒ noiseless ring-MLWE recovery (matrix inverse over `Rq`);
- SIS: gadget-form trapdoor ⇒ explicit nonzero kernel witness.
-/

namespace StageC
namespace Faithful

open HeytingLean.Crypto.Lattice.RingMLWE
open HeytingLean.Crypto.Lattice.GadgetSIS
open HeytingLean.Crypto.Lattice.BlockSIS

/-- Faithful Stage C (MLWE side): inversion trapdoor ⇒ noiseless ring-MLWE recovery. -/
noncomputable abbrev bridgeInvTrapdoorToRingMLWE (P : MLWEParams) :
    Reduction.BridgeData (RingMLWE.InvView P) (RingMLWE.View P) :=
  RingMLWE.bridgeInvTrapdoorToMLWE P

/-- Faithful Stage C (SIS side): gadget-form trapdoor ⇒ SIS witness recovery. -/
noncomputable abbrev bridgeGadgetTrapdoorToSIS (P : GadgetSIS.Params) (ht : 0 < P.t) [Fact (1 < P.q)] :
    Reduction.BridgeData (GadgetSIS.TrapdoorView P) (GadgetSIS.SISView P) :=
  GadgetSIS.bridgeTrapdoorToSIS (P := P) ht

/-- Faithful Stage C (SIS side, generalized): invertible-left-block trapdoor ⇒ SIS witness recovery. -/
noncomputable abbrev bridgeBlockTrapdoorToSIS (P : BlockSIS.Params) (ht : 0 < P.t) [Fact (1 < P.q)] :
    Reduction.BridgeData (BlockSIS.TrapdoorView P) (BlockSIS.SISView P) :=
  BlockSIS.bridgeTrapdoorToSIS (P := P) ht

end Faithful
end StageC

end StageBC

end Lattice
end Crypto
end HeytingLean
