/-
# Crypto.ZK.Spec.ZkEvm

Abstract equivalence skeleton between an EVM-style semantics and a
zkEVM-style semantics.

We keep both semantics and the cross-language relations abstract and
package the intended equivalence property as a field of `Model`. This
mirrors the pattern used for STARK and FRI: concrete zkEVM designs are
expected to instantiate `Model` and justify the `equiv` field from
their own semantics.
-/

namespace HeytingLean
namespace Crypto
namespace ZK
namespace Spec
namespace ZkEvm

/-- Abstract zkEVM equivalence model.

  * `ProgramEvm`, `StateEvm` describe the base EVM-style semantics;
  * `ProgramZk`, `StateZk` describe the zkEVM execution model;
  * `SemEvm pe se se'` is the EVM semantic relation;
  * `SemZk pz sz sz'` is the zkEVM semantic relation;
  * `relProg pz pe` relates zkEVM programs to EVM programs;
  * `relState sz se` relates zkEVM states to EVM states;
  * `equiv` expresses that related programs and states have
    semantically equivalent behaviours in the sense that every EVM step
    corresponds to a zkEVM step and conversely. -/
structure Model where
  ProgramEvm : Type
  StateEvm   : Type
  ProgramZk  : Type
  StateZk    : Type
  SemEvm     : ProgramEvm → StateEvm → StateEvm → Prop
  SemZk      : ProgramZk → StateZk → StateZk → Prop
  relProg    : ProgramZk → ProgramEvm → Prop
  relState   : StateZk → StateEvm → Prop
  equiv :
    ∀ {pz pe sz se},
      relProg pz pe → relState sz se →
        (∀ se', SemEvm pe se se' ↔
          ∃ sz', SemZk pz sz sz' ∧ relState sz' se')

/-- Bundled zkEVM equivalence statement for a fixed model: whenever
    programs and states are related, the EVM and zkEVM semantic
    relations coincide up to the state relation. -/
def EquivalenceStatement (M : Model) : Prop :=
  ∀ {pz pe sz se},
    M.relProg pz pe → M.relState sz se →
      (∀ se', M.SemEvm pe se se' ↔
        ∃ sz', M.SemZk pz sz sz' ∧ M.relState sz' se')

/-- `EquivalenceStatement M` holds for any abstract model `M` by
    definition of its `equiv` field. -/
theorem equivalenceStatement_holds (M : Model) :
    EquivalenceStatement M :=
  M.equiv

/-! ## Example zkEVM instance

As a sanity check, we provide a trivial model where both semantics are the
identity relation on `Unit`. This makes the equivalence field provable from
the definitions.
-/

namespace Example

def model : Model :=
  { ProgramEvm := Unit
    , StateEvm := Unit
    , ProgramZk := Unit
    , StateZk := Unit
    , SemEvm := fun _ _ se' => se' = ()
    , SemZk := fun _ _ sz' => sz' = ()
    , relProg := fun _ _ => True
    , relState := fun _ _ => True
    , equiv := by
        intro pz pe sz se _ _ se'
        constructor
        · intro h
          refine ⟨(), ?_, trivial⟩
          simp
        · intro h
          rcases h with ⟨sz', hSem, _⟩
          -- Both semantics are definitionally `(_ = ())`.
          simp }

theorem model_equivalence :
    EquivalenceStatement model :=
  equivalenceStatement_holds model

end Example

end ZkEvm
end Spec
end ZK
end Crypto
end HeytingLean
