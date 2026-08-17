import EvmSpecsVerify.Relations.Warm
import EvmSpecsVerify.Representation.AddressWord

/-!
# Warm address relation

The address analogue of [`WarmRel`](Warm.lean), with one twist: the
extraction's `k_account_is_warm` short-circuits **active precompiles as
always warm** (and `k_account_mark_warm` never stamps them), while SpecRef
gets the same behavior from transaction-start prewarming — the precompile
addresses are inserted into `accessedAddresses` before the first frame
runs. The step-level relation therefore compares SpecRef's set against
the extraction's *effective* warmth: precompile-or-current-stamp.

`WarmAddrRel` is parameterized by the pointwise value `pid` of the
extraction's classifier (`precompile_id_for_address`) — the classifier
reads only the profile register, so under a fixed register file it is a
function of the address. Its run shape is supplied to the step theorems
as a (mechanically dischargeable) hypothesis; the relation itself encodes
the prewarm invariant, discharged at transaction level.
-/

open private assocGet assocPut from Evm.HostAxioms

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

instance : LawfulBEq PrecompileId where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> rfl

/-- SpecRef's warm address set vs the extraction's epoch stamps, modulo
precompile prewarming (see the module docstring). -/
def WarmAddrRel (pid : Evm.Defs.address → PrecompileId)
    (sRef : Machine) (hs : Evm.HostState) : Prop :=
  ∀ aV : Evm.Defs.address,
    (sRef.evm.accessedAddresses.contains aV.toList = true
      ↔ (pid aV ≠ PrecompileId.NotPrecompile ∨
          hs.warmEpoch ≤ (assocGet hs.warmAddresses aV).getD 0))

/-- The cold-path update preserves the relation: SpecRef `setAdd` of the
byte list vs the extraction's fresh epoch stamp on the vector. (For a
warm SpecRef key the `setAdd` is the identity — `setAdd_eq_of_contains` —
so this also covers the extraction's stamp refresh of a warm
non-precompile address.) -/
theorem warmaddr_after_mark (pid : Evm.Defs.address → PrecompileId)
    (keys : List Address) (slots : List (Evm.Defs.address × Nat))
    (epoch : Nat) (aM : Evm.Defs.address)
    (h : ∀ aV : Evm.Defs.address, keys.contains aV.toList = true
      ↔ (pid aV ≠ PrecompileId.NotPrecompile ∨
          epoch ≤ (assocGet slots aV).getD 0)) :
    ∀ aV : Evm.Defs.address,
      (setAdd keys aM.toList).contains aV.toList = true
        ↔ (pid aV ≠ PrecompileId.NotPrecompile ∨
            epoch ≤ (assocGet (assocPut slots aM epoch) aV).getD 0) := by
  intro aV
  by_cases hkey : aV = aM
  · subst hkey
    rw [assocGet_put_self]
    simp only [Option.getD_some, le_refl, or_true, iff_true]
    unfold EvmAsm.Stateless.SpecRef.setAdd
    split
    · rename_i hc
      exact hc
    · simp
  · have hlist : aV.toList ≠ aM.toList := fun hc =>
      hkey (Vector.toList_inj.mp hc)
    rw [assocGet_put_ne _ _ _ _ hkey]
    rw [show (setAdd keys aM.toList).contains aV.toList
        = keys.contains aV.toList from by
      unfold EvmAsm.Stateless.SpecRef.setAdd
      split
      · rfl
      · rw [List.contains_append]
        simp [hlist]]
    exact h aV

end EvmSpecsVerify
