import EvmSpecsVerify.Relations.Warm
import EvmSpecsVerify.Representation.AddressWord
import EvmSpecsVerify.Representation.EvmMonad

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

/-! ## The extraction's run shapes

`k_account_is_warm` and `k_account_mark_warm` both consult the
precompile classifier first, so both take its run shape as a hypothesis
(`hpid`). They live here rather than with an opcode because BALANCE,
EXTCODEHASH, EXTCODESIZE, EXTCODECOPY and SELFDESTRUCT all use them. -/

/-- The warm-address table after `k_account_mark_warm`: precompiles are
never stamped. (Named so structure-update literals stay single-line.) -/
def wsAfterMark (pid : Evm.Defs.address → PrecompileId)
    (aV : Evm.Defs.address) (hs : Evm.HostState) :
    List (Evm.Defs.address × Nat) :=
  if (pid aV != PrecompileId.NotPrecompile) then hs.warmAddresses
  else assocPut hs.warmAddresses aV hs.warmEpoch

/-- **The extraction's warmth test is SpecRef's set membership.** The
value `k_account_is_warm` returns (see below) reduces to
`accessedAddresses.contains`, in both directions at once: a precompile is
warm on the extraction by short-circuit and warm on SpecRef by the
prewarm invariant `WarmAddrRel` carries, and a non-precompile is decided
by the epoch stamp.

Every access-list opcode needs this to price its access, and each one was
deriving it inline (BALANCE, EXTCODEHASH, EXTCODESIZE, EXTCODECOPY, and
now SELFDESTRUCT) — twenty-odd lines twice per opcode, once per branch of
the membership test. -/
theorem warm_of_warmAddrRel (pid : Evm.Defs.address → PrecompileId)
    {sRef : Machine} {hs : Evm.HostState} (hwrel : WarmAddrRel pid sRef hs)
    (aV : Evm.Defs.address) :
    (if (pid aV != PrecompileId.NotPrecompile) then true
        else decide (hs.warmEpoch ≤ (assocGet hs.warmAddresses aV).getD 0))
      = sRef.evm.accessedAddresses.contains aV.toList := by
  have hiff := hwrel aV
  cases hwc : sRef.evm.accessedAddresses.contains aV.toList with
  | true =>
    by_cases hp : (pid aV != PrecompileId.NotPrecompile) = true
    · rw [if_pos hp]
    · rw [if_neg hp]
      rcases hiff.mp hwc with hpre | hle
      · exact absurd (bne_iff_ne.mpr hpre) hp
      · exact decide_eq_true hle
  | false =>
    have hnot : pid aV = PrecompileId.NotPrecompile
        ∧ ¬ hs.warmEpoch ≤ (assocGet hs.warmAddresses aV).getD 0 := by
      by_cases hp : pid aV = PrecompileId.NotPrecompile
      · refine ⟨hp, fun hle => ?_⟩
        rw [hiff.mpr (Or.inr hle)] at hwc
        cases hwc
      · exact absurd (hiff.mpr (Or.inl hp)) (by rw [hwc]; simp)
    rw [if_neg (by simp [hnot.1]), decide_eq_false hnot.2]

open Evm.Functions in
/-- `k_account_is_warm`: precompiles short-circuit warm, otherwise the
epoch stamp decides. -/
theorem runS_k_account_is_warm (pid : Evm.Defs.address → PrecompileId)
    (aV : Evm.Defs.address) (hs : Evm.HostState) (ss : SeqState)
    (hpid : runS (Evm.Functions.precompile_id_for_address aV) hs ss
      = .ok (pid aV, hs) ss) :
    runS (Evm.Functions.k_account_is_warm aV) hs ss =
      .ok ((if (pid aV != PrecompileId.NotPrecompile) then true
        else decide (hs.warmEpoch
          ≤ (assocGet hs.warmAddresses aV).getD 0)), hs) ss := by
  simp only [Evm.Functions.k_account_is_warm, runS_bind, hpid]
  by_cases hp : (pid aV != PrecompileId.NotPrecompile) = true
  · rw [if_pos hp, if_pos hp]
    exact runS_pure _ _ _
  · rw [if_neg hp, if_neg hp]
    simp only [Evm.Functions.account_is_warm, runS_bind, runS_get, runS_pure]

open Evm.Functions in
/-- `k_account_mark_warm` stamps non-precompiles, skips precompiles. -/
theorem runS_k_account_mark_warm (pid : Evm.Defs.address → PrecompileId)
    (aV : Evm.Defs.address) (hs : Evm.HostState) (ss : SeqState)
    (hpid : runS (Evm.Functions.precompile_id_for_address aV) hs ss
      = .ok (pid aV, hs) ss) :
    runS (Evm.Functions.k_account_mark_warm aV) hs ss =
      .ok ((), { hs with warmAddresses := wsAfterMark pid aV hs }) ss := by
  simp only [Evm.Functions.k_account_mark_warm, runS_bind, hpid, wsAfterMark]
  by_cases hp : (pid aV != PrecompileId.NotPrecompile) = true
  · rw [if_pos hp, if_pos hp]
    exact runS_pure _ _ _
  · rw [if_neg hp, if_neg hp]
    simp only [Evm.Functions.account_mark_warm, runS_modify]

end EvmSpecsVerify
