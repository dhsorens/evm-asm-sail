import EvmSpecsVerify.Relations.Assoc
import EvmSpecsVerify.Relations.Base
import EvmSpecsVerify.Representation.EvmSailME
import Batteries.Tactic.OpenPrivate

/-!
# Persistent storage relation

Both sides resolve a slot through a two-level overlay over the witness
trie, and the two levels line up:

| layer | SpecRef | extraction |
| --- | --- | --- |
| transaction | `TransactionState.storageWrites` (address → slot dict) | `HostState.storageTx : List (StorageKey × StorageValue)` |
| block | `ts.parent.storageWrites` | `HostState.storageBlock` (also the read-through cache) |
| base | `get_storage ts.parent.preState` | `stateless_storage_by_key` |

`StorageRel` relates the **transaction** layer pointwise, which is the
layer opcode steps write: SpecRef's `setStorage` does a nested `dictSet`,
the extraction's `k_sstore` an `assocPut` of a `StorageValue`. The
extraction's row carries `orig` (the EIP-2200 transaction-start value)
next to the live `curr`; SpecRef recomputes that from the block layer with
`getStorageOriginal`, so the relation ties the stored `orig` to
[`specOrig`](#) rather than to another stored field.

The `curr` component is **one-directional** — every row the extraction
holds, SpecRef holds with the same live value, but not conversely.
Mismatch ledger MM-16 is why: a `SSTORE` writing the value already in the
slot is skipped by the extraction (`if entry.curr != v`) and recorded by
SpecRef (`setStorage` unconditionally), so a spec-side row with no
extraction row is a reachable state. Every consumer needs exactly the
direction that survives — `sloadAgree_of_storageRel` starts from an
extraction row — and `storageRel_write_noop` is the preservation lemma
for that step.

Below the transaction layer the two sides are not related here: the
extraction's block overlay doubles as its witness read-through cache and
its miss path is a keccak-hashed authenticated trie walk, which stays in
the world tranche (as does `HostState.storageCleared`, whose SpecRef
counterpart is the `destroyStorage`/`createdAccounts` pair of the CREATE
family). Consequently the relation discharges exactly the
transaction-overlay *hit* of `k_sload` — see `sloadAgree_of_storageRel`
in [SLOAD](../Opcodes/Sload.lean) — and that is also the only branch of
`k_sload` that touches no state (a miss records an EIP-7928 read).
-/

open private assocGet assocPut from Evm.HostAxioms

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## SpecRef's overlays, as functions -/

/-- The transaction-layer slot lookup inside `getStorage`/`setStorage`. -/
def specTxSlot (ts : TransactionState) (a : Address) (k : Bytes32) :
    Option U256 :=
  (dictGet? ts.storageWrites a).bind (fun slots => dictGet? slots k)

/-- The block-layer slot lookup (`getStorage`'s second probe, and the
whole of `getStorageOriginal`'s overlay). -/
def specBlockSlot (ts : TransactionState) (a : Address) (k : Bytes32) :
    Option U256 :=
  (dictGet? ts.parent.storageWrites a).bind (fun slots => dictGet? slots k)

/-- `getStorage`'s bookkeeping: the read is recorded before the probes. -/
def specStorageReadOf (ts : TransactionState) (a : Address) (k : Bytes32) :
    TransactionState :=
  { ts with storageReads := setAdd ts.storageReads (a, k) }

/-- `recordPreStateRead`'s effect. -/
def specPreStateReadOf (ts : TransactionState) (a : Address) :
    TransactionState :=
  { ts with parent :=
      { ts.parent with
          preStateReads := setAdd ts.parent.preStateReads a } }

/-- SpecRef's `setStorage` effect (its account-existence rejection is
handled by the caller — see `runTx_setStorage`). -/
def specStorageWrite (ts : TransactionState) (a : Address) (k : Bytes32)
    (v : U256) : TransactionState :=
  { ts with
      storageWrites :=
        dictSet ts.storageWrites a
          (dictSet ((dictGet? ts.storageWrites a).getD []) k v) }

/-- The transaction-start value `getStorageOriginal` computes, as a pure
function of the state (it can reject, hence `Except`). -/
def specOrig (ts : TransactionState) (a : Address) (k : Bytes32) :
    Except SpecError U256 :=
  if ts.createdAccounts.contains a then .ok 0
  else
    match specBlockSlot ts a k with
    | some v => .ok v
    | none => get_storage ts.parent.preState a k

/-! ## SpecRef run shapes -/

/-- `TxM`'s base monad is `Except`, whose bind on a success is the
continuation; `pure_bind` does not fire on the `Except.ok` spelling the
`StateT` run lemmas leave behind. -/
private theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a : Except ε α) >>= f = f a := rfl

/-- A transaction-overlay hit: the value comes back and the only state
change is the recorded read. -/
theorem runTx_getStorage_tx_hit (ts : TransactionState) (a : Address)
    (k : Bytes32) (v : U256) (h : specTxSlot ts a k = some v) :
    (getStorage a k).run ts = .ok (v, specStorageReadOf ts a k) := by
  unfold getStorage specTxSlot at *
  simp only [StateT.run_bind, StateT.run_modify, StateT.run_get, pure_bind, h]
  rfl

/-- The full `getStorageOriginal`, value and state. -/
theorem runTx_getStorageOriginal (ts : TransactionState) (a : Address)
    (k : Bytes32) :
    (getStorageOriginal a k).run ts =
      (if ts.createdAccounts.contains a then .ok (0, ts)
       else
         match specBlockSlot ts a k with
         | some v => .ok (v, ts)
         | none =>
           (get_storage ts.parent.preState a k).map
             (fun v => (v, specPreStateReadOf ts a))) := by
  unfold getStorageOriginal specBlockSlot specPreStateReadOf
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hc : ts.createdAccounts.contains a = true
  · rw [if_pos hc, if_pos hc]
    rfl
  · rw [if_neg hc, if_neg hc]
    cases hslot :
        (dictGet? ts.parent.storageWrites a).bind (fun slots => dictGet? slots k) with
    | some v => rfl
    | none => cases get_storage ts.parent.preState a k <;> rfl

/-- `getStorageOriginal`'s value is `specOrig`, and its state change is
invisible to both overlays. -/
theorem runTx_getStorageOriginal_ok (ts : TransactionState) (a : Address)
    (k : Bytes32) (v : U256) (h : specOrig ts a k = .ok v) :
    ∃ ts', (getStorageOriginal a k).run ts = .ok (v, ts')
      ∧ ts'.storageWrites = ts.storageWrites
      ∧ ts'.parent.storageWrites = ts.parent.storageWrites
      ∧ ts'.parent.preState = ts.parent.preState
      ∧ ts'.createdAccounts = ts.createdAccounts := by
  rw [runTx_getStorageOriginal]
  unfold specOrig at h
  by_cases hc : ts.createdAccounts.contains a = true
  · rw [if_pos hc] at h ⊢
    obtain rfl : (0 : U256) = v := Except.ok.inj h
    exact ⟨ts, rfl, rfl, rfl, rfl, rfl⟩
  · rw [if_neg hc] at h ⊢
    cases hslot : specBlockSlot ts a k with
    | some w =>
      simp only [hslot] at h
      obtain rfl : w = v := Except.ok.inj h
      exact ⟨ts, rfl, rfl, rfl, rfl, rfl⟩
    | none =>
      simp only [hslot] at h
      exact ⟨specPreStateReadOf ts a, by rw [h]; rfl, rfl, rfl, rfl, rfl⟩

/-- `setStorage` after its account-existence check. -/
theorem runTx_setStorage (ts ts₁ : TransactionState) (a : Address)
    (k : Bytes32) (v : U256) (acct : EvmAsm.Stateless.SpecRef.Account)
    (h : (getAccountOptional a).run ts = .ok (some acct, ts₁)) :
    (setStorage a k v).run ts = .ok ((), specStorageWrite ts₁ a k v) := by
  unfold setStorage specStorageWrite
  simp only [StateT.run_bind, h, except_ok_bind]
  rw [if_neg (by simp)]
  rfl

/-! ## SpecRef's nested `dictSet`, through its lookup -/

theorem specTxSlot_write_self (ts : TransactionState) (a : Address)
    (k : Bytes32) (v : U256) :
    specTxSlot (specStorageWrite ts a k v) a k = some v := by
  unfold specTxSlot specStorageWrite
  dsimp only
  rw [dictGet?_dictSet_self]
  exact dictGet?_dictSet_self _ _ _

theorem specTxSlot_write_ne (ts : TransactionState) (a a' : Address)
    (k k' : Bytes32) (v : U256) (h : ¬(a' = a ∧ k' = k)) :
    specTxSlot (specStorageWrite ts a k v) a' k'
      = specTxSlot ts a' k' := by
  unfold specTxSlot specStorageWrite
  dsimp only
  by_cases ha : a' = a
  · subst ha
    have hk : k' ≠ k := fun hc => h ⟨rfl, hc⟩
    rw [dictGet?_dictSet_self]
    show dictGet? (dictSet ((dictGet? ts.storageWrites a').getD []) k v) k' = _
    rw [dictGet?_dictSet_ne _ _ _ _ hk]
    cases hs : dictGet? ts.storageWrites a' with
    | none => simp [dictGet?]
    | some slots => simp
  · rw [dictGet?_dictSet_ne _ _ _ _ ha]

/-- A storage write is invisible to `specOrig`: the transaction-start
value is read out of the block layer. -/
theorem specOrig_write (ts : TransactionState) (a a' : Address)
    (k k' : Bytes32) (v : U256) :
    specOrig (specStorageWrite ts a k v) a' k' = specOrig ts a' k' := rfl

/-! ## The extraction's overlay -/

/-- The extraction's transaction-layer row for a host key. -/
def hostStorageSlot (hs : Evm.HostState) (aV : Evm.Defs.address) (x : Nat) :
    Option Evm.Defs.StorageValue :=
  assocGet hs.storageTx ({ addr := aV, slot := x } : Evm.Defs.StorageKey)

/-- The extraction's `k_sstore` effect. -/
def hostStorageWrite (hs : Evm.HostState) (aV : Evm.Defs.address) (x : Nat)
    (e : Evm.Defs.StorageValue) : Evm.HostState :=
  { hs with
      storageTx :=
        assocPut hs.storageTx
          ({ addr := aV, slot := x } : Evm.Defs.StorageKey) e }

theorem runS_storage_tx_get_hit (aV : Evm.Defs.address) (x : Nat)
    (e : Evm.Defs.StorageValue) (hs : Evm.HostState) (ss : SeqState)
    (h : hostStorageSlot hs aV x = some e) :
    runS (Evm.Functions.storage_tx_get (Evm.Functions.storage_key aV x)) hs ss
      = .ok (Evm.Defs.StorageTxLookup.StorageTxHit e, hs) ss := by
  unfold hostStorageSlot at h
  refine runS_bind_ok (runS_get _ _) ?_
  show runS (match assocGet hs.storageTx
      ({ addr := aV, slot := x } : Evm.Defs.StorageKey) with
    | some value => pure (Evm.Defs.StorageTxLookup.StorageTxHit value)
    | none => _) hs ss = _
  rw [h]
  exact runS_pure _ _ _

/-- `k_sload` on a transaction-overlay hit: the row is returned as it
stands and **no** state is touched (the EIP-7928 read was recorded when
the row was established). -/
theorem runS_k_sload_hit (aV : Evm.Defs.address) (x : Nat)
    (e : Evm.Defs.StorageValue) (hs : Evm.HostState) (ss : SeqState)
    (h : hostStorageSlot hs aV x = some e) :
    runS (Evm.Functions.k_sload aV x) hs ss = .ok (e, hs) ss := by
  refine runS_sailME_throw ?_
  refine runE_bind_ok (runE_lift (runS_storage_tx_get_hit aV x e hs ss h)) ?_
  refine runE_bind_throw ?_
  exact runE_throw _ _ _

theorem runS_k_sstore (aV : Evm.Defs.address) (x : Nat)
    (e : Evm.Defs.StorageValue) (hs : Evm.HostState) (ss : SeqState) :
    runS (Evm.Functions.k_sstore aV x e) hs ss
      = .ok ((), hostStorageWrite hs aV x e) ss := by
  unfold hostStorageWrite
  exact runS_modify _ _ _

/-! ## The relation -/

/-- SpecRef's transaction-layer storage writes vs the extraction's
`storageTx` overlay, pointwise over host keys (address vector × slot
word). Presence is part of the agreement: a row exists on one side
exactly when the slot has a transaction-layer write on the other. -/
structure StorageRel (ts : TransactionState) (hs : Evm.HostState) :
    Prop where
  /-- Every row the extraction holds, SpecRef holds with the same live
  value. The converse fails by design — see MM-16 in the ledger: a
  `SSTORE` that writes the value already there records a row on SpecRef's
  side and none on the extraction's. -/
  curr : ∀ (aV : Evm.Defs.address) (w : Nat), WordWf w →
    ∀ e, hostStorageSlot hs aV w = some e →
      specTxSlot ts aV.toList (toBeBytes32 w) = some e.curr
  /-- The extraction's `orig` is the transaction-start value SpecRef
  recomputes with `getStorageOriginal`. -/
  orig : ∀ (aV : Evm.Defs.address) (w : Nat), WordWf w →
    ∀ e, hostStorageSlot hs aV w = some e →
      specOrig ts aV.toList (toBeBytes32 w) = .ok e.orig
  /-- Every stored live value is a well-formed word — what lets an
  `SLOAD` result be pushed back onto the stack, exactly as
  `TransientRel.wf` does. -/
  wf : ∀ (aV : Evm.Defs.address) (w : Nat), WordWf w →
    ∀ e, hostStorageSlot hs aV w = some e → WordWf e.curr

/-- The relation only reads four fields of the transaction state, so the
bookkeeping every SpecRef read performs (`storageReads`,
`accountReads`, `preStateReads`) cannot break it. -/
theorem storageRel_frame {ts ts' : TransactionState} {hs : Evm.HostState}
    (h1 : ts'.storageWrites = ts.storageWrites)
    (h2 : ts'.parent.storageWrites = ts.parent.storageWrites)
    (h3 : ts'.parent.preState = ts.parent.preState)
    (h4 : ts'.createdAccounts = ts.createdAccounts)
    (hrel : StorageRel ts hs) : StorageRel ts' hs := by
  have hslot : ∀ a k, specTxSlot ts' a k = specTxSlot ts a k := by
    intro a k
    unfold specTxSlot
    rw [h1]
  have horig : ∀ a k, specOrig ts' a k = specOrig ts a k := by
    intro a k
    unfold specOrig specBlockSlot
    rw [h2, h3, h4]
  exact
    { curr := fun aV w hw e he => by rw [hslot]; exact hrel.curr aV w hw e he
      orig := fun aV w hw e he => by
        rw [horig]; exact hrel.orig aV w hw e he
      wf := hrel.wf }

/-- The two key-inequalities every "some other slot" case needs: the
extraction's `StorageKey` and SpecRef's `(address, 32-byte key)` pair are
both injective in the host key. -/
private theorem storageKey_ne (aV bV : Evm.Defs.address) (x w : Nat)
    (hx : WordWf x) (hw : WordWf w) (hkey : ¬(bV = aV ∧ w = x)) :
    ({ addr := bV, slot := w } : Evm.Defs.StorageKey)
        ≠ { addr := aV, slot := x }
      ∧ ¬(bV.toList = aV.toList ∧ toBeBytes32 w = toBeBytes32 x) := by
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · injection hc with h1 h2
    exact hkey ⟨h1, h2⟩
  · exact hkey ⟨Vector.toList_inj.mp hc.1, toBeBytes32_inj hw hx hc.2⟩

/-- **`StorageRel` is stable under one `SSTORE`.** The extraction writes
the whole `StorageValue`; SpecRef writes only the live value and leaves
the transaction-start value to be recomputed, so the new row's `orig`
has to be supplied — by the `k_sload` that `SSTORE` performs first. -/
theorem storageRel_write (ts : TransactionState) (hs : Evm.HostState)
    (aV : Evm.Defs.address) (x : Nat) (e : Evm.Defs.StorageValue)
    (hx : WordWf x) (hwf : WordWf e.curr)
    (horig : specOrig ts aV.toList (toBeBytes32 x) = .ok e.orig)
    (hrel : StorageRel ts hs) :
    StorageRel (specStorageWrite ts aV.toList (toBeBytes32 x) e.curr)
      (hostStorageWrite hs aV x e) := by
  have hne : ∀ (bV : Evm.Defs.address) (w : Nat), WordWf w →
      ¬(bV = aV ∧ w = x) →
      ({ addr := bV, slot := w } : Evm.Defs.StorageKey)
          ≠ { addr := aV, slot := x }
        ∧ ¬(bV.toList = aV.toList ∧ toBeBytes32 w = toBeBytes32 x) :=
    fun bV w hw hkey => storageKey_ne aV bV x w hx hw hkey
  constructor
  case curr =>
    intro bV w hw e' he'
    by_cases hkey : bV = aV ∧ w = x
    · obtain ⟨rfl, rfl⟩ := hkey
      rw [hostStorageSlot, hostStorageWrite, assocGet_put_self] at he'
      rw [← Option.some.inj he', specTxSlot_write_self]
    · obtain ⟨h1, h2⟩ := hne bV w hw hkey
      rw [hostStorageSlot, hostStorageWrite, assocGet_put_ne _ _ _ _ h1] at he'
      rw [specTxSlot_write_ne _ _ _ _ _ _ h2]
      exact hrel.curr bV w hw e' he'
  case orig =>
    intro bV w hw e' he'
    rw [specOrig_write]
    by_cases hkey : bV = aV ∧ w = x
    · obtain ⟨rfl, rfl⟩ := hkey
      rw [hostStorageSlot, hostStorageWrite, assocGet_put_self] at he'
      rw [← Option.some.inj he']
      exact horig
    · obtain ⟨h1, _⟩ := hne bV w hw hkey
      rw [hostStorageSlot, hostStorageWrite, assocGet_put_ne _ _ _ _ h1] at he'
      exact hrel.orig bV w hw e' he'
  case wf =>
    intro bV w hw e' he'
    by_cases hkey : bV = aV ∧ w = x
    · obtain ⟨rfl, rfl⟩ := hkey
      rw [hostStorageSlot, hostStorageWrite, assocGet_put_self] at he'
      rw [← Option.some.inj he']
      exact hwf
    · obtain ⟨h1, _⟩ := hne bV w hw hkey
      rw [hostStorageSlot, hostStorageWrite, assocGet_put_ne _ _ _ _ h1] at he'
      exact hrel.wf bV w hw e' he'

/-- **The no-op `SSTORE` (MM-16).** When the value written is the value
already there, the extraction skips `k_sstore` while SpecRef's
`setStorage` records the row anyway. The relation is one-directional
precisely so that this step preserves it: the new SpecRef row agrees with
the extraction's row if there is one, and is invisible to the relation if
there is not. -/
theorem storageRel_write_noop (ts : TransactionState) (hs : Evm.HostState)
    (aV : Evm.Defs.address) (x v : Nat) (hx : WordWf x)
    (hsame : ∀ e, hostStorageSlot hs aV x = some e → e.curr = v)
    (hrel : StorageRel ts hs) :
    StorageRel (specStorageWrite ts aV.toList (toBeBytes32 x) v) hs := by
  constructor
  case curr =>
    intro bV w hw e' he'
    by_cases hkey : bV = aV ∧ w = x
    · obtain ⟨rfl, rfl⟩ := hkey
      rw [specTxSlot_write_self, hsame e' he']
    · obtain ⟨_, h2⟩ := storageKey_ne aV bV x w hx hw hkey
      rw [specTxSlot_write_ne _ _ _ _ _ _ h2]
      exact hrel.curr bV w hw e' he'
  case orig =>
    intro bV w hw e' he'
    rw [specOrig_write]
    exact hrel.orig bV w hw e' he'
  case wf => exact hrel.wf

/-! ## The success post for the persistent writer -/

/-- The base post plus the storage correspondence — `SSTORE`'s whole
observable effect is the write. -/
def StoragePost (mem : EvmMemorySlice) (sR' : Machine) (step : EvmStep)
    (hs' : Evm.HostState) (ss' : SeqState) : Prop :=
  BasePost mem sR' step hs' ss' ∧ StorageRel sR'.txState hs'

end EvmSpecsVerify
