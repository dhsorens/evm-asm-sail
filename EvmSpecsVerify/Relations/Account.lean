import EvmSpecsVerify.Relations.Storage
import EvmSpecsVerify.Representation.AddressWord

/-!
# Account relation (transaction overlay)

The account sibling of [`StorageRel`](Storage.lean), and the world
component that three ledgered read-agreement hypotheses wait on
(`BalanceAgree`, `SelfBalanceAgree`, `ExtcodehashAgree`).

Both sides keep a two-layer overlay over the witness. SpecRef's
transaction layer is `TransactionState.accountWrites : List (Address ×
Option Account)` — the `Option` *is* existence, `none` meaning "deleted
in this transaction" — over `parent.accountWrites` and the witness
pre-state. The extraction's is `HostState.accountTx : List (address ×
AcctValue)`, whose `curr` is a whole `Evm.Defs.Account`: the same three
trie fields plus a `storage_root` and four lifecycle flags (`present`,
`storage_cleared`, `created`, `selfdestructed`). Existence is the
`present` flag rather than the shape of the row, so the relation compares
SpecRef's entry against the extraction row's **EIP-161 view**
(`hostAcctView`).

Two of the relation's fields are that discipline, and they are load-bearing
rather than cosmetic: the extraction's readers return `info` fields
straight out of the row, while SpecRef's `getAccount` substitutes
`EMPTY_ACCOUNT` for a `none` entry. So an absent row must carry the empty
tuple (`absentEmpty`) and a present one must not (`presentNonEmpty`) —
which is exactly what `account_set_info` maintains ("collapsing to the
non-existent form when it is EIP-161-empty", Kernel/Accounts.lean) and
what `account_delete` installs. A future `accountRel_write` has to
re-establish both, which is where a host that broke the discipline would
be caught.

The discipline is maintainable because **both sides collapse**, and with
the same test: SpecRef's `modifyState` (StateTracker.lean:273) writes the
new tuple and then, `if accountExistsAndIsEmpty`, calls `destroyAccount`
— and every balance/nonce/code write goes through it (`moveEther`,
`createEther`, `setAccountBalance`, `incrementNonce`). The extraction's
`account_set_info` collapses the same three conditions inline.
`accountRel_isEmpty` below proves the two predicates agree on a related
row, which is the fact a future `accountRel_write` turns into
preservation. Both sides also clear storage as part of the collapse
(SpecRef's `destroyAccount` → `destroyStorage`, the extraction's
`store_account_info` → `storage_tx_clear`); how those two representations
of "cleared" line up is the open thread already recorded in
[`Storage.lean`](Storage.lean)'s docstring, not a new one.

This file imports [`StorageRel`](Storage.lean) for one shared piece:
`specAccountReadOf` and `storageFieldsEq_getAccountOptional`, the
bookkeeping frame of the very same account lookup, which storage needed
first because `setStorage` performs it.
-/

open private assocGet from Evm.HostAxioms

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## The empty-code-hash constant

SpecRef *computes* `keccak256 []` with its own permutation; the extraction
carries the digest as a literal. They agree, and the kernel checks it —
so the codeless-account hash needs no trust assumption, unlike the
`nativeAccelerateBytes` opacity that covers keccak on general input. -/

set_option exponentiation.threshold 400 in
theorem empty_code_hash_eq :
    EMPTY_CODE_HASH = Evm.Functions.KECCAK_EMPTY.toList := by decide

/-- The extraction's zero word is the numeral. -/
private theorem word_zero_eq' : Evm.Functions.WORD_ZERO = 0 := rfl

/-- SpecRef's `Account` derives `BEq` but no `LawfulBEq`, and
`isAccountAlive` / `EXTCODEHASH` both compare against `EMPTY_ACCOUNT`. -/
private theorem account_beq_eq (n₁ n₂ : Uint) (b₁ b₂ : U256)
    (h₁ h₂ : Hash32) :
    (({ nonce := n₁, balance := b₁, codeHash := h₁ } :
          EvmAsm.Stateless.SpecRef.Account)
        == { nonce := n₂, balance := b₂, codeHash := h₂ })
      = (n₁ == n₂ && (b₁ == b₂ && h₁ == h₂)) := rfl

instance : LawfulBEq EvmAsm.Stateless.SpecRef.Account where
  eq_of_beq {a b} h := by
    cases a
    cases b
    rw [account_beq_eq] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    simp only [EvmAsm.Stateless.SpecRef.Account.mk.injEq]
    tauto
  rfl {a} := by
    cases a
    rw [account_beq_eq]
    simp

/-! ## The two overlays -/

/-- SpecRef's transaction-layer account entry: `none` = no entry (fall
through to the block layer), `some none` = deleted in this transaction. -/
def specAcctRow (ts : TransactionState) (a : Address) :
    Option (Option EvmAsm.Stateless.SpecRef.Account) :=
  dictGet? ts.accountWrites a

/-- The extraction's transaction-layer account row. -/
def hostAcctRow (hs : Evm.HostState) (aV : Evm.Defs.address) :
    Option Evm.Defs.AcctValue :=
  assocGet hs.accountTx aV

/-- The EIP-161 view of an extraction account row: the three trie fields
SpecRef stores, or `none` when the row is not present. -/
def hostAcctView (a : Evm.Defs.Account) :
    Option EvmAsm.Stateless.SpecRef.Account :=
  if a.present then
    some
      { nonce := a.info.nonce
        balance := a.info.balance
        codeHash := a.info.code_hash.toList }
  else none

/-! ## SpecRef run shapes -/

/-- A transaction-overlay hit: the entry comes back and the only state
change is the recorded read. -/
theorem runTx_getAccountOptional_hit (ts : TransactionState) (a : Address)
    (r : Option EvmAsm.Stateless.SpecRef.Account) (h : specAcctRow ts a = some r) :
    (getAccountOptional a).run ts = .ok (r, specAccountReadOf ts a) := by
  unfold getAccountOptional specAcctRow specAccountReadOf at *
  simp only [StateT.run_bind, StateT.run_modify, StateT.run_get, pure_bind, h]
  rfl

theorem runTx_getAccount_hit (ts : TransactionState) (a : Address)
    (r : Option EvmAsm.Stateless.SpecRef.Account) (h : specAcctRow ts a = some r) :
    (getAccount a).run ts = .ok (r.getD EMPTY_ACCOUNT, specAccountReadOf ts a) := by
  unfold getAccount
  simp only [StateT.run_bind, runTx_getAccountOptional_hit ts a r h]
  rfl

/-- `isAccountAlive` on a hit: `EMPTY_ACCOUNT` and a deleted entry are
both dead. -/
theorem runTx_isAccountAlive_hit (ts : TransactionState) (a : Address)
    (r : Option EvmAsm.Stateless.SpecRef.Account) (h : specAcctRow ts a = some r) :
    (isAccountAlive a).run ts =
      .ok ((r.getD EMPTY_ACCOUNT != EMPTY_ACCOUNT), specAccountReadOf ts a) := by
  unfold isAccountAlive
  simp only [StateT.run_bind, runTx_getAccountOptional_hit ts a r h]
  cases r with
  | none => rfl
  | some acct => rfl

/-! ## `Evm` run shapes

`k_aload`'s first probe is the transaction overlay, and a hit touches no
state — the EIP-7928 account touch is recorded on the miss path, when the
row is established. -/

theorem runS_acct_tx_get_hit (aV : Evm.Defs.address) (v : Evm.Defs.AcctValue)
    (hs : Evm.HostState) (ss : SeqState) (h : hostAcctRow hs aV = some v) :
    runS (Evm.Functions.acct_tx_get aV) hs ss
      = .ok ({ found := true, account := v.curr }, hs) ss := by
  unfold hostAcctRow at h
  refine runS_bind_ok (runS_get _ _) ?_
  show runS (match assocGet hs.accountTx aV with
      | some value =>
        pure ({ found := true, account := value.curr } : Evm.Defs.AccountRow)
      | none =>
        pure ({ found := false, account := default } : Evm.Defs.AccountRow))
      hs ss = _
  rw [h]
  exact runS_pure _ _ _

theorem runS_k_aload_hit (aV : Evm.Defs.address) (v : Evm.Defs.AcctValue)
    (hs : Evm.HostState) (ss : SeqState) (h : hostAcctRow hs aV = some v) :
    runS (Evm.Functions.k_aload aV) hs ss = .ok (v.curr, hs) ss := by
  refine runS_bind_ok (runS_acct_tx_get_hit aV v hs ss h) ?_
  exact runS_pure _ _ _

theorem runS_k_get_balance_hit (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (hs : Evm.HostState) (ss : SeqState)
    (h : hostAcctRow hs aV = some v) :
    runS (Evm.Functions.k_get_balance aV) hs ss
      = .ok (v.curr.info.balance, hs) ss := by
  refine runS_bind_ok (runS_k_aload_hit aV v hs ss h) ?_
  exact runS_pure _ _ _

theorem runS_k_account_exists_hit (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (hs : Evm.HostState) (ss : SeqState)
    (h : hostAcctRow hs aV = some v) :
    runS (Evm.Functions.k_account_exists aV) hs ss
      = .ok (v.curr.present, hs) ss := by
  refine runS_bind_ok (runS_k_aload_hit aV v hs ss h) ?_
  exact runS_pure _ _ _

/-- `k_get_codehash` reports the zero hash for an absent account, where
SpecRef reports `0` for `EMPTY_ACCOUNT` — see `accountRel_codehash`. -/
theorem runS_k_get_codehash_hit (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (hs : Evm.HostState) (ss : SeqState)
    (h : hostAcctRow hs aV = some v) :
    runS (Evm.Functions.k_get_codehash aV) hs ss
      = .ok (if v.curr.present then v.curr.info.code_hash
          else Evm.Functions.ZERO_HASH, hs) ss := by
  refine runS_bind_ok (runS_k_aload_hit aV v hs ss h) ?_
  show runS (if (!v.curr.present) = true then
      (pure Evm.Functions.ZERO_HASH : Evm.SailM (Vector (BitVec 8) 32))
    else pure v.curr.info.code_hash) hs ss = _
  by_cases hp : v.curr.present = true
  · rw [if_pos hp, if_neg (by rw [hp]; decide)]
    exact runS_pure _ _ _
  · rw [if_neg hp, if_pos (by simp only [Bool.not_eq_true] at hp; rw [hp]; decide)]
    exact runS_pure _ _ _

/-! ## The relation -/

/-- SpecRef's transaction-layer account writes vs the extraction's
`accountTx` overlay, pointwise over host addresses. One-directional in
the same sense as [`StorageRel`](Storage.lean): every row the extraction
holds, SpecRef holds with the same EIP-161 view. -/
structure AccountRel (ts : TransactionState) (hs : Evm.HostState) : Prop where
  /-- Every row the extraction holds, SpecRef holds as its EIP-161 view. -/
  curr : ∀ (aV : Evm.Defs.address) (v : Evm.Defs.AcctValue),
    hostAcctRow hs aV = some v →
      specAcctRow ts aV.toList = some (hostAcctView v.curr)
  /-- A row marked absent carries the empty tuple — what
  `account_set_info` and `account_delete` install. Without it the
  extraction's `info`-field readers and SpecRef's `EMPTY_ACCOUNT`
  fallback would disagree. -/
  absentEmpty : ∀ (aV : Evm.Defs.address) (v : Evm.Defs.AcctValue),
    hostAcctRow hs aV = some v → v.curr.present = false →
      v.curr.info.balance = 0 ∧ v.curr.info.nonce = 0
        ∧ v.curr.info.code_hash = Evm.Functions.KECCAK_EMPTY
  /-- Dually, a present row is not EIP-161-empty: `account_set_info`
  collapses that case to the absent form. Without it a present-but-empty
  row would read back as `EMPTY_ACCOUNT` on SpecRef's side, where
  `EXTCODEHASH` pushes `0` rather than the hash. -/
  presentNonEmpty : ∀ (aV : Evm.Defs.address) (v : Evm.Defs.AcctValue),
    hostAcctRow hs aV = some v → v.curr.present = true →
      Evm.Functions.account_info_empty v.curr.info = false
  /-- Every stored balance is a well-formed word — what lets a balance be
  pushed onto the stack, exactly as `StorageRel.wf` does. -/
  wf : ∀ (aV : Evm.Defs.address) (v : Evm.Defs.AcctValue),
    hostAcctRow hs aV = some v → WordWf v.curr.info.balance

/-! ## The readers agree

Three consequences, one per ledgered hypothesis this relation reduces.
Each is stated on the *view*, so the opcode-level eliminators are a
rewrite away. -/

/-- The balance SpecRef reads is the row's balance. -/
theorem accountRel_balance {ts : TransactionState} {hs : Evm.HostState}
    (hrel : AccountRel ts hs) (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (hrow : hostAcctRow hs aV = some v) :
    ((hostAcctView v.curr).getD EMPTY_ACCOUNT).balance
      = v.curr.info.balance := by
  unfold hostAcctView
  by_cases hp : v.curr.present = true
  · rw [if_pos hp]
    rfl
  · rw [if_neg hp]
    exact ((hrel.absentEmpty aV v hrow (by simpa using hp)).1).symm

/-- The liveness SpecRef reads is the row's `present` flag. -/
theorem accountRel_alive {ts : TransactionState} {hs : Evm.HostState}
    (hrel : AccountRel ts hs) (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (hrow : hostAcctRow hs aV = some v) :
    ((hostAcctView v.curr).getD EMPTY_ACCOUNT != EMPTY_ACCOUNT)
      = v.curr.present := by
  unfold hostAcctView
  by_cases hp : v.curr.present = true
  · have hne := hrel.presentNonEmpty aV v hrow hp
    rw [if_pos hp, hp, Option.getD_some]
    refine bne_iff_ne.mpr (fun hc => ?_)
    obtain ⟨hn, hb, hh⟩ :
        v.curr.info.nonce = 0 ∧ v.curr.info.balance = 0
          ∧ v.curr.info.code_hash.toList = EMPTY_CODE_HASH := by
      simpa only [EMPTY_ACCOUNT,
        EvmAsm.Stateless.SpecRef.Account.mk.injEq] using hc
    rw [Evm.Functions.account_info_empty,
      show v.curr.info.code_hash = Evm.Functions.KECCAK_EMPTY from
        Vector.toList_inj.mp (hh.trans empty_code_hash_eq),
      hn, hb] at hne
    simp [Evm.Functions.word_is_zero, word_zero_eq'] at hne
  · rw [if_neg hp, show v.curr.present = false from by simpa using hp,
      Option.getD_none, bne_self_eq_false]

/-- **The EIP-161 collapse tests agree.** SpecRef's
`accountExistsAndIsEmpty` is `nonce == 0 && codeHash == EMPTY_CODE_HASH
&& balance == 0` on the tuple it stores; the extraction's
`account_info_empty` is the same three conditions on the row's `info`
(modulo `empty_code_hash_eq`). Since `modifyState` runs the first after
*every* account write and `account_set_info` the second, this is what
makes the relation's two discipline fields preservable. -/
theorem accountRel_isEmpty {ts : TransactionState} {hs : Evm.HostState}
    (hrel : AccountRel ts hs) (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (hrow : hostAcctRow hs aV = some v) :
    (((hostAcctView v.curr).getD EMPTY_ACCOUNT).nonce == 0
        && (((hostAcctView v.curr).getD EMPTY_ACCOUNT).codeHash
              == EMPTY_CODE_HASH
          && ((hostAcctView v.curr).getD EMPTY_ACCOUNT).balance == 0))
      = Evm.Functions.account_info_empty v.curr.info := by
  unfold hostAcctView
  by_cases hp : v.curr.present = true
  · have hne := hrel.presentNonEmpty aV v hrow hp
    rw [if_pos hp, Option.getD_some, hne]
    refine Bool.eq_false_iff.mpr (fun hc => ?_)
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    rw [Evm.Functions.account_info_empty,
      show v.curr.info.code_hash = Evm.Functions.KECCAK_EMPTY from
        Vector.toList_inj.mp (hc.2.1.trans empty_code_hash_eq),
      hc.1, hc.2.2] at hne
    simp [Evm.Functions.word_is_zero, word_zero_eq'] at hne
  · obtain ⟨hb, hn, hh⟩ := hrel.absentEmpty aV v hrow (by simpa using hp)
    rw [if_neg hp, Option.getD_none, Evm.Functions.account_info_empty,
      hb, hn, hh]
    simp [EMPTY_ACCOUNT, Evm.Functions.word_is_zero, word_zero_eq']

/-! ## Frames -/

/-- The relation reads one field of the transaction state, so the
`accountReads` bookkeeping every SpecRef lookup performs cannot break
it. -/
theorem accountRel_frame {ts ts' : TransactionState} {hs : Evm.HostState}
    (h : ts'.accountWrites = ts.accountWrites) (hrel : AccountRel ts hs) :
    AccountRel ts' hs := by
  have hrow : ∀ a, specAcctRow ts' a = specAcctRow ts a := by
    intro a
    unfold specAcctRow
    rw [h]
  exact
    { curr := fun aV v hv => by rw [hrow]; exact hrel.curr aV v hv
      absentEmpty := hrel.absentEmpty
      presentNonEmpty := hrel.presentNonEmpty
      wf := hrel.wf }

/-- And one field of the host state, so a host step that leaves
`accountTx` alone — `k_aload`'s block-level caching, a warm stamp, a
storage write — cannot break it either. -/
theorem accountRel_hostFrame {ts : TransactionState}
    {hs hs' : Evm.HostState} (h : hs'.accountTx = hs.accountTx)
    (hrel : AccountRel ts hs) : AccountRel ts hs' := by
  have hrow : ∀ aV, hostAcctRow hs' aV = hostAcctRow hs aV := by
    intro aV
    unfold hostAcctRow
    rw [h]
  exact
    { curr := fun aV v hv => hrel.curr aV v (by rw [← hrow]; exact hv)
      absentEmpty := fun aV v hv => hrel.absentEmpty aV v (by rw [← hrow]; exact hv)
      presentNonEmpty := fun aV v hv =>
        hrel.presentNonEmpty aV v (by rw [← hrow]; exact hv)
      wf := fun aV v hv => hrel.wf aV v (by rw [← hrow]; exact hv) }

end EvmSpecsVerify
