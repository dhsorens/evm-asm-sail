import EvmSpecsVerify.Relations.Assoc
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
the same test: SpecRef's `modifyState` (StateTracker.lean:274) writes the
new tuple and then, `if accountExistsAndIsEmpty`, calls `destroyAccount`
— and every balance/nonce/code write goes through it (`moveEther`,
`createEther`, `setAccountBalance`, `incrementNonce`). The extraction's
`account_set_info` collapses the same three conditions inline, and
`specAcctEmpty_eq` proves the two predicates are the same function of the
tuple. `accountRel_write` turns that into preservation for one
**non-collapsing** write.

The collapse is now proven for the **account** overlay
(`accountRel_write_collapse`, against `runS_store_account_info_clear`):
both sides land "no account" at the address, so the relation crosses it,
and the proof is shorter than the non-collapsing one because an absent
row's view is `none` unconditionally.

The **storage** overlays are a different matter, and the statement says
so rather than eliding it: SpecRef's `destroyAccount` → `destroyStorage`
is the identity on an account with no pending storage writes, while the
extraction's `storage_tx_clear` unconditionally records the address in a
clear generation that makes every later uncached slot read zero. That is
**MM-21**, with the reason it is unreachable — an account holding storage
is never EIP-161-empty. `HostAcctClearWritten` is framed against
`hostStorageClear hs aV` precisely so a caller cannot forget it.

One asymmetry worth naming, ledgered as **MM-18** and the account
analogue of MM-16 — the relation is one-directional for the same reason:
a **self** transfer. SpecRef's `moveEther a a v` runs `modifyState` twice (balance
`- v`, then `+ v`) and so records an `accountWrites` row, while the
extraction's `k_transfer` returns immediately when `src == dst` and
records nothing. The net values agree; only the presence of the row
differs, and the relation does not constrain a SpecRef row the extraction
lacks.

This file imports [`StorageRel`](Storage.lean) for one shared piece:
`specAccountReadOf` and `storageFieldsEq_getAccountOptional`, the
bookkeeping frame of the very same account lookup, which storage needed
first because `setStorage` performs it.
-/

open private assocGet assocPut accountTxValue from Evm.HostAxioms

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

/-- The two spellings of "codeless": SpecRef compares the 32 bytes
against its computed `keccak256 []`, the extraction the hash against its
literal. -/
theorem codeHash_beq_empty (h : Evm.Defs.hash) :
    (h.toList == EMPTY_CODE_HASH) = (h == Evm.Functions.KECCAK_EMPTY) := by
  by_cases hh : h = Evm.Functions.KECCAK_EMPTY
  · rw [hh]
    simp [empty_code_hash_eq]
  · rw [show (h == Evm.Functions.KECCAK_EMPTY) = false from by simpa using hh]
    refine beq_eq_false_iff_ne.mpr (fun hc => hh ?_)
    exact Vector.toList_inj.mp (hc.trans empty_code_hash_eq)

/-- **The EIP-161 tests agree on the tuple.** SpecRef's
`accountExistsAndIsEmpty` predicate, on the three trie fields it stores,
is the extraction's `account_info_empty` on the tuple they came from.
Everything else about the collapse follows from this. -/
theorem specAcctEmpty_eq (info : Evm.Defs.AccountInfo) :
    ((info.nonce == 0) && (info.code_hash.toList == EMPTY_CODE_HASH)
        && (info.balance == 0))
      = Evm.Functions.account_info_empty info := by
  unfold Evm.Functions.account_info_empty Evm.Functions.word_is_zero
  rw [word_zero_eq', codeHash_beq_empty]
  cases hh : (info.code_hash == Evm.Functions.KECCAK_EMPTY) <;>
    cases hn : (info.nonce == 0) <;> cases hb : (info.balance == 0) <;> rfl

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

/-- The SpecRef account a row's tuple projects to: the three trie fields,
named because a multi-line record literal does not parse inside a
structure-instance field or a tactic argument. -/
def specAcctOfInfo (info : Evm.Defs.AccountInfo) :
    EvmAsm.Stateless.SpecRef.Account :=
  { nonce := info.nonce
    balance := info.balance
    codeHash := info.code_hash.toList }

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

/-- EIP-161 emptiness of the row's `info`. `beneficiaryDead_eq` is what
identifies it with SpecRef's `EMPTY_ACCOUNT` test. -/
theorem runS_k_account_is_empty_hit (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (hs : Evm.HostState) (ss : SeqState)
    (h : hostAcctRow hs aV = some v) :
    runS (Evm.Functions.k_account_is_empty aV) hs ss
      = .ok (Evm.Functions.account_info_empty v.curr.info, hs) ss := by
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

/-! ## SpecRef's writes

Every SpecRef account write goes through `modifyState`
(StateTracker.lean:274): write the new tuple, then collapse it if the
result is EIP-161-empty. Only the **non-collapsing** case is proven here
— the collapse also destroys storage on both sides (`destroyAccount` →
`destroyStorage` vs `store_account_info` → `storage_tx_clear`), and how
those two representations of "cleared" line up is the open thread
[`Storage.lean`](Storage.lean) records. `SELFDESTRUCT`'s two writes are
both non-collapsing (the originator keeps its code, the beneficiary gains
balance), so this is the case its transfer needs. -/

/-- SpecRef's `setAccount` effect. -/
def specSetAccount (ts : TransactionState) (a : Address)
    (r : Option EvmAsm.Stateless.SpecRef.Account) : TransactionState :=
  { ts with accountWrites := dictSet ts.accountWrites a r }

theorem runTx_setAccount (ts : TransactionState) (a : Address)
    (r : Option EvmAsm.Stateless.SpecRef.Account) :
    (setAccount a r).run ts = .ok ((), specSetAccount ts a r) := rfl

/-- `TxM`'s base monad is `Except`, whose bind on a success is the
continuation (see the same bridge in Relations/Storage.lean). -/
private theorem except_ok_bind' {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a : Except ε α) >>= f = f a := rfl

/-- Fused bind for the tracker monad: a success step then the
continuation. Supplying both halves as terms keeps the proof out of
`rw`/`simp`'s syntactic matching, which the record literals `modifyState`
receives would otherwise defeat. -/
theorem runTx_bind_ok {α β : Type} {m : TxM α} {k : α → TxM β}
    {ts ts' : TransactionState} {a : α}
    {r : Except SpecError (β × TransactionState)}
    (h1 : m.run ts = .ok (a, ts')) (h2 : (k a).run ts' = r) :
    (m >>= k).run ts = r := by
  rw [show (m >>= k).run ts
      = (m.run ts) >>= (fun p => (k p.1).run p.2) from rfl, h1]
  exact h2

/-- The EIP-161 collapse test, on a transaction-overlay hit. -/
theorem runTx_accountExistsAndIsEmpty_hit (ts : TransactionState)
    (a : Address) (r : Option EvmAsm.Stateless.SpecRef.Account)
    (h : specAcctRow ts a = some r) :
    (accountExistsAndIsEmpty a).run ts =
      .ok (match r with
        | some acct =>
          (acct.nonce == 0 && acct.codeHash == EMPTY_CODE_HASH
            && acct.balance == 0)
        | none => false, specAccountReadOf ts a) := by
  unfold accountExistsAndIsEmpty
  simp only [StateT.run_bind, runTx_getAccountOptional_hit ts a r h]
  cases r with
  | none => rfl
  | some acct => rfl

/-- The same, on an entry that exists — the form the write lemma uses,
with no `match` left to reduce. -/
theorem runTx_accountExistsAndIsEmpty_some (ts : TransactionState)
    (a : Address) (acct : EvmAsm.Stateless.SpecRef.Account)
    (h : specAcctRow ts a = some (some acct)) :
    (accountExistsAndIsEmpty a).run ts =
      .ok ((acct.nonce == 0 && acct.codeHash == EMPTY_CODE_HASH
        && acct.balance == 0), specAccountReadOf ts a) :=
  runTx_accountExistsAndIsEmpty_hit ts a (some acct) h

/-- The transaction state after one non-collapsing `modifyState`: a read
mark, the write, and the collapse test's own read mark. -/
def specModifyStateOut (ts : TransactionState) (a : Address)
    (acct : EvmAsm.Stateless.SpecRef.Account) : TransactionState :=
  specAccountReadOf
    (specSetAccount (specAccountReadOf ts a) a (some acct)) a

theorem specModifyStateOut_accountWrites (ts : TransactionState)
    (a : Address) (acct : EvmAsm.Stateless.SpecRef.Account) :
    (specModifyStateOut ts a acct).accountWrites
      = dictSet ts.accountWrites a (some acct) := rfl

/-- **One non-collapsing account write.** `AccountRel` reads only
`accountWrites`, and `specModifyStateOut_accountWrites` is that field —
the read-bookkeeping marks `modifyState` leaves on the way are invisible
to the relation. -/
theorem runTx_modifyState_nonEmpty (ts : TransactionState) (a : Address)
    (f : EvmAsm.Stateless.SpecRef.Account → EvmAsm.Stateless.SpecRef.Account)
    (r : Option EvmAsm.Stateless.SpecRef.Account)
    (h : specAcctRow ts a = some r)
    (hne : ((f (r.getD EMPTY_ACCOUNT)).nonce == 0
      && (f (r.getD EMPTY_ACCOUNT)).codeHash == EMPTY_CODE_HASH
      && (f (r.getD EMPTY_ACCOUNT)).balance == 0) = false) :
    (modifyState a f).run ts
      = .ok ((), specModifyStateOut ts a (f (r.getD EMPTY_ACCOUNT))) := by
  have hwrite : specAcctRow
      (specSetAccount (specAccountReadOf ts a) a
        (some (f (r.getD EMPTY_ACCOUNT)))) a
      = some (some (f (r.getD EMPTY_ACCOUNT))) :=
    dictGet?_dictSet_self _ a _
  unfold modifyState specModifyStateOut
  simp only [StateT.run_bind, runTx_getAccount_hit ts a r h, except_ok_bind',
    runTx_setAccount,
    runTx_accountExistsAndIsEmpty_some _ a _ hwrite, hne]
  rfl

/-- SpecRef's **collapsing** `modifyState`: the write, then
`destroyAccount` — `destroyStorage` (a no-op exactly when the account has
no pending storage writes) followed by `setAccount … none`. -/
def specModifyStateCollapseOut (ts : TransactionState) (a : Address)
    (acct : EvmAsm.Stateless.SpecRef.Account) : TransactionState :=
  specSetAccount (specModifyStateOut ts a acct) a none

theorem specModifyStateCollapseOut_accountWrites (ts : TransactionState)
    (a : Address) (acct : EvmAsm.Stateless.SpecRef.Account) :
    (specModifyStateCollapseOut ts a acct).accountWrites
      = dictSet (dictSet ts.accountWrites a (some acct)) a none := rfl

/-- `destroyStorage` on an account with no pending storage writes is the
identity — the `none` branch of its `match` returns the state unchanged.
`hstore` is what confines the collapse to that branch; see
`Assumptions.lean` for why every reachable collapse satisfies it (only a
code-bearing account receives `setStorage`, and a collapsing account has
no code). -/
theorem runTx_destroyStorage_none (ts : TransactionState) (a : Address)
    (hstore : dictGet? ts.storageWrites a = none) :
    (destroyStorage a).run ts = .ok ((), ts) := by
  unfold destroyStorage
  simp only [StateT.run_modify, hstore]
  rfl

/-- **One collapsing account write.** The EIP-161 branch `modifyState`
takes when the value it just wrote is empty. -/
theorem runTx_modifyState_collapse (ts : TransactionState) (a : Address)
    (f : EvmAsm.Stateless.SpecRef.Account → EvmAsm.Stateless.SpecRef.Account)
    (r : Option EvmAsm.Stateless.SpecRef.Account)
    (h : specAcctRow ts a = some r)
    (hemp : ((f (r.getD EMPTY_ACCOUNT)).nonce == 0
      && (f (r.getD EMPTY_ACCOUNT)).codeHash == EMPTY_CODE_HASH
      && (f (r.getD EMPTY_ACCOUNT)).balance == 0) = true)
    (hstore : dictGet? ts.storageWrites a = none) :
    (modifyState a f).run ts
      = .ok ((), specModifyStateCollapseOut ts a (f (r.getD EMPTY_ACCOUNT))) := by
  have hwrite : specAcctRow
      (specSetAccount (specAccountReadOf ts a) a
        (some (f (r.getD EMPTY_ACCOUNT)))) a
      = some (some (f (r.getD EMPTY_ACCOUNT))) :=
    dictGet?_dictSet_self _ a _
  have hstore' : dictGet?
      (specModifyStateOut ts a (f (r.getD EMPTY_ACCOUNT))).storageWrites a
      = none := hstore
  unfold modifyState specModifyStateCollapseOut
  simp only [StateT.run_bind, runTx_getAccount_hit ts a r h, except_ok_bind',
    runTx_setAccount,
    runTx_accountExistsAndIsEmpty_some _ a _ hwrite, hemp]
  unfold destroyAccount
  rw [if_pos trivial]
  refine runTx_bind_ok (runTx_destroyStorage_none _ a hstore') ?_
  exact runTx_setAccount _ a none

/-! ## The extraction's writes

`store_account_info` (Kernel/Accounts.lean) is the extraction's only
account writer outside whole-row installs. Its storage clear is a
**prefix**, not one of three alternative shapes: when the new tuple is
EIP-161-empty it runs `storage_tx_clear` and *then* takes the same branch
it would otherwise — install the whole row when existence, the storage
root or the clear flag moves, else up to three scalar `acct_tx_set_*`
fast paths. So there are two shapes under an optional prefix, and the two
lemmas below split on the prefix rather than on the branch.

The fast-path branch applies only `balance`/`nonce`/`code_hash`, which is
complete: `AccountInfo` has exactly those three plus `storage_root`, and
the branch condition is what guarantees `storage_root` did not move.

Both lemmas report through their **rows** rather than their `accountTx`
list: `assocPut` moves the entry to the front, so the all-fields-unchanged
case produces a *reordered* list with the same contents, and `AccountRel`
reads only rows. -/

/-- The extraction's overlay write: one `assocPut` of the row, keeping
the transaction-start `orig`. -/
def hostAcctWrite (hs : Evm.HostState) (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (c : Evm.Defs.Account) : Evm.HostState :=
  { hs with accountTx := assocPut hs.accountTx aV { v with curr := c } }

theorem hostAcctWrite_row (hs : Evm.HostState) (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (c : Evm.Defs.Account) :
    hostAcctRow (hostAcctWrite hs aV v c) aV = some { v with curr := c } :=
  assocGet_put_self _ _ _

theorem hostAcctWrite_row_ne (hs : Evm.HostState)
    (aV bV : Evm.Defs.address) (v : Evm.Defs.AcctValue)
    (c : Evm.Defs.Account) (h : bV ≠ aV) :
    hostAcctRow (hostAcctWrite hs aV v c) bV = hostAcctRow hs bV :=
  assocGet_put_ne _ _ _ _ h

/-- Two writes at the same address collapse. -/
theorem hostAcctWrite_write (hs : Evm.HostState) (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (c c' : Evm.Defs.Account) :
    hostAcctWrite (hostAcctWrite hs aV v c) aV { v with curr := c } c'
      = hostAcctWrite hs aV v c' := by
  unfold hostAcctWrite
  simp only [assocPut_put_self]

/-- On a hit, the `prior` row `acct_tx_update` seeds is the row itself. -/
private theorem accountTxValue_hit (hs : Evm.HostState)
    (aV : Evm.Defs.address) (v : Evm.Defs.AcctValue)
    (h : hostAcctRow hs aV = some v) : accountTxValue hs aV = v := by
  unfold accountTxValue
  unfold hostAcctRow at h
  rw [h]

theorem runS_acct_tx_update_hit (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (c : Evm.Defs.Account) (hs : Evm.HostState)
    (ss : SeqState) (h : hostAcctRow hs aV = some v) :
    runS (Evm.Functions.acct_tx_update aV c) hs ss
      = .ok ((), hostAcctWrite hs aV v c) ss := by
  unfold hostAcctWrite
  rw [← accountTxValue_hit hs aV v h]
  exact runS_modify _ _ _

theorem runS_store_account_hit (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (c : Evm.Defs.Account) (hs : Evm.HostState)
    (ss : SeqState) (h : hostAcctRow hs aV = some v) :
    runS (Evm.Functions.store_account aV c) hs ss
      = .ok ((), hostAcctWrite hs aV v c) ss :=
  runS_acct_tx_update_hit aV v c hs ss h

theorem runS_acct_tx_set_balance_hit (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (val : Evm.Defs.word) (hs : Evm.HostState)
    (ss : SeqState) (h : hostAcctRow hs aV = some v) :
    runS (Evm.Functions.acct_tx_set_balance aV val) hs ss
      = .ok ((), hostAcctWrite hs aV v
          { v.curr with info := { v.curr.info with balance := val } }) ss := by
  unfold hostAcctWrite
  rw [← accountTxValue_hit hs aV v h]
  exact runS_modify _ _ _

theorem runS_acct_tx_set_nonce_hit (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (val : Evm.Defs.account_nonce)
    (hs : Evm.HostState) (ss : SeqState) (h : hostAcctRow hs aV = some v) :
    runS (Evm.Functions.acct_tx_set_nonce aV val) hs ss
      = .ok ((), hostAcctWrite hs aV v
          { v.curr with info := { v.curr.info with nonce := val } }) ss := by
  unfold hostAcctWrite
  rw [← accountTxValue_hit hs aV v h]
  exact runS_modify _ _ _

theorem runS_acct_tx_set_code_hash_hit (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (val : Evm.Defs.hash) (hs : Evm.HostState)
    (ss : SeqState) (h : hostAcctRow hs aV = some v) :
    runS (Evm.Functions.acct_tx_set_code_hash aV val) hs ss
      = .ok ((), hostAcctWrite hs aV v
          { v.curr with info := { v.curr.info with code_hash := val } }) ss := by
  unfold hostAcctWrite
  rw [← accountTxValue_hit hs aV v h]
  exact runS_modify _ _ _

/-- The row-level facts a write leaves behind, as an `∃`: the written row,
every other row, and — since every account writer is one `accountTx`
update — that **nothing else in the host state moved**. The last clause
subsumes the individual field-preservation facts an opcode needs
(`hostAcctWritten_frame`) and is what carries the log store, the warm
stamps and the storage overlay across a write. -/
def HostAcctWritten (hs hs' : Evm.HostState) (aV : Evm.Defs.address)
    (r : Evm.Defs.AcctValue) : Prop :=
  hostAcctRow hs' aV = some r
    ∧ (∀ bV, bV ≠ aV → hostAcctRow hs' bV = hostAcctRow hs bV)
    ∧ hs' = { hs with accountTx := hs'.accountTx }

/-- Every host field but `accountTx` reads back unchanged. -/
theorem hostAcctWritten_frame {hs hs' : Evm.HostState}
    {aV : Evm.Defs.address} {r : Evm.Defs.AcctValue}
    (h : HostAcctWritten hs hs' aV r) :
    hs'.stackFrames = hs.stackFrames ∧ hs'.warmAddresses = hs.warmAddresses
      ∧ hs'.warmEpoch = hs.warmEpoch ∧ hs'.storageTx = hs.storageTx
      ∧ hs'.logs = hs.logs ∧ hs'.logBytes = hs.logBytes
      ∧ hs'.memoryFrames = hs.memoryFrames
      ∧ hs'.memoryBytes = hs.memoryBytes := by
  rw [h.2.2]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hostAcctWritten_write (hs : Evm.HostState) (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (c : Evm.Defs.Account) :
    HostAcctWritten hs (hostAcctWrite hs aV v c) aV { v with curr := c } :=
  ⟨hostAcctWrite_row hs aV v c,
    fun bV hbV => hostAcctWrite_row_ne hs aV bV v c hbV, rfl⟩

theorem hostAcctWritten_refl (hs : Evm.HostState) (aV : Evm.Defs.address)
    (r : Evm.Defs.AcctValue) (h : hostAcctRow hs aV = some r) :
    HostAcctWritten hs hs aV r :=
  ⟨h, fun _ _ => rfl, rfl⟩

theorem hostAcctWritten_trans {hs hs' hs'' : Evm.HostState}
    {aV : Evm.Defs.address} {r r' : Evm.Defs.AcctValue}
    (h1 : HostAcctWritten hs hs' aV r) (h2 : HostAcctWritten hs' hs'' aV r') :
    HostAcctWritten hs hs'' aV r' :=
  ⟨h2.1, fun bV hbV => (h2.2.1 bV hbV).trans (h1.2.1 bV hbV),
    by rw [h2.2.2, h1.2.2]⟩

/-- A write at one address, seen from another: the second address'
`HostAcctWritten` facts survive it. What lets the transfer's two writes
compose even though each is reported at its own address. -/
theorem hostAcctWritten_of_ne {hs hs' : Evm.HostState}
    {aV bV : Evm.Defs.address} {r : Evm.Defs.AcctValue}
    (h : HostAcctWritten hs hs' aV r) (hb : bV ≠ aV)
    (r' : Evm.Defs.AcctValue) (hrow : hostAcctRow hs bV = some r') :
    hostAcctRow hs' bV = some r' := by
  rw [h.2.1 bV hb]; exact hrow

/-- One of `store_account_info`'s optional scalar sets. The result state
is existentially bound (an all-fields-unchanged run performs **no**
`assocPut`, and `assocPut` reorders, so the two runs' lists differ while
their rows agree), and the lemma hands back both the plain run equation
and a step-over principle for the do-elaborator's pushed continuation. -/
private theorem runS_opt_step (aV : Evm.Defs.address) (v : Evm.Defs.AcctValue)
    (c c' : Evm.Defs.Account) (cond : Bool) (m : Evm.SailM Unit)
    (hs : Evm.HostState)
    (hrow : hostAcctRow hs aV = some { v with curr := c })
    (hyes : cond = true → ∀ ss : SeqState, runS m hs ss
      = .ok ((), hostAcctWrite hs aV { v with curr := c } c') ss)
    (hno : cond = false → c = c') :
    ∃ hs' : Evm.HostState,
      HostAcctWritten hs hs' aV { v with curr := c' }
      ∧ (∀ ss : SeqState,
          runS (if cond = true then m else pure ()) hs ss = .ok ((), hs') ss)
      ∧ (∀ {α : Type} (k : Unit → Evm.SailM α) (ss : SeqState)
          {r : EStateM.Result SailError SeqState (α × Evm.HostState)},
          runS (k ()) hs' ss = r
          → runS (if cond = true then m >>= k else pure () >>= k) hs ss = r) := by
  by_cases hc : cond = true
  · refine ⟨hostAcctWrite hs aV { v with curr := c } c', ?_, fun ss => ?_, ?_⟩
    · simpa using hostAcctWritten_write hs aV { v with curr := c } c'
    · rw [if_pos hc]
      exact hyes hc ss
    · intro α k ss r hk
      rw [if_pos hc]
      exact runS_bind_ok (hyes hc ss) hk
  · refine ⟨hs, ?_, fun ss => ?_, ?_⟩
    · rw [← hno (by simpa using hc)]
      exact hostAcctWritten_refl hs aV _ hrow
    · rw [if_neg hc]
      exact runS_pure _ _ _
    · intro α k ss r hk
      rw [if_neg hc]
      exact runS_bind_ok (runS_pure _ _ _) hk

/-! ### The composite -/

/-- The row a non-collapsing `account_set_info` installs. Named because a
structure-instance field value has to fit on one physical line. -/
def acctRowSet (c : Evm.Defs.Account) (info : Evm.Defs.AccountInfo) :
    Evm.Defs.Account :=
  { c with info := info, present := true }

@[simp] theorem acctRowSet_info (c : Evm.Defs.Account)
    (info : Evm.Defs.AccountInfo) : (acctRowSet c info).info = info := rfl

@[simp] theorem acctRowSet_present (c : Evm.Defs.Account)
    (info : Evm.Defs.AccountInfo) : (acctRowSet c info).present = true := rfl

@[simp] theorem acctRowSet_created (c : Evm.Defs.Account)
    (info : Evm.Defs.AccountInfo) :
    (acctRowSet c info).created = c.created := rfl

@[simp] theorem acctRowSet_selfdestructed (c : Evm.Defs.Account)
    (info : Evm.Defs.AccountInfo) :
    (acctRowSet c info).selfdestructed = c.selfdestructed := rfl

@[simp] theorem acctRowSet_cleared (c : Evm.Defs.Account)
    (info : Evm.Defs.AccountInfo) :
    (acctRowSet c info).storage_cleared = c.storage_cleared := rfl

/-- **Every row's lifecycle flags survive one `store_account_info`.**
The value installed is `acctRowSet` of the old row, which replaces `info`
and `present` and nothing else — so `LifecycleRel` (and the EIP-6780 test
a caller makes after a balance write) crosses it. Stated as one equation
over the flag pair so it cannot fall behind either flag. -/
theorem hostAcctFlags_of_written {hs hs' : Evm.HostState}
    {aV : Evm.Defs.address} {v : Evm.Defs.AcctValue}
    {info : Evm.Defs.AccountInfo}
    (hrow : hostAcctRow hs aV = some v)
    (hw : HostAcctWritten hs hs' aV { v with curr := acctRowSet v.curr info }) :
    ∀ bV : Evm.Defs.address,
      (hostAcctRow hs' bV).map
          (fun w => (w.curr.created, w.curr.selfdestructed))
        = (hostAcctRow hs bV).map
            (fun w => (w.curr.created, w.curr.selfdestructed)) := by
  intro bV
  by_cases hb : bV = aV
  · rw [hb, hw.1, hrow]
    rfl
  · rw [hw.2.1 bV hb]

/-- The rows the three scalar fast paths leave, in order. -/
private def acctRow1 (c : Evm.Defs.Account) (info : Evm.Defs.AccountInfo) :
    Evm.Defs.Account :=
  { c with info := { c.info with balance := info.balance } }

private def acctRow2 (c : Evm.Defs.Account) (info : Evm.Defs.AccountInfo) :
    Evm.Defs.Account :=
  { acctRow1 c info with info := { (acctRow1 c info).info with nonce := info.nonce } }

private def acctRow3 (c : Evm.Defs.Account) (info : Evm.Defs.AccountInfo) :
    Evm.Defs.Account :=
  { acctRow2 c info with
      info := { (acctRow2 c info).info with code_hash := info.code_hash } }

theorem account_set_info_nonEmpty (acc : Evm.Defs.Account)
    (info : Evm.Defs.AccountInfo)
    (hne : Evm.Functions.account_info_empty info = false) :
    Evm.Functions.account_set_info acc info = acctRowSet acc info := by
  unfold Evm.Functions.account_set_info acctRowSet
  rw [hne]
  rfl

/-! ### The clearing shape

`store_account_info`'s storage clear is a **prefix**, not one of three
alternative shapes: when the new tuple is EIP-161-empty it runs
`storage_tx_clear` and *then* takes the same branch the non-clearing case
takes. The two lemmas below therefore differ in their prefix and in which
row `account_set_info` returns, not in structure.

They cannot share a tail lemma. `store_account_info`'s `do` block
elaborates through `have`-bound join points (`__do_jp`), so the tail is
not definitionally equal to any hand-written factoring of it — `rfl`
rejects the bridge even with `maxRecDepth` raised. -/

/-- The extraction's `storage_tx_clear` post-state: the account's
transaction-overlay storage rows dropped, and the account recorded in the
clear generation. `hostAcctRow` is untouched — the clear and the row
write hit disjoint parts of the host state. -/
def hostStorageClear (hs : Evm.HostState) (aV : Evm.Defs.address) :
    Evm.HostState :=
  { hs with
      storageTx := hs.storageTx.filter (·.1.addr != aV)
      storageCleared :=
        if hs.storageCleared.contains aV then hs.storageCleared
        else aV :: hs.storageCleared }

@[simp] theorem hostStorageClear_row (hs : Evm.HostState)
    (aV bV : Evm.Defs.address) :
    hostAcctRow (hostStorageClear hs aV) bV = hostAcctRow hs bV := rfl

theorem runS_storage_tx_clear (aV : Evm.Defs.address) (hs : Evm.HostState)
    (ss : SeqState) :
    runS (Evm.Functions.storage_tx_clear aV) hs ss
      = .ok ((), hostStorageClear hs aV) ss :=
  runS_modify _ _ _

/-- The row `account_set_info` installs when the new tuple is
EIP-161-empty: the empty tuple, absent, storage marked cleared — but with
the **old `storage_root` kept**, which is what leaves the shape-moved
branch able to be false at all. -/
def acctRowClear (c : Evm.Defs.Account) : Evm.Defs.Account :=
  { c with
      info := { Evm.Functions.EMPTY_ACCOUNT_INFO with
                  storage_root := c.info.storage_root }
      present := false
      storage_cleared := true }

@[simp] theorem acctRowClear_present (c : Evm.Defs.Account) :
    (acctRowClear c).present = false := rfl

@[simp] theorem acctRowClear_cleared (c : Evm.Defs.Account) :
    (acctRowClear c).storage_cleared = true := rfl

@[simp] theorem acctRowClear_root (c : Evm.Defs.Account) :
    (acctRowClear c).info.storage_root = c.info.storage_root := rfl

/-- The clearing row is independent of the `info` that triggered it: only
its emptiness is used. -/
theorem account_set_info_empty (acc : Evm.Defs.Account)
    (info : Evm.Defs.AccountInfo)
    (he : Evm.Functions.account_info_empty info = true) :
    Evm.Functions.account_set_info acc info = acctRowClear acc := by
  unfold Evm.Functions.account_set_info acctRowClear
  rw [he]
  rfl

/-- What a clearing write leaves: the row facts of an ordinary write, but
against the **cleared** state rather than `hs`. Stated by composition so
the frame clause reads `hs' = { hostStorageClear hs aV with accountTx := … }`
— i.e. the storage overlay moved, and it is the *only* thing besides the
row that did. That is not a weakness of the lemma: it is the content of
the clearing shape, and MM-21 records what SpecRef does not do here. -/
def HostAcctClearWritten (hs hs' : Evm.HostState) (aV : Evm.Defs.address)
    (r : Evm.Defs.AcctValue) : Prop :=
  HostAcctWritten (hostStorageClear hs aV) hs' aV r

/-- **One clearing `store_account_info`.** The shape-moved branch is
`present || !storage_cleared` once `next` is `acctRowClear`, since the
`storage_root` is preserved. Its false side needs `habs`: an absent row
already carries the empty tuple, so all three scalar tests fail and the
write is a complete no-op. `AccountRel.absentEmpty` is exactly that
hypothesis, so a caller under the relation gets it for free — and it is
what the field was introduced for. -/
theorem runS_store_account_info_clear (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (info : Evm.Defs.AccountInfo)
    (hs : Evm.HostState)
    (hrow : hostAcctRow hs aV = some v)
    (he : Evm.Functions.account_info_empty info = true)
    (habs : v.curr.present = false →
      v.curr.info.balance = 0 ∧ v.curr.info.nonce = 0
        ∧ v.curr.info.code_hash = Evm.Functions.KECCAK_EMPTY) :
    ∃ hs', (∀ ss : SeqState,
        runS (Evm.Functions.store_account_info aV v.curr info) hs ss
          = .ok ((), hs') ss)
      ∧ HostAcctClearWritten hs hs' aV { v with curr := acctRowClear v.curr } := by
  have hrow' : hostAcctRow (hostStorageClear hs aV) aV = some v := hrow
  unfold Evm.Functions.store_account_info HostAcctClearWritten
  rw [account_set_info_empty v.curr info he, he]
  simp only [acctRowClear_present, acctRowClear_cleared, acctRowClear_root,
    bne_self_eq_false, Bool.false_or]
  by_cases hb : (Evm.Functions.neq_bool false v.curr.present
      || Evm.Functions.neq_bool true v.curr.storage_cleared) = true
  · -- the whole-row install
    refine ⟨hostAcctWrite (hostStorageClear hs aV) aV v (acctRowClear v.curr),
      fun ss => ?_,
      hostAcctWritten_write _ aV v (acctRowClear v.curr)⟩
    refine runS_bind_ok (runS_storage_tx_clear aV hs ss) ?_
    rw [if_pos hb]
    exact runS_store_account_hit aV v _ _ ss hrow'
  · -- the fast paths, all three of them vacuous
    have hpr : v.curr.present = false := by
      by_contra hcon
      refine hb ?_
      rw [show v.curr.present = true from by simpa using hcon]
      rfl
    have hcl : v.curr.storage_cleared = true := by
      by_contra hcon
      refine hb ?_
      rw [show v.curr.storage_cleared = false from by simpa using hcon]
      simp [Evm.Functions.neq_bool]
    obtain ⟨hbal, hnon, hcode⟩ := habs hpr
    have hbal' : v.curr.info.balance = Evm.Functions.ZERO_WORD := by
      rw [hbal]; rfl
    have hinfo : ({ Evm.Functions.EMPTY_ACCOUNT_INFO with
          storage_root := v.curr.info.storage_root } : Evm.Defs.AccountInfo)
        = v.curr.info := by
      simp only [Evm.Functions.EMPTY_ACCOUNT_INFO]
      rw [← hnon, ← hbal', ← hcode]
    have hself : acctRowClear v.curr = v.curr := by
      unfold acctRowClear
      rw [hinfo, ← hpr, ← hcl]
    refine ⟨hostStorageClear hs aV, fun ss => ?_, ?_⟩
    · refine runS_bind_ok (runS_storage_tx_clear aV hs ss) ?_
      rw [if_neg hb, if_neg (by simp [hself]), if_neg (by simp [hself]),
        if_neg (by simp [hself])]
      exact runS_pure _ _ _
    · rw [hself]
      exact hostAcctWritten_refl _ aV v hrow'

/-- **One non-clearing `store_account_info`.** Both surviving shapes —
the whole-row install and the scalar fast paths — leave the same row. -/
theorem runS_store_account_info_hit (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (info : Evm.Defs.AccountInfo)
    (hs : Evm.HostState)
    (hrow : hostAcctRow hs aV = some v)
    (hne : Evm.Functions.account_info_empty info = false) :
    ∃ hs', (∀ ss : SeqState,
        runS (Evm.Functions.store_account_info aV v.curr info) hs ss
          = .ok ((), hs') ss)
      ∧ HostAcctWritten hs hs' aV
          { v with curr := Evm.Functions.account_set_info v.curr info } := by
  have hset := account_set_info_nonEmpty v.curr info hne
  unfold Evm.Functions.store_account_info
  rw [hset]
  simp only [acctRowSet_info, acctRowSet_present, acctRowSet_cleared]
  rw [hne, if_neg (by decide)]
  by_cases hb : (info.storage_root != v.curr.info.storage_root
      || (Evm.Functions.neq_bool true v.curr.present
        || Evm.Functions.neq_bool v.curr.storage_cleared v.curr.storage_cleared))
      = true
  · -- the whole-row install
    refine ⟨hostAcctWrite hs aV v (acctRowSet v.curr info),
      fun ss => runS_bind_ok (runS_pure _ _ _) ?_,
      hostAcctWritten_write hs aV v (acctRowSet v.curr info)⟩
    rw [if_pos hb]
    exact runS_store_account_hit aV v _ hs ss hrow
  · -- the scalar fast paths
    have hb' := (by simpa using hb :
      ¬((info.storage_root != v.curr.info.storage_root) = true
        ∨ (Evm.Functions.neq_bool true v.curr.present) = true
        ∨ (Evm.Functions.neq_bool v.curr.storage_cleared
            v.curr.storage_cleared) = true))
    have hsr : info.storage_root = v.curr.info.storage_root := by
      by_contra hcon
      exact hb' (Or.inl (by simpa using hcon))
    have hpr : v.curr.present = true := by
      by_contra hcon
      refine hb' (Or.inr (Or.inl ?_))
      rw [show v.curr.present = false from by simpa using hcon]
      rfl
    obtain ⟨hs1, w1, -, step1⟩ := runS_opt_step aV v v.curr
      (acctRow1 v.curr info) (info.balance != v.curr.info.balance)
      (Evm.Functions.acct_tx_set_balance aV info.balance) hs
      (by simpa using hrow)
      (fun _ ss => by
        simpa [acctRow1] using
          runS_acct_tx_set_balance_hit aV v info.balance hs ss hrow)
      (fun hc => by
        unfold acctRow1
        rw [show info.balance = v.curr.info.balance from by simpa using hc])
    obtain ⟨hs2, w2, -, step2⟩ := runS_opt_step aV v (acctRow1 v.curr info)
      (acctRow2 v.curr info) (info.nonce != v.curr.info.nonce)
      (Evm.Functions.acct_tx_set_nonce aV info.nonce) hs1 w1.1
      (fun _ ss => by
        simpa [acctRow2] using
          runS_acct_tx_set_nonce_hit aV _ info.nonce hs1 ss w1.1)
      (fun hc => by
        unfold acctRow2
        rw [show info.nonce = v.curr.info.nonce from by simpa using hc]
        rfl)
    obtain ⟨hs3, w3, plain3, -⟩ := runS_opt_step aV v (acctRow2 v.curr info)
      (acctRow3 v.curr info) (info.code_hash != v.curr.info.code_hash)
      (Evm.Functions.acct_tx_set_code_hash aV info.code_hash) hs2 w2.1
      (fun _ ss => by
        simpa [acctRow3] using
          runS_acct_tx_set_code_hash_hit aV _ info.code_hash hs2 ss w2.1)
      (fun hc => by
        unfold acctRow3
        rw [show info.code_hash = v.curr.info.code_hash from by simpa using hc]
        rfl)
    have hrow3 : acctRow3 v.curr info = acctRowSet v.curr info := by
      simp only [acctRow3, acctRow2, acctRow1, acctRowSet, hpr, ← hsr]
    refine ⟨hs3, fun ss => runS_bind_ok (runS_pure _ _ _) ?_, ?_⟩
    · rw [if_neg hb]
      exact step1 _ ss (step2 _ ss (plain3 ss))
    · rw [← hrow3]
      exact hostAcctWritten_trans w1 (hostAcctWritten_trans w2 w3)

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

/-- **The whole tuple SpecRef reads is the row's `info`.** Strengthens
`accountRel_balance` to all three trie fields, and holds on absent rows
too: there the view is `none`, SpecRef falls back to `EMPTY_ACCOUNT`, and
`absentEmpty` says the row's tuple is exactly that. This is what lets a
SpecRef `modifyState`'s field update be read off the extraction's
`info`. -/
theorem accountRel_view_eq {ts : TransactionState} {hs : Evm.HostState}
    (hrel : AccountRel ts hs) (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (hrow : hostAcctRow hs aV = some v) :
    (hostAcctView v.curr).getD EMPTY_ACCOUNT = specAcctOfInfo v.curr.info := by
  unfold hostAcctView specAcctOfInfo
  by_cases hp : v.curr.present = true
  · rw [if_pos hp]
    rfl
  · obtain ⟨hb, hn, hh⟩ := hrel.absentEmpty aV v hrow (by simpa using hp)
    rw [if_neg hp, Option.getD_none, EMPTY_ACCOUNT, hb, hn, hh,
      empty_code_hash_eq]

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
        && ((hostAcctView v.curr).getD EMPTY_ACCOUNT).codeHash
              == EMPTY_CODE_HASH
        && ((hostAcctView v.curr).getD EMPTY_ACCOUNT).balance == 0)
      = Evm.Functions.account_info_empty v.curr.info := by
  unfold hostAcctView
  by_cases hp : v.curr.present = true
  · rw [if_pos hp, Option.getD_some]
    exact specAcctEmpty_eq v.curr.info
  · obtain ⟨hb, hn, hh⟩ := hrel.absentEmpty aV v hrow (by simpa using hp)
    rw [if_neg hp, Option.getD_none, ← specAcctEmpty_eq v.curr.info, hb, hn, hh]
    simp [EMPTY_ACCOUNT, empty_code_hash_eq]

/-- **A row is EIP-161-empty exactly when it is absent.** The two
discipline fields, packaged as the equation the readers actually want:
`absentEmpty` gives one direction, `presentNonEmpty` the other. -/
theorem accountRel_empty_iff_absent {ts : TransactionState}
    {hs : Evm.HostState} (hrel : AccountRel ts hs) (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (hrow : hostAcctRow hs aV = some v) :
    Evm.Functions.account_info_empty v.curr.info = !v.curr.present := by
  by_cases hp : v.curr.present = true
  · rw [hp, hrel.presentNonEmpty aV v hrow hp]
    rfl
  · obtain ⟨hb, hn, hh⟩ := hrel.absentEmpty aV v hrow (by simpa using hp)
    rw [show v.curr.present = false from by simpa using hp,
      Evm.Functions.account_info_empty, hb, hn, hh]
    simp [Evm.Functions.word_is_zero, word_zero_eq']

/-! ## Preservation

The write direction of the relation. Together with `accountRel_isEmpty`
above — which says both sides' EIP-161 collapse tests agree — this is
what makes the discipline fields of [`AccountRel`](#AccountRel)
preservable rather than merely assumed. -/

theorem specAcctRow_setAccount_self (ts : TransactionState) (a : Address)
    (r : Option EvmAsm.Stateless.SpecRef.Account) :
    specAcctRow (specSetAccount ts a r) a = some r :=
  dictGet?_dictSet_self _ _ _

theorem specAcctRow_setAccount_ne (ts : TransactionState) (a a' : Address)
    (r : Option EvmAsm.Stateless.SpecRef.Account) (h : a' ≠ a) :
    specAcctRow (specSetAccount ts a r) a' = specAcctRow ts a' :=
  dictGet?_dictSet_ne _ _ _ _ h

/-- The view of a non-collapsing write's row. -/
theorem hostAcctView_rowSet (c : Evm.Defs.Account)
    (info : Evm.Defs.AccountInfo) :
    hostAcctView (acctRowSet c info) = some (specAcctOfInfo info) := by
  unfold hostAcctView specAcctOfInfo
  rw [if_pos (acctRowSet_present c info)]
  rfl

/-- The write-side corollary of [`specAcctEmpty_eq`](#specAcctEmpty_eq):
SpecRef's collapse test on the value it writes is the extraction's on the
tuple it installs, so one hypothesis serves both sides' writers. -/
theorem specAcctEmpty_view (c : Evm.Defs.Account)
    (info : Evm.Defs.AccountInfo) (acct : EvmAsm.Stateless.SpecRef.Account)
    (hval : hostAcctView (acctRowSet c info) = some acct) :
    ((acct.nonce == 0) && (acct.codeHash == EMPTY_CODE_HASH)
        && (acct.balance == 0))
      = Evm.Functions.account_info_empty info := by
  rw [hostAcctView_rowSet] at hval
  have hacct := Option.some.inj hval
  subst hacct
  exact specAcctEmpty_eq info

/-- **`AccountRel` is stable under one non-collapsing write.** The
extraction installs the whole `Account` (four lifecycle flags and a
storage root included); SpecRef stores the three trie fields, so the
value it writes has to be the row's EIP-161 view — `hval`, which
`hostAcctView_rowSet` computes. -/
theorem accountRel_write {ts : TransactionState} {hs hs' : Evm.HostState}
    (hrel : AccountRel ts hs) (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (info : Evm.Defs.AccountInfo)
    (hne : Evm.Functions.account_info_empty info = false)
    (hwf : WordWf info.balance)
    (acct : EvmAsm.Stateless.SpecRef.Account)
    (hval : hostAcctView (acctRowSet v.curr info) = some acct)
    (hw : HostAcctWritten hs hs' aV { v with curr := acctRowSet v.curr info }) :
    AccountRel (specSetAccount ts aV.toList (some acct)) hs' := by
  have hne' : ∀ bV : Evm.Defs.address, bV ≠ aV → bV.toList ≠ aV.toList :=
    fun bV hbV hc => hbV (Vector.toList_inj.mp hc)
  constructor
  case curr =>
    intro bV v' hv'
    by_cases hkey : bV = aV
    · subst hkey
      rw [hw.1] at hv'
      rw [← Option.some.inj hv', specAcctRow_setAccount_self, hval]
    · rw [specAcctRow_setAccount_ne _ _ _ _ (hne' bV hkey)]
      exact hrel.curr bV v' (by rw [← hw.2.1 bV hkey]; exact hv')
  case absentEmpty =>
    intro bV v' hv' habs
    by_cases hkey : bV = aV
    · subst hkey
      rw [hw.1] at hv'
      rw [← Option.some.inj hv'] at habs
      rw [acctRowSet_present] at habs
      cases habs
    · exact hrel.absentEmpty bV v' (by rw [← hw.2.1 bV hkey]; exact hv') habs
  case presentNonEmpty =>
    intro bV v' hv' hpres
    by_cases hkey : bV = aV
    · subst hkey
      rw [hw.1] at hv'
      rw [← Option.some.inj hv', acctRowSet_info]
      exact hne
    · exact hrel.presentNonEmpty bV v' (by rw [← hw.2.1 bV hkey]; exact hv')
        hpres
  case wf =>
    intro bV v' hv'
    by_cases hkey : bV = aV
    · subst hkey
      rw [hw.1] at hv'
      rw [← Option.some.inj hv']
      show WordWf (acctRowSet v.curr info).info.balance
      rw [acctRowSet_info]
      exact hwf
    · exact hrel.wf bV v' (by rw [← hw.2.1 bV hkey]; exact hv')

/-- The absent row projects to no account — the EIP-161 view of a
collapse. -/
@[simp] theorem hostAcctView_acctRowClear (c : Evm.Defs.Account) :
    hostAcctView (acctRowClear c) = none := rfl

/-- **`AccountRel` is stable under one collapsing write** — the deferred
half, and simpler than the non-collapsing one: the installed row is
absent, so its view is `none` unconditionally and no `hval` is needed.
SpecRef's `destroyAccount` leaves `some none` at the address and the
extraction's `acctRowClear` leaves an absent row; both read back as "no
account", which is what the relation compares.

`acct` is deliberately unconstrained: SpecRef writes it and then
overwrites it with `none` in the same `modifyState`, so the tuple it
collapsed *through* is not observable in the post-state. That is why this
lemma needs no counterpart to `accountRel_write`'s `hval` — there is no
written value left to relate.

The storage overlays are **not** related across this step and the
statement does not pretend otherwise: `HostAcctClearWritten`'s frame
clause is stated against `hostStorageClear hs aV`, and MM-21 records the
asymmetry that leaves — SpecRef marks nothing cleared. -/
theorem accountRel_write_collapse {ts : TransactionState}
    {hs hs' : Evm.HostState}
    (hrel : AccountRel ts hs) (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue)
    (acct : EvmAsm.Stateless.SpecRef.Account)
    (hw : HostAcctClearWritten hs hs' aV
      { v with curr := acctRowClear v.curr }) :
    AccountRel (specModifyStateCollapseOut ts aV.toList acct) hs' := by
  have hne' : ∀ bV : Evm.Defs.address, bV ≠ aV → bV.toList ≠ aV.toList :=
    fun bV hbV hc => hbV (Vector.toList_inj.mp hc)
  -- the two `dictSet`s of the collapse, seen through the relation's one field
  have hself : specAcctRow (specModifyStateCollapseOut ts aV.toList acct)
      aV.toList = some none := by
    unfold specAcctRow
    rw [specModifyStateCollapseOut_accountWrites]
    exact dictGet?_dictSet_self _ _ _
  have hother : ∀ b : Address, b ≠ aV.toList →
      specAcctRow (specModifyStateCollapseOut ts aV.toList acct) b
        = specAcctRow ts b := by
    intro b hb
    unfold specAcctRow
    rw [specModifyStateCollapseOut_accountWrites,
      dictGet?_dictSet_ne _ _ _ _ hb, dictGet?_dictSet_ne _ _ _ _ hb]
  constructor
  case curr =>
    intro bV v' hv'
    by_cases hkey : bV = aV
    · subst hkey
      rw [hw.1] at hv'
      rw [← Option.some.inj hv', hself, hostAcctView_acctRowClear]
    · rw [hother bV.toList (hne' bV hkey)]
      exact hrel.curr bV v' ((hw.2.1 bV hkey).symm.trans hv')
  case absentEmpty =>
    intro bV v' hv' _
    by_cases hkey : bV = aV
    · subst hkey
      rw [hw.1] at hv'
      rw [← Option.some.inj hv']
      exact ⟨rfl, rfl, rfl⟩
    · exact hrel.absentEmpty bV v' ((hw.2.1 bV hkey).symm.trans hv')
        (by assumption)
  case presentNonEmpty =>
    intro bV v' hv' hpres
    by_cases hkey : bV = aV
    · subst hkey
      rw [hw.1] at hv'
      rw [← Option.some.inj hv'] at hpres
      rw [acctRowClear_present] at hpres
      cases hpres
    · exact hrel.presentNonEmpty bV v' ((hw.2.1 bV hkey).symm.trans hv')
        hpres
  case wf =>
    intro bV v' hv'
    by_cases hkey : bV = aV
    · subst hkey
      rw [hw.1] at hv'
      rw [← Option.some.inj hv']
      show WordWf (acctRowClear v.curr).info.balance
      exact Nat.two_pow_pos 256
    · exact hrel.wf bV v' ((hw.2.1 bV hkey).symm.trans hv')

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

/-- The weaker frame the degenerate transfers need: `accountWrites` may
be rebuilt as long as every **row** reads back the same. A `dictSet` that
writes the value already there is exactly this, and so is a
`dictSet … none` on an entry that was already `some none`. -/
theorem accountRel_rowsFrame {ts ts' : TransactionState} {hs : Evm.HostState}
    (h : ∀ a : Address, specAcctRow ts' a = specAcctRow ts a)
    (hrel : AccountRel ts hs) : AccountRel ts' hs :=
  { curr := fun aV v hv => by rw [h]; exact hrel.curr aV v hv
    absentEmpty := hrel.absentEmpty
    presentNonEmpty := hrel.presentNonEmpty
    wf := hrel.wf }

/-- A row that is not `some none` when its tuple is not EIP-161-empty:
SpecRef's `EMPTY_ACCOUNT` fallback *is* empty, so a non-collapsing write
value proves the entry was really there. What lets the degenerate
transfers conclude that restoring a balance restores the row. -/
theorem specAcctRow_some_of_nonEmpty
    (r : Option EvmAsm.Stateless.SpecRef.Account)
    (h : ((r.getD EMPTY_ACCOUNT).nonce == 0
      && (r.getD EMPTY_ACCOUNT).codeHash == EMPTY_CODE_HASH
      && (r.getD EMPTY_ACCOUNT).balance == 0) = false) :
    r = some (r.getD EMPTY_ACCOUNT) := by
  cases r with
  | none =>
    rw [Option.getD_none] at h
    simp [EMPTY_ACCOUNT] at h
  | some acct => rfl

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

/-- **`AccountRel` is stable under one non-collapsing `modifyState`.**
`accountRel_write` phrased against the state `runTx_modifyState_nonEmpty`
actually produces: `modifyState` wraps its write in two read marks, and
the relation reads only `accountWrites`. -/
theorem accountRel_modifyState {ts : TransactionState}
    {hs hs' : Evm.HostState} (hrel : AccountRel ts hs)
    (aV : Evm.Defs.address) (v : Evm.Defs.AcctValue)
    (info : Evm.Defs.AccountInfo)
    (hne : Evm.Functions.account_info_empty info = false)
    (hwf : WordWf info.balance)
    (hw : HostAcctWritten hs hs' aV { v with curr := acctRowSet v.curr info }) :
    AccountRel (specModifyStateOut ts aV.toList (specAcctOfInfo info)) hs' :=
  accountRel_frame
    (show (specModifyStateOut ts aV.toList (specAcctOfInfo info)).accountWrites
      = (specSetAccount ts aV.toList (some (specAcctOfInfo info))).accountWrites
      from rfl)
    (accountRel_write hrel aV v info hne hwf (specAcctOfInfo info)
      (hostAcctView_rowSet v.curr info) hw)

end EvmSpecsVerify
