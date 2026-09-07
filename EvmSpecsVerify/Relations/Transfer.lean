import EvmSpecsVerify.Relations.Account
import EvmSpecsVerify.Relations.Log

/-!
# The value transfer

SpecRef and the extraction agree on moving wei, but they cut the work in
different places. SpecRef's `moveEther`
(SpecRef/StateTracker.lean:298) is a pure state-tracker action — reject
on insufficient balance, then two `modifyState`s — and its callers emit
the EIP-7708 transfer log themselves, each behind its own `!=` guard
(`iSelfdestruct`, Interpreter.lean:304, and `executeBody`,
Interpreter.lean:382). The extraction's `k_transfer`
(Kernel/Accounts.lean:168) does all three: two `store_account_info`
writes and `k_emit_transfer_log`, which carries the guard *inside* the
emitter. `specTransfer` below is the composite both SpecRef call sites
spell, and `transfer_equiv` pairs it with `k_transfer`.

## What this file settles

* **The EIP-7708 constants agree.** `transferLogAddress_eq` and
  `transferTopic_eq` are kernel computations, not assumptions:
  `keccak256 "Transfer(address,address,uint256)"` really is
  `0xddf252ad…`, and SpecRef's `SYSTEM_ADDRESS` really is the
  extraction's `EIP7708_SYSTEM_ADDRESS`. The topic needs one bridge on
  the way — `String.toUTF8.toList` is `ByteArray.toList`, which is
  well-founded and so opaque to `decide`; `byteArray_toList` rewrites it
  to the reducible `.data.toList`.
* **The self-transfer guards agree.** SpecRef checks
  `beneficiary != originator` in the *caller* and the extraction checks
  `src == dst` in the *emitter*, and the two produce the same log or
  absence of one. This was the suspected divergence behind mismatch
  ledger MM-18's log clause; it is disproven, and MM-18 is now only about
  the account row.

* **The degenerate branches agree too.** `k_transfer`'s early return
  covers `word_is_zero v || src == dst`, and both are reachable through
  `SELFDESTRUCT` — a zero-balance originator gives the first,
  `SELFDESTRUCT(address(this))` the second. `transfer_equiv` excludes
  them (`hv`, `hne`); `transfer_equiv_self`, `transfer_equiv_zero` and
  `transfer_equiv_zero_collapse` discharge them. Each shows SpecRef's two
  writes leave every **row** holding the value it already held, so
  mismatch ledger MM-18's "harmless" is now a theorem rather than an
  argument. The collapsing branch is included: a dead beneficiary is
  written as the empty tuple and immediately deleted again, landing back
  on the `some none` entry the relation had — which is where
  `AccountRel`'s `presentNonEmpty` field earns its keep.

## What it does not settle

The destination's balance, and this one is representational: the
extraction reduces the sum modulo `2^256` (`alu_add`), SpecRef adds two
`Nat`s (`a.balance + amount`). They agree exactly under `hsum`, the
no-overflow invariant the total ether supply guarantees and neither
specification checks (mismatch ledger MM-19).

The collapsing write also carries `hstore`: `destroyStorage` is the
identity only when the account has no pending storage writes. Every
reachable collapse satisfies it — `iSstore` writes storage only to
`message.currentTarget`, which is executing code, and an account with
code is never EIP-161-empty — but that argument is transaction-level, so
it stays a hypothesis (`Assumptions.lean`).
-/

set_option maxHeartbeats 4000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## `ByteArray.toList` is its array's list

Needed only to make `TRANSFER_TOPIC` computable in the kernel:
`ByteArray.toList` is defined by a well-founded loop, so `decide` gets
stuck on it, while `ByteArray.data.toList` reduces. -/

private theorem byteArray_size_eq (bs : ByteArray) :
    bs.size = bs.data.toList.length := rfl

set_option maxRecDepth 4000 in
private theorem toList_loop_eq (bs : ByteArray) :
    ∀ (n i : Nat) (r : List UInt8), bs.size - i = n →
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  intro n
  induction n with
  | zero =>
    intro i r hn
    rw [ByteArray.toList.loop, if_neg (by omega)]
    rw [byteArray_size_eq] at hn
    rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
  | succ n ih =>
    intro i r hn
    have hlt : i < bs.size := by omega
    have hlt' : i < bs.data.toList.length := by
      rw [← byteArray_size_eq]; exact hlt
    rw [ByteArray.toList.loop, if_pos hlt, ih (i + 1) _ (by omega)]
    have hg : bs.get! i = bs.data.toList[i] := by
      have hlt2 : i < bs.data.size := hlt'
      obtain ⟨d⟩ := bs
      show d[i]! = _
      rw [getElem!_pos d i (by exact hlt')]
      exact (Array.getElem_toList (i := i) (by exact hlt2)).symm
    rw [hg, List.drop_eq_getElem_cons hlt']
    simp

theorem byteArray_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  have h := toList_loop_eq bs (bs.size - 0) 0 [] rfl
  rw [show ByteArray.toList bs = ByteArray.toList.loop bs 0 [] from rfl, h]
  simp

/-! ## The EIP-7708 constants agree -/

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 400 in
/-- SpecRef's `SYSTEM_ADDRESS` is the extraction's
`EIP7708_SYSTEM_ADDRESS` (`0xff…fe`). -/
theorem transferLogAddress_eq :
    Evm.Functions.EIP7708_SYSTEM_ADDRESS.toList = VM_SYSTEM_ADDRESS := by
  decide

set_option maxRecDepth 1000000 in
set_option exponentiation.threshold 400 in
set_option maxHeartbeats 4000000 in
/-- `keccak256 "Transfer(address,address,uint256)"` is the extraction's
`EIP7708_TRANSFER_TOPIC`. Computed, not assumed. -/
theorem transferTopic_eq :
    toBeBytes32 Evm.Functions.EIP7708_TRANSFER_TOPIC = TRANSFER_TOPIC := by
  rw [show TRANSFER_TOPIC = keccak256
      (("Transfer(address,address,uint256)".toUTF8.data.toList).map
        (fun b => BitVec.ofNat 8 b.toNat)) from by
    rw [show TRANSFER_TOPIC = keccak256
        (("Transfer(address,address,uint256)".toUTF8.toList).map
          (fun b => BitVec.ofNat 8 b.toNat)) from rfl, byteArray_toList]]
  decide

/-! ## The log record -/

/-- The record SpecRef's `emit_transfer_log` appends. -/
def specTransferLog (src dst : Address) (v : U256) : Log :=
  { address := VM_SYSTEM_ADDRESS
    topics := [TRANSFER_TOPIC, List.replicate 12 0x00 ++ src,
               List.replicate 12 0x00 ++ dst]
    data := toBeBytes32 v }

/-- The extraction's three topic operands, in emission order. -/
def transferTopics (srcV dstV : Evm.Defs.address) : LogTopics :=
  .LogTopics3 (Evm.Functions.EIP7708_TRANSFER_TOPIC,
    Evm.Functions.address_to_word srcV, Evm.Functions.address_to_word dstV)

/-- **The two records are the same record.** Every field goes through a
different codec and they all land on the same bytes. -/
theorem logOf_transfer (srcV dstV : Evm.Defs.address) (v : U256) :
    logOf Evm.Functions.EIP7708_SYSTEM_ADDRESS
        (topicWords (transferTopics srcV dstV)) (toBeBytes32 v)
      = specTransferLog srcV.toList dstV.toList v := by
  unfold logOf specTransferLog transferTopics topicWords
  rw [transferLogAddress_eq]
  simp only [List.map_cons, List.map_nil, transferTopic_eq,
    toBeBytes32_address_to_word]

/-! ## SpecRef's side -/

/-- The machine after one `emit_transfer_log`. -/
def specLogAppend (s : Machine) (l : Log) : Evm :=
  { s.evm with logs := s.evm.logs ++ [l] }

/-- The machine a *degenerate* transfer leaves: only the tracker moved.
Named because a structure-instance field value has to fit on one physical
line. -/
def specTxOut (s : Machine) (ts' : TransactionState) : Machine :=
  { s with txState := ts' }

/-- The machine `specTransfer` leaves: the tracker's new state and one
appended log record. -/
def specTransferOut (s : Machine) (ts' : TransactionState) (l : Log) :
    Machine :=
  { s with
      txState := ts'
      evm := { s.evm with logs := s.evm.logs ++ [l] } }

theorem runR_emit_transfer_log (src dst : Address) (v : U256) (s : Machine)
    (hv : v ≠ 0) :
    runR (emit_transfer_log src dst v) s
      = .ok (.ok (), { s with evm := specLogAppend s (specTransferLog src dst v) }) := by
  unfold emit_transfer_log
  rw [if_neg (by simpa using hv)]
  rfl

/-- SpecRef's transfer, as its two call sites spell it: the tracker's
`move_ether`, then the EIP-7708 log behind the self-transfer guard. -/
def specTransfer (src dst : Address) (v : U256) : EvmM Unit := do
  EvmM.liftTx (moveEther src dst v)
  if dst != src then emit_transfer_log src dst v

/-- The two accounts SpecRef writes. Named for the record-literal parse
constraint. -/
def acctSubBalance (a : EvmAsm.Stateless.SpecRef.Account) (v : U256) :
    EvmAsm.Stateless.SpecRef.Account :=
  { a with balance := a.balance - v }

def acctAddBalance (a : EvmAsm.Stateless.SpecRef.Account) (v : U256) :
    EvmAsm.Stateless.SpecRef.Account :=
  { a with balance := a.balance + v }

/-- The transaction state `moveEther` leaves: `getAccount`'s read mark,
then the two `modifyState` writes with their own bookkeeping. -/
def specMoveEtherOut (ts : TransactionState) (src dst : Address)
    (sa da : EvmAsm.Stateless.SpecRef.Account) : TransactionState :=
  specModifyStateOut (specModifyStateOut (specAccountReadOf ts src) src sa) dst da

/-- `TxM`'s base monad is `Except`, whose bind on a success is the
continuation. -/
private theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a : Except ε α) >>= f = f a := rfl

private theorem except_pure_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (pure a : Except ε α) >>= f = f a := rfl

/-- **`moveEther` on the non-degenerate case.** Sufficient balance, two
distinct addresses, and neither write collapsing: the sub then the add,
with the recipient read at the state the sender's write left. -/
theorem runTx_moveEther (ts : TransactionState) (src dst : Address) (v : U256)
    (rs rd : Option EvmAsm.Stateless.SpecRef.Account)
    (hsrc : specAcctRow ts src = some rs)
    (hdst : specAcctRow ts dst = some rd)
    (hne : dst ≠ src)
    (hbal : v ≤ (rs.getD EMPTY_ACCOUNT).balance)
    (hsne : ((rs.getD EMPTY_ACCOUNT).nonce == 0
      && (rs.getD EMPTY_ACCOUNT).codeHash == EMPTY_CODE_HASH
      && (rs.getD EMPTY_ACCOUNT).balance - v == 0) = false)
    (hdne : ((rd.getD EMPTY_ACCOUNT).nonce == 0
      && (rd.getD EMPTY_ACCOUNT).codeHash == EMPTY_CODE_HASH
      && (rd.getD EMPTY_ACCOUNT).balance + v == 0) = false) :
    (moveEther src dst v).run ts
      = .ok ((), specMoveEtherOut ts src dst
          (acctSubBalance (rs.getD EMPTY_ACCOUNT) v)
          (acctAddBalance (rd.getD EMPTY_ACCOUNT) v)) := by
  have hsrc1 : specAcctRow (specAccountReadOf ts src) src = some rs := hsrc
  have hdst1 : specAcctRow
      (specModifyStateOut (specAccountReadOf ts src) src
        (acctSubBalance (rs.getD EMPTY_ACCOUNT) v)) dst = some rd := by
    unfold specAcctRow
    rw [specModifyStateOut_accountWrites, dictGet?_dictSet_ne _ _ _ _ hne]
    exact hdst
  unfold moveEther specMoveEtherOut
  refine runTx_bind_ok (runTx_getAccount_hit ts src rs hsrc) ?_
  rw [if_neg (by simpa using hbal)]
  refine runTx_bind_ok (m := pure ()) rfl ?_
  refine runTx_bind_ok
    (runTx_modifyState_nonEmpty (specAccountReadOf ts src) src _ rs hsrc1 hsne)
    ?_
  exact runTx_modifyState_nonEmpty _ dst _ rd hdst1 hdne

/-! ## The extraction's side -/

/-- The tuples the extraction's two `store_account_info` calls install. -/
def transferSrcInfo (info : Evm.Defs.AccountInfo) (v : U256) :
    Evm.Defs.AccountInfo :=
  { info with balance := info.balance - v }

def transferDstInfo (info : Evm.Defs.AccountInfo) (v : U256) :
    Evm.Defs.AccountInfo :=
  { info with balance := info.balance + v }

theorem alu_sub_of_le (a b : Nat) (h : b ≤ a) :
    Evm.Functions.alu_sub a b = a - b := by
  unfold Evm.Functions.alu_sub Evm.Functions.word_sub_word
  rw [if_pos (by simpa using h)]

/-- The extraction reduces the sum modulo `2^256`; SpecRef adds two
`Nat`s. They agree exactly below the wrap — the no-overflow invariant the
ether supply guarantees and neither specification checks. -/
theorem alu_add_of_lt (a b : Nat) (h : a + b < 2 ^ 256) :
    Evm.Functions.alu_add a b = a + b := by
  unfold Evm.Functions.alu_add Evm.Functions.word_add_word Evm.Functions.u256
  exact Nat.mod_eq_of_lt h

theorem word_is_zero_of_ne (v : Nat) (hv : v ≠ 0) :
    Evm.Functions.word_is_zero v = false := by
  unfold Evm.Functions.word_is_zero
  rw [show Evm.Functions.WORD_ZERO = 0 from rfl]
  simpa using hv

/-- `k_emit_transfer_log` on the case that emits: Amsterdam or later, a
nonzero value, and two distinct addresses. The extraction carries all
three guards inside the emitter; SpecRef's `emit_transfer_log` carries
only the value guard and leaves the self-transfer check to its callers,
which is why `hne` appears here and in `specTransfer`'s `if`. -/
theorem runS_k_emit_transfer_log (srcV dstV : Evm.Defs.address) (v : Nat)
    (hs : Evm.HostState) (ss : SeqState) (prof : ExecutionProfile)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hfork : AmsterdamProfile prof) (hv : v ≠ 0) (hne : (srcV == dstV) = false) :
    runS (Evm.Functions.k_emit_transfer_log srcV dstV v) hs ss
      = .ok ((), logAppend hs Evm.Functions.EIP7708_SYSTEM_ADDRESS
          (topicWords (transferTopics srcV dstV)) (toBeBytes32 v)) ss := by
  obtain ⟨fork, t, mx, dn, cl, il, ptl, prl, tbl, rd, bl, ttl, trl, epf⟩ := prof
  unfold AmsterdamProfile at hfork
  simp only at hfork
  unfold Evm.Functions.k_emit_transfer_log
  refine runS_bind_ok (runS_readReg _ _ _ _ hprof) ?_
  simp only [ProtocolProfileFields.fork, word_is_zero_of_ne v hv, hne]
  rw [if_neg (by simpa using Nat.not_lt.mpr hfork)]
  exact runS_k_log_word _ (transferTopics srcV dstV) v hs ss

/-- The rows the two `store_account_info` calls install. -/
def transferSrcRow (sv : Evm.Defs.AcctValue) (v : U256) : Evm.Defs.AcctValue :=
  { sv with curr := acctRowSet sv.curr (transferSrcInfo sv.curr.info v) }

def transferDstRow (dv : Evm.Defs.AcctValue) (v : U256) : Evm.Defs.AcctValue :=
  { dv with curr := acctRowSet dv.curr (transferDstInfo dv.curr.info v) }

/-- **`k_transfer` on the non-degenerate case.** Two writes and one
emission. The intermediate states are existentially bound because
`store_account_info` reports through rows, not through the `accountTx`
list (`assocPut` reorders, and an all-unchanged run performs no put). -/
theorem runS_k_transfer (srcV dstV : Evm.Defs.address) (v : U256)
    (sv dv : Evm.Defs.AcctValue) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hfork : AmsterdamProfile prof)
    (hsrc : hostAcctRow hs srcV = some sv)
    (hdst : hostAcctRow hs dstV = some dv)
    (hne : dstV ≠ srcV) (hv : v ≠ 0)
    (hbal : v ≤ sv.curr.info.balance)
    (hsum : dv.curr.info.balance + v < 2 ^ 256)
    (hsne : Evm.Functions.account_info_empty (transferSrcInfo sv.curr.info v)
      = false)
    (hdne : Evm.Functions.account_info_empty (transferDstInfo dv.curr.info v)
      = false) :
    ∃ hs1 hs2 : Evm.HostState,
      HostAcctWritten hs hs1 srcV (transferSrcRow sv v)
      ∧ HostAcctWritten hs1 hs2 dstV (transferDstRow dv v)
      ∧ runS (Evm.Functions.k_transfer srcV dstV v) hs ss
        = .ok ((), logAppend hs2 Evm.Functions.EIP7708_SYSTEM_ADDRESS
            (topicWords (transferTopics srcV dstV)) (toBeBytes32 v)) ss := by
  have hbeq : (srcV == dstV) = false := by
    simpa using fun hc => hne (Vector.toList_inj.mp
      (congrArg Vector.toList hc)).symm
  obtain ⟨hs1, run1, w1⟩ := runS_store_account_info_hit srcV sv
    (transferSrcInfo sv.curr.info v) hs ss hsrc hsne
  have hdst1 : hostAcctRow hs1 dstV = some dv :=
    hostAcctWritten_of_ne w1 hne dv hdst
  obtain ⟨hs2, run2, w2⟩ := runS_store_account_info_hit dstV dv
    (transferDstInfo dv.curr.info v) hs1 ss hdst1 hdne
  have hw1 : HostAcctWritten hs hs1 srcV (transferSrcRow sv v) := by
    unfold transferSrcRow
    rw [← account_set_info_nonEmpty sv.curr _ hsne]
    exact w1
  have hw2 : HostAcctWritten hs1 hs2 dstV (transferDstRow dv v) := by
    unfold transferDstRow
    rw [← account_set_info_nonEmpty dv.curr _ hdne]
    exact w2
  refine ⟨hs1, hs2, hw1, hw2, ?_⟩
  unfold Evm.Functions.k_transfer
  refine runS_bind_ok (runS_k_aload_hit srcV sv hs ss hsrc) ?_
  refine runS_bind_ok (runS_k_aload_hit dstV dv hs ss hdst) ?_
  simp only [word_is_zero_of_ne v hv, hbeq]
  rw [if_neg (by decide)]
  rw [show Evm.Functions.alu_sub sv.curr.info.balance v
      = sv.curr.info.balance - v from alu_sub_of_le _ _ hbal]
  refine runS_bind_ok (show runS (Evm.Functions.store_account_info srcV
      sv.curr (transferSrcInfo sv.curr.info v)) hs ss = .ok ((), hs1) ss
    from run1) ?_
  rw [show Evm.Functions.alu_add dv.curr.info.balance v
      = dv.curr.info.balance + v from alu_add_of_lt _ _ hsum]
  refine runS_bind_ok (show runS (Evm.Functions.store_account_info dstV
      dv.curr (transferDstInfo dv.curr.info v)) hs1 ss = .ok ((), hs2) ss
    from run2) ?_
  exact runS_k_emit_transfer_log srcV dstV v hs2 ss prof hprof hfork hv hbeq

/-! ## The degenerate cases

`k_transfer`'s early return covers `word_is_zero v || src == dst`, and
both branches are reachable through `SELFDESTRUCT` — a zero-balance
originator gives the first, `SELFDESTRUCT(address(this))` the second.
SpecRef runs its two `modifyState`s regardless, so mismatch ledger MM-18
recorded the row asymmetry and `transfer_equiv` excluded both. The two
theorems below discharge them instead: SpecRef's writes are
relation-preserving in each case, so the ledger entry's "harmless"
becomes a proof.

The self-transfer needs no extra hypothesis beyond the first write's
non-collapse: the second `modifyState` reads the balance the first left
and adds `v` back, and `v ≤ balance` makes the restored balance nonzero,
so the second write cannot collapse. The zero-value transfer *does* let
the destination collapse — the beneficiary of a `SELFDESTRUCT` may be
dead — and that branch is exactly where `AccountRel` earns its
`presentNonEmpty` field: a collapsing SpecRef write and an absent
extraction row agree, because `hostAcctView` of a non-`present` row is
`none`. -/

/-- `k_transfer`'s early return: the two `k_aload`s hit the overlay and
touch nothing, then the guard short-circuits. -/
theorem runS_k_transfer_noop (srcV dstV : Evm.Defs.address) (v : U256)
    (sv dv : Evm.Defs.AcctValue) (hs : Evm.HostState) (ss : SeqState)
    (hsrc : hostAcctRow hs srcV = some sv)
    (hdst : hostAcctRow hs dstV = some dv)
    (hguard : (Evm.Functions.word_is_zero v || (srcV == dstV)) = true) :
    runS (Evm.Functions.k_transfer srcV dstV v) hs ss = .ok ((), hs) ss := by
  unfold Evm.Functions.k_transfer
  refine runS_bind_ok (runS_k_aload_hit srcV sv hs ss hsrc) ?_
  refine runS_bind_ok (runS_k_aload_hit dstV dv hs ss hdst) ?_
  show runS (if (Evm.Functions.word_is_zero v || (srcV == dstV)) = true then
      pure () else _) hs ss = _
  rw [if_pos hguard]
  exact runS_pure _ _ _

/-! ### The self-transfer -/

/-- The transaction state a self-transfer leaves: two writes at the same
address, the second restoring the balance the first debited. -/
def specSelfTransferOut (ts : TransactionState) (a : Address)
    (sa fa : EvmAsm.Stateless.SpecRef.Account) : TransactionState :=
  specModifyStateOut (specModifyStateOut (specAccountReadOf ts a) a sa) a fa

/-- The credit undoes the debit when the balance covers it. -/
theorem acctAddBalance_acctSubBalance (acct : EvmAsm.Stateless.SpecRef.Account)
    (v : U256) (h : v ≤ acct.balance) :
    acctAddBalance (acctSubBalance acct v) v = acct := by
  unfold acctAddBalance acctSubBalance
  rw [Nat.sub_add_cancel h]

/-- **`moveEther a a v` on the reachable regime.** The debit then the
credit, both at `a`; only the *first* needs a non-collapse hypothesis,
because `v ≤ balance` together with `v ≠ 0` makes the restored balance
nonzero. The net effect on the row is the identity, which is why
`AccountRel` survives it. -/
theorem runTx_moveEther_self (ts : TransactionState) (a : Address) (v : U256)
    (r : Option EvmAsm.Stateless.SpecRef.Account)
    (hrow : specAcctRow ts a = some r)
    (hbal : v ≤ (r.getD EMPTY_ACCOUNT).balance)
    (hv : v ≠ 0)
    (hsne : ((r.getD EMPTY_ACCOUNT).nonce == 0
      && (r.getD EMPTY_ACCOUNT).codeHash == EMPTY_CODE_HASH
      && (r.getD EMPTY_ACCOUNT).balance - v == 0) = false) :
    (moveEther a a v).run ts
      = .ok ((), specSelfTransferOut ts a
          (acctSubBalance (r.getD EMPTY_ACCOUNT) v) (r.getD EMPTY_ACCOUNT)) := by
  have hrow1 : specAcctRow (specAccountReadOf ts a) a = some r := hrow
  have hrow2 : specAcctRow
      (specModifyStateOut (specAccountReadOf ts a) a
        (acctSubBalance (r.getD EMPTY_ACCOUNT) v)) a
      = some (some (acctSubBalance (r.getD EMPTY_ACCOUNT) v)) :=
    dictGet?_dictSet_self _ a _
  have hrestore := acctAddBalance_acctSubBalance (r.getD EMPTY_ACCOUNT) v hbal
  have hbalpos : (r.getD EMPTY_ACCOUNT).balance ≠ 0 := by
    intro hc
    rw [hc] at hbal
    exact hv (Nat.le_zero.mp hbal)
  have hdne : ((acctSubBalance (r.getD EMPTY_ACCOUNT) v).nonce == 0
      && (acctSubBalance (r.getD EMPTY_ACCOUNT) v).codeHash == EMPTY_CODE_HASH
      && (acctSubBalance (r.getD EMPTY_ACCOUNT) v).balance + v == 0) = false := by
    simp [acctSubBalance, Nat.sub_add_cancel hbal, hbalpos]
  have hraw : (moveEther a a v).run ts
      = .ok ((), specSelfTransferOut ts a
          (acctSubBalance (r.getD EMPTY_ACCOUNT) v)
          (acctAddBalance (acctSubBalance (r.getD EMPTY_ACCOUNT) v) v)) := by
    unfold moveEther specSelfTransferOut
    refine runTx_bind_ok (runTx_getAccount_hit ts a r hrow) ?_
    rw [if_neg (by simpa using hbal)]
    refine runTx_bind_ok (m := pure ()) rfl ?_
    refine runTx_bind_ok
      (runTx_modifyState_nonEmpty (specAccountReadOf ts a) a _ r hrow1 hsne) ?_
    exact runTx_modifyState_nonEmpty _ a
      (fun x => { nonce := x.nonce, balance := x.balance + v, codeHash := x.codeHash })
      _ hrow2 hdne
  rw [hraw, hrestore]

/-! ### The zero-value transfer -/

/-- The transaction state a zero-value transfer leaves when the
destination survives: two no-op writes. -/
def specZeroTransferOut (ts : TransactionState) (src dst : Address)
    (sa da : EvmAsm.Stateless.SpecRef.Account) : TransactionState :=
  specModifyStateOut (specModifyStateOut (specAccountReadOf ts src) src sa) dst da

/-- The same when the destination collapses: EIP-161 deletes it. -/
def specZeroTransferCollapseOut (ts : TransactionState) (src dst : Address)
    (sa da : EvmAsm.Stateless.SpecRef.Account) : TransactionState :=
  specModifyStateCollapseOut
    (specModifyStateOut (specAccountReadOf ts src) src sa) dst da

theorem acctSubBalance_zero (acct : EvmAsm.Stateless.SpecRef.Account) :
    acctSubBalance acct 0 = acct := by
  unfold acctSubBalance
  rw [Nat.sub_zero]

theorem acctAddBalance_zero (acct : EvmAsm.Stateless.SpecRef.Account) :
    acctAddBalance acct 0 = acct := by
  unfold acctAddBalance
  rw [Nat.add_zero]

/-- **`moveEther src dst 0`, destination surviving.** Both writes store
the value that was already there. -/
theorem runTx_moveEther_zero (ts : TransactionState) (src dst : Address)
    (rs rd : Option EvmAsm.Stateless.SpecRef.Account)
    (hsrc : specAcctRow ts src = some rs)
    (hdst : specAcctRow ts dst = some rd)
    (hne : dst ≠ src)
    (hsne : ((rs.getD EMPTY_ACCOUNT).nonce == 0
      && (rs.getD EMPTY_ACCOUNT).codeHash == EMPTY_CODE_HASH
      && (rs.getD EMPTY_ACCOUNT).balance == 0) = false)
    (hdne : ((rd.getD EMPTY_ACCOUNT).nonce == 0
      && (rd.getD EMPTY_ACCOUNT).codeHash == EMPTY_CODE_HASH
      && (rd.getD EMPTY_ACCOUNT).balance == 0) = false) :
    (moveEther src dst 0).run ts
      = .ok ((), specZeroTransferOut ts src dst
          (rs.getD EMPTY_ACCOUNT) (rd.getD EMPTY_ACCOUNT)) := by
  have h := runTx_moveEther ts src dst 0 rs rd hsrc hdst hne (Nat.zero_le _)
    (by rw [Nat.sub_zero]; exact hsne) (by rw [Nat.add_zero]; exact hdne)
  rw [h]
  unfold specMoveEtherOut specZeroTransferOut
  rw [acctSubBalance_zero, acctAddBalance_zero]

/-- **`moveEther src dst 0`, destination collapsing.** The reachable
shape of a zero-balance `SELFDESTRUCT` to a dead beneficiary: SpecRef
writes the empty tuple and EIP-161 immediately deletes it. -/
theorem runTx_moveEther_zero_collapse (ts : TransactionState)
    (src dst : Address)
    (rs rd : Option EvmAsm.Stateless.SpecRef.Account)
    (hsrc : specAcctRow ts src = some rs)
    (hdst : specAcctRow ts dst = some rd)
    (hne : dst ≠ src)
    (hsne : ((rs.getD EMPTY_ACCOUNT).nonce == 0
      && (rs.getD EMPTY_ACCOUNT).codeHash == EMPTY_CODE_HASH
      && (rs.getD EMPTY_ACCOUNT).balance == 0) = false)
    (hdemp : ((rd.getD EMPTY_ACCOUNT).nonce == 0
      && (rd.getD EMPTY_ACCOUNT).codeHash == EMPTY_CODE_HASH
      && (rd.getD EMPTY_ACCOUNT).balance == 0) = true)
    (hstore : dictGet? ts.storageWrites dst = none) :
    (moveEther src dst 0).run ts
      = .ok ((), specZeroTransferCollapseOut ts src dst
          (rs.getD EMPTY_ACCOUNT) (rd.getD EMPTY_ACCOUNT)) := by
  have hsrc1 : specAcctRow (specAccountReadOf ts src) src = some rs := hsrc
  have hdst1 : specAcctRow
      (specModifyStateOut (specAccountReadOf ts src) src
        (rs.getD EMPTY_ACCOUNT)) dst = some rd := by
    unfold specAcctRow
    rw [specModifyStateOut_accountWrites, dictGet?_dictSet_ne _ _ _ _ hne]
    exact hdst
  have hstore1 : dictGet?
      (specModifyStateOut (specAccountReadOf ts src) src
        (rs.getD EMPTY_ACCOUNT)).storageWrites dst = none := hstore
  unfold moveEther specZeroTransferCollapseOut
  refine runTx_bind_ok (runTx_getAccount_hit ts src rs hsrc) ?_
  rw [if_neg (by simp)]
  refine runTx_bind_ok (m := pure ()) rfl ?_
  refine runTx_bind_ok
    (show (modifyState src _).run (specAccountReadOf ts src)
        = .ok ((), specModifyStateOut (specAccountReadOf ts src) src
            (rs.getD EMPTY_ACCOUNT))
      from by
        rw [← acctSubBalance_zero (rs.getD EMPTY_ACCOUNT)]
        exact runTx_modifyState_nonEmpty (specAccountReadOf ts src) src _ rs
          hsrc1 (by rw [Nat.sub_zero]; exact hsne)) ?_
  rw [← acctAddBalance_zero (rd.getD EMPTY_ACCOUNT)]
  exact runTx_modifyState_collapse _ dst _ rd hdst1 hdemp hstore1

/-! ## The pairing -/

/-- What a transfer preserves: the account overlay and the log store. -/
def TransferPost (base : Nat) (sR' : Machine) (hs' : Evm.HostState) : Prop :=
  AccountRel sR'.txState hs' ∧ LogRel sR'.evm.logs hs' base

/-- **The value transfer agrees.** SpecRef's `move_ether` plus the
caller's guarded `emit_transfer_log`, against the extraction's
`k_transfer`: the same two balances move, and the same one EIP-7708
record is appended.

The hypotheses are the ledger, and each excludes a case rather than
hiding one: `hne` and `hv` exclude the two branches of `k_transfer`'s
early return (mismatch ledger MM-18), `hsne`/`hdne` exclude SpecRef's
EIP-161 collapse — which on `modifyState`'s collapse branch also destroys
storage — and `hsum` excludes the wrap where the extraction reduces
modulo `2^256` and SpecRef does not. -/
theorem transfer_equiv (srcV dstV : Evm.Defs.address) (v : U256)
    (sRef : Machine) (hs : Evm.HostState) (ss : SeqState) (base : Nat)
    (sv dv : Evm.Defs.AcctValue) (prof : ExecutionProfile)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hfork : AmsterdamProfile prof)
    (harel : AccountRel sRef.txState hs)
    (hlrel : LogRel sRef.evm.logs hs base)
    (hsrc : hostAcctRow hs srcV = some sv)
    (hdst : hostAcctRow hs dstV = some dv)
    (hne : dstV ≠ srcV) (hv : v ≠ 0)
    (hbal : v ≤ sv.curr.info.balance)
    (hsum : dv.curr.info.balance + v < 2 ^ 256)
    (hsne : Evm.Functions.account_info_empty (transferSrcInfo sv.curr.info v)
      = false)
    (hdne : Evm.Functions.account_info_empty (transferDstInfo dv.curr.info v)
      = false) :
    ∃ (sR' : Machine) (hs' : Evm.HostState),
      runR (specTransfer srcV.toList dstV.toList v) sRef = .ok (.ok (), sR')
      ∧ runS (Evm.Functions.k_transfer srcV dstV v) hs ss = .ok ((), hs') ss
      ∧ TransferPost base sR' hs'
      ∧ sR'.evm.logs
          = sRef.evm.logs ++ [specTransferLog srcV.toList dstV.toList v] := by
  -- The SpecRef rows, and the tuples they read back as.
  have hsrcR := harel.curr srcV sv hsrc
  have hdstR := harel.curr dstV dv hdst
  have hsview := accountRel_view_eq harel srcV sv hsrc
  have hdview := accountRel_view_eq harel dstV dv hdst
  have hlistne : dstV.toList ≠ srcV.toList :=
    fun hc => hne (Vector.toList_inj.mp hc)
  -- SpecRef's collapse tests, transported to the extraction's.
  have hsneR : (((hostAcctView sv.curr).getD EMPTY_ACCOUNT).nonce == 0
      && ((hostAcctView sv.curr).getD EMPTY_ACCOUNT).codeHash
            == EMPTY_CODE_HASH
      && ((hostAcctView sv.curr).getD EMPTY_ACCOUNT).balance - v == 0)
      = false := by
    rw [hsview]
    exact (specAcctEmpty_eq (transferSrcInfo sv.curr.info v)).trans hsne
  have hdneR : (((hostAcctView dv.curr).getD EMPTY_ACCOUNT).nonce == 0
      && ((hostAcctView dv.curr).getD EMPTY_ACCOUNT).codeHash
            == EMPTY_CODE_HASH
      && ((hostAcctView dv.curr).getD EMPTY_ACCOUNT).balance + v == 0)
      = false := by
    rw [hdview]
    exact (specAcctEmpty_eq (transferDstInfo dv.curr.info v)).trans hdne
  -- The two runs.
  obtain ⟨hs1, hs2, hw1, hw2, hrun⟩ := runS_k_transfer srcV dstV v sv dv hs ss
    prof hprof hfork hsrc hdst hne hv hbal hsum hsne hdne
  have hmove := runTx_moveEther sRef.txState srcV.toList dstV.toList v
    (hostAcctView sv.curr) (hostAcctView dv.curr) hsrcR hdstR hlistne
    (by rw [hsview]; exact hbal) hsneR hdneR
  -- The values the two writes install coincide.
  have hsval : acctSubBalance
      ((hostAcctView sv.curr).getD EMPTY_ACCOUNT) v
      = specAcctOfInfo (transferSrcInfo sv.curr.info v) := by
    rw [hsview]
    rfl
  have hdval : acctAddBalance
      ((hostAcctView dv.curr).getD EMPTY_ACCOUNT) v
      = specAcctOfInfo (transferDstInfo dv.curr.info v) := by
    rw [hdview]
    rfl
  have hspec : runR (specTransfer srcV.toList dstV.toList v) sRef
      = .ok (.ok (), specTransferOut sRef
          (specMoveEtherOut sRef.txState srcV.toList dstV.toList
            (acctSubBalance ((hostAcctView sv.curr).getD EMPTY_ACCOUNT) v)
            (acctAddBalance ((hostAcctView dv.curr).getD EMPTY_ACCOUNT) v))
          (specTransferLog srcV.toList dstV.toList v)) := by
    unfold specTransfer
    refine runR_bind_ok (runR_liftTx_ok _ _ () _ hmove) ?_
    rw [if_pos (show (dstV.toList != srcV.toList) = true from
      bne_iff_ne.mpr hlistne)]
    exact runR_emit_transfer_log _ _ v _ hv
  refine ⟨_, _, hspec, hrun, ⟨?_, ?_⟩, ?_⟩
  · -- the account overlay
    have hwfs : WordWf (transferSrcInfo sv.curr.info v).balance := by
      have hw : sv.curr.info.balance < 2 ^ 256 := harel.wf srcV sv hsrc
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hw
    have hwfd : WordWf (transferDstInfo dv.curr.info v).balance :=
      show dv.curr.info.balance + v < 2 ^ 256 from hsum
    have h0 : AccountRel
        (specAccountReadOf sRef.txState srcV.toList) hs :=
      accountRel_frame
        (show (specAccountReadOf sRef.txState srcV.toList).accountWrites
          = sRef.txState.accountWrites from rfl) harel
    have h1 := accountRel_modifyState h0 srcV sv
      (transferSrcInfo sv.curr.info v) hsne hwfs hw1
    have h2 := accountRel_modifyState h1 dstV dv
      (transferDstInfo dv.curr.info v) hdne hwfd hw2
    have h3 : AccountRel
        (specMoveEtherOut sRef.txState srcV.toList dstV.toList
          (acctSubBalance ((hostAcctView sv.curr).getD EMPTY_ACCOUNT) v)
          (acctAddBalance ((hostAcctView dv.curr).getD EMPTY_ACCOUNT) v))
        hs2 := by
      unfold specMoveEtherOut
      rw [hsval, hdval]
      exact h2
    exact accountRel_hostFrame (logAppend_accountTx hs2 _ _ _) h3
  · -- the log store
    have hf1 := hostAcctWritten_frame hw1
    have hf2 := hostAcctWritten_frame hw2
    have hbase : LogRel sRef.evm.logs hs2 base :=
      logRel_frame _ base (hf2.2.2.2.2.1.trans hf1.2.2.2.2.1)
        (hf2.2.2.2.2.2.1.trans hf1.2.2.2.2.2.1) hlrel
    have hfinal : LogRel
        (sRef.evm.logs ++ [specTransferLog srcV.toList dstV.toList v])
        (logAppend hs2 Evm.Functions.EIP7708_SYSTEM_ADDRESS
          (topicWords (transferTopics srcV dstV)) (toBeBytes32 v)) base := by
      rw [← logOf_transfer srcV dstV v]
      exact logRel_append _ hs2 base _ _ _ hbase
    exact hfinal
  · rfl

/-! ## The degenerate pairings

The two branches `transfer_equiv` excludes, now discharged. Both emit no
log on either side: the extraction's guard is inside
`k_emit_transfer_log`, and SpecRef's is split between the caller
(`dst != src`) and `emit_transfer_log`'s own `transfer_amount == 0` early
return — so a zero-value transfer takes the caller's branch and then
returns immediately anyway.

Each concludes that the transaction state's **rows** are unchanged, which
is what `accountRel_rowsFrame` needs. That is the precise content of
mismatch ledger MM-18's "harmless": SpecRef writes where the extraction
does not, and every row it writes holds the value that was already
there. -/

/-- **The self-transfer agrees.** SpecRef debits and credits the same
row; the extraction returns immediately. -/
theorem transfer_equiv_self (aV : Evm.Defs.address) (v : U256)
    (sRef : Machine) (hs : Evm.HostState) (ss : SeqState) (base : Nat)
    (av : Evm.Defs.AcctValue)
    (harel : AccountRel sRef.txState hs)
    (hlrel : LogRel sRef.evm.logs hs base)
    (hrow : hostAcctRow hs aV = some av)
    (hv : v ≠ 0)
    (hbal : v ≤ av.curr.info.balance)
    (hsne : Evm.Functions.account_info_empty (transferSrcInfo av.curr.info v)
      = false) :
    ∃ sR' : Machine,
      runR (specTransfer aV.toList aV.toList v) sRef = .ok (.ok (), sR')
      ∧ runS (Evm.Functions.k_transfer aV aV v) hs ss = .ok ((), hs) ss
      ∧ TransferPost base sR' hs
      ∧ sR'.evm.logs = sRef.evm.logs := by
  have hrowR := harel.curr aV av hrow
  have hview := accountRel_view_eq harel aV av hrow
  have hsneR : (((hostAcctView av.curr).getD EMPTY_ACCOUNT).nonce == 0
      && ((hostAcctView av.curr).getD EMPTY_ACCOUNT).codeHash
            == EMPTY_CODE_HASH
      && ((hostAcctView av.curr).getD EMPTY_ACCOUNT).balance - v == 0)
      = false := by
    rw [hview]
    exact (specAcctEmpty_eq (transferSrcInfo av.curr.info v)).trans hsne
  -- A nonzero balance means the entry is really there, so restoring the
  -- balance restores the row.
  have hp : av.curr.present = true := by
    by_contra hc
    obtain ⟨hb, -, -⟩ := harel.absentEmpty aV av hrow (by simpa using hc)
    rw [hb] at hbal
    exact hv (Nat.le_zero.mp hbal)
  have hsome : hostAcctView av.curr
      = some ((hostAcctView av.curr).getD EMPTY_ACCOUNT) := by
    unfold hostAcctView
    rw [if_pos hp]
    rfl
  have hmove := runTx_moveEther_self sRef.txState aV.toList v
    (hostAcctView av.curr) hrowR (by rw [hview]; exact hbal) hv hsneR
  have hspec : runR (specTransfer aV.toList aV.toList v) sRef
      = .ok (.ok (), specTxOut sRef
          (specSelfTransferOut sRef.txState aV.toList
            (acctSubBalance ((hostAcctView av.curr).getD EMPTY_ACCOUNT) v)
            ((hostAcctView av.curr).getD EMPTY_ACCOUNT))) := by
    unfold specTransfer
    refine runR_bind_ok (runR_liftTx_ok _ _ () _ hmove) ?_
    rw [if_neg (by simp)]
    rfl
  refine ⟨_, hspec, runS_k_transfer_noop aV aV v av av hs ss hrow hrow
      (by simp), ⟨?_, hlrel⟩, rfl⟩
  refine accountRel_rowsFrame (fun b => ?_) harel
  show specAcctRow (specSelfTransferOut sRef.txState aV.toList _ _) b
    = specAcctRow sRef.txState b
  unfold specSelfTransferOut specAcctRow
  rw [specModifyStateOut_accountWrites, specModifyStateOut_accountWrites]
  by_cases hkey : b = aV.toList
  · rw [hkey, dictGet?_dictSet_self, ← hsome]
    exact hrowR.symm
  · rw [dictGet?_dictSet_ne _ _ _ _ hkey, dictGet?_dictSet_ne _ _ _ _ hkey]
    rfl

/-- **The zero-value transfer agrees, destination surviving.** Both of
SpecRef's writes store the value that was already there. -/
theorem transfer_equiv_zero (srcV dstV : Evm.Defs.address)
    (sRef : Machine) (hs : Evm.HostState) (ss : SeqState) (base : Nat)
    (sv dv : Evm.Defs.AcctValue)
    (harel : AccountRel sRef.txState hs)
    (hlrel : LogRel sRef.evm.logs hs base)
    (hsrc : hostAcctRow hs srcV = some sv)
    (hdst : hostAcctRow hs dstV = some dv)
    (hne : dstV ≠ srcV)
    (hsne : Evm.Functions.account_info_empty sv.curr.info = false)
    (hdne : Evm.Functions.account_info_empty dv.curr.info = false) :
    ∃ sR' : Machine,
      runR (specTransfer srcV.toList dstV.toList 0) sRef = .ok (.ok (), sR')
      ∧ runS (Evm.Functions.k_transfer srcV dstV 0) hs ss = .ok ((), hs) ss
      ∧ TransferPost base sR' hs
      ∧ sR'.evm.logs = sRef.evm.logs := by
  have hsrcR := harel.curr srcV sv hsrc
  have hdstR := harel.curr dstV dv hdst
  have hsview := accountRel_view_eq harel srcV sv hsrc
  have hdview := accountRel_view_eq harel dstV dv hdst
  have hlistne : dstV.toList ≠ srcV.toList :=
    fun hc => hne (Vector.toList_inj.mp hc)
  have hsneR : (((hostAcctView sv.curr).getD EMPTY_ACCOUNT).nonce == 0
      && ((hostAcctView sv.curr).getD EMPTY_ACCOUNT).codeHash
            == EMPTY_CODE_HASH
      && ((hostAcctView sv.curr).getD EMPTY_ACCOUNT).balance == 0) = false := by
    rw [hsview]
    exact (specAcctEmpty_eq sv.curr.info).trans hsne
  have hdneR : (((hostAcctView dv.curr).getD EMPTY_ACCOUNT).nonce == 0
      && ((hostAcctView dv.curr).getD EMPTY_ACCOUNT).codeHash
            == EMPTY_CODE_HASH
      && ((hostAcctView dv.curr).getD EMPTY_ACCOUNT).balance == 0) = false := by
    rw [hdview]
    exact (specAcctEmpty_eq dv.curr.info).trans hdne
  have hssome := specAcctRow_some_of_nonEmpty (hostAcctView sv.curr) hsneR
  have hdsome := specAcctRow_some_of_nonEmpty (hostAcctView dv.curr) hdneR
  have hmove := runTx_moveEther_zero sRef.txState srcV.toList dstV.toList
    (hostAcctView sv.curr) (hostAcctView dv.curr) hsrcR hdstR hlistne hsneR hdneR
  have hspec : runR (specTransfer srcV.toList dstV.toList 0) sRef
      = .ok (.ok (), specTxOut sRef
          (specZeroTransferOut sRef.txState srcV.toList dstV.toList
            ((hostAcctView sv.curr).getD EMPTY_ACCOUNT)
            ((hostAcctView dv.curr).getD EMPTY_ACCOUNT))) := by
    unfold specTransfer
    refine runR_bind_ok (runR_liftTx_ok _ _ () _ hmove) ?_
    rw [if_pos (show (dstV.toList != srcV.toList) = true from
      bne_iff_ne.mpr hlistne)]
    unfold emit_transfer_log
    rw [if_pos (by decide)]
    rfl
  refine ⟨_, hspec, runS_k_transfer_noop srcV dstV 0 sv dv hs ss hsrc hdst
      (by simp [Evm.Functions.word_is_zero,
        show Evm.Functions.WORD_ZERO = 0 from rfl]), ⟨?_, hlrel⟩, rfl⟩
  refine accountRel_rowsFrame (fun b => ?_) harel
  show specAcctRow (specZeroTransferOut sRef.txState srcV.toList dstV.toList _ _) b
    = specAcctRow sRef.txState b
  unfold specZeroTransferOut specAcctRow
  rw [specModifyStateOut_accountWrites, specModifyStateOut_accountWrites]
  by_cases hkd : b = dstV.toList
  · rw [hkd, dictGet?_dictSet_self, ← hdsome]
    exact hdstR.symm
  · rw [dictGet?_dictSet_ne _ _ _ _ hkd]
    by_cases hks : b = srcV.toList
    · rw [hks, dictGet?_dictSet_self, ← hssome]
      exact hsrcR.symm
    · rw [dictGet?_dictSet_ne _ _ _ _ hks]
      rfl

/-- **The zero-value transfer agrees, destination collapsing.** The
reachable shape of a zero-balance `SELFDESTRUCT` to a dead beneficiary:
SpecRef writes the empty tuple and EIP-161 deletes it again, landing back
on the `some none` entry the relation already had. -/
theorem transfer_equiv_zero_collapse (srcV dstV : Evm.Defs.address)
    (sRef : Machine) (hs : Evm.HostState) (ss : SeqState) (base : Nat)
    (sv dv : Evm.Defs.AcctValue)
    (harel : AccountRel sRef.txState hs)
    (hlrel : LogRel sRef.evm.logs hs base)
    (hsrc : hostAcctRow hs srcV = some sv)
    (hdst : hostAcctRow hs dstV = some dv)
    (hne : dstV ≠ srcV)
    (hsne : Evm.Functions.account_info_empty sv.curr.info = false)
    (hdemp : Evm.Functions.account_info_empty dv.curr.info = true)
    (hstore : dictGet? sRef.txState.storageWrites dstV.toList = none) :
    ∃ sR' : Machine,
      runR (specTransfer srcV.toList dstV.toList 0) sRef = .ok (.ok (), sR')
      ∧ runS (Evm.Functions.k_transfer srcV dstV 0) hs ss = .ok ((), hs) ss
      ∧ TransferPost base sR' hs
      ∧ sR'.evm.logs = sRef.evm.logs := by
  have hsrcR := harel.curr srcV sv hsrc
  have hdstR := harel.curr dstV dv hdst
  have hsview := accountRel_view_eq harel srcV sv hsrc
  have hdview := accountRel_view_eq harel dstV dv hdst
  have hlistne : dstV.toList ≠ srcV.toList :=
    fun hc => hne (Vector.toList_inj.mp hc)
  have hsneR : (((hostAcctView sv.curr).getD EMPTY_ACCOUNT).nonce == 0
      && ((hostAcctView sv.curr).getD EMPTY_ACCOUNT).codeHash
            == EMPTY_CODE_HASH
      && ((hostAcctView sv.curr).getD EMPTY_ACCOUNT).balance == 0) = false := by
    rw [hsview]
    exact (specAcctEmpty_eq sv.curr.info).trans hsne
  have hdempR : (((hostAcctView dv.curr).getD EMPTY_ACCOUNT).nonce == 0
      && ((hostAcctView dv.curr).getD EMPTY_ACCOUNT).codeHash
            == EMPTY_CODE_HASH
      && ((hostAcctView dv.curr).getD EMPTY_ACCOUNT).balance == 0) = true := by
    rw [hdview]
    exact (specAcctEmpty_eq dv.curr.info).trans hdemp
  -- The collapse fires exactly when the row is absent, so SpecRef's entry
  -- was `some none` to begin with.
  have hdabs : hostAcctView dv.curr = none := by
    have hp : dv.curr.present = false := by
      have h := (accountRel_empty_iff_absent harel dstV dv hdst).symm.trans hdemp
      cases hq : dv.curr.present with
      | false => rfl
      | true => rw [hq] at h; exact absurd h (by decide)
    unfold hostAcctView
    rw [if_neg (by rw [hp]; decide)]
  have hssome := specAcctRow_some_of_nonEmpty (hostAcctView sv.curr) hsneR
  have hmove := runTx_moveEther_zero_collapse sRef.txState srcV.toList
    dstV.toList (hostAcctView sv.curr) (hostAcctView dv.curr) hsrcR hdstR
    hlistne hsneR hdempR hstore
  have hspec : runR (specTransfer srcV.toList dstV.toList 0) sRef
      = .ok (.ok (), specTxOut sRef
          (specZeroTransferCollapseOut sRef.txState srcV.toList dstV.toList
            ((hostAcctView sv.curr).getD EMPTY_ACCOUNT)
            ((hostAcctView dv.curr).getD EMPTY_ACCOUNT))) := by
    unfold specTransfer
    refine runR_bind_ok (runR_liftTx_ok _ _ () _ hmove) ?_
    rw [if_pos (show (dstV.toList != srcV.toList) = true from
      bne_iff_ne.mpr hlistne)]
    unfold emit_transfer_log
    rw [if_pos (by decide)]
    rfl
  refine ⟨_, hspec, runS_k_transfer_noop srcV dstV 0 sv dv hs ss hsrc hdst
      (by simp [Evm.Functions.word_is_zero,
        show Evm.Functions.WORD_ZERO = 0 from rfl]), ⟨?_, hlrel⟩, rfl⟩
  refine accountRel_rowsFrame (fun b => ?_) harel
  show specAcctRow (specZeroTransferCollapseOut sRef.txState srcV.toList
      dstV.toList _ _) b = specAcctRow sRef.txState b
  unfold specZeroTransferCollapseOut specAcctRow
  rw [specModifyStateCollapseOut_accountWrites, specModifyStateOut_accountWrites]
  by_cases hkd : b = dstV.toList
  · rw [hkd, dictGet?_dictSet_self, ← hdabs]
    exact hdstR.symm
  · rw [dictGet?_dictSet_ne _ _ _ _ hkd, dictGet?_dictSet_ne _ _ _ _ hkd]
    by_cases hks : b = srcV.toList
    · rw [hks, dictGet?_dictSet_self, ← hssome]
      exact hsrcR.symm
    · rw [dictGet?_dictSet_ne _ _ _ _ hks]
      rfl

end EvmSpecsVerify
