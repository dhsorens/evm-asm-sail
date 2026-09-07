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

## What it does not settle

`k_transfer`'s early return also covers `value_is_zero`, where SpecRef
runs its two `modifyState`s regardless. That case is MM-18's second half
(see `docs/mismatches.md`) and the hypothesis `hv : v ≠ 0` excludes it,
as `hne : dstV ≠ srcV` excludes the self-transfer. Both exclusions are
recorded in the ledger rather than proven away, because on SpecRef's side
they run a `modifyState` whose collapse branch destroys storage — a
different slice.

The destination's balance is a second exclusion, and this one is
representational: the extraction reduces the sum modulo `2^256`
(`alu_add`), SpecRef adds two `Nat`s (`a.balance + amount`). They agree
exactly under `hsum`, the no-overflow invariant the total ether supply
guarantees and neither specification checks.
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

/-- Fused bind for the tracker monad: a success step then the
continuation. Supplying both halves as terms keeps the proof out of
`rw`'s syntactic matching, which the record literals `modifyState`
receives would otherwise defeat. -/
private theorem runTx_bind_ok {α β : Type} {m : TxM α} {k : α → TxM β}
    {ts ts' : TransactionState} {a : α}
    {r : Except SpecError (β × TransactionState)}
    (h1 : m.run ts = .ok (a, ts')) (h2 : (k a).run ts' = r) :
    (m >>= k).run ts = r := by
  rw [show (m >>= k).run ts
      = (m.run ts) >>= (fun p => (k p.1).run p.2) from rfl, h1]
  exact h2

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

end EvmSpecsVerify
