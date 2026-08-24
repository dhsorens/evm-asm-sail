import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Relations.WarmAddr
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# EXTCODEHASH

The address-warmth sibling of [SLOAD](Sload.lean). Both sides pop the
target word, mask it to 20 bytes (`to_address_masked` ↔ `word_to_address`,
identified in `Representation/AddressWord.lean`), meter EIP-2929 warm/cold
account access, and push zero for a missing account or its code hash otherwise.

Warm/cold accounting runs through [`WarmAddrRel`](../Relations/WarmAddr.lean),
which folds in the extraction's precompiles-always-warm short-circuit
against SpecRef's transaction-start prewarming. The classifier's run shape
(`hpid`) is a hypothesis of the step theorem — it reads only the profile
register and is mechanically dischargeable; the relation itself is the
tx-level prewarm invariant. Gas constants agree at Amsterdam
(warm `100`, cold account `3000` — `WARM_ACCESS`/`G_warm_access`,
`COLD_ACCOUNT_ACCESS`/`G_amsterdam_cold_account_access`), narrowing MM-2
further.

The **code-hash read** is behind the ledgered `ExtcodehashAgree` hypothesis
(SpecRef's journalled `getAccount` = the kernel's `k_get_codehash`, which
misses through caches into the witness trie), quantified over the ambient
address stamps since the extraction marks warm before reading — exactly
the `SloadAgree` pattern; the world tranche discharges both.

Both sides pop before charging: no MM-5. Reachable outcomes: success
(warm/cold) / stack underflow / OOG (warm/cold); overflow unreachable for
1-in/1-out.
-/

open private pcNext from EvmAsm.Stateless.SpecRef.InstructionsEnv
open private writeListAt assocGet assocPut from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## The ledgered read-agreement hypothesis -/

/-- SpecRef's EIP-1052 result word for an account lookup. -/
def extcodehashWord (acct : EvmAsm.Stateless.SpecRef.Account) : Nat :=
  if acct == EMPTY_ACCOUNT then 0 else bytesBEtoNat acct.codeHash

/-- **Ledgered hypothesis** (see `Assumptions.lean`): the two sides' account
reads agree for the masked target of the popped word `x`. SpecRef's
`getAccount` walks the journalled tracker; the extraction's
`k_get_codehash` misses through its caches into the keccak-hashed witness
trie. Discharged by the world tranche's account relation. -/
def ExtcodehashAgree (sRef : Machine) (hs : Evm.HostState) (ss : SeqState)
    (x : Nat) : Prop :=
  ∃ (acct : EvmAsm.Stateless.SpecRef.Account) (ts' : TransactionState)
    (hash : Vector (BitVec 8) 32)
    (hostAfter : List (Evm.Defs.address × Nat) → Evm.HostState),
    WordWf (extcodehashWord acct) ∧
    (getAccount (to_address_masked x)).run sRef.txState = .ok (acct, ts') ∧
    (∀ ws, runS (Evm.Functions.k_get_codehash
        (Evm.Functions.word_to_address x))
      { hs with warmAddresses := ws } ss = .ok (hash, hostAfter ws) ss) ∧
    Evm.Functions.hash_to_word hash = extcodehashWord acct ∧
    (∀ ws, (hostAfter ws).stackFrames = hs.stackFrames) ∧
    (∀ ws, (hostAfter ws).warmAddresses = ws) ∧
    (∀ ws, (hostAfter ws).warmEpoch = hs.warmEpoch)

/-- Record-update projections (whnf-safe `rfl` mini-lemmas). -/
private theorem hostState_frames_warmAddresses (h : Evm.HostState)
    (f : List (List word)) :
    ({ h with stackFrames := f } : Evm.HostState).warmAddresses
      = h.warmAddresses := rfl

private theorem hostState_frames_warmEpoch' (h : Evm.HostState)
    (f : List (List word)) :
    ({ h with stackFrames := f } : Evm.HostState).warmEpoch = h.warmEpoch :=
  rfl

private theorem hostState_frames_frames' (h : Evm.HostState)
    (f : List (List word)) :
    ({ h with stackFrames := f } : Evm.HostState).stackFrames = f := rfl

/-! ## SpecRef run shapes -/

theorem runR_extcodehash_accessGasCost_warm (s : Machine) (a : Address)
    (hwarm : s.evm.accessedAddresses.contains a = true) :
    runR (accessGasCost a) s = .ok (.ok GasCosts.WARM_ACCESS, s) := by
  simp only [accessGasCost]
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_pos hwarm]
  exact runR_pure _ _

theorem runR_extcodehash_accessGasCost_cold (s : Machine) (a : Address)
    (hcold : s.evm.accessedAddresses.contains a = false) :
    runR (accessGasCost a) s =
      .ok (.ok GasCosts.COLD_ACCOUNT_ACCESS,
        { s with evm := { s.evm with
            accessedAddresses := setAdd s.evm.accessedAddresses a } }) := by
  simp only [accessGasCost]
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_neg (by simpa using hcold)]
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  exact runR_pure _ _

theorem runR_iExtcodehash_underflow (s : Machine) (hstack : s.evm.stack = []) :
    runR iExtcodehash s = .ok (.error .stackUnderflow, s) := by
  simp only [iExtcodehash]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_iExtcodehash_warm_success (s : Machine) (x : U256)
    (rest : List U256) (acct : EvmAsm.Stateless.SpecRef.Account)
    (ts' : TransactionState)
    (hstack : s.evm.stack = x :: rest)
    (hwarm : s.evm.accessedAddresses.contains (to_address_masked x) = true)
    (hgas : GasCosts.WARM_ACCESS ≤ s.evm.gasLeft)
    (hread : (getAccount (to_address_masked x)).run s.txState
      = .ok (acct, ts'))
    (hlim : s.evm.stack.length ≤ 1024) :
    runR iExtcodehash s =
      .ok (.ok (), { s with
        evm := { s.evm with
          stack := extcodehashWord acct :: rest
          gasLeft := s.evm.gasLeft - GasCosts.WARM_ACCESS
          regularGasUsed := s.evm.regularGasUsed + GasCosts.WARM_ACCESS
          pc := s.evm.pc + 1 }
        txState := ts' }) := by
  have hlen : rest.length ≠ 1024 := by
    rw [hstack] at hlim; simp at hlim; omega
  simp only [iExtcodehash, extcodehashWord, pcNext]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_extcodehash_accessGasCost_warm _ _ hwarm) ?_
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_liftTx_ok _ _ acct ts' hread) ?_
  refine runR_bind_ok (runR_stackPush _ _ (by simpa using hlen)) ?_
  exact runR_modifyEvm _ _

theorem runR_iExtcodehash_cold_success (s : Machine) (x : U256)
    (rest : List U256) (acct : EvmAsm.Stateless.SpecRef.Account)
    (ts' : TransactionState)
    (hstack : s.evm.stack = x :: rest)
    (hcold : s.evm.accessedAddresses.contains (to_address_masked x) = false)
    (hgas : GasCosts.COLD_ACCOUNT_ACCESS ≤ s.evm.gasLeft)
    (hread : (getAccount (to_address_masked x)).run s.txState
      = .ok (acct, ts'))
    (hlim : s.evm.stack.length ≤ 1024) :
    runR iExtcodehash s =
      .ok (.ok (), { s with
        evm := { s.evm with
          stack := extcodehashWord acct :: rest
          gasLeft := s.evm.gasLeft - GasCosts.COLD_ACCOUNT_ACCESS
          regularGasUsed :=
            s.evm.regularGasUsed + GasCosts.COLD_ACCOUNT_ACCESS
          pc := s.evm.pc + 1
          accessedAddresses := setAdd s.evm.accessedAddresses
            (to_address_masked x) }
        txState := ts' }) := by
  have hlen : rest.length ≠ 1024 := by
    rw [hstack] at hlim; simp at hlim; omega
  simp only [iExtcodehash, extcodehashWord, pcNext]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_extcodehash_accessGasCost_cold _ _ hcold) ?_
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_liftTx_ok _ _ acct ts' hread) ?_
  refine runR_bind_ok (runR_stackPush _ _ (by simpa using hlen)) ?_
  exact runR_modifyEvm _ _

theorem runR_iExtcodehash_warm_oog (s : Machine) (x : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: rest)
    (hwarm : s.evm.accessedAddresses.contains (to_address_masked x) = true)
    (hgas : s.evm.gasLeft < GasCosts.WARM_ACCESS) :
    runR iExtcodehash s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [iExtcodehash]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_extcodehash_accessGasCost_warm _ _ hwarm) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _ hgas)

theorem runR_iExtcodehash_cold_oog (s : Machine) (x : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: rest)
    (hcold : s.evm.accessedAddresses.contains (to_address_masked x) = false)
    (hgas : s.evm.gasLeft < GasCosts.COLD_ACCOUNT_ACCESS) :
    runR iExtcodehash s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with
            stack := rest
            accessedAddresses := setAdd s.evm.accessedAddresses
              (to_address_masked x) } }) := by
  simp only [iExtcodehash]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_extcodehash_accessGasCost_cold _ _ hcold) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _ hgas)

/-! ## `Evm` run shapes -/

/-- The warm-address table after `k_account_mark_warm`: precompiles are
never stamped. (Named so structure-update literals stay single-line.) -/
def extcodehashWsAfterMark (pid : Evm.Defs.address → PrecompileId)
    (aV : Evm.Defs.address) (hs : Evm.HostState) :
    List (Evm.Defs.address × Nat) :=
  if (pid aV != PrecompileId.NotPrecompile) then hs.warmAddresses
  else assocPut hs.warmAddresses aV hs.warmEpoch

open Evm.Functions in
/-- `k_account_is_warm`: precompiles short-circuit warm, otherwise the
epoch stamp decides. -/
theorem runS_extcodehash_k_account_is_warm (pid : Evm.Defs.address → PrecompileId)
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
theorem runS_extcodehash_k_account_mark_warm (pid : Evm.Defs.address → PrecompileId)
    (aV : Evm.Defs.address) (hs : Evm.HostState) (ss : SeqState)
    (hpid : runS (Evm.Functions.precompile_id_for_address aV) hs ss
      = .ok (pid aV, hs) ss) :
    runS (Evm.Functions.k_account_mark_warm aV) hs ss =
      .ok ((), { hs with warmAddresses := extcodehashWsAfterMark pid aV hs }) ss := by
  simp only [Evm.Functions.k_account_mark_warm, runS_bind, hpid, extcodehashWsAfterMark]
  by_cases hp : (pid aV != PrecompileId.NotPrecompile) = true
  · rw [if_pos hp, if_pos hp]
    exact runS_pure _ _ _
  · rw [if_neg hp, if_neg hp]
    simp only [Evm.Functions.account_mark_warm, runS_modify]

open Evm.Functions in
/-- The Amsterdam account-access charge, warm or cold. -/
theorem runS_extcodehash_account_cost (warmb : Bool) (hs : Evm.HostState)
    (ss : SeqState) (prof : ExecutionProfile)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hfork : Amsterdam ≤ prof.1) :
    runS (Evm.Functions.account_cost warmb) hs ss =
      .ok ((if warmb then G_warm_access
        else G_amsterdam_cold_account_access : Nat), hs) ss := by
  obtain ⟨fork, t, mx, dn, cl, il, ptl, prl, tbl, rd, bl, ttl, trl, epf⟩ := prof
  simp only at hfork
  simp only [Evm.Functions.account_cost, runS_bind, runS_readReg _ _ _ _ hprof]
  cases warmb
  · simp only [Bool.false_eq_true, if_false]
    simp only [ProtocolProfileFields.fork, decide_eq_true_eq]
    rw [if_pos (by simpa using hfork)]
    exact runS_pure _ _ _
  · simp only [if_true]
    exact runS_pure _ _ _

open Evm.Functions in
/-- The dispatch equation for EXTCODEHASH. -/
theorem extcodehash_dispatch (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_opcode (.EXTCODEHASH ()) pc_in top mem g =
      Evm.Functions.execute_extcodehash top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
theorem runS_extcodehash_body_ok (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (prof : ExecutionProfile)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hfork : Amsterdam ≤ prof.1)
    (pid : Evm.Defs.address → PrecompileId)
    (hpid : runS (Evm.Functions.precompile_id_for_address
        (Evm.Functions.word_to_address x)) hs ss
      = .ok (pid (Evm.Functions.word_to_address x), hs) ss)
    (warmb : Bool)
    (hwarmb : (if (pid (Evm.Functions.word_to_address x)
          != PrecompileId.NotPrecompile) then true
        else decide (hs.warmEpoch ≤ (assocGet hs.warmAddresses
          (Evm.Functions.word_to_address x)).getD 0)) = warmb)
    (hgas : (if warmb then G_warm_access
      else G_amsterdam_cold_account_access : Nat) ≤ g)
    (hash : Vector (BitVec 8) 32) (v : word)
    (hostAfter : List (Evm.Defs.address × Nat) → Evm.HostState)
    (hrun : ∀ ws, runS (k_get_codehash (Evm.Functions.word_to_address x))
      { hs with warmAddresses := ws } ss = .ok (hash, hostAfter ws) ss)
    (hword : hash_to_word hash = v)
    (hframes : ∀ ws, (hostAfter ws).stackFrames = hs.stackFrames) :
    runS (Evm.Functions.execute_extcodehash top g) hs ss =
      .ok ((top, g - (if warmb then G_warm_access
          else G_amsterdam_cold_account_access : Nat)),
        { hostAfter (extcodehashWsAfterMark pid (Evm.Functions.word_to_address x) hs)
          with stackFrames := writeListAt l (top.toNat - 1) v :: frest })
        ss := by
  have hn : top.toNat = rest.length + 1 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  simp only [Evm.Functions.execute_extcodehash]
  refine runS_bind_ok (runS_pop top hs ss l frest x rest hframe hpfx htop) ?_
  refine runS_bind_ok
    (by rw [runS_extcodehash_k_account_is_warm pid _ hs ss hpid, hwarmb]) ?_
  refine runS_bind_ok (runS_extcodehash_account_cost warmb hs ss prof hprof hfork) ?_
  refine runS_bind_ok (runS_charge_ok g _ hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_extcodehash_k_account_mark_warm pid _ hs ss hpid) ?_
  refine runS_bind_ok (hrun _) ?_
  rw [hword]
  refine runS_bind_ok
    (runS_push_word (top - BitVec.ofNat 64 1) v _ ss l frest
      (by rw [hframes]; exact hframe) (by rw [hret1]; omega)) ?_
  rw [BitVec.sub_add_cancel, hret1]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_extcodehash_body_oog (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (pid : Evm.Defs.address → PrecompileId)
    (hpid : runS (Evm.Functions.precompile_id_for_address
        (Evm.Functions.word_to_address x)) hs ss
      = .ok (pid (Evm.Functions.word_to_address x), hs) ss)
    (warmb : Bool)
    (hwarmb : (if (pid (Evm.Functions.word_to_address x)
          != PrecompileId.NotPrecompile) then true
        else decide (hs.warmEpoch ≤ (assocGet hs.warmAddresses
          (Evm.Functions.word_to_address x)).getD 0)) = warmb)
    (hgas : g < (if warmb then G_warm_access
      else G_amsterdam_cold_account_access : Nat)) :
    runS (Evm.Functions.execute_extcodehash top g) hs ss =
      .ok ((top - BitVec.ofNat 64 1, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_extcodehash]
  refine runS_bind_ok (runS_pop top hs ss l frest x rest hframe hpfx htop) ?_
  refine runS_bind_ok
    (by rw [runS_extcodehash_k_account_is_warm pid _ hs ss hpid, hwarmb]) ?_
  refine runS_bind_ok (runS_extcodehash_account_cost warmb hs ss prof hprof hfork) ?_
  refine runS_bind_ok
    (runS_charge_oog g _ hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_extcodehash_ok (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hfork : Amsterdam ≤ prof.1)
    (pid : Evm.Defs.address → PrecompileId)
    (hpid : runS (Evm.Functions.precompile_id_for_address
        (Evm.Functions.word_to_address x)) hs ss
      = .ok (pid (Evm.Functions.word_to_address x), hs) ss)
    (warmb : Bool)
    (hwarmb : (if (pid (Evm.Functions.word_to_address x)
          != PrecompileId.NotPrecompile) then true
        else decide (hs.warmEpoch ≤ (assocGet hs.warmAddresses
          (Evm.Functions.word_to_address x)).getD 0)) = warmb)
    (hgas : (if warmb then G_warm_access
      else G_amsterdam_cold_account_access : Nat) ≤ g)
    (hash : Vector (BitVec 8) 32) (v : word)
    (hostAfter : List (Evm.Defs.address × Nat) → Evm.HostState)
    (hrun : ∀ ws, runS (k_get_codehash (Evm.Functions.word_to_address x))
      { hs with warmAddresses := ws } ss = .ok (hash, hostAfter ws) ss)
    (hword : hash_to_word hash = v)
    (hframes : ∀ ws, (hostAfter ws).stackFrames = hs.stackFrames) :
    runS (Evm.Functions.execute (.EXTCODEHASH ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, g - (if warmb then G_warm_access
          else G_amsterdam_cold_account_access : Nat)),
        { hostAfter (extcodehashWsAfterMark pid (Evm.Functions.word_to_address x) hs)
          with stackFrames := writeListAt l (top.toNat - 1) v :: frest })
        ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.EXTCODEHASH ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 1 hs ss (by simp at htop; omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, extcodehash_dispatch]
  refine runS_bind_ok
    (runS_extcodehash_body_ok top g hs ss l frest x rest hframe hpfx htop prof
      hprof hfork pid hpid warmb hwarmb hgas hash v hostAfter hrun hword
      hframes) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_extcodehash_oog (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (pid : Evm.Defs.address → PrecompileId)
    (hpid : runS (Evm.Functions.precompile_id_for_address
        (Evm.Functions.word_to_address x)) hs ss
      = .ok (pid (Evm.Functions.word_to_address x), hs) ss)
    (warmb : Bool)
    (hwarmb : (if (pid (Evm.Functions.word_to_address x)
          != PrecompileId.NotPrecompile) then true
        else decide (hs.warmEpoch ≤ (assocGet hs.warmAddresses
          (Evm.Functions.word_to_address x)).getD 0)) = warmb)
    (hgas : g < (if warmb then G_warm_access
      else G_amsterdam_cold_account_access : Nat)) :
    runS (Evm.Functions.execute (.EXTCODEHASH ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.EXTCODEHASH ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 1 hs ss (by simp at htop; omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, extcodehash_dispatch]
  refine runS_bind_ok
    (runS_extcodehash_body_oog top g hs ss l frest x rest hframe hpfx htop prof
      sp msg hprof hsp hmsg hfork pid hpid warmb hwarmb hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_extcodehash_underflow (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 1) :
    runS (Evm.Functions.execute (.EXTCODEHASH ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.EXTCODEHASH ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 1 1 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

/-! ## The step equivalence -/

/-- Success post-relation for EXTCODEHASH: the ALU-slice relation plus the
warm address relation on the post-states. -/
def ExtcodehashPost (pid : Evm.Defs.address → PrecompileId)
    (mem : EvmMemorySlice) (sR' : Machine) (step : EvmStep)
    (hs' : Evm.HostState) (ss' : SeqState) : Prop :=
  BasePost mem sR' step hs' ss' ∧ WarmAddrRel pid sR' hs'

open Evm.Functions in
/-- **EXTCODEHASH, all reachable outcomes.** Warm/cold accounting and gas are
proven against `WarmAddrRel` (prewarm invariant + classifier shape as
hypotheses); the extcodehash read is supplied by the ledgered `ExtcodehashAgree`
hypothesis. -/
theorem extcodehash_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat) (pid : Evm.Defs.address → PrecompileId)
    (hrel : StateRel sRef top g hs ss)
    (hwrel : WarmAddrRel pid sRef hs)
    (hpc : pc_in = sRef.evm.pc + 1)
    (hpid : ∀ aV, runS (Evm.Functions.precompile_id_for_address aV) hs ss
      = .ok (pid aV, hs) ss)
    (hagree : ∀ (x : U256) (rest : List U256),
      sRef.evm.stack = x :: rest → ExtcodehashAgree sRef hs ss x) :
    StepResultRel (ExtcodehashPost pid mem) (runR iExtcodehash sRef)
      (runS (Evm.Functions.execute (.EXTCODEHASH ()) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_iExtcodehash_underflow sRef hS,
      runS_execute_extcodehash_underflow pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | x :: rest =>
    rw [hS] at hpfx htop hlim hwfS
    obtain ⟨acct, ts', hash, hostAfter, hwfb, hspec, hrun, hword, hframes,
      hslots, hepoch⟩ := hagree x rest hS
    have hiff := hwrel (Evm.Functions.word_to_address x)
    rw [word_to_address_toList] at hiff
    have hlim' : top.toNat ≤ 1024 := by simp at htop hlim; omega
    set aV := Evm.Functions.word_to_address x with haVdef
    cases hwc : sRef.evm.accessedAddresses.contains (to_address_masked x) with
    | true =>
      have heff := hiff.mp hwc
      have hwb : (if (pid aV != PrecompileId.NotPrecompile) then true
          else decide (hs.warmEpoch
            ≤ (assocGet hs.warmAddresses aV).getD 0)) = true := by
        by_cases hp : (pid aV != PrecompileId.NotPrecompile) = true
        · rw [if_pos hp]
        · rw [if_neg hp]
          rcases heff with hpre | hle
          · exact absurd (bne_iff_ne.mpr hpre) hp
          · exact decide_eq_true hle
      by_cases hg : sRef.evm.gasLeft < GasCosts.WARM_ACCESS
      · rw [runR_iExtcodehash_warm_oog sRef x rest hS hwc hg,
          runS_execute_extcodehash_oog pc_in top g mem hs ss l frest x rest
            hframe hpfx htop hlim' prof sRef.evm.stateGasSpilled msg hprof
            hsp hmsg hfork pid (hpid aV) true hwb
            (by rw [if_pos rfl, hlive]; exact hg)]
        exact StepResultRel.halted ErrorRel.outOfGas
          (haltRegs_frame_status ss msg .OutOfGas)
      · push Not at hg
        rw [runR_iExtcodehash_warm_success sRef x rest acct ts' hS hwc hg hspec
            (by rw [hS]; exact hlim),
          runS_execute_extcodehash_ok pc_in top g mem hs ss l frest x rest
            hframe hpfx htop hlim' prof hprof hfork pid (hpid aV) true hwb
            (by rw [if_pos rfl, hlive]; exact hg) hash
            (extcodehashWord acct) hostAfter hrun hword hframes]
        rw [if_pos rfl]
        refine StepResultRel.success ⟨⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
          ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, hpc, rfl⟩, ?_⟩
        · exact pop_push_post_stack top _ l frest x rest (extcodehashWord acct)
            (hostState_frames_frames' _ _) hpfx htop hlim hlen hwfS hwfb
        · exact ⟨by rw [hlive]; rfl, hres, hsp⟩
        · intro bV
          rw [hostState_frames_warmAddresses, hostState_frames_warmEpoch',
            hslots, hepoch]
          by_cases hp : (pid aV != PrecompileId.NotPrecompile) = true
          · rw [show extcodehashWsAfterMark pid aV hs = hs.warmAddresses from by
              unfold extcodehashWsAfterMark; rw [if_pos hp]]
            exact hwrel bV
          · rw [show extcodehashWsAfterMark pid aV hs
                = assocPut hs.warmAddresses aV hs.warmEpoch from by
              unfold extcodehashWsAfterMark; rw [if_neg hp]]
            have hmark := warmaddr_after_mark pid sRef.evm.accessedAddresses
              hs.warmAddresses hs.warmEpoch aV hwrel bV
            rw [word_to_address_toList, setAdd_eq_of_contains _ _ hwc]
              at hmark
            exact hmark
    | false =>
      have hnot : pid aV = PrecompileId.NotPrecompile ∧
          ¬ hs.warmEpoch ≤ (assocGet hs.warmAddresses aV).getD 0 := by
        by_cases hp : pid aV = PrecompileId.NotPrecompile
        · refine ⟨hp, fun hle => ?_⟩
          rw [hiff.mpr (Or.inr hle)] at hwc
          cases hwc
        · exfalso
          rw [hiff.mpr (Or.inl hp)] at hwc
          cases hwc
      have hwb : (if (pid aV != PrecompileId.NotPrecompile) then true
          else decide (hs.warmEpoch
            ≤ (assocGet hs.warmAddresses aV).getD 0)) = false := by
        rw [if_neg (by simp [hnot.1]), decide_eq_false hnot.2]
      by_cases hg : sRef.evm.gasLeft < GasCosts.COLD_ACCOUNT_ACCESS
      · rw [runR_iExtcodehash_cold_oog sRef x rest hS hwc hg,
          runS_execute_extcodehash_oog pc_in top g mem hs ss l frest x rest
            hframe hpfx htop hlim' prof sRef.evm.stateGasSpilled msg hprof
            hsp hmsg hfork pid (hpid aV) false hwb
            (by rw [if_neg (by simp), hlive]; exact hg)]
        exact StepResultRel.halted ErrorRel.outOfGas
          (haltRegs_frame_status ss msg .OutOfGas)
      · push Not at hg
        rw [runR_iExtcodehash_cold_success sRef x rest acct ts' hS hwc hg hspec
            (by rw [hS]; exact hlim),
          runS_execute_extcodehash_ok pc_in top g mem hs ss l frest x rest
            hframe hpfx htop hlim' prof hprof hfork pid (hpid aV) false hwb
            (by rw [if_neg (by simp), hlive]; exact hg) hash
            (extcodehashWord acct) hostAfter hrun hword hframes]
        rw [if_neg (by simp),
          show extcodehashWsAfterMark pid aV hs
            = assocPut hs.warmAddresses aV hs.warmEpoch from by
            unfold extcodehashWsAfterMark; rw [if_neg (by simp [hnot.1])]]
        refine StepResultRel.success ⟨⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
          ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, hpc, rfl⟩, ?_⟩
        · exact pop_push_post_stack top _ l frest x rest (extcodehashWord acct)
            (hostState_frames_frames' _ _) hpfx htop hlim hlen hwfS hwfb
        · exact ⟨by rw [hlive]; rfl, hres, hsp⟩
        · intro bV
          rw [hostState_frames_warmAddresses, hostState_frames_warmEpoch',
            hslots, hepoch]
          have hmark := warmaddr_after_mark pid sRef.evm.accessedAddresses
            hs.warmAddresses hs.warmEpoch aV hwrel bV
          rw [word_to_address_toList] at hmark
          exact hmark

end EvmSpecsVerify
