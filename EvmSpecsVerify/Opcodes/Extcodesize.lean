import EvmSpecsVerify.Opcodes.Balance

/-!
# EXTCODESIZE

The external-code analogue of BALANCE. Both sides pop and mask the target
address, meter warm/cold account access plus Amsterdam's second warm-access
charge for the code-store read, mark the account warm, and push the code
length.

Warmth uses `WarmAddrRel` and BALANCE's classifier/run-shape machinery. The
account/code-store lookup is behind the ledgered `ExtcodesizeAgree` hypothesis
until the world relation lands. Its length bound makes
`word_of_source_byte_count`'s assertion unreachable.

Both sides pop before charging. Reachable outcomes: success (warm/cold), stack
underflow, and OOG (warm/cold); overflow is unreachable for 1-in/1-out.
-/

open private pcNext from EvmAsm.Stateless.SpecRef.InstructionsEnv
open private writeListAt assocGet assocPut from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- Amsterdam's EXTCODESIZE charge: account access plus one warm access for
the code-store read (EIP-8038). -/
def extcodesizeCost (warm : Bool) : Nat :=
  (if warm then Evm.Functions.G_warm_access
    else Evm.Functions.G_amsterdam_cold_account_access)
    + Evm.Functions.G_warm_access

/-! ## Ledgered lookup agreement -/

/-- The two sides return the same external-code length for the masked target.
SpecRef walks its account and code journals; the extraction resolves the
account's code hash through its caches and witness-backed code database. -/
def ExtcodesizeAgree (sRef : Machine) (hs : Evm.HostState) (ss : SeqState)
    (x : Nat) : Prop :=
  ∃ (acct : EvmAsm.Stateless.SpecRef.Account) (code : Bytes)
    (ts1 ts2 : TransactionState)
    (hostAfter : List (Evm.Defs.address × Nat) → Evm.HostState),
    WordWf code.length ∧
    (getAccount (to_address_masked x)).run sRef.txState = .ok (acct, ts1) ∧
    (getCode acct.codeHash (to_address_masked x)).run ts1 = .ok (code, ts2) ∧
    (∀ ws, runS (Evm.Functions.k_get_code_size
        (Evm.Functions.word_to_address x))
      { hs with warmAddresses := ws } ss = .ok (code.length, hostAfter ws)
        ss) ∧
    (∀ ws, (hostAfter ws).stackFrames = hs.stackFrames) ∧
    (∀ ws, (hostAfter ws).warmAddresses = ws) ∧
    (∀ ws, (hostAfter ws).warmEpoch = hs.warmEpoch)

private theorem hostState_frames_warmAddresses (h : Evm.HostState)
    (f : List (List word)) :
    ({ h with stackFrames := f } : Evm.HostState).warmAddresses
      = h.warmAddresses := rfl

private theorem hostState_frames_warmEpoch (h : Evm.HostState)
    (f : List (List word)) :
    ({ h with stackFrames := f } : Evm.HostState).warmEpoch = h.warmEpoch :=
  rfl

private theorem hostState_frames_frames (h : Evm.HostState)
    (f : List (List word)) :
    ({ h with stackFrames := f } : Evm.HostState).stackFrames = f := rfl

/-! ## SpecRef run shapes -/

theorem runR_extCodeOf_ok (s : Machine) (a : Address)
    (acct : EvmAsm.Stateless.SpecRef.Account) (code : Bytes)
    (ts1 ts2 : TransactionState)
    (hacc : (getAccount a).run s.txState = .ok (acct, ts1))
    (hcode : (getCode acct.codeHash a).run ts1 = .ok (code, ts2)) :
    runR (extCodeOf a) s = .ok (.ok code, { s with txState := ts2 }) := by
  simp only [extCodeOf]
  refine runR_bind_ok (runR_liftTx_ok _ _ acct ts1 hacc) ?_
  exact runR_liftTx_ok _ _ code ts2 hcode

theorem runR_iExtcodesize_underflow (s : Machine)
    (hstack : s.evm.stack = []) :
    runR iExtcodesize s = .ok (.error .stackUnderflow, s) := by
  simp only [iExtcodesize]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_iExtcodesize_warm_success (s : Machine) (x : U256)
    (rest : List U256) (acct : EvmAsm.Stateless.SpecRef.Account)
    (code : Bytes) (ts1 ts2 : TransactionState)
    (hstack : s.evm.stack = x :: rest)
    (hwarm : s.evm.accessedAddresses.contains (to_address_masked x) = true)
    (hgas : GasCosts.WARM_ACCESS + GasCosts.WARM_ACCESS ≤ s.evm.gasLeft)
    (hacc : (getAccount (to_address_masked x)).run s.txState
      = .ok (acct, ts1))
    (hcode : (getCode acct.codeHash (to_address_masked x)).run ts1
      = .ok (code, ts2))
    (hlim : s.evm.stack.length ≤ 1024) :
    runR iExtcodesize s =
      .ok (.ok (), { s with
        evm := { s.evm with
          stack := code.length :: rest
          gasLeft := s.evm.gasLeft
            - (GasCosts.WARM_ACCESS + GasCosts.WARM_ACCESS)
          regularGasUsed := s.evm.regularGasUsed
            + (GasCosts.WARM_ACCESS + GasCosts.WARM_ACCESS)
          pc := s.evm.pc + 1 }
        txState := ts2 }) := by
  have hlen : rest.length ≠ 1024 := by
    rw [hstack] at hlim; simp at hlim; omega
  simp only [iExtcodesize, pcNext]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_accessGasCost_warm _ _ hwarm) ?_
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok
    (runR_extCodeOf_ok _ _ acct code ts1 ts2 hacc hcode) ?_
  refine runR_bind_ok (runR_stackPush _ _ (by simpa using hlen)) ?_
  exact runR_modifyEvm _ _

theorem runR_iExtcodesize_cold_success (s : Machine) (x : U256)
    (rest : List U256) (acct : EvmAsm.Stateless.SpecRef.Account)
    (code : Bytes) (ts1 ts2 : TransactionState)
    (hstack : s.evm.stack = x :: rest)
    (hcold : s.evm.accessedAddresses.contains (to_address_masked x) = false)
    (hgas : GasCosts.COLD_ACCOUNT_ACCESS + GasCosts.WARM_ACCESS
      ≤ s.evm.gasLeft)
    (hacc : (getAccount (to_address_masked x)).run s.txState
      = .ok (acct, ts1))
    (hcode : (getCode acct.codeHash (to_address_masked x)).run ts1
      = .ok (code, ts2))
    (hlim : s.evm.stack.length ≤ 1024) :
    runR iExtcodesize s =
      .ok (.ok (), { s with
        evm := { s.evm with
          stack := code.length :: rest
          gasLeft := s.evm.gasLeft
            - (GasCosts.COLD_ACCOUNT_ACCESS + GasCosts.WARM_ACCESS)
          regularGasUsed := s.evm.regularGasUsed
            + (GasCosts.COLD_ACCOUNT_ACCESS + GasCosts.WARM_ACCESS)
          pc := s.evm.pc + 1
          accessedAddresses := setAdd s.evm.accessedAddresses
            (to_address_masked x) }
        txState := ts2 }) := by
  have hlen : rest.length ≠ 1024 := by
    rw [hstack] at hlim; simp at hlim; omega
  simp only [iExtcodesize, pcNext]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_accessGasCost_cold _ _ hcold) ?_
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok
    (runR_extCodeOf_ok _ _ acct code ts1 ts2 hacc hcode) ?_
  refine runR_bind_ok (runR_stackPush _ _ (by simpa using hlen)) ?_
  exact runR_modifyEvm _ _

theorem runR_iExtcodesize_warm_oog (s : Machine) (x : U256)
    (rest : List U256) (hstack : s.evm.stack = x :: rest)
    (hwarm : s.evm.accessedAddresses.contains (to_address_masked x) = true)
    (hgas : s.evm.gasLeft
      < GasCosts.WARM_ACCESS + GasCosts.WARM_ACCESS) :
    runR iExtcodesize s =
      .ok (.error .outOfGas, { s with evm := { s.evm with stack := rest } }) := by
  simp only [iExtcodesize]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_accessGasCost_warm _ _ hwarm) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _ hgas)

theorem runR_iExtcodesize_cold_oog (s : Machine) (x : U256)
    (rest : List U256) (hstack : s.evm.stack = x :: rest)
    (hcold : s.evm.accessedAddresses.contains (to_address_masked x) = false)
    (hgas : s.evm.gasLeft
      < GasCosts.COLD_ACCOUNT_ACCESS + GasCosts.WARM_ACCESS) :
    runR iExtcodesize s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with
            stack := rest
            accessedAddresses := setAdd s.evm.accessedAddresses
              (to_address_masked x) } }) := by
  simp only [iExtcodesize]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_accessGasCost_cold _ _ hcold) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _ hgas)

/-! ## `Evm` run shapes -/

open Evm.Functions in
theorem runS_external_code_read_cost (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hfork : Amsterdam ≤ prof.1) :
    runS (Evm.Functions.external_code_read_cost ()) hs ss =
      .ok (G_warm_access, hs) ss := by
  obtain ⟨fork, t, mx, dn, cl, il, ptl, prl, tbl, rd, bl, ttl, trl, epf⟩ := prof
  simp only at hfork
  simp only [Evm.Functions.external_code_read_cost, runS_bind,
    runS_readReg _ _ _ _ hprof, ProtocolProfileFields.fork,
    decide_eq_true_eq]
  rw [if_pos (by simpa using hfork)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem extcodesize_dispatch (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_opcode (.EXTCODESIZE ()) pc_in top mem g =
      Evm.Functions.execute_extcodesize top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
theorem runS_extcodesize_body_ok (top : StackTop) (g : Nat)
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
    (hgas : extcodesizeCost warmb ≤ g)
    (codeLen : Nat) (hwf : WordWf codeLen)
    (hostAfter : List (Evm.Defs.address × Nat) → Evm.HostState)
    (hrun : ∀ ws, runS (k_get_code_size (Evm.Functions.word_to_address x))
      { hs with warmAddresses := ws } ss = .ok (codeLen, hostAfter ws) ss)
    (hframes : ∀ ws, (hostAfter ws).stackFrames = hs.stackFrames) :
    runS (Evm.Functions.execute_extcodesize top g) hs ss =
      .ok ((top, g - extcodesizeCost warmb),
        { hostAfter (wsAfterMark pid (Evm.Functions.word_to_address x) hs)
          with stackFrames := writeListAt l (top.toNat - 1) codeLen :: frest })
        ss := by
  have hn : top.toNat = rest.length + 1 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  simp only [Evm.Functions.execute_extcodesize]
  refine runS_bind_ok (runS_pop top hs ss l frest x rest hframe hpfx htop) ?_
  refine runS_bind_ok
    (by rw [runS_k_account_is_warm pid _ hs ss hpid, hwarmb]) ?_
  refine runS_bind_ok (runS_account_cost warmb hs ss prof hprof hfork) ?_
  refine runS_bind_ok (runS_external_code_read_cost hs ss prof hprof hfork) ?_
  refine runS_bind_ok (runS_charge_ok g _ hs ss (by
    unfold extcodesizeCost at hgas; exact hgas)) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_k_account_mark_warm pid _ hs ss hpid) ?_
  refine runS_bind_ok (hrun _) ?_
  refine runS_bind_ok (runS_word_of_source_byte_count codeLen _ _ hwf) ?_
  refine runS_bind_ok
    (runS_push_word (top - BitVec.ofNat 64 1) codeLen _ ss l frest
      (by rw [hframes]; exact hframe) (by rw [hret1]; omega)) ?_
  rw [BitVec.sub_add_cancel, hret1]
  unfold extcodesizeCost
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_extcodesize_body_oog (top : StackTop) (g : Nat)
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
    (hgas : g < extcodesizeCost warmb) :
    runS (Evm.Functions.execute_extcodesize top g) hs ss =
      .ok ((top - BitVec.ofNat 64 1, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_extcodesize]
  refine runS_bind_ok (runS_pop top hs ss l frest x rest hframe hpfx htop) ?_
  refine runS_bind_ok
    (by rw [runS_k_account_is_warm pid _ hs ss hpid, hwarmb]) ?_
  refine runS_bind_ok (runS_account_cost warmb hs ss prof hprof hfork) ?_
  refine runS_bind_ok (runS_external_code_read_cost hs ss prof hprof hfork) ?_
  refine runS_bind_ok
    (runS_charge_oog g _ hs ss prof sp msg hprof hsp hmsg hfork (by
      unfold extcodesizeCost at hgas; exact hgas)) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_extcodesize_ok (pc_in : Nat) (top : StackTop) (g : Nat)
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
    (hgas : extcodesizeCost warmb ≤ g)
    (codeLen : Nat) (hwf : WordWf codeLen)
    (hostAfter : List (Evm.Defs.address × Nat) → Evm.HostState)
    (hrun : ∀ ws, runS (k_get_code_size (Evm.Functions.word_to_address x))
      { hs with warmAddresses := ws } ss = .ok (codeLen, hostAfter ws) ss)
    (hframes : ∀ ws, (hostAfter ws).stackFrames = hs.stackFrames) :
    runS (Evm.Functions.execute (.EXTCODESIZE ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, g - extcodesizeCost warmb),
        { hostAfter (wsAfterMark pid (Evm.Functions.word_to_address x) hs)
          with stackFrames := writeListAt l (top.toNat - 1) codeLen :: frest })
        ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.EXTCODESIZE ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 1 hs ss (by simp at htop; omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, extcodesize_dispatch]
  refine runS_bind_ok
    (runS_extcodesize_body_ok top g hs ss l frest x rest hframe hpfx htop
      prof hprof hfork pid hpid warmb hwarmb hgas codeLen hwf hostAfter hrun
      hframes) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_extcodesize_oog (pc_in : Nat) (top : StackTop) (g : Nat)
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
    (hgas : g < extcodesizeCost warmb) :
    runS (Evm.Functions.execute (.EXTCODESIZE ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.EXTCODESIZE ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 1 hs ss (by simp at htop; omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, extcodesize_dispatch]
  refine runS_bind_ok
    (runS_extcodesize_body_oog top g hs ss l frest x rest hframe hpfx htop
      prof sp msg hprof hsp hmsg hfork pid hpid warmb hwarmb hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_extcodesize_underflow (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 1) :
    runS (Evm.Functions.execute (.EXTCODESIZE ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.EXTCODESIZE ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 1 1 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

/-! ## Step equivalence -/

/-- Success post-relation: base machine state plus address warmth. -/
def ExtcodesizePost (pid : Evm.Defs.address → PrecompileId)
    (mem : EvmMemorySlice) (sR' : Machine) (step : EvmStep)
    (hs' : Evm.HostState) (ss' : SeqState) : Prop :=
  BasePost mem sR' step hs' ss' ∧ WarmAddrRel pid sR' hs'

open Evm.Functions in
/-- **EXTCODESIZE, all reachable outcomes.** Warm/cold accounting and the
Amsterdam code-read surcharge are proven; the account/code lookup is supplied
by the ledgered `ExtcodesizeAgree` hypothesis. -/
theorem extcodesize_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat) (pid : Evm.Defs.address → PrecompileId)
    (hrel : StateRel sRef top g hs ss)
    (hwrel : WarmAddrRel pid sRef hs)
    (hpc : pc_in = sRef.evm.pc + 1)
    (hpid : ∀ aV, runS (Evm.Functions.precompile_id_for_address aV) hs ss
      = .ok (pid aV, hs) ss)
    (hagree : ∀ (x : U256) (rest : List U256),
      sRef.evm.stack = x :: rest → ExtcodesizeAgree sRef hs ss x) :
    StepResultRel (ExtcodesizePost pid mem) (runR iExtcodesize sRef)
      (runS (Evm.Functions.execute (.EXTCODESIZE ()) pc_in top mem g)
        hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_iExtcodesize_underflow sRef hS,
      runS_execute_extcodesize_underflow pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | x :: rest =>
    rw [hS] at hpfx htop hlim hwfS
    obtain ⟨acct, code, ts1, ts2, hostAfter, hwflen, hacc, hcode, hkcode,
      hframes, hslots, hepoch⟩ := hagree x rest hS
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
      by_cases hg : sRef.evm.gasLeft
          < GasCosts.WARM_ACCESS + GasCosts.WARM_ACCESS
      · rw [runR_iExtcodesize_warm_oog sRef x rest hS hwc hg,
          runS_execute_extcodesize_oog pc_in top g mem hs ss l frest x rest
            hframe hpfx htop hlim' prof sRef.evm.stateGasSpilled msg hprof
            hsp hmsg hfork pid (hpid aV) true hwb
            (by unfold extcodesizeCost; rw [if_pos rfl, hlive]; exact hg)]
        exact StepResultRel.halted ErrorRel.outOfGas
          (haltRegs_frame_status ss msg .OutOfGas)
      · push Not at hg
        rw [runR_iExtcodesize_warm_success sRef x rest acct code ts1 ts2 hS
            hwc hg hacc hcode (by rw [hS]; exact hlim),
          runS_execute_extcodesize_ok pc_in top g mem hs ss l frest x rest
            hframe hpfx htop hlim' prof hprof hfork pid (hpid aV) true hwb
            (by unfold extcodesizeCost; rw [if_pos rfl, hlive]; exact hg)
            code.length hwflen hostAfter hkcode hframes]
        unfold extcodesizeCost
        rw [if_pos rfl]
        refine StepResultRel.success ⟨⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
          ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, hpc, rfl⟩, ?_⟩
        · exact pop_push_post_stack top _ l frest x rest code.length
            (hostState_frames_frames _ _) hpfx htop hlim hlen hwfS hwflen
        · exact ⟨by rw [hlive]; rfl, hres, hsp⟩
        · intro bV
          rw [hostState_frames_warmAddresses, hostState_frames_warmEpoch,
            hslots, hepoch]
          by_cases hp : (pid aV != PrecompileId.NotPrecompile) = true
          · rw [show wsAfterMark pid aV hs = hs.warmAddresses from by
              unfold wsAfterMark; rw [if_pos hp]]
            exact hwrel bV
          · rw [show wsAfterMark pid aV hs
                = assocPut hs.warmAddresses aV hs.warmEpoch from by
              unfold wsAfterMark; rw [if_neg hp]]
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
      by_cases hg : sRef.evm.gasLeft
          < GasCosts.COLD_ACCOUNT_ACCESS + GasCosts.WARM_ACCESS
      · rw [runR_iExtcodesize_cold_oog sRef x rest hS hwc hg,
          runS_execute_extcodesize_oog pc_in top g mem hs ss l frest x rest
            hframe hpfx htop hlim' prof sRef.evm.stateGasSpilled msg hprof
            hsp hmsg hfork pid (hpid aV) false hwb
            (by unfold extcodesizeCost; rw [if_neg (by simp), hlive]; exact hg)]
        exact StepResultRel.halted ErrorRel.outOfGas
          (haltRegs_frame_status ss msg .OutOfGas)
      · push Not at hg
        rw [runR_iExtcodesize_cold_success sRef x rest acct code ts1 ts2 hS
            hwc hg hacc hcode (by rw [hS]; exact hlim),
          runS_execute_extcodesize_ok pc_in top g mem hs ss l frest x rest
            hframe hpfx htop hlim' prof hprof hfork pid (hpid aV) false hwb
            (by unfold extcodesizeCost; rw [if_neg (by simp), hlive]; exact hg)
            code.length hwflen hostAfter hkcode hframes]
        unfold extcodesizeCost
        rw [if_neg (by simp),
          show wsAfterMark pid aV hs
            = assocPut hs.warmAddresses aV hs.warmEpoch from by
            unfold wsAfterMark; rw [if_neg (by simp [hnot.1])]]
        refine StepResultRel.success ⟨⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
          ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, hpc, rfl⟩, ?_⟩
        · exact pop_push_post_stack top _ l frest x rest code.length
            (hostState_frames_frames _ _) hpfx htop hlim hlen hwfS hwflen
        · exact ⟨by rw [hlive]; rfl, hres, hsp⟩
        · intro bV
          rw [hostState_frames_warmAddresses, hostState_frames_warmEpoch,
            hslots, hepoch]
          have hmark := warmaddr_after_mark pid sRef.evm.accessedAddresses
            hs.warmAddresses hs.warmEpoch aV hwrel bV
          rw [word_to_address_toList] at hmark
          exact hmark

end EvmSpecsVerify
