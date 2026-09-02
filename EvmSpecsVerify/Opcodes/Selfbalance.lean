import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# SELFBALANCE

The 0-in/1-out sibling of [`BALANCE`](Balance.lean), and the cheap one:
the account is the executing frame's own, so **there is no warm/cold
accounting at all** — both sides charge a flat `5` and neither consults
the access set. `iSelfbalance` charges `FAST_STEP`, reads
`message.currentTarget`'s account through the journalled tracker and
pushes its balance; `execute_selfbalance` charges `G_low`, resolves
`self_addr` from the message register and pushes `k_get_balance`.

Because the extraction's `k_get_balance` reads no warmth here, the
agreement hypothesis is strictly weaker than BALANCE's: no quantification
over ambient warm stamps is needed — see
[`SelfBalanceAgree`](#SelfBalanceAgree) against
[`BalanceAgree`](Balance.lean).

Charge-first on both sides, so the double-fault states land on MM-5.
Reachable outcomes: success / stack overflow / OOG / MM-5 double fault;
underflow is impossible for 0-in.

Gas (MM-2): `GasCosts.FAST_STEP = 5 = G_low`. Note SpecRef names this
constant `FAST_STEP` rather than an `OPCODE_SELFBALANCE`, so the
correspondence is with the tier constant directly.
-/

open private pcNext from EvmAsm.Stateless.SpecRef.InstructionsEnv
open private writeListAt from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- The two sides' own-account reads agree, and the extraction's read
leaves the operand stack alone. The `BalanceAgree` sibling minus the warm
machinery: SELFBALANCE consults no access set, so nothing needs to be
quantified over ambient stamps. -/
def SelfBalanceAgree (sRef : Machine) (hs : Evm.HostState) (ss : SeqState)
    (a : Evm.Defs.address) : Prop :=
  ∃ (acct : EvmAsm.Stateless.SpecRef.Account) (ts' : TransactionState)
    (hostAfter : Evm.HostState),
    WordWf acct.balance ∧
    (getAccount sRef.evm.message.currentTarget).run sRef.txState
      = .ok (acct, ts') ∧
    runS (Evm.Functions.k_get_balance a) hs ss
      = .ok (acct.balance, hostAfter) ss ∧
    hostAfter.stackFrames = hs.stackFrames

/-! ## SpecRef run shapes -/

theorem runR_iSelfbalance_success (s : Machine)
    (acct : EvmAsm.Stateless.SpecRef.Account) (ts' : TransactionState)
    (hacct : (getAccount s.evm.message.currentTarget).run s.txState
      = .ok (acct, ts'))
    (hlen : s.evm.stack.length ≠ 1024)
    (hgas : GasCosts.FAST_STEP ≤ s.evm.gasLeft) :
    runR iSelfbalance s =
      .ok (.ok (),
        { s with
          txState := ts'
          evm := { s.evm with
            stack := acct.balance :: s.evm.stack
            gasLeft := s.evm.gasLeft - GasCosts.FAST_STEP
            regularGasUsed := s.evm.regularGasUsed + GasCosts.FAST_STEP
            pc := s.evm.pc + 1 } }) := by
  simp only [iSelfbalance, pcNext]
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_liftTx_ok _ _ acct ts' (by exact hacct)) ?_
  refine runR_bind_ok (runR_stackPush _ _
    (by show s.evm.stack.length ≠ 1024; exact hlen)) ?_
  exact runR_modifyEvm _ _

theorem runR_iSelfbalance_overflow (s : Machine)
    (acct : EvmAsm.Stateless.SpecRef.Account) (ts' : TransactionState)
    (hacct : (getAccount s.evm.message.currentTarget).run s.txState
      = .ok (acct, ts'))
    (hlen : s.evm.stack.length = 1024)
    (hgas : GasCosts.FAST_STEP ≤ s.evm.gasLeft) :
    runR iSelfbalance s =
      .ok (.error .stackOverflow,
        { s with
          txState := ts'
          evm := { s.evm with
            gasLeft := s.evm.gasLeft - GasCosts.FAST_STEP
            regularGasUsed := s.evm.regularGasUsed + GasCosts.FAST_STEP } })
        := by
  simp only [iSelfbalance]
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_liftTx_ok _ _ acct ts' (by exact hacct)) ?_
  exact runR_bind_err (runR_stackPush_overflow _ _
    (by show s.evm.stack.length = 1024; exact hlen))

/-- OOG fires at the leading charge, before the account read (MM-5). -/
theorem runR_iSelfbalance_oog (s : Machine)
    (hgas : s.evm.gasLeft < GasCosts.FAST_STEP) :
    runR iSelfbalance s = .ok (.error .outOfGas, s) := by
  simp only [iSelfbalance]
  exact runR_bind_err (runR_charge_gas_oog _ _ hgas)

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for SELFBALANCE. -/
theorem selfbalance_dispatch (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_opcode (.SELFBALANCE ()) pc_in top mem g =
      Evm.Functions.execute_selfbalance top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
theorem runS_selfbalance_body_ok (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (msg : Evm.Defs.Message) (v : word) (hs' : Evm.HostState)
    (l : List word) (frest : List (List word))
    (hmsg : ss.regs.get? Register.message = some msg)
    (hval : runS (Evm.Functions.k_get_balance msg.address) hs ss
      = .ok (v, hs') ss)
    (hframe : hs'.stackFrames = l :: frest)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hgas : (G_low : Nat) ≤ g) :
    runS (Evm.Functions.execute_selfbalance top g) hs ss =
      .ok ((top + BitVec.ofNat 64 1, g - G_low),
        { hs' with stackFrames :=
            writeListAt l top.toNat v :: frest }) ss := by
  simp only [Evm.Functions.execute_selfbalance]
  refine runS_bind_ok (runS_charge_ok g G_low hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_self_addr msg hs ss hmsg) ?_
  refine runS_bind_ok hval ?_
  refine runS_bind_ok (runS_push_word top v hs' ss l frest hframe hbound) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_selfbalance_body_oog (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < (G_low : Nat)) :
    runS (Evm.Functions.execute_selfbalance top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_selfbalance]
  refine runS_bind_ok
    (runS_charge_oog g G_low hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_selfbalance_success (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (msg : Evm.Defs.Message) (v : word) (hs' : Evm.HostState)
    (l : List word) (frest : List (List word))
    (hmsg : ss.regs.get? Register.message = some msg)
    (hval : runS (Evm.Functions.k_get_balance msg.address) hs ss
      = .ok (v, hs') ss)
    (hframe : hs'.stackFrames = l :: frest)
    (hlim : top.toNat + 1 ≤ 1024)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hgas : (G_low : Nat) ≤ g) :
    runS (Evm.Functions.execute (.SELFBALANCE ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top + BitVec.ofNat 64 1, mem, g - G_low),
        { hs' with stackFrames :=
            writeListAt l top.toNat v :: frest }) ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.SELFBALANCE ()) = pure (0, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 1 hs ss (by omega)
      (by have h : top.toNat - 0 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, selfbalance_dispatch]
  refine runS_bind_ok
    (runS_selfbalance_body_ok top g hs ss msg v hs' l frest hmsg hval hframe
      hbound hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_selfbalance_overflow (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hover : 1024 < top.toNat + 1) :
    runS (Evm.Functions.execute (.SELFBALANCE ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackOverflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.SELFBALANCE ()) = pure (0, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_overflow g top 0 1 hs ss prof sp msg hprof hsp hmsg
      hfork (by omega)
      (by have h : (1024 : Nat) < top.toNat - 0 + 1 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_selfbalance_oog (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hlim : top.toNat + 1 ≤ 1024)
    (hgas : g < (G_low : Nat)) :
    runS (Evm.Functions.execute (.SELFBALANCE ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.SELFBALANCE ()) = pure (0, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 1 hs ss (by omega)
      (by have h : top.toNat - 0 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, selfbalance_dispatch]
  refine runS_bind_ok
    (runS_selfbalance_body_oog top g hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **SELFBALANCE, all reachable outcomes**: success / stack overflow /
OOG / MM-5 double fault. Underflow is impossible for 0-in, and there is no
warm/cold split — the own account is charged a flat `5` by both sides. -/
theorem selfbalance_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (hbal : ∀ msg : Evm.Defs.Message,
      ss.regs.get? Register.message = some msg →
      SelfBalanceAgree sRef hs ss msg.address) :
    StepResultRel (BasePost mem) (runR iSelfbalance sRef)
      (runS (Evm.Functions.execute (.SELFBALANCE ()) pc_in top mem g)
        hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  obtain ⟨acct, ts', hostAfter, hwfb, hacct, hread, hstk⟩ := hbal msg hmsg
  have hgl : (G_low : Nat) = GasCosts.FAST_STEP := rfl
  by_cases hg : sRef.evm.gasLeft < GasCosts.FAST_STEP
  · rw [runR_iSelfbalance_oog sRef hg]
    by_cases hov : sRef.evm.stack.length = 1024
    · rw [runS_execute_selfbalance_overflow pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.haltedChargeFirst (Or.inr rfl)
        (haltRegs_frame_status ss msg .StackOverflow)
    · rw [runS_execute_selfbalance_oog pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)
        (by rw [hgl, hlive]; exact hg)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
  · push Not at hg
    by_cases hov : sRef.evm.stack.length = 1024
    · rw [runR_iSelfbalance_overflow sRef acct ts' hacct hov hg,
        runS_execute_selfbalance_overflow pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.halted ErrorRel.stackOverflow
        (haltRegs_frame_status ss msg .StackOverflow)
    · have hbound : top.toNat + 1 < 2 ^ 64 := by
        have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
        omega
      have hframe' : hostAfter.stackFrames = l :: frest := by
        rw [hstk]; exact hframe
      rw [runR_iSelfbalance_success sRef acct ts' hacct hov hg,
        runS_execute_selfbalance_success pc_in top g mem hs ss msg
          acct.balance hostAfter l frest hmsg hread hframe' (by omega)
          hbound (by rw [hgl, hlive]; exact hg)]
      have hadv : (top + BitVec.ofNat 64 1).toNat = top.toNat + 1 :=
        cursor_advance_toNat top hbound
      refine StepResultRel.success ?_
      refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
        ⟨msg, hmsg⟩⟩, by simp [hpc], rfl⟩
      · refine ⟨⟨writeListAt l top.toNat acct.balance, frest, rfl, ?_, ?_⟩,
          ?_, ?_, ?_⟩
        · rw [hadv, take_writeListAt l top.toNat _ (by omega), hpfx]
          simp
        · rw [hadv, length_writeListAt]
          omega
        · rw [hadv]
          simp
          omega
        · simp
          omega
        · intro w hw
          rcases List.mem_cons.mp hw with hw | hw
          · subst hw
            exact hwfb
          · exact hwfS w hw
      · exact ⟨by rw [hlive, hgl], hres, hsp⟩

end EvmSpecsVerify
