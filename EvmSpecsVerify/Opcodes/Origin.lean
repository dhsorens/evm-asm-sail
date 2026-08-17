import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Representation.AddressWord
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# ORIGIN

Same charge-first pusher shape as [ADDRESS](Address.lean), with the value
read from the transaction environment instead of the message: the
extraction reads the `k_tx` register (`k_env F_Origin` returns
`address_to_word active_tx.origin`), SpecRef reads
`message.txEnv.origin` — identified by `address_to_word_eq` under the
`horigin` register-tie hypothesis (the ORIGIN analogue of `haddr`; the
`k_tx` register is not part of `StateRel`, so the read and the tie are
both hypotheses of the step theorem).

MM-5 applies to the double-fault states exactly as for ADDRESS.
Reachable outcomes: success / stack overflow / OOG / MM-5 double fault.
-/

open private pcNext from EvmAsm.Stateless.SpecRef.InstructionsEnv
open private writeListAt from Evm.HostAxioms

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## SpecRef run shapes -/

theorem runR_iOrigin_success (s : Machine)
    (hlen : s.evm.stack.length ≠ 1024)
    (hgas : GasCosts.OPCODE_ORIGIN ≤ s.evm.gasLeft) :
    runR iOrigin s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := bytesBEtoNat s.evm.message.txEnv.origin :: s.evm.stack
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_ORIGIN
            regularGasUsed := s.evm.regularGasUsed + GasCosts.OPCODE_ORIGIN
            pc := s.evm.pc + 1 } }) := by
  simp only [iOrigin, pcNext]
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_stackPush _ _
    (by show s.evm.stack.length ≠ 1024; exact hlen)) ?_
  exact runR_modifyEvm _ _

theorem runR_iOrigin_overflow (s : Machine)
    (hlen : s.evm.stack.length = 1024)
    (hgas : GasCosts.OPCODE_ORIGIN ≤ s.evm.gasLeft) :
    runR iOrigin s =
      .ok (.error .stackOverflow,
        { s with evm := { s.evm with
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_ORIGIN
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_ORIGIN } }) := by
  simp only [iOrigin]
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  exact runR_bind_err (runR_stackPush_overflow _ _
    (by show s.evm.stack.length = 1024; exact hlen))

/-- OOG fires at the leading charge, before the push (MM-5). -/
theorem runR_iOrigin_oog (s : Machine)
    (hgas : s.evm.gasLeft < GasCosts.OPCODE_ORIGIN) :
    runR iOrigin s = .ok (.error .outOfGas, s) := by
  simp only [iOrigin]
  exact runR_bind_err (runR_charge_gas_oog _ _ hgas)

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for ORIGIN. -/
theorem origin_dispatch (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_opcode (.ORIGIN ()) pc_in top mem g =
      Evm.Functions.execute_origin top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
/-- `k_env F_Origin` reads the transaction's origin as a word. -/
theorem runS_k_env_origin (txp : TxEnv) (hs : Evm.HostState) (ss : SeqState)
    (htx : ss.regs.get? Register.k_tx = some txp) :
    runS (Evm.Functions.k_env EnvField.F_Origin) hs ss =
      .ok (address_to_word txp.2.origin, hs) ss := by
  obtain ⟨lim, tx⟩ := txp
  simp only [Evm.Functions.k_env, runS_bind, runS_readReg _ _ _ _ htx,
    runS_pure]

open Evm.Functions in
theorem runS_origin_body_ok (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (txp : TxEnv)
    (hframe : hs.stackFrames = l :: frest)
    (htx : ss.regs.get? Register.k_tx = some txp)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hgas : (GasCosts.OPCODE_ORIGIN : Nat) ≤ g) :
    runS (Evm.Functions.execute_origin top g) hs ss =
      .ok ((top + BitVec.ofNat 64 1, g - GasCosts.OPCODE_ORIGIN),
        { hs with stackFrames :=
            writeListAt l top.toNat (address_to_word txp.2.origin)
              :: frest }) ss := by
  simp only [Evm.Functions.execute_origin]
  refine runS_bind_ok (runS_charge_ok g G_base hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_k_env_origin txp hs ss htx) ?_
  refine runS_bind_ok
    (runS_push_word top (address_to_word txp.2.origin) hs ss l frest hframe
      hbound) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_origin_body_oog (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < (GasCosts.OPCODE_ORIGIN : Nat)) :
    runS (Evm.Functions.execute_origin top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_origin]
  refine runS_bind_ok
    (runS_charge_oog g G_base hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_origin_success (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (txp : TxEnv)
    (hframe : hs.stackFrames = l :: frest)
    (htx : ss.regs.get? Register.k_tx = some txp)
    (hlim : top.toNat + 1 ≤ 1024)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hgas : (GasCosts.OPCODE_ORIGIN : Nat) ≤ g) :
    runS (Evm.Functions.execute (.ORIGIN ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top + BitVec.ofNat 64 1, mem, g - GasCosts.OPCODE_ORIGIN),
        { hs with stackFrames :=
            writeListAt l top.toNat (address_to_word txp.2.origin)
              :: frest }) ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.ORIGIN ()) = pure (0, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 1 hs ss (by omega)
      (by have h : top.toNat - 0 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, origin_dispatch]
  refine runS_bind_ok
    (runS_origin_body_ok top g hs ss l frest txp hframe htx hbound hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_origin_overflow (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hover : 1024 < top.toNat + 1) :
    runS (Evm.Functions.execute (.ORIGIN ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackOverflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.ORIGIN ()) = pure (0, 1)
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
theorem runS_execute_origin_oog (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hlim : top.toNat + 1 ≤ 1024)
    (hgas : g < (GasCosts.OPCODE_ORIGIN : Nat)) :
    runS (Evm.Functions.execute (.ORIGIN ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.ORIGIN ()) = pure (0, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 1 hs ss (by omega)
      (by have h : top.toNat - 0 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, origin_dispatch]
  refine runS_bind_ok
    (runS_origin_body_oog top g hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **ORIGIN, all reachable outcomes.** `htx`/`horigin` supply the `k_tx`
register read and tie its origin to SpecRef's transaction environment;
double-fault states use the MM-5 constructor. -/
theorem origin_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat) (txp : TxEnv)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (htx : ss.regs.get? Register.k_tx = some txp)
    (horigin : txp.2.origin.toList = sRef.evm.message.txEnv.origin) :
    StepResultRel (BasePost mem) (runR iOrigin sRef)
      (runS (Evm.Functions.execute (.ORIGIN ()) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_ORIGIN
  · rw [runR_iOrigin_oog sRef hg]
    by_cases hov : sRef.evm.stack.length = 1024
    · rw [runS_execute_origin_overflow pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.haltedChargeFirst (Or.inr rfl)
        (haltRegs_frame_status ss msg .StackOverflow)
    · rw [runS_execute_origin_oog pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)
        (by rw [hlive]; exact hg)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
  · push Not at hg
    by_cases hov : sRef.evm.stack.length = 1024
    · rw [runR_iOrigin_overflow sRef hov hg,
        runS_execute_origin_overflow pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.halted ErrorRel.stackOverflow
        (haltRegs_frame_status ss msg .StackOverflow)
    · have hbound : top.toNat + 1 < 2 ^ 64 := by
        have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
        omega
      rw [runR_iOrigin_success sRef hov hg,
        runS_execute_origin_success pc_in top g mem hs ss l frest txp
          hframe htx (by omega) hbound (by rw [hlive]; exact hg),
        address_to_word_eq, horigin]
      have hadv : (top + BitVec.ofNat 64 1).toNat = top.toNat + 1 :=
        cursor_advance_toNat top hbound
      refine StepResultRel.success ?_
      refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
        ⟨msg, hmsg⟩⟩, by simp [hpc], rfl⟩
      · refine ⟨⟨writeListAt l top.toNat
            (bytesBEtoNat sRef.evm.message.txEnv.origin), frest, rfl,
            ?_, ?_⟩, ?_, ?_, ?_⟩
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
            rw [← horigin, ← address_to_word_eq]
            exact address_to_word_wf txp.2.origin
          · exact hwfS w hw
      · exact ⟨by rw [hlive], hres, hsp⟩

end EvmSpecsVerify
