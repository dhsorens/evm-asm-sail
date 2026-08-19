import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Relations.Calldata
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack

/-!
# CALLDATASIZE

An env pusher in the CALLVALUE mold: charge `G_base`/`OPCODE_CALLDATASIZE`
(= 2, both sides), push the calldata byte length. The value agreement is
[`calldataRel_length`](../Relations/Calldata.lean) — either window
constructor reports SpecRef's `message.data.length`. The pushed length's
word bound `hwf` is the slice invariant (the extraction's slice types cap
lengths at `2^32 - 1`, where `word_of_source_byte_count`'s assert is
unreachable; SpecRef never states it) — hypothesized like CALLVALUE's
`hwfv`, discharged at frame entry in M3. MM-5 applies to the double-fault
states. Reachable outcomes: success / stack overflow / OOG / MM-5 double
fault.
-/

open private pcNext from EvmAsm.Stateless.SpecRef.InstructionsEnv
open private writeListAt from Evm.HostAxioms

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## SpecRef run shapes -/

theorem runR_iCalldatasize_success (s : Machine)
    (hlen : s.evm.stack.length ≠ 1024)
    (hgas : GasCosts.OPCODE_CALLDATASIZE ≤ s.evm.gasLeft) :
    runR iCalldatasize s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := s.evm.message.data.length :: s.evm.stack
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_CALLDATASIZE
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_CALLDATASIZE
            pc := s.evm.pc + 1 } }) := by
  simp only [iCalldatasize, pcNext]
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_stackPush _ _
    (by show s.evm.stack.length ≠ 1024; exact hlen)) ?_
  exact runR_modifyEvm _ _

theorem runR_iCalldatasize_overflow (s : Machine)
    (hlen : s.evm.stack.length = 1024)
    (hgas : GasCosts.OPCODE_CALLDATASIZE ≤ s.evm.gasLeft) :
    runR iCalldatasize s =
      .ok (.error .stackOverflow,
        { s with evm := { s.evm with
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_CALLDATASIZE
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_CALLDATASIZE } }) := by
  simp only [iCalldatasize]
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  exact runR_bind_err (runR_stackPush_overflow _ _
    (by show s.evm.stack.length = 1024; exact hlen))

/-- OOG fires at the leading charge, before the push (MM-5). -/
theorem runR_iCalldatasize_oog (s : Machine)
    (hgas : s.evm.gasLeft < GasCosts.OPCODE_CALLDATASIZE) :
    runR iCalldatasize s = .ok (.error .outOfGas, s) := by
  simp only [iCalldatasize]
  exact runR_bind_err (runR_charge_gas_oog _ _ hgas)

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for CALLDATASIZE. -/
theorem calldatasize_dispatch (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_opcode (.CALLDATASIZE ()) pc_in top mem g =
      Evm.Functions.execute_calldatasize top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
theorem runS_calldatasize_body_ok (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (D : Bytes)
    (cd : CalldataSlice)
    (hframe : hs.stackFrames = l :: frest)
    (hcdreg : ss.regs.get? Register.calldata = some cd)
    (hcdrel : CalldataRel D hs cd)
    (hwf : D.length < 2 ^ 256)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hgas : (GasCosts.OPCODE_CALLDATASIZE : Nat) ≤ g) :
    runS (Evm.Functions.execute_calldatasize top g) hs ss =
      .ok ((top + BitVec.ofNat 64 1, g - GasCosts.OPCODE_CALLDATASIZE),
        { hs with stackFrames :=
            writeListAt l top.toNat D.length :: frest })
        ss := by
  simp only [Evm.Functions.execute_calldatasize]
  refine runS_bind_ok (runS_charge_ok g G_base hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_readReg _ _ _ _ hcdreg) ?_
  rw [calldataRel_length D hs cd hcdrel]
  refine runS_bind_ok
    (runS_word_of_source_byte_count D.length hs ss hwf) ?_
  refine runS_bind_ok
    (runS_push_word top D.length hs ss l frest hframe hbound) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_calldatasize_body_oog (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < (GasCosts.OPCODE_CALLDATASIZE : Nat)) :
    runS (Evm.Functions.execute_calldatasize top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_calldatasize]
  refine runS_bind_ok
    (runS_charge_oog g G_base hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_calldatasize_success (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (D : Bytes)
    (cd : CalldataSlice)
    (hframe : hs.stackFrames = l :: frest)
    (hcdreg : ss.regs.get? Register.calldata = some cd)
    (hcdrel : CalldataRel D hs cd)
    (hwf : D.length < 2 ^ 256)
    (hlim : top.toNat + 1 ≤ 1024)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hgas : (GasCosts.OPCODE_CALLDATASIZE : Nat) ≤ g) :
    runS (Evm.Functions.execute (.CALLDATASIZE ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top + BitVec.ofNat 64 1, mem,
          g - GasCosts.OPCODE_CALLDATASIZE),
        { hs with stackFrames :=
            writeListAt l top.toNat D.length :: frest })
        ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.CALLDATASIZE ()) = pure (0, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 1 hs ss (by omega)
      (by have h : top.toNat - 0 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, calldatasize_dispatch]
  refine runS_bind_ok
    (runS_calldatasize_body_ok top g hs ss l frest D cd hframe hcdreg
      hcdrel hwf hbound hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_calldatasize_overflow (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hover : 1024 < top.toNat + 1) :
    runS (Evm.Functions.execute (.CALLDATASIZE ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackOverflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.CALLDATASIZE ()) = pure (0, 1)
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
theorem runS_execute_calldatasize_oog (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hlim : top.toNat + 1 ≤ 1024)
    (hgas : g < (GasCosts.OPCODE_CALLDATASIZE : Nat)) :
    runS (Evm.Functions.execute (.CALLDATASIZE ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.CALLDATASIZE ()) = pure (0, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 1 hs ss (by omega)
      (by have h : top.toNat - 0 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, calldatasize_dispatch]
  refine runS_bind_ok
    (runS_calldatasize_body_oog top g hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **CALLDATASIZE, all reachable outcomes.** Double-fault states (full
stack ∧ OOG) use the MM-5 constructor; `hcdreg`/`hcdrel` supply the
`calldata` register read and the calldata relation, `hwf` the slice-length
word bound (the extraction's `≤ 2^32 - 1` slice invariant). -/
theorem calldatasize_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat) (cd : CalldataSlice)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (hcdreg : ss.regs.get? Register.calldata = some cd)
    (hcdrel : CalldataRel sRef.evm.message.data hs cd)
    (hwf : WordWf sRef.evm.message.data.length) :
    StepResultRel (BasePost mem) (runR iCalldatasize sRef)
      (runS (Evm.Functions.execute (.CALLDATASIZE ()) pc_in top mem g)
        hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_CALLDATASIZE
  · rw [runR_iCalldatasize_oog sRef hg]
    by_cases hov : sRef.evm.stack.length = 1024
    · rw [runS_execute_calldatasize_overflow pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.haltedChargeFirst (Or.inr rfl)
        (haltRegs_frame_status ss msg .StackOverflow)
    · rw [runS_execute_calldatasize_oog pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)
        (by rw [hlive]; exact hg)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
  · push Not at hg
    by_cases hov : sRef.evm.stack.length = 1024
    · rw [runR_iCalldatasize_overflow sRef hov hg,
        runS_execute_calldatasize_overflow pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.halted ErrorRel.stackOverflow
        (haltRegs_frame_status ss msg .StackOverflow)
    · have hbound : top.toNat + 1 < 2 ^ 64 := by
        have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
        omega
      rw [runR_iCalldatasize_success sRef hov hg,
        runS_execute_calldatasize_success pc_in top g mem hs ss l frest
          sRef.evm.message.data cd hframe hcdreg hcdrel hwf (by omega)
          hbound (by rw [hlive]; exact hg)]
      have hadv : (top + BitVec.ofNat 64 1).toNat = top.toNat + 1 :=
        cursor_advance_toNat top hbound
      refine StepResultRel.success ?_
      refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
        ⟨msg, hmsg⟩⟩, by simp [hpc], rfl⟩
      · refine ⟨⟨writeListAt l top.toNat sRef.evm.message.data.length, frest,
            rfl, ?_, ?_⟩, ?_, ?_, ?_⟩
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
            exact hwf
          · exact hwfS w hw
      · exact ⟨by rw [hlive], hres, hsp⟩

end EvmSpecsVerify
