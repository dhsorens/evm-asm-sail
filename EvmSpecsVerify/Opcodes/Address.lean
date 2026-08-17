import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Representation.AddressWord
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# ADDRESS

The first env-family pusher: charge `G_base`/`OPCODE_ADDRESS` (= 2, both
sides), push the executing account's address as a word. The extraction
reads the `message` register (`self_addr`) and encodes with
`address_to_word`; SpecRef reads `message.currentTarget` and decodes with
`bytesBEtoNat` — identified by `address_to_word_eq`
(Representation/AddressWord.lean) under the `haddr` register-tie
hypothesis (the same tie SLOAD uses).

SpecRef charges **before** touching the stack, so double-fault states
(full stack ∧ OOG) diverge in halt kind exactly as PUSH/DUP/SWAP do —
mismatch ledger MM-5, `StepResultRel.haltedChargeFirst`. Reachable
outcomes: success / stack overflow / OOG / MM-5 double fault (underflow
unreachable for 0-in).
-/

open private pcNext from EvmAsm.Stateless.SpecRef.InstructionsEnv
open private writeListAt from Evm.HostAxioms

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## SpecRef run shapes -/

theorem runR_iAddress_success (s : Machine)
    (hlen : s.evm.stack.length ≠ 1024)
    (hgas : GasCosts.OPCODE_ADDRESS ≤ s.evm.gasLeft) :
    runR iAddress s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := bytesBEtoNat s.evm.message.currentTarget :: s.evm.stack
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_ADDRESS
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_ADDRESS
            pc := s.evm.pc + 1 } }) := by
  simp only [iAddress, pcNext]
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_stackPush _ _
    (by show s.evm.stack.length ≠ 1024; exact hlen)) ?_
  exact runR_modifyEvm _ _

theorem runR_iAddress_overflow (s : Machine)
    (hlen : s.evm.stack.length = 1024)
    (hgas : GasCosts.OPCODE_ADDRESS ≤ s.evm.gasLeft) :
    runR iAddress s =
      .ok (.error .stackOverflow,
        { s with evm := { s.evm with
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_ADDRESS
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_ADDRESS } }) := by
  simp only [iAddress]
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  exact runR_bind_err (runR_stackPush_overflow _ _
    (by show s.evm.stack.length = 1024; exact hlen))

/-- OOG fires at the leading charge, before the push (MM-5). -/
theorem runR_iAddress_oog (s : Machine)
    (hgas : s.evm.gasLeft < GasCosts.OPCODE_ADDRESS) :
    runR iAddress s = .ok (.error .outOfGas, s) := by
  simp only [iAddress]
  exact runR_bind_err (runR_charge_gas_oog _ _ hgas)

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for ADDRESS. -/
theorem address_dispatch (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_opcode (.ADDRESS ()) pc_in top mem g =
      Evm.Functions.execute_address top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
theorem runS_address_body_ok (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (msg : Evm.Defs.Message)
    (hframe : hs.stackFrames = l :: frest)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hgas : (GasCosts.OPCODE_ADDRESS : Nat) ≤ g) :
    runS (Evm.Functions.execute_address top g) hs ss =
      .ok ((top + BitVec.ofNat 64 1, g - GasCosts.OPCODE_ADDRESS),
        { hs with stackFrames :=
            writeListAt l top.toNat (address_to_word msg.address) :: frest })
        ss := by
  simp only [Evm.Functions.execute_address]
  refine runS_bind_ok (runS_charge_ok g G_base hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_self_addr msg hs ss hmsg) ?_
  refine runS_bind_ok
    (runS_push_word top (address_to_word msg.address) hs ss l frest hframe
      hbound) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_address_body_oog (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < (GasCosts.OPCODE_ADDRESS : Nat)) :
    runS (Evm.Functions.execute_address top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_address]
  refine runS_bind_ok
    (runS_charge_oog g G_base hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_address_success (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (msg : Evm.Defs.Message)
    (hframe : hs.stackFrames = l :: frest)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hlim : top.toNat + 1 ≤ 1024)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hgas : (GasCosts.OPCODE_ADDRESS : Nat) ≤ g) :
    runS (Evm.Functions.execute (.ADDRESS ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top + BitVec.ofNat 64 1, mem,
          g - GasCosts.OPCODE_ADDRESS),
        { hs with stackFrames :=
            writeListAt l top.toNat (address_to_word msg.address) :: frest })
        ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.ADDRESS ()) = pure (0, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 1 hs ss (by omega)
      (by have h : top.toNat - 0 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, address_dispatch]
  refine runS_bind_ok
    (runS_address_body_ok top g hs ss l frest msg hframe hmsg hbound
      hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_address_overflow (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hover : 1024 < top.toNat + 1) :
    runS (Evm.Functions.execute (.ADDRESS ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackOverflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.ADDRESS ()) = pure (0, 1)
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
theorem runS_execute_address_oog (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hlim : top.toNat + 1 ≤ 1024)
    (hgas : g < (GasCosts.OPCODE_ADDRESS : Nat)) :
    runS (Evm.Functions.execute (.ADDRESS ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.ADDRESS ()) = pure (0, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 1 hs ss (by omega)
      (by have h : top.toNat - 0 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, address_dispatch]
  refine runS_bind_ok
    (runS_address_body_oog top g hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **ADDRESS, all reachable outcomes.** Double-fault states (full stack ∧
OOG) use the MM-5 constructor; `haddr` ties the message register to
SpecRef's executing account. -/
theorem address_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (haddr : ∀ msg : Evm.Defs.Message,
      ss.regs.get? Register.message = some msg →
      msg.address.toList = sRef.evm.message.currentTarget) :
    StepResultRel (AluPost mem) (runR iAddress sRef)
      (runS (Evm.Functions.execute (.ADDRESS ()) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  have hax : msg.address.toList = sRef.evm.message.currentTarget :=
    haddr msg hmsg
  by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_ADDRESS
  · rw [runR_iAddress_oog sRef hg]
    by_cases hov : sRef.evm.stack.length = 1024
    · rw [runS_execute_address_overflow pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.haltedChargeFirst (Or.inr rfl)
        (haltRegs_frame_status ss msg .StackOverflow)
    · rw [runS_execute_address_oog pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)
        (by rw [hlive]; exact hg)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
  · push Not at hg
    by_cases hov : sRef.evm.stack.length = 1024
    · rw [runR_iAddress_overflow sRef hov hg,
        runS_execute_address_overflow pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.halted ErrorRel.stackOverflow
        (haltRegs_frame_status ss msg .StackOverflow)
    · have hbound : top.toNat + 1 < 2 ^ 64 := by
        have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
        omega
      rw [runR_iAddress_success sRef hov hg,
        runS_execute_address_success pc_in top g mem hs ss l frest msg
          hframe hmsg (by omega) hbound (by rw [hlive]; exact hg),
        address_to_word_eq, hax]
      have hadv : (top + BitVec.ofNat 64 1).toNat = top.toNat + 1 :=
        cursor_advance_toNat top hbound
      refine StepResultRel.success ?_
      refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
        ⟨msg, hmsg⟩⟩, by simp [hpc], rfl⟩
      · refine ⟨⟨writeListAt l top.toNat
            (bytesBEtoNat sRef.evm.message.currentTarget), frest, rfl,
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
            rw [← hax, ← address_to_word_eq]
            exact address_to_word_wf msg.address
          · exact hwfS w hw
      · exact ⟨by rw [hlive], hres, hsp⟩

end EvmSpecsVerify
