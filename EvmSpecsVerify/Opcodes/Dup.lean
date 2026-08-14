import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# DUP1–DUP16

`iDupN k` (0-indexed depth, dispatched as `iDupN (op - 0x80)`) vs
`execute (.DUP n)` with `n = k + 1` (1-indexed, stack effect `(n, n+1)`).
First opcode family where **overflow is reachable** (the height grows), and
first **charge-first** SpecRef handler: `iDupN` charges before its depth
check, so double-fault states (bad depth/height ∧ OOG) halt with different
kinds — mismatch ledger **MM-5**, related via
`StepResultRel.haltedChargeFirst`. Single-fault outcomes align kind-for-kind:
success / underflow / overflow / OOG.
-/

open private pcAdd from EvmAsm.Stateless.SpecRef.InstructionsCore
open private writeListAt from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## SpecRef run shapes (`k` is the 0-indexed depth) -/

theorem runR_iDupN_success (s : Machine) (k : Nat)
    (hk : k < s.evm.stack.length)
    (hlen : s.evm.stack.length ≠ 1024)
    (hgas : GasCosts.OPCODE_DUP ≤ s.evm.gasLeft) :
    runR (iDupN k) s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := s.evm.stack.getD k 0 :: s.evm.stack
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_DUP
            regularGasUsed := s.evm.regularGasUsed + GasCosts.OPCODE_DUP
            pc := s.evm.pc + 1 } }) := by
  simp only [iDupN, pcAdd]
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_neg (by show ¬(k ≥ s.evm.stack.length); omega)]
  refine runR_bind_ok (runR_pure _ _) ?_
  refine runR_bind_ok (runR_stackPush _ _
    (by show s.evm.stack.length ≠ 1024; exact hlen)) ?_
  exact runR_modifyEvm _ _

theorem runR_iDupN_underflow (s : Machine) (k : Nat)
    (hk : s.evm.stack.length ≤ k)
    (hgas : GasCosts.OPCODE_DUP ≤ s.evm.gasLeft) :
    runR (iDupN k) s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_DUP
            regularGasUsed := s.evm.regularGasUsed + GasCosts.OPCODE_DUP } }) := by
  simp only [iDupN]
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_pos (by show k ≥ s.evm.stack.length; omega)]
  exact runR_bind_err (runR_throw _ _)

theorem runR_iDupN_overflow (s : Machine) (k : Nat)
    (hk : k < s.evm.stack.length)
    (hlen : s.evm.stack.length = 1024)
    (hgas : GasCosts.OPCODE_DUP ≤ s.evm.gasLeft) :
    runR (iDupN k) s =
      .ok (.error .stackOverflow,
        { s with evm := { s.evm with
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_DUP
            regularGasUsed := s.evm.regularGasUsed + GasCosts.OPCODE_DUP } }) := by
  simp only [iDupN]
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_neg (by show ¬(k ≥ s.evm.stack.length); omega)]
  refine runR_bind_ok (runR_pure _ _) ?_
  exact runR_bind_err (runR_stackPush_overflow _ _
    (by show s.evm.stack.length = 1024; exact hlen))

/-- OOG fires at the leading charge, before any stack inspection (MM-5). -/
theorem runR_iDupN_oog (s : Machine) (k : Nat)
    (hgas : s.evm.gasLeft < GasCosts.OPCODE_DUP) :
    runR (iDupN k) s = .ok (.error .outOfGas, s) := by
  simp only [iDupN]
  exact runR_bind_err (runR_charge_gas_oog _ _ (by simpa using hgas))

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for the DUP family. -/
theorem dup_dispatch (n : Nat) (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_opcode (.DUP n) pc_in top mem g =
      Evm.Functions.execute_dup n top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
theorem runS_dup_body_ok (n : Nat) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (S : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = S.reverse)
    (htop : top.toNat = S.length)
    (hi : n - 1 < S.length)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hgas : G_verylow ≤ g) :
    runS (Evm.Functions.execute_dup n top g) hs ss =
      .ok ((top + BitVec.ofNat 64 1, g - G_verylow),
        { hs with stackFrames :=
            writeListAt l top.toNat (S.getD (n - 1) default) :: frest }) ss := by
  simp only [Evm.Functions.execute_dup]
  refine runS_bind_ok (runS_charge_ok g G_verylow hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_peek top (n - 1) hs ss l frest S hframe hpfx htop hi) ?_
  refine runS_bind_ok (runS_push_word top (S.getD (n - 1) default) hs ss l frest
    hframe hbound) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_dup_body_oog (n : Nat) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < G_verylow) :
    runS (Evm.Functions.execute_dup n top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_dup]
  refine runS_bind_ok
    (runS_charge_oog g G_verylow hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_dup_success (n : Nat) (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (S : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = S.reverse)
    (htop : top.toNat = S.length)
    (hin : n ≤ top.toNat) (hn1 : 1 ≤ n)
    (hlim : top.toNat + 1 ≤ 1024)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hgas : G_verylow ≤ g) :
    runS (Evm.Functions.execute (.DUP n) pc_in top mem g) hs ss =
      .ok ((pc_in, top + BitVec.ofNat 64 1, mem, g - G_verylow),
        { hs with stackFrames :=
            writeListAt l top.toNat (S.getD (n - 1) default) :: frest }) ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.DUP n) = pure (n, n + 1) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top n (n + 1) hs ss hin
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, dup_dispatch]
  refine runS_bind_ok
    (runS_dup_body_ok n top g hs ss l frest S hframe hpfx htop
      (by omega) hbound hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_dup_underflow (n : Nat) (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < n) :
    runS (Evm.Functions.execute (.DUP n) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.DUP n) = pure (n, n + 1) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top n (n + 1) hs ss prof sp msg hprof hsp
      hmsg hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_dup_overflow (n : Nat) (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hin : n ≤ top.toNat)
    (hover : 1024 < top.toNat + 1) :
    runS (Evm.Functions.execute (.DUP n) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackOverflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.DUP n) = pure (n, n + 1) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_overflow g top n (n + 1) hs ss prof sp msg hprof hsp
      hmsg hfork hin
      (by have h : (1024 : Nat) < top.toNat - n + (n + 1) := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_dup_oog (n : Nat) (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hin : n ≤ top.toNat)
    (hlim : top.toNat + 1 ≤ 1024)
    (hgas : g < G_verylow) :
    runS (Evm.Functions.execute (.DUP n) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.DUP n) = pure (n, n + 1) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top n (n + 1) hs ss hin
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, dup_dispatch]
  refine runS_bind_ok
    (runS_dup_body_oog n top g hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **DUPn, all reachable outcomes** (n 1-indexed, `iDupN (n-1)` 0-indexed).
Double-fault states (bad depth/height ∧ OOG) use the MM-5 constructor. -/
theorem dup_step_equiv (n : Nat) (hn1 : 1 ≤ n)
    (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR (iDupN (n - 1)) sRef)
      (runS (Evm.Functions.execute (.DUP n) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_DUP
  · -- SpecRef charges first: OOG regardless of stack shape (MM-5 overlap)
    rw [runR_iDupN_oog sRef (n - 1) hg]
    by_cases hu : sRef.evm.stack.length < n
    · rw [runS_execute_dup_underflow n pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.haltedChargeFirst (Or.inl rfl)
        (haltRegs_frame_status ss msg .StackUnderflow)
    · by_cases hov : sRef.evm.stack.length = 1024
      · rw [runS_execute_dup_overflow n pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)
          (by omega)]
        exact StepResultRel.haltedChargeFirst (Or.inr rfl)
          (haltRegs_frame_status ss msg .StackOverflow)
      · rw [runS_execute_dup_oog n pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)
          (by omega) (by rw [hlive]; exact hg)]
        exact StepResultRel.halted ErrorRel.outOfGas
          (haltRegs_frame_status ss msg .OutOfGas)
  · push Not at hg
    by_cases hu : sRef.evm.stack.length < n
    · rw [runR_iDupN_underflow sRef (n - 1) (by omega) hg,
        runS_execute_dup_underflow n pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.halted ErrorRel.stackUnderflow
        (haltRegs_frame_status ss msg .StackUnderflow)
    · by_cases hov : sRef.evm.stack.length = 1024
      · rw [runR_iDupN_overflow sRef (n - 1) (by omega) hov hg,
          runS_execute_dup_overflow n pc_in top g mem hs ss prof
            sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)
            (by omega)]
        exact StepResultRel.halted ErrorRel.stackOverflow
          (haltRegs_frame_status ss msg .StackOverflow)
      · have hbound : top.toNat + 1 < 2 ^ 64 := by
          have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
          omega
        rw [runR_iDupN_success sRef (n - 1) (by omega) hov hg,
          runS_execute_dup_success n pc_in top g mem hs ss l frest
            sRef.evm.stack hframe hpfx htop (by omega) hn1 (by omega) hbound
            (by rw [hlive]; exact hg)]
        have hadv : (top + BitVec.ofNat 64 1).toNat = top.toNat + 1 :=
          cursor_advance_toNat top hbound
        refine StepResultRel.success ?_
        refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
          ⟨msg, hmsg⟩⟩, by simp [hpc], rfl⟩
        · have hv : sRef.evm.stack.getD (n - 1) (default : word)
              = sRef.evm.stack.getD (n - 1) 0 := rfl
          refine ⟨⟨writeListAt l top.toNat
              (sRef.evm.stack.getD (n - 1) default), frest, rfl, ?_, ?_⟩,
            ?_, ?_, ?_⟩
          · rw [hadv, take_writeListAt l top.toNat _ (by omega), hpfx, hv]
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
              have hget : sRef.evm.stack.getD (n - 1) 0
                  = sRef.evm.stack[n - 1]'(by omega) := by
                show (sRef.evm.stack[n - 1]?).getD 0 = _
                rw [List.getElem?_eq_getElem (by omega)]
                rfl
              rw [hget]
              exact hwfS _ (List.getElem_mem _)
            · exact hwfS w hw
        · exact ⟨by simp [hlive, Evm.Functions.G_verylow, GasCosts.OPCODE_DUP],
            hres, hsp⟩

end EvmSpecsVerify
