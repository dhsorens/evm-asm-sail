import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas
import Batteries.Tactic.OpenPrivate

/-!
# PC

The first 0-in/1-out pusher whose value is *not* a `k_env` block field but
the live step state, so it sits beside the
[`env pusher shape`](Shapes/EnvPusher.lean) rather than inside it.

SpecRef's `iPc` charges `OPCODE_PC`, pushes `evm.pc` — the opcode's own
position — and advances the pc. The extraction receives the *already
advanced* `pc_in` (mismatch ledger MM-4) and recovers the opcode position
by subtracting one: `word_of_source_byte_count pc_in` embeds the counter as
a word, then `alu_sub … WORD_ONE`. Under `pc_in = sRef.evm.pc + 1` the two
values coincide, and the subtraction never wraps because `pc_in ≥ 1`.

Charge-first on both sides, so the double-fault states (full stack ∧ out of
gas) land on MM-5: SpecRef reports `outOfGas`, the extraction's hoisted
`validate_stack` reports `StackOverflow`. Reachable outcomes: success /
stack overflow / OOG / MM-5 double fault. Underflow is impossible for
0-in.

Gas (MM-2): `GasCosts.OPCODE_PC = 2 = G_base`.
-/

open private pcAdd from EvmAsm.Stateless.SpecRef.InstructionsCore
open private writeListAt from Evm.HostAxioms

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## SpecRef run shapes -/

theorem runR_iPc_success (s : Machine)
    (hlen : s.evm.stack.length ≠ 1024)
    (hgas : GasCosts.OPCODE_PC ≤ s.evm.gasLeft) :
    runR iPc s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := s.evm.pc :: s.evm.stack
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_PC
            regularGasUsed := s.evm.regularGasUsed + GasCosts.OPCODE_PC
            pc := s.evm.pc + 1 } }) := by
  simp only [iPc, pcAdd]
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_stackPush _ _
    (by show s.evm.stack.length ≠ 1024; exact hlen)) ?_
  exact runR_modifyEvm _ _

theorem runR_iPc_overflow (s : Machine)
    (hlen : s.evm.stack.length = 1024)
    (hgas : GasCosts.OPCODE_PC ≤ s.evm.gasLeft) :
    runR iPc s =
      .ok (.error .stackOverflow,
        { s with evm := { s.evm with
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_PC
            regularGasUsed := s.evm.regularGasUsed + GasCosts.OPCODE_PC } })
        := by
  simp only [iPc]
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  exact runR_bind_err (runR_stackPush_overflow _ _
    (by show s.evm.stack.length = 1024; exact hlen))

/-- OOG fires at the leading charge, before the push (MM-5). -/
theorem runR_iPc_oog (s : Machine)
    (hgas : s.evm.gasLeft < GasCosts.OPCODE_PC) :
    runR iPc s = .ok (.error .outOfGas, s) := by
  simp only [iPc]
  exact runR_bind_err (runR_charge_gas_oog _ _ hgas)

/-! ## The opcode-position recovery -/

/-- The extraction recovers the opcode's own position from the advanced
counter. No wrap: `pc_in ≥ 1` on every reachable state. -/
theorem alu_sub_one (n : Nat) (hn : 1 ≤ n) :
    Evm.Functions.alu_sub n Evm.Functions.WORD_ONE = n - 1 := by
  have h1 : (Evm.Functions.WORD_ONE : Nat) = 1 := by decide
  show Evm.Functions.word_sub_word n Evm.Functions.WORD_ONE = n - 1
  rw [Evm.Functions.word_sub_word, h1]
  simp [hn]

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for PC: the *incoming* pc is returned unchanged
(the handler only reads it to compute the pushed word). -/
theorem pc_dispatch (pc_in : Nat) (top : StackTop) (mem : EvmMemorySlice)
    (g : Nat) :
    Evm.Functions.execute_opcode (.PC ()) pc_in top mem g =
      Evm.Functions.execute_pc pc_in top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
theorem runS_pc_body_ok (pc_in : Nat) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word))
    (hframe : hs.stackFrames = l :: frest)
    (hwfpc : pc_in < 2 ^ 256) (hpos : 1 ≤ pc_in)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hgas : (G_base : Nat) ≤ g) :
    runS (Evm.Functions.execute_pc pc_in top g) hs ss =
      .ok ((top + BitVec.ofNat 64 1, g - G_base),
        { hs with stackFrames :=
            writeListAt l top.toNat (pc_in - 1) :: frest }) ss := by
  simp only [Evm.Functions.execute_pc]
  refine runS_bind_ok (runS_charge_ok g G_base hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_word_of_source_byte_count pc_in hs ss hwfpc) ?_
  rw [alu_sub_one pc_in hpos]
  refine runS_bind_ok (runS_push_word top _ hs ss l frest hframe hbound) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_pc_body_oog (pc_in : Nat) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < (G_base : Nat)) :
    runS (Evm.Functions.execute_pc pc_in top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_pc]
  refine runS_bind_ok
    (runS_charge_oog g G_base hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_pc_success (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word))
    (hframe : hs.stackFrames = l :: frest)
    (hwfpc : pc_in < 2 ^ 256) (hpos : 1 ≤ pc_in)
    (hlim : top.toNat + 1 ≤ 1024)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hgas : (G_base : Nat) ≤ g) :
    runS (Evm.Functions.execute (.PC ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top + BitVec.ofNat 64 1, mem, g - G_base),
        { hs with stackFrames :=
            writeListAt l top.toNat (pc_in - 1) :: frest }) ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.PC ()) = pure (0, 1) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 1 hs ss (by omega)
      (by have h : top.toNat - 0 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, pc_dispatch]
  refine runS_bind_ok
    (runS_pc_body_ok pc_in top g hs ss l frest hframe hwfpc hpos hbound
      hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_pc_overflow (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hover : 1024 < top.toNat + 1) :
    runS (Evm.Functions.execute (.PC ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackOverflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.PC ()) = pure (0, 1) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_overflow g top 0 1 hs ss prof sp msg hprof hsp hmsg
      hfork (by omega)
      (by have h : (1024 : Nat) < top.toNat - 0 + 1 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_pc_oog (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hlim : top.toNat + 1 ≤ 1024)
    (hgas : g < (G_base : Nat)) :
    runS (Evm.Functions.execute (.PC ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.PC ()) = pure (0, 1) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 1 hs ss (by omega)
      (by have h : top.toNat - 0 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, pc_dispatch]
  refine runS_bind_ok
    (runS_pc_body_oog pc_in top g hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **PC, all reachable outcomes**: success / stack overflow / OOG / MM-5
double fault. Underflow is impossible for 0-in. `hwfpc` is the
program-counter well-formedness bound both sides need to agree on the
pushed word — the same shape as the other pushers' value bounds. -/
theorem pc_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (hwfpc : WordWf pc_in) :
    StepResultRel (BasePost mem) (runR iPc sRef)
      (runS (Evm.Functions.execute (.PC ()) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  have hgb : (G_base : Nat) = GasCosts.OPCODE_PC := rfl
  have hpos : 1 ≤ pc_in := by omega
  have hval : pc_in - 1 = sRef.evm.pc := by omega
  by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_PC
  · rw [runR_iPc_oog sRef hg]
    by_cases hov : sRef.evm.stack.length = 1024
    · rw [runS_execute_pc_overflow pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.haltedChargeFirst (Or.inr rfl)
        (haltRegs_frame_status ss msg .StackOverflow)
    · rw [runS_execute_pc_oog pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)
        (by rw [hgb, hlive]; exact hg)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
  · push Not at hg
    by_cases hov : sRef.evm.stack.length = 1024
    · rw [runR_iPc_overflow sRef hov hg,
        runS_execute_pc_overflow pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.halted ErrorRel.stackOverflow
        (haltRegs_frame_status ss msg .StackOverflow)
    · have hbound : top.toNat + 1 < 2 ^ 64 := by
        have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
        omega
      rw [runR_iPc_success sRef hov hg,
        runS_execute_pc_success pc_in top g mem hs ss l frest hframe hwfpc
          hpos (by omega) hbound (by rw [hgb, hlive]; exact hg)]
      have hadv : (top + BitVec.ofNat 64 1).toNat = top.toNat + 1 :=
        cursor_advance_toNat top hbound
      refine StepResultRel.success ?_
      refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
        ⟨msg, hmsg⟩⟩, by simp [hpc], rfl⟩
      · refine ⟨⟨writeListAt l top.toNat (pc_in - 1), frest, rfl, ?_, ?_⟩,
          ?_, ?_, ?_⟩
        · rw [hadv, take_writeListAt l top.toNat _ (by omega), hpfx, hval]
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
            have : WordWf pc_in := hwfpc
            unfold WordWf at this ⊢
            omega
          · exact hwfS w hw
      · exact ⟨by rw [hlive, hgb], hres, hsp⟩

end EvmSpecsVerify
