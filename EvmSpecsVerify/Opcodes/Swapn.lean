import EvmSpecsVerify.Opcodes.Dupn
import EvmSpecsVerify.Opcodes.Swap

/-!
# SWAPN

The immediate-carrying sibling of [`SWAP`](Swap.lean), and the second
consumer of [`DUPN`](Dupn.lean)'s immediate decoder. It is a genuine
harvest in both directions:

* the *decoder* half comes from DUPN — `decode_single` is shared by both
  opcodes (its error message even names both), so `dupnIndex`,
  `decode_single_agree`/`_invalid` and `runS_decode_single_stack_index`
  are reused verbatim;
* the *permutation* half comes from SWAP — `execute_swapn`'s tail is
  byte-for-byte `execute_swap`'s (`peek 0`, `peek n`, `stack_set 0`,
  `stack_set n`), so `take_swap_writes`, `listSwap_mem`/`_length` and
  `swapHost` carry over unchanged.

What is new is only the layering: SpecRef charges, *then* decodes, while
the extraction validates the immediate, *then* charges, *then* decodes —
so both MM-10 divergences recur here exactly as for DUPN, and the
`.invalidParameter "DUPN/SWAPN immediate out of range"` message is
literally the same string.

Overflow is unreachable, as for SWAP: `opcode_stack_effect (.SWAPN imm)`
is `(n + 1, n + 1)` for a valid immediate, so the post-height is the
pre-height. With an invalid immediate it is `(0, 0)`, so `validate_stack`
waves the step through and `execute_swapn`'s own check halts.

Reachable outcomes: success / invalid immediate / underflow / OOG, plus
the MM-5 and MM-10 double faults.

Gas (MM-2): `GasCosts.OPCODE_SWAPN = 3 = G_verylow`.
-/

open private pcAdd listSwap from EvmAsm.Stateless.SpecRef.InstructionsCore
open private writeListAt from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## SpecRef run shapes (`b` is the immediate byte) -/

theorem runR_iSwapn_oog (s : Machine)
    (hgas : s.evm.gasLeft < GasCosts.OPCODE_SWAPN) :
    runR iSwapn s = .ok (.error .outOfGas, s) := by
  simp only [iSwapn]
  exact runR_bind_err (runR_charge_gas_oog _ _ (by simpa using hgas))

/-- MM-10: the invalid-immediate throw fires **after** the charge. -/
theorem runR_iSwapn_invalid (s : Machine) (why : String)
    (hdec : decode_single (immByte s) = .error (.invalidParameter why))
    (hgas : GasCosts.OPCODE_SWAPN ≤ s.evm.gasLeft) :
    runR iSwapn s =
      .ok (.error (.invalidParameter why),
        { s with evm := { s.evm with
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_SWAPN
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_SWAPN } }) := by
  simp only [immByte] at hdec
  simp only [iSwapn]
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [hdec]
  exact runR_bind_err (runR_throw _ _)

theorem runR_iSwapn_underflow (s : Machine) (n : Nat)
    (hdec : decode_single (immByte s) = .ok n)
    (hn : s.evm.stack.length < n + 1)
    (hgas : GasCosts.OPCODE_SWAPN ≤ s.evm.gasLeft) :
    runR iSwapn s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_SWAPN
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_SWAPN } }) := by
  simp only [immByte] at hdec
  simp only [iSwapn]
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [hdec]
  refine runR_bind_ok (runR_pure _ _) ?_
  rw [if_pos (by show n + 1 > s.evm.stack.length; omega)]
  exact runR_bind_err (runR_throw _ _)

theorem runR_iSwapn_success (s : Machine) (n : Nat)
    (hdec : decode_single (immByte s) = .ok n)
    (hn : n + 1 ≤ s.evm.stack.length)
    (hgas : GasCosts.OPCODE_SWAPN ≤ s.evm.gasLeft) :
    runR iSwapn s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := listSwap s.evm.stack 0 n
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_SWAPN
            regularGasUsed := s.evm.regularGasUsed + GasCosts.OPCODE_SWAPN
            pc := s.evm.pc + 2 } }) := by
  simp only [immByte] at hdec
  simp only [iSwapn, pcAdd]
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [hdec]
  refine runR_bind_ok (runR_pure _ _) ?_
  rw [if_neg (by show ¬(n + 1 > s.evm.stack.length); omega)]
  refine runR_bind_ok (runR_pure _ _) ?_
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  exact runR_modifyEvm _ _

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for SWAPN. -/
theorem swapn_dispatch (b : BitVec 8) (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_opcode (.SWAPN b) pc_in top mem g =
      Evm.Functions.execute_swapn b top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
/-- Unlike DUPN's `(n, n + 1)`, SWAPN's effect is height-preserving. -/
theorem runS_stack_effect_swapn_valid (b : BitVec 8) (hs : Evm.HostState)
    (ss : SeqState)
    (hv : Evm.Functions.deep_stack_immediate_valid b = true) :
    runS (Evm.Functions.opcode_stack_effect (.SWAPN b)) hs ss =
      .ok ((dupnIndex b + 1, dupnIndex b + 1), hs) ss := by
  simp only [Evm.Functions.opcode_stack_effect, hv]
  refine runS_bind_ok (runS_decode_single_stack_index b hs ss hv) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_stack_effect_swapn_invalid (b : BitVec 8) (hs : Evm.HostState)
    (ss : SeqState)
    (hv : Evm.Functions.deep_stack_immediate_valid b = false) :
    runS (Evm.Functions.opcode_stack_effect (.SWAPN b)) hs ss =
      .ok ((0, 0), hs) ss := by
  simp only [Evm.Functions.opcode_stack_effect, hv]
  exact runS_pure _ _ _

open Evm.Functions in
/-- MM-10: the immediate check runs **before** the charge, so the halt
carries the frame's full gas into `exc_halt`. -/
theorem runS_swapn_body_invalid (b : BitVec 8) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hv : Evm.Functions.deep_stack_immediate_valid b = false) :
    runS (Evm.Functions.execute_swapn b top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .InvalidOpcode } := by
  simp only [Evm.Functions.execute_swapn, hv]
  rw [if_pos (by simp)]
  refine runS_bind_ok
    (runS_exc_halt g .InvalidOpcode hs ss prof sp msg hprof hsp hmsg
      hfork) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_swapn_body_oog (b : BitVec 8) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hv : Evm.Functions.deep_stack_immediate_valid b = true)
    (hgas : g < G_verylow) :
    runS (Evm.Functions.execute_swapn b top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_swapn, hv]
  rw [if_neg (by simp)]
  refine runS_bind_ok
    (runS_charge_oog g G_verylow hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
/-- The tail is `execute_swap`'s, so `swapHost` describes the result. -/
theorem runS_swapn_body_ok (b : BitVec 8) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (S : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = S.reverse)
    (htop : top.toNat = S.length)
    (hv : Evm.Functions.deep_stack_immediate_valid b = true)
    (hnt : dupnIndex b < S.length) (hn : 0 < dupnIndex b)
    (hlen : top.toNat ≤ l.length)
    (hgas : G_verylow ≤ g) :
    runS (Evm.Functions.execute_swapn b top g) hs ss =
      .ok ((top, g - G_verylow),
        swapHost hs l frest top.toNat (dupnIndex b)
          (S.getD (dupnIndex b) default) (S.getD 0 default)) ss := by
  have hset1 : writeListAt l (top.toNat - 1) (S.getD (dupnIndex b) default)
      = l.set (top.toNat - 1) (S.getD (dupnIndex b) default) :=
    writeListAt_eq_set l _ _ (by omega)
  have hset2 : writeListAt
        (l.set (top.toNat - 1) (S.getD (dupnIndex b) default))
        (top.toNat - 1 - dupnIndex b) (S.getD 0 default)
      = (l.set (top.toNat - 1) (S.getD (dupnIndex b) default)).set
          (top.toNat - 1 - dupnIndex b) (S.getD 0 default) :=
    writeListAt_eq_set _ _ _ (by simp; omega)
  simp only [Evm.Functions.execute_swapn, hv]
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_charge_ok g G_verylow hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_decode_single_stack_index b hs ss hv) ?_
  refine runS_bind_ok
    (runS_peek top 0 hs ss l frest S hframe hpfx htop (by omega)) ?_
  refine runS_bind_ok
    (runS_peek top (dupnIndex b) hs ss l frest S hframe hpfx htop hnt) ?_
  refine runS_bind_ok
    (runS_stack_set top 0 (S.getD (dupnIndex b) default) hs ss l frest
      hframe) ?_
  refine runS_bind_ok
    (runS_stack_set top (dupnIndex b) (S.getD 0 default) _ ss
      (writeListAt l (top.toNat - 1) (S.getD (dupnIndex b) default)) frest
      rfl) ?_
  rw [hset1, hset2]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_swapn_invalid (b : BitVec 8) (pc_in : Nat)
    (top : StackTop) (g : Nat) (mem : EvmMemorySlice)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hlim : top.toNat ≤ 1024)
    (hv : Evm.Functions.deep_stack_immediate_valid b = false) :
    runS (Evm.Functions.execute (.SWAPN b) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .InvalidOpcode } := by
  simp only [Evm.Functions.execute]
  refine runS_bind_ok (runS_stack_effect_swapn_invalid b hs ss hv) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 0 hs ss (by omega)
      (by simpa [Evm.Functions.STACK_LIMIT] using hlim)) ?_
  rw [dif_pos rfl, swapn_dispatch]
  refine runS_bind_ok
    (runS_swapn_body_invalid b top g hs ss prof sp msg hprof hsp hmsg hfork
      hv) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_swapn_underflow (b : BitVec 8) (pc_in : Nat)
    (top : StackTop) (g : Nat) (mem : EvmMemorySlice)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hv : Evm.Functions.deep_stack_immediate_valid b = true)
    (hunder : top.toNat < dupnIndex b + 1) :
    runS (Evm.Functions.execute (.SWAPN b) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute]
  refine runS_bind_ok (runS_stack_effect_swapn_valid b hs ss hv) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top (dupnIndex b + 1)
      (dupnIndex b + 1) hs ss prof sp msg hprof hsp hmsg hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_swapn_oog (b : BitVec 8) (pc_in : Nat)
    (top : StackTop) (g : Nat) (mem : EvmMemorySlice)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hv : Evm.Functions.deep_stack_immediate_valid b = true)
    (hin : dupnIndex b + 1 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (hgas : g < G_verylow) :
    runS (Evm.Functions.execute (.SWAPN b) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute]
  refine runS_bind_ok (runS_stack_effect_swapn_valid b hs ss hv) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top (dupnIndex b + 1) (dupnIndex b + 1) hs ss
      hin
      (by have h : top.toNat - (dupnIndex b + 1) + (dupnIndex b + 1) ≤ 1024 :=
            by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, swapn_dispatch]
  refine runS_bind_ok
    (runS_swapn_body_oog b top g hs ss prof sp msg hprof hsp hmsg hfork hv
      hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_swapn_success (b : BitVec 8) (pc_in : Nat)
    (top : StackTop) (g : Nat) (mem : EvmMemorySlice)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (S : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = S.reverse)
    (htop : top.toNat = S.length)
    (hv : Evm.Functions.deep_stack_immediate_valid b = true)
    (hnt : dupnIndex b < S.length) (hn : 0 < dupnIndex b)
    (hlen : top.toNat ≤ l.length)
    (hlim : top.toNat ≤ 1024)
    (hgas : G_verylow ≤ g) :
    runS (Evm.Functions.execute (.SWAPN b) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, g - G_verylow),
        swapHost hs l frest top.toNat (dupnIndex b)
          (S.getD (dupnIndex b) default) (S.getD 0 default)) ss := by
  simp only [Evm.Functions.execute]
  refine runS_bind_ok (runS_stack_effect_swapn_valid b hs ss hv) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top (dupnIndex b + 1) (dupnIndex b + 1) hs ss
      (by omega)
      (by have h : top.toNat - (dupnIndex b + 1) + (dupnIndex b + 1) ≤ 1024 :=
            by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, swapn_dispatch]
  refine runS_bind_ok
    (runS_swapn_body_ok b top g hs ss l frest S hframe hpfx htop hv hnt hn
      hlen hgas) ?_
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **SWAPN, all reachable outcomes**: success / invalid immediate /
underflow / OOG, plus the MM-5 and MM-10 double faults. Overflow is
unreachable (height-preserving, as for SWAP). `himm` and `hpc` are DUPN's
hypotheses unchanged. -/
theorem swapn_step_equiv (b : BitVec 8)
    (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 2)
    (himm : immByte sRef = b.toNat) :
    StepResultRel (BasePost mem) (runR iSwapn sRef)
      (runS (Evm.Functions.execute (.SWAPN b) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  by_cases hv : Evm.Functions.deep_stack_immediate_valid b = true
  · have hdec : decode_single (immByte sRef) = .ok (dupnIndex b) := by
      rw [himm]; exact decode_single_agree b hv
    have hn1 : 1 ≤ dupnIndex b := dupnIndex_pos b hv
    by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_SWAPN
    · rw [runR_iSwapn_oog sRef hg]
      by_cases hu : sRef.evm.stack.length < dupnIndex b + 1
      · rw [runS_execute_swapn_underflow b pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hv (by omega)]
        exact StepResultRel.haltedChargeFirst (Or.inl rfl)
          (haltRegs_frame_status ss msg .StackUnderflow)
      · rw [runS_execute_swapn_oog b pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hv (by omega)
          (by omega) (by rw [hlive]; exact hg)]
        exact StepResultRel.halted ErrorRel.outOfGas
          (haltRegs_frame_status ss msg .OutOfGas)
    · push Not at hg
      by_cases hu : sRef.evm.stack.length < dupnIndex b + 1
      · rw [runR_iSwapn_underflow sRef (dupnIndex b) hdec hu hg,
          runS_execute_swapn_underflow b pc_in top g mem hs ss prof
            sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hv
            (by omega)]
        exact StepResultRel.halted ErrorRel.stackUnderflow
          (haltRegs_frame_status ss msg .StackUnderflow)
      · rw [runR_iSwapn_success sRef (dupnIndex b) hdec (by omega) hg,
          runS_execute_swapn_success b pc_in top g mem hs ss l frest
            sRef.evm.stack hframe hpfx htop hv (by omega) hn1 hlen
            (by omega) (by rw [hlive]; exact hg)]
        refine StepResultRel.success ?_
        refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
          ⟨msg, hmsg⟩⟩, by simp [hpc], rfl⟩
        · refine ⟨⟨(l.set (top.toNat - 1)
                (sRef.evm.stack.getD (dupnIndex b) default)).set
                (top.toNat - 1 - dupnIndex b)
                (sRef.evm.stack.getD 0 default),
              frest, rfl, ?_, ?_⟩, ?_, ?_, ?_⟩
          · exact take_swap_writes l sRef.evm.stack top.toNat (dupnIndex b)
              hpfx htop hn1 (by omega) hlen
          · simp
            omega
          · rw [listSwap_length]
            exact htop
          · rw [listSwap_length]
            exact hlim
          · intro w hw
            exact hwfS w
              (listSwap_mem sRef.evm.stack top.toNat (dupnIndex b) htop hn1
                (by omega) hw)
        · exact ⟨by
            simp [hlive, Evm.Functions.G_verylow, GasCosts.OPCODE_SWAPN],
            hres, hsp⟩
  · have hv' : Evm.Functions.deep_stack_immediate_valid b = false := by
      simpa using hv
    have hdec : decode_single (immByte sRef)
        = .error (.invalidParameter
            "DUPN/SWAPN immediate out of range") := by
      rw [himm]; exact decode_single_invalid b hv'
    have hlim' : top.toNat ≤ 1024 := by omega
    by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_SWAPN
    · rw [runR_iSwapn_oog sRef hg,
        runS_execute_swapn_invalid b pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hlim' hv']
      exact StepResultRel.haltedChargeFirst (Or.inr (Or.inr rfl))
        (haltRegs_frame_status ss msg .InvalidOpcode)
    · push Not at hg
      rw [runR_iSwapn_invalid sRef _ hdec hg,
        runS_execute_swapn_invalid b pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hlim' hv']
      exact StepResultRel.halted (ErrorRel.invalidParameter _)
        (haltRegs_frame_status ss msg .InvalidOpcode)

end EvmSpecsVerify
