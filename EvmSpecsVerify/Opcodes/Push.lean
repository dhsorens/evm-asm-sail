import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# PUSH0–PUSH32

`iPushN n` (dispatched as `iPushN (op - 0x5F)`) reads its immediate from the
frame code itself (`buffer_read` at `pc + 1`, zero-padded); the extraction
decodes the immediate in `fetch` and passes it as the `.PUSH (n, v)` AST
payload. The theorem therefore takes the **decode-fidelity hypothesis**
`hv : v = bytesBEtoNat (buffer_read code (pc+1) n)` — fetch-level equivalence
is out of scope while SpecRef dispatch is `partial` (mismatch ledger MM-3) —
and the MM-4 pc hypothesis generalizes to `pc_in = pc + (1 + n)` (fetch
advances past the immediate too).

Charge-first handler (MM-5): on double-fault states (full stack ∧ OOG)
SpecRef reports `outOfGas` where the extraction reports `StackOverflow` —
related via `StepResultRel.haltedChargeFirst`. Reachable outcomes: success /
overflow / OOG (underflow unreachable for 0-in/1-out).
-/

open private pcAdd from EvmAsm.Stateless.SpecRef.InstructionsCore
open private writeListAt from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- The PUSH charge: 2 for PUSH0, 3 otherwise (both sides agree; MM-2). -/
def pushCost (n : Nat) : Nat :=
  if n == 0 then GasCosts.OPCODE_PUSH0 else GasCosts.OPCODE_PUSH

/-- `buffer_read` zero-pads to exactly `size` bytes. -/
theorem buffer_read_length (buf : Bytes) (p n : Nat) :
    (buffer_read buf p n).length = n := by
  simp only [buffer_read, List.length_append, List.length_replicate]
  have h : ((buf.drop p).take n).length ≤ n := by
    simp [List.length_take]
  omega

/-- A ≤32-byte code immediate decodes to a well-formed word. -/
theorem pushVal_wf (buf : Bytes) (p n : Nat) (hn : n ≤ 32) :
    WordWf (bytesBEtoNat (buffer_read buf p n)) := by
  unfold WordWf
  have h := EvmAsm.EL.RLP.Nat.fromBytesBE_lt (buffer_read buf p n)
  rw [buffer_read_length] at h
  calc bytesBEtoNat (buffer_read buf p n) < 256 ^ n := h
    _ ≤ 256 ^ 32 := Nat.pow_le_pow_right (by omega) hn
    _ = 2 ^ 256 := by decide

/-! ## SpecRef run shapes -/

theorem runR_iPushN_success (s : Machine) (n : Nat)
    (hlen : s.evm.stack.length ≠ 1024)
    (hgas : pushCost n ≤ s.evm.gasLeft) :
    runR (iPushN n) s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := bytesBEtoNat (buffer_read s.evm.code (s.evm.pc + 1) n)
              :: s.evm.stack
            gasLeft := s.evm.gasLeft - pushCost n
            regularGasUsed := s.evm.regularGasUsed + pushCost n
            pc := s.evm.pc + (1 + n) } }) := by
  simp only [iPushN, pcAdd, pushCost]
  refine runR_bind_ok (runR_charge_gas _ _
    (by simpa [pushCost] using hgas)) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_stackPush _ _
    (by show s.evm.stack.length ≠ 1024; exact hlen)) ?_
  exact runR_modifyEvm _ _

theorem runR_iPushN_overflow (s : Machine) (n : Nat)
    (hlen : s.evm.stack.length = 1024)
    (hgas : pushCost n ≤ s.evm.gasLeft) :
    runR (iPushN n) s =
      .ok (.error .stackOverflow,
        { s with evm := { s.evm with
            gasLeft := s.evm.gasLeft - pushCost n
            regularGasUsed := s.evm.regularGasUsed + pushCost n } }) := by
  simp only [iPushN, pushCost]
  refine runR_bind_ok (runR_charge_gas _ _
    (by simpa [pushCost] using hgas)) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  exact runR_bind_err (runR_stackPush_overflow _ _
    (by show s.evm.stack.length = 1024; exact hlen))

/-- OOG fires at the leading charge, before the push (MM-5). -/
theorem runR_iPushN_oog (s : Machine) (n : Nat)
    (hgas : s.evm.gasLeft < pushCost n) :
    runR (iPushN n) s = .ok (.error .outOfGas, s) := by
  simp only [iPushN]
  exact runR_bind_err (runR_charge_gas_oog _ _
    (by simpa [pushCost] using hgas))

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for the PUSH family. -/
theorem push_dispatch (n v : Nat) (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_opcode (.PUSH (n, v)) pc_in top mem g =
      Evm.Functions.execute_push n v top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
/-- Both sides of `execute_push`'s PUSH0 split have the same charge-push
shape; `evmPushCost` names the split cost. -/
theorem evmPushCost_eq (n : Nat) :
    (if (n == 0 : Bool) then G_base else G_verylow) = pushCost n := by
  unfold pushCost
  split <;> rfl

open Evm.Functions in
theorem runS_push_body_ok (n v : Nat) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word))
    (hframe : hs.stackFrames = l :: frest)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hgas : pushCost n ≤ g) :
    runS (Evm.Functions.execute_push n v top g) hs ss =
      .ok ((top + BitVec.ofNat 64 1, g - pushCost n),
        { hs with stackFrames := writeListAt l top.toNat v :: frest }) ss := by
  simp only [Evm.Functions.execute_push]
  by_cases h0 : (n == 0) = true
  · rw [if_pos h0, show pushCost n = G_base from by simp [pushCost, h0, GasCosts.OPCODE_PUSH0, Evm.Functions.G_base]]
    refine runS_bind_ok (runS_charge_ok g G_base hs ss
      (by rw [show (G_base : Nat) = pushCost n from by simp [pushCost, h0, GasCosts.OPCODE_PUSH0, Evm.Functions.G_base]]
          exact hgas)) ?_
    rw [if_neg (by simp)]
    refine runS_bind_ok (runS_push_word top v hs ss l frest hframe hbound) ?_
    exact runS_pure _ _ _
  · rw [if_neg h0, show pushCost n = G_verylow from by simp [pushCost, h0, GasCosts.OPCODE_PUSH, Evm.Functions.G_verylow]]
    refine runS_bind_ok (runS_charge_ok g G_verylow hs ss
      (by rw [show (G_verylow : Nat) = pushCost n from by simp [pushCost, h0, GasCosts.OPCODE_PUSH, Evm.Functions.G_verylow]]
          exact hgas)) ?_
    rw [if_neg (by simp)]
    refine runS_bind_ok (runS_push_word top v hs ss l frest hframe hbound) ?_
    exact runS_pure _ _ _

open Evm.Functions in
theorem runS_push_body_oog (n v : Nat) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < pushCost n) :
    runS (Evm.Functions.execute_push n v top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_push]
  by_cases h0 : (n == 0) = true
  · rw [if_pos h0]
    refine runS_bind_ok (runS_charge_oog g G_base hs ss prof sp msg hprof hsp
      hmsg hfork (by rw [show (G_base : Nat) = pushCost n from by
        simp [pushCost, h0, GasCosts.OPCODE_PUSH0, Evm.Functions.G_base]]; exact hgas)) ?_
    rw [if_pos (by simp)]
    exact runS_pure _ _ _
  · rw [if_neg h0]
    refine runS_bind_ok (runS_charge_oog g G_verylow hs ss prof sp msg hprof
      hsp hmsg hfork (by rw [show (G_verylow : Nat) = pushCost n from by
        simp [pushCost, h0, GasCosts.OPCODE_PUSH, Evm.Functions.G_verylow]]; exact hgas)) ?_
    rw [if_pos (by simp)]
    exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_push_success (n v : Nat) (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word))
    (hframe : hs.stackFrames = l :: frest)
    (hlim : top.toNat + 1 ≤ 1024)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hgas : pushCost n ≤ g) :
    runS (Evm.Functions.execute (.PUSH (n, v)) pc_in top mem g) hs ss =
      .ok ((pc_in, top + BitVec.ofNat 64 1, mem, g - pushCost n),
        { hs with stackFrames := writeListAt l top.toNat v :: frest }) ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.PUSH (n, v)) = pure (0, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 1 hs ss (by omega)
      (by have h : top.toNat - 0 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, push_dispatch]
  refine runS_bind_ok
    (runS_push_body_ok n v top g hs ss l frest hframe hbound hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_push_overflow (n v : Nat) (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hover : 1024 < top.toNat + 1) :
    runS (Evm.Functions.execute (.PUSH (n, v)) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackOverflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.PUSH (n, v)) = pure (0, 1)
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
theorem runS_execute_push_oog (n v : Nat) (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hlim : top.toNat + 1 ≤ 1024)
    (hgas : g < pushCost n) :
    runS (Evm.Functions.execute (.PUSH (n, v)) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.PUSH (n, v)) = pure (0, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 1 hs ss (by omega)
      (by have h : top.toNat - 0 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, push_dispatch]
  refine runS_bind_ok
    (runS_push_body_oog n v top g hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **PUSHn, all reachable outcomes**, under the decode-fidelity hypothesis
`hv` (the fetched immediate is SpecRef's zero-padded code read) and the
immediate-extended MM-4 pc hypothesis. Double-fault states (full stack ∧ OOG)
use the MM-5 constructor. -/
theorem push_step_equiv (n v : Nat) (hn32 : n ≤ 32)
    (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + (1 + n))
    (hv : v = bytesBEtoNat (buffer_read sRef.evm.code (sRef.evm.pc + 1) n)) :
    StepResultRel (AluPost mem) (runR (iPushN n) sRef)
      (runS (Evm.Functions.execute (.PUSH (n, v)) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  by_cases hg : sRef.evm.gasLeft < pushCost n
  · rw [runR_iPushN_oog sRef n hg]
    by_cases hov : sRef.evm.stack.length = 1024
    · rw [runS_execute_push_overflow n v pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.haltedChargeFirst (Or.inr rfl)
        (haltRegs_frame_status ss msg .StackOverflow)
    · rw [runS_execute_push_oog n v pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)
        (by rw [hlive]; exact hg)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
  · push Not at hg
    by_cases hov : sRef.evm.stack.length = 1024
    · rw [runR_iPushN_overflow sRef n hov hg,
        runS_execute_push_overflow n v pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.halted ErrorRel.stackOverflow
        (haltRegs_frame_status ss msg .StackOverflow)
    · have hbound : top.toNat + 1 < 2 ^ 64 := by
        have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
        omega
      rw [runR_iPushN_success sRef n hov hg,
        runS_execute_push_success n v pc_in top g mem hs ss l frest hframe
          (by omega) hbound (by rw [hlive]; exact hg)]
      have hadv : (top + BitVec.ofNat 64 1).toNat = top.toNat + 1 :=
        cursor_advance_toNat top hbound
      refine StepResultRel.success ?_
      refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
        ⟨msg, hmsg⟩⟩, by simp [hpc], rfl⟩
      · refine ⟨⟨writeListAt l top.toNat v, frest, rfl, ?_, ?_⟩, ?_, ?_, ?_⟩
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
            exact pushVal_wf sRef.evm.code (sRef.evm.pc + 1) n hn32
          · exact hwfS w hw
      · exact ⟨by rw [hlive], hres, hsp⟩

end EvmSpecsVerify
