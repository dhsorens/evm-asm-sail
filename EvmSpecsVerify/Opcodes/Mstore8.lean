import EvmSpecsVerify.Relations.Memory
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# MSTORE8

The single-byte [MSTORE](Mstore.lean): pop offset and value, charge
base + expansion for one byte, extend by the ceil32 block, and splice the
masked low byte. The value codec is `word_low_byte` ↔
`BitVec.ofNat 8 (v &&& 0xFF)` (`word_low_byte_masked`); the write goes
through the generic `memoryRel_write` with a singleton list
(`writeArrayBytes_singleton`). Same charge-split equivalence, MM-6 budget
discharge, and grow/in-window split as MSTORE. Reachable outcomes:
success ×2 / underflow ×2 / OOG at either charge; overflow unreachable
(2-in/0-out).
-/

open private pcAdd chargeWithMemory from EvmAsm.Stateless.SpecRef.InstructionsCore
open private writeArrayByte writeArrayBytes zeroMemoryRange from Evm.HostAxioms

set_option maxHeartbeats 4000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- The SpecRef MSTORE8 charge for offset `x` against memory size `msz`. -/
def mstore8Cost (msz x : Nat) : Nat :=
  GasCosts.OPCODE_MSTORE8_BASE
    + (calculate_gas_extend_memory msz [(x, 1)]).cost

/-! ## SpecRef run shapes -/

theorem runR_iMstore8_underflow_nil (s : Machine)
    (hstack : s.evm.stack = []) :
    runR iMstore8 s = .ok (.error .stackUnderflow, s) := by
  simp only [iMstore8]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_iMstore8_underflow_one (s : Machine) (x : U256)
    (hstack : s.evm.stack = [x]) :
    runR iMstore8 s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with stack := [] } }) := by
  simp only [iMstore8]
  refine runR_bind_ok (runR_stackPop_cons s x [] hstack) ?_
  exact runR_bind_err (runR_stackPop_nil _ (by simp))

theorem runR_iMstore8_oog (s : Machine) (x y : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: y :: rest)
    (hgas : s.evm.gasLeft < mstore8Cost s.evm.memory.length x) :
    runR iMstore8 s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [iMstore8, chargeWithMemory]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y rest (by simp)) ?_
  exact runR_bind_err (runR_bind_ok (runR_getEvm_map _ _)
    (runR_bind_err (runR_charge_gas_oog _ _
      (by simpa [mstore8Cost] using hgas))))

theorem runR_iMstore8_success (s : Machine) (x y : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: y :: rest)
    (hgas : mstore8Cost s.evm.memory.length x ≤ s.evm.gasLeft) :
    runR iMstore8 s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := rest
            memory := memory_write
              (s.evm.memory ++ List.replicate
                (calculate_gas_extend_memory s.evm.memory.length
                  [(x, 1)]).expandBy 0x00) x
              [BitVec.ofNat 8 (y &&& 0xFF)]
            gasLeft := s.evm.gasLeft - mstore8Cost s.evm.memory.length x
            regularGasUsed :=
              s.evm.regularGasUsed + mstore8Cost s.evm.memory.length x
            pc := s.evm.pc + 1 } }) := by
  simp only [iMstore8, chargeWithMemory, extendMemory, pcAdd]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y rest (by simp)) ?_
  refine runR_bind_ok (runR_bind_ok (runR_getEvm_map _ _)
    (runR_bind_ok (runR_charge_gas _ _ (by simpa [mstore8Cost] using hgas))
      (runR_modifyEvm _ _))) ?_
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  exact runR_modifyEvm _ _

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for MSTORE8. -/
theorem mstore8_dispatch (pc_in : Nat) (top : StackTop) (off len : Nat)
    (msf : EvmMemorySliceFields off len) (g : Nat) :
    Evm.Functions.execute_opcode (.MSTORE8 ()) pc_in top ⟨off, len, msf⟩ g =
      Evm.Functions.execute_mstore8 top ⟨off, len, msf⟩ g >>= fun p =>
        pure (pc_in, p.1, p.2.1, p.2.2) := rfl

/-- The one-byte required size, in the `WORD_ONE` spelling
`execute_mstore8` produces. -/
theorem memory_required_size_one (x : Nat) :
    Evm.Functions.memory_required_size x Evm.Functions.WORD_ONE
      = x + 1 := rfl

open Evm.Functions in
theorem runS_execute_mstore8_underflow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 2) :
    runS (Evm.Functions.execute (.MSTORE8 ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.MSTORE8 ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 2 0 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_mstore8_oog_base (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hin : 2 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (hgas : g < G_verylow) :
    runS (Evm.Functions.execute (.MSTORE8 ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.MSTORE8 ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss hin
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, mstore8_dispatch]
  have hbody : runS (Evm.Functions.execute_mstore8 top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top, (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_mstore8]
    refine runS_bind_ok
      (runS_charge_oog g G_verylow hs ss prof sp msg hprof hsp hmsg hfork
        hgas) ?_
    rw [dif_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
theorem runS_execute_mstore8_oog_exp (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : Nat) (y : word)
    (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: rest).reverse)
    (htop : top.toNat = (x :: y :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hbase : G_verylow ≤ g)
    (hgas : g - G_verylow
      < Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + 1)) :
    runS (Evm.Functions.execute (.MSTORE8 ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hpfx' : l.take ((top.toNat - 1) + 1) = (x :: y :: rest).reverse := by
    rw [show top.toNat - 1 + 1 = top.toNat from by omega]
    exact hpfx
  have hpfx1 : l.take (top.toNat - 1) = (y :: rest).reverse :=
    take_shrink l _ x _ hpfx' (by simp; omega)
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.MSTORE8 ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, mstore8_dispatch]
  have hbody : runS (Evm.Functions.execute_mstore8 top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_mstore8]
    refine runS_bind_ok (runS_charge_ok g G_verylow hs ss hbase) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (y :: rest) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest y rest hframe
        (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
    rw [memory_required_size_one]
    refine runS_bind_ok
      (runS_charge_oog (g - G_verylow) _ hs ss prof sp msg hprof hsp hmsg
        hfork hgas) ?_
    rw [dif_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
theorem runS_execute_mstore8_ok_grow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : Nat) (y : word)
    (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: rest).reverse)
    (htop : top.toNat = (x :: y :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (mfrest : List Evm.MemoryFrame)
    (hmframe : hs.memoryFrames
      = ({ base := off, established := len } : Evm.MemoryFrame) :: mfrest)
    (hbase : G_verylow ≤ g)
    (hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + 1)
      ≤ g - G_verylow)
    (hreq : x + 1 ≤ 2 ^ 32 - 32)
    (hgrow : len < x + 1) :
    runS (Evm.Functions.execute (.MSTORE8 ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, x + 1, {}⟩ : EvmMemorySlice),
          g - G_verylow
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + 1)),
        { hs with
          memoryBytes := writeArrayByte
            (zeroMemoryRange hs.memoryBytes (off + len) (x + 1 - len))
            (off + x) (Evm.Functions.word_low_byte y)
          memoryFrames :=
            ({ base := off, established := x + 1 } : Evm.MemoryFrame)
              :: mfrest }) ss := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hpfx' : l.take ((top.toNat - 1) + 1) = (x :: y :: rest).reverse := by
    rw [show top.toNat - 1 + 1 = top.toNat from by omega]
    exact hpfx
  have hpfx1 : l.take (top.toNat - 1) = (y :: rest).reverse :=
    take_shrink l _ x _ hpfx' (by simp; omega)
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.MSTORE8 ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, mstore8_dispatch]
  have hbody : runS (Evm.Functions.execute_mstore8 top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, x + 1, {}⟩ : EvmMemorySlice),
          g - G_verylow
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + 1)),
        { hs with
          memoryBytes := writeArrayByte
            (zeroMemoryRange hs.memoryBytes (off + len) (x + 1 - len))
            (off + x) (Evm.Functions.word_low_byte y)
          memoryFrames :=
            ({ base := off, established := x + 1 } : Evm.MemoryFrame)
              :: mfrest }) ss := by
    simp only [Evm.Functions.execute_mstore8]
    refine runS_bind_ok (runS_charge_ok g G_verylow hs ss hbase) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (y :: rest) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest y rest hframe
        (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
    rw [memory_required_size_one]
    refine runS_bind_ok (runS_charge_ok (g - G_verylow) _ hs ss hexp) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_memory_access_ok x 1 hs ss (by decide)
        (show x ≤ 2 ^ 32 - 1 by omega)
        (show (1 : Nat) ≤ 2 ^ 32 - 1 - x by omega)) ?_
    refine runS_bind_ok
      (runS_expand_memory_grow off len (x + 1) msf hs ss len mfrest hmframe
        rfl hgrow) ?_
    refine runS_bind_ok
      (runS_mem_store_byte x y _ ss
        ({ base := off, established := x + 1 } : Evm.MemoryFrame) mfrest
        rfl (le_refl _)) ?_
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
theorem runS_execute_mstore8_ok_nogrow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : Nat) (y : word)
    (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: rest).reverse)
    (htop : top.toNat = (x :: y :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (mfrest : List Evm.MemoryFrame)
    (hmframe : hs.memoryFrames
      = ({ base := off, established := len } : Evm.MemoryFrame) :: mfrest)
    (hbase : G_verylow ≤ g)
    (hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + 1)
      ≤ g - G_verylow)
    (hreq : x + 1 ≤ 2 ^ 32 - 32)
    (hgrow : x + 1 ≤ len) :
    runS (Evm.Functions.execute (.MSTORE8 ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice),
          g - G_verylow
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + 1)),
        { hs with
          memoryBytes := writeArrayByte hs.memoryBytes (off + x)
            (Evm.Functions.word_low_byte y) }) ss := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hpfx' : l.take ((top.toNat - 1) + 1) = (x :: y :: rest).reverse := by
    rw [show top.toNat - 1 + 1 = top.toNat from by omega]
    exact hpfx
  have hpfx1 : l.take (top.toNat - 1) = (y :: rest).reverse :=
    take_shrink l _ x _ hpfx' (by simp; omega)
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.MSTORE8 ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, mstore8_dispatch]
  have hbody : runS (Evm.Functions.execute_mstore8 top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice),
          g - G_verylow
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + 1)),
        { hs with
          memoryBytes := writeArrayByte hs.memoryBytes (off + x)
            (Evm.Functions.word_low_byte y) }) ss := by
    simp only [Evm.Functions.execute_mstore8]
    refine runS_bind_ok (runS_charge_ok g G_verylow hs ss hbase) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (y :: rest) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest y rest hframe
        (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
    rw [memory_required_size_one]
    refine runS_bind_ok (runS_charge_ok (g - G_verylow) _ hs ss hexp) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_memory_access_ok x 1 hs ss (by decide)
        (show x ≤ 2 ^ 32 - 1 by omega)
        (show (1 : Nat) ≤ 2 ^ 32 - 1 - x by omega)) ?_
    refine runS_bind_ok
      (runS_expand_memory_le off len (x + 1) msf hs ss hgrow) ?_
    refine runS_bind_ok
      (runS_mem_store_byte x y hs ss
        ({ base := off, established := len } : Evm.MemoryFrame) mfrest
        hmframe (by omega)) ?_
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

/-! ## The step equivalence -/

open Evm.Functions in
/-- **MSTORE8, all reachable outcomes** (success splits on whether the
frame window grows). Requires the memory relation and the MM-6 gas
budget. -/
theorem mstore8_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (off len : Nat)
    (msf : EvmMemorySliceFields off len) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hmem : MemoryRel sRef.evm.memory hs off len)
    (hsafe : MemGasSafe sRef.evm.memory sRef.evm.gasLeft)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel MemPost (runR iMstore8 sRef)
      (runS (Evm.Functions.execute (.MSTORE8 ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_iMstore8_underflow_nil sRef hS,
      runS_execute_mstore8_underflow pc_in top off len g msf hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | [x] =>
    rw [hS] at hpfx htop
    rw [runR_iMstore8_underflow_one sRef x hS,
      runS_execute_mstore8_underflow pc_in top off len g msf hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | x :: y :: rest =>
    rw [hS] at hpfx htop hlim hwfS
    have hin2 : 2 ≤ top.toNat := by simp at htop; omega
    have hlim' : top.toNat ≤ 1024 := by simp at htop ⊢; simp at hlim; omega
    obtain ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩ := hmem
    have hcost : (calculate_gas_extend_memory sRef.evm.memory.length
        [(x, 1)]).cost
        = Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + 1) := by
      have h1 := extend_cost_eq sRef.evm.memory off len x 1 msf haligned
      rwa [show Evm.Functions.memory_required_size x 1 = x + 1 from rfl]
        at h1
    have hwcM : Evm.Functions.memory_word_count sRef.evm.memory.length
        = Evm.Functions.memory_word_count len := by
      rw [haligned, memory_word_count_eq, memory_word_count_eq]
      omega
    have hexpandBy : ((calculate_gas_extend_memory sRef.evm.memory.length
        [(x, 1)]).expandBy : Nat)
        = 32 * Evm.Functions.memory_word_count (x + 1)
          - sRef.evm.memory.length := by
      have hiff0 : ∀ a b : Nat, (32 * a ≤ 32 * b) ↔ (a ≤ b) :=
        fun a b => by omega
      have hiff : ((ceil32 (x + 1) : Nat) ≤ ceil32 sRef.evm.memory.length)
          ↔ (Evm.Functions.memory_word_count (x + 1)
              ≤ Evm.Functions.memory_word_count len) := by
        rw [ceil32_eq, ceil32_eq, hwcM]
        exact hiff0 _ _
      rw [calc_extend_single]
      rw [if_neg (by decide)]
      by_cases hle : Evm.Functions.memory_word_count (x + 1)
          ≤ Evm.Functions.memory_word_count len
      · rw [if_pos (hiff.mpr hle)]
        show (0 : Nat) = _
        have h1 : 32 * Evm.Functions.memory_word_count (x + 1)
            ≤ sRef.evm.memory.length := by
          rw [haligned]
          omega
        omega
      · rw [if_neg (fun hc => hle (hiff.mp hc))]
        show ((ceil32 (x + 1) : Nat) - ceil32 sRef.evm.memory.length) = _
        rw [ceil32_eq, ceil32_eq, hwcM, ← haligned]
    have hv1 : ([BitVec.ofNat 8 (y &&& 0xFF)] :
        List EvmAsm.EL.RLP.Byte).length = 1 := rfl
    by_cases hg : sRef.evm.gasLeft < mstore8Cost sRef.evm.memory.length x
    · rw [runR_iMstore8_oog sRef x y rest hS hg]
      by_cases hb : g < G_verylow
      · rw [runS_execute_mstore8_oog_base pc_in top off len g msf hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hin2 hlim' hb]
        exact StepResultRel.halted ErrorRel.outOfGas
          (haltRegs_frame_status ss msg .OutOfGas)
      · push Not at hb
        have hbN : (3 : Nat) ≤ g := hb
        have hgg : g < 3 + ((calculate_gas_extend_memory
            sRef.evm.memory.length [(x, 1)]).cost : Nat) := by
          rw [hlive]
          exact hg
        have hb2 : g - G_verylow
            < Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                (x + 1) := by
          rw [← hcost]
          have key : g - 3 < ((calculate_gas_extend_memory
              sRef.evm.memory.length [(x, 1)]).cost : Nat) := by omega
          exact key
        rw [runS_execute_mstore8_oog_exp pc_in top off len g msf hs ss l
          frest x y rest hframe hpfx htop hlim' prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hb hb2]
        exact StepResultRel.halted ErrorRel.outOfGas
          (haltRegs_frame_status ss msg .OutOfGas)
    · push Not at hg
      have hgc : g ≥ 3 + ((calculate_gas_extend_memory
          sRef.evm.memory.length [(x, 1)]).cost : Nat) := by
        rw [hlive]
        exact hg
      have hbase : G_verylow ≤ g := by
        have h3 : (3 : Nat) ≤ g := by omega
        exact h3
      have hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
          (x + 1) ≤ g - G_verylow := by
        rw [← hcost]
        have key : g - 3 ≥ ((calculate_gas_extend_memory
            sRef.evm.memory.length [(x, 1)]).cost : Nat) := by omega
        exact key
      have hreq : x + 1 ≤ 2 ^ 32 - 32 :=
        safe_required_bound sRef.evm.memory off len (x + 1)
          (g - G_verylow) sRef.evm.gasLeft msf haligned hsafe
          (le_trans (Nat.sub_le _ _) (le_of_eq hlive)) hexp
      have hnn : top.toNat = rest.length + 2 := by simpa using htop
      have hll : rest.length + 2 ≤ 1024 := by simpa using hlim
      have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
        cursor_retreat_toNat top (by omega)
      have hret2 : (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1).toNat
          = top.toNat - 2 := by
        rw [cursor_retreat_toNat _ (by rw [hret1]; omega), hret1]
        omega
      have hpfx2 : l.take (top.toNat - 2) = rest.reverse := by
        have hview : l.take (top.toNat - 2) =
            (l.take top.toNat).take (top.toNat - 2) := by
          rw [List.take_take, Nat.min_eq_left (by omega)]
        rw [hview, hpfx]
        have hrl : rest.reverse.length = top.toNat - 2 := by simp; omega
        calc ((x :: y :: rest).reverse).take (top.toNat - 2)
            = (rest.reverse ++ [y, x]).take (top.toNat - 2) := by simp
          _ = rest.reverse := by
              rw [List.take_append_of_le_length (by omega), ← hrl,
                List.take_length]
      rw [runR_iMstore8_success sRef x y rest hS hg]
      have hpost := fun (hs' : Evm.HostState)
          (hframe' : hs'.stackFrames = l :: frest) =>
        (⟨⟨l, frest, hframe', by rw [hret2]; exact hpfx2, by
            rw [hret2]; omega⟩,
          by rw [hret2]; omega,
          by omega,
          fun w hw => hwfS w (by simp [hw])⟩ :
          StackRel rest hs' (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1))
      by_cases hgrow : len < x + 1
      · rw [runS_execute_mstore8_ok_grow pc_in top off len g msf hs ss l
          frest x y rest hframe hpfx htop hlim' mfrest hmframe hbase hexp
          hreq hgrow]
        rw [word_low_byte_masked, ← writeArrayBytes_singleton]
        have hrel' := memoryRel_expand sRef.evm.memory hs off len (x + 1)
          mfrest ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩ hgrow
        have hrelStored := memoryRel_write _ _ off (x + 1) x
          [BitVec.ofNat 8 (y &&& 0xFF)] hrel' (by rw [hv1])
        rw [hexpandBy]
        refine StepResultRel.success ?_
        refine ⟨⟨hpost _ hframe, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
          ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, by simp [hpc], ?_⟩
        · refine ⟨?_, hres, hsp⟩
          rw [← hcost, hlive]
          have key : ∀ a c : Nat, a - 3 - c = a - (3 + c) :=
            fun a c => by omega
          exact key _ _
        · refine ⟨off, x + 1, {}, rfl, ?_, ?_⟩
          · exact ⟨hrelStored.frame, hrelStored.aligned, hrelStored.bytes,
              hrelStored.tail⟩
          · show MemGasSafe _ (sRef.evm.gasLeft - mstore8Cost
              sRef.evm.memory.length x)
            have hsafe2 := memGasSafe_after_expand sRef.evm.memory off len
              (x + 1) sRef.evm.gasLeft
              (mstore8Cost sRef.evm.memory.length x) msf haligned hsafe
              (by rw [← hcost]
                  have key : ∀ c : Nat, c ≤ 3 + c := fun c => by omega
                  exact key _) hg
            unfold MemGasSafe at hsafe2 ⊢
            rw [memory_write_length _ _ _ (by
              rw [hv1]
              simp only [List.length_append, List.length_replicate]
              have h32 := le_32_wc (x + 1)
              have hwc := wc_mono (Nat.le_of_lt hgrow)
              have hal := haligned
              omega)]
            exact hsafe2
      · push Not at hgrow
        rw [runS_execute_mstore8_ok_nogrow pc_in top off len g msf hs ss l
          frest x y rest hframe hpfx htop hlim' mfrest hmframe hbase hexp
          hreq hgrow]
        rw [word_low_byte_masked, ← writeArrayBytes_singleton]
        have hrelStored := memoryRel_write sRef.evm.memory hs off len x
          [BitVec.ofNat 8 (y &&& 0xFF)]
          ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩
          (by rw [hv1]; exact hgrow)
        have hzero : (0 : Nat) = (calculate_gas_extend_memory
            sRef.evm.memory.length [(x, 1)]).expandBy := by
          rw [hexpandBy]
          have hwc := wc_mono hgrow
          have hal := haligned
          rw [memory_word_count_eq] at hwc hal ⊢
          omega
        rw [← hzero]
        rw [show List.replicate 0 (0x00 : EvmAsm.EL.RLP.Byte) = [] from rfl,
          List.append_nil]
        refine StepResultRel.success ?_
        refine ⟨⟨hpost _ hframe, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
          ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, by simp [hpc], ?_⟩
        · refine ⟨?_, hres, hsp⟩
          rw [← hcost, hlive]
          have key : ∀ a c : Nat, a - 3 - c = a - (3 + c) :=
            fun a c => by omega
          exact key _ _
        · refine ⟨off, len, msf, rfl, ?_, ?_⟩
          · exact ⟨hrelStored.frame, hrelStored.aligned, hrelStored.bytes,
              hrelStored.tail⟩
          · show MemGasSafe _ (sRef.evm.gasLeft - mstore8Cost
              sRef.evm.memory.length x)
            have hsafe2 := memGasSafe_mono_gas sRef.evm.memory
              (g' := sRef.evm.gasLeft
                - mstore8Cost sRef.evm.memory.length x)
              (Nat.sub_le _ _) hsafe
            unfold MemGasSafe at hsafe2 ⊢
            rw [memory_write_length _ _ _ (by
              rw [hv1]
              have h32 := le_32_wc len
              have hal := haligned
              omega)]
            exact hsafe2

end EvmSpecsVerify
