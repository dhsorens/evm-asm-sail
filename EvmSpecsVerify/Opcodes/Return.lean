import EvmSpecsVerify.Relations.Memory
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# RETURN

First normal halt. `iReturn` pops offset and size, charges the expansion
(base `ZERO`), extends, and sets `output` + `running := false` — monadically
still a **success** (`.ok (.ok ())`), so no new `StepResultRel` constructor
is needed: the halt lives in the states, related by the RETURN-specific
[`ReturnPost`](#ReturnPost) (normal-halt status with matching output bytes,
remaining gas, and state-gas registers; the discarded stack/pc/memory are
not frame-boundary observable). The extraction copies the returned window
into the host output buffer (`freeze_memory_output`) and sets
`frame_status := Halted (HaltReturn …)`.

Sub-shapes: the size-zero return skips expansion and charge entirely on
both sides (OOG unreachable there) and produces the empty output slice.
Reachable outcomes: success (zero / grow / in-window) / underflow ×2 / OOG
on the expansion charge (size ≠ 0 only).
-/

open private chargeWithMemory from EvmAsm.Stateless.SpecRef.InstructionsCore
open private writeArrayBytes wordBytes zeroMemoryRange readArrayBytes
  memoryBytesOf from Evm.HostAxioms

set_option maxHeartbeats 4000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- The SpecRef RETURN charge (`ZERO` base + expansion). -/
def returnCost (msz x y : Nat) : Nat :=
  GasCosts.ZERO + (calculate_gas_extend_memory msz [(x, y)]).cost

/-- The success post for RETURN: both sides halted normally, with the
same output bytes, remaining gas, and state-gas registers. A halted
frame's stack, pc, and memory are not observable past the frame
boundary. -/
def ReturnPost (sR' : Machine) (step : EvmStep)
    (hs' : Evm.HostState) (ss' : SeqState) : Prop :=
  sR'.evm.running = false ∧
  step.2.2.2 = sR'.evm.gasLeft ∧
  ss'.regs.get? Register.state_gas_remaining
    = some sR'.evm.stateGasLeft ∧
  ss'.regs.get? Register.state_gas_spilled
    = some sR'.evm.stateGasSpilled ∧
  ∃ (oo ol : Nat) (osf : OutputSliceFields oo ol),
    ss'.regs.get? Register.frame_status
      = some (FrameStatus.Halted (HaltKind.HaltReturn ⟨oo, ol, osf⟩)) ∧
    ol = sR'.evm.output.length ∧
    ∀ i, i < ol → hs'.outputBytes.getD (oo + i) 0
      = sR'.evm.output.getD i 0

/-- The frame status a successful RETURN writes. -/
def returnedStatus (oo ol : Nat) (osf : OutputSliceFields oo ol) :
    FrameStatus :=
  FrameStatus.Halted (HaltKind.HaltReturn ⟨oo, ol, osf⟩)

theorem memory_required_size_zero (x : Nat) :
    Evm.Functions.memory_required_size x (Evm.Functions.u256 0) = 0 := rfl

theorem memory_required_size_ne (x y : Nat) (hy : (y == 0) = false) :
    Evm.Functions.memory_required_size x y = x + y := by
  unfold Evm.Functions.memory_required_size
  rw [if_neg (by simp [hy])]

/-! ## SpecRef run shapes -/

theorem runR_iReturn_underflow_nil (s : Machine)
    (hstack : s.evm.stack = []) :
    runR iReturn s = .ok (.error .stackUnderflow, s) := by
  simp only [iReturn]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_iReturn_underflow_one (s : Machine) (x : U256)
    (hstack : s.evm.stack = [x]) :
    runR iReturn s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with stack := [] } }) := by
  simp only [iReturn]
  refine runR_bind_ok (runR_stackPop_cons s x [] hstack) ?_
  exact runR_bind_err (runR_stackPop_nil _ (by simp))

theorem runR_iReturn_oog (s : Machine) (x y : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: y :: rest)
    (hgas : s.evm.gasLeft < returnCost s.evm.memory.length x y) :
    runR iReturn s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [iReturn]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y rest (by simp)) ?_
  refine runR_bind_ok (runR_getEvm_map _ _) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _
    (by simpa [returnCost] using hgas))

theorem runR_iReturn_success (s : Machine) (x y : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: y :: rest)
    (hgas : returnCost s.evm.memory.length x y ≤ s.evm.gasLeft) :
    runR iReturn s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := rest
            memory := s.evm.memory ++ List.replicate
              (calculate_gas_extend_memory s.evm.memory.length
                [(x, y)]).expandBy 0x00
            output := memory_read_bytes
              (s.evm.memory ++ List.replicate
                (calculate_gas_extend_memory s.evm.memory.length
                  [(x, y)]).expandBy 0x00) x y
            running := false
            gasLeft := s.evm.gasLeft - returnCost s.evm.memory.length x y
            regularGasUsed :=
              s.evm.regularGasUsed
                + returnCost s.evm.memory.length x y } }) := by
  simp only [iReturn, extendMemory]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y rest (by simp)) ?_
  refine runR_bind_ok (runR_getEvm_map _ _) ?_
  refine runR_bind_ok (runR_charge_gas _ _
    (by simpa [returnCost] using hgas)) ?_
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  exact runR_modifyEvm _ _


/-! ## `Evm` run shapes: expand/slice/output helpers -/

theorem readArrayBytes_getD (b : Array byte) (base cnt i : Nat)
    (hi : i < cnt) :
    (readArrayBytes b base cnt).getD i 0 = b.getD (base + i) 0 := by
  unfold readArrayBytes
  simp [List.getD, hi]

theorem readArrayBytes_length (b : Array byte) (base cnt : Nat) :
    (readArrayBytes b base cnt).length = cnt := by
  unfold readArrayBytes
  simp

open Evm.Functions in
theorem runS_memory_expand_to_le (off len req : Nat)
    (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState) (h : req ≤ len) :
    runS (Evm.Functions.memory_expand_to ⟨off, len, msf⟩ req) hs ss =
      .ok (((⟨off + 0, req, memory_sub_slice msf 0 req⟩ : EvmMemorySlice),
        (⟨off, len, msf⟩ : EvmMemorySlice)), hs) ss := by
  simp only [Evm.Functions.memory_expand_to]
  rw [dif_neg (by simp only [EvmMemorySliceFields.len]; simpa using
    Nat.not_lt.mpr h)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_active_memory_slice_zero (off len : Nat)
    (msf : EvmMemorySliceFields off len) (o : Nat)
    (hs : Evm.HostState) (ss : SeqState) :
    runS (Evm.Functions.active_memory_slice ⟨off, len, msf⟩ o 0) hs ss =
      .ok (((⟨0, 0, EMPTY_EVM_MEMORY_SLICE⟩ : EvmMemorySlice),
        (⟨off, len, msf⟩ : EvmMemorySlice)), hs) ss := by
  simp only [Evm.Functions.active_memory_slice]
  rw [dif_pos (by decide)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_active_memory_slice_le (off len o n : Nat)
    (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (hn : (n == 0) = false) (h : o + n ≤ len) :
    runS (Evm.Functions.active_memory_slice ⟨off, len, msf⟩ o n) hs ss =
      .ok (((⟨off + 0 + o, n,
          memory_sub_slice (memory_sub_slice msf 0 (o + n)) o n⟩ :
            EvmMemorySlice),
        (⟨off, len, msf⟩ : EvmMemorySlice)), hs) ss := by
  simp only [Evm.Functions.active_memory_slice]
  rw [dif_neg (by simp [hn])]
  refine runS_bind_ok (runS_memory_expand_to_le off len (o + n) msf hs ss
    h) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_output_buffer_store_memory (b blen : Nat)
    (f : EvmMemorySliceFields b blen)
    (hs : Evm.HostState) (ss : SeqState) :
    runS (Evm.Functions.output_buffer_store_memory ⟨b, blen, f⟩) hs ss =
      .ok (true, { hs with outputBytes :=
        (readArrayBytes hs.memoryBytes b blen).toArray }) ss := by
  unfold Evm.Functions.output_buffer_store_memory
  refine runS_bind_ok (runS_get _ _) ?_
  refine runS_bind_ok (runS_modify _ _ _) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem output_buffer_slice_ne (n : Nat) (hn : (n == 0) = false) :
    Evm.Functions.output_buffer_slice n
      = (⟨0, n, Evm.Functions.output_slice 0 n⟩ :
          (Sigma fun oo => Sigma fun ol => OutputSliceFields oo ol)) := by
  unfold Evm.Functions.output_buffer_slice
  rw [dif_neg (by simp [hn])]

open Evm.Functions in
theorem runS_freeze_zero (hs : Evm.HostState) (ss : SeqState) :
    runS (Evm.Functions.freeze_memory_output
        ⟨0, 0, EMPTY_EVM_MEMORY_SLICE⟩) hs ss =
      .ok ((⟨0, 0, EMPTY_OUTPUT_SLICE⟩ :
        (Sigma fun oo => Sigma fun ol => OutputSliceFields oo ol)), hs) ss := by
  simp only [Evm.Functions.freeze_memory_output]
  rw [dif_pos (by decide)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_freeze_ne (b n : Nat) (f : EvmMemorySliceFields b n)
    (hs : Evm.HostState) (ss : SeqState) (hn : (n == 0) = false) :
    runS (Evm.Functions.freeze_memory_output ⟨b, n, f⟩) hs ss =
      .ok ((⟨0, n, Evm.Functions.output_slice 0 n⟩ :
          (Sigma fun oo => Sigma fun ol => OutputSliceFields oo ol)),
        { hs with outputBytes :=
          (readArrayBytes hs.memoryBytes b n).toArray }) ss := by
  simp only [Evm.Functions.freeze_memory_output]
  rw [dif_neg (by simp only [EvmMemorySliceFields.len]; simp [hn])]
  refine runS_bind_ok (runS_output_buffer_store_memory b n f hs ss) ?_
  rw [dif_pos rfl,
    (show Evm.Functions.output_buffer_slice f.len = _ from
      output_buffer_slice_ne n hn)]
  exact runS_pure _ _ _

/-! ## `Evm` run shapes: `execute_return` -/

open Evm.Functions in
/-- The dispatch equation for RETURN. -/
theorem return_dispatch (pc_in : Nat) (top : StackTop) (off len : Nat)
    (msf : EvmMemorySliceFields off len) (g : Nat) :
    Evm.Functions.execute_opcode (.RETURN ()) pc_in top ⟨off, len, msf⟩ g =
      Evm.Functions.execute_return top ⟨off, len, msf⟩ g >>= fun p =>
        pure (pc_in, p.1, p.2.1, p.2.2) := rfl

open Evm.Functions in
theorem runS_execute_return_underflow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 2) :
    runS (Evm.Functions.execute (.RETURN ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.RETURN ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 2 0 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_return_oog (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y : Nat)
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
    (hgas : g < Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
      (Evm.Functions.memory_required_size x y)) :
    runS (Evm.Functions.execute (.RETURN ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  have hbound := top.isLt
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hpfx' : l.take ((top.toNat - 1) + 1) = (x :: y :: rest).reverse := by
    rw [show top.toNat - 1 + 1 = top.toNat from by omega]
    exact hpfx
  have hpfx1 : l.take (top.toNat - 1) = (y :: rest).reverse :=
    take_shrink l _ x _ hpfx' (by simp; omega)
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.RETURN ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, return_dispatch]
  have hbody : runS (Evm.Functions.execute_return top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_return]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (y :: rest) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest y rest hframe
        (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_charge_oog g _ hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
    rw [dif_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)


open Evm.Functions in
theorem memory_expansion_cost_zero (off len : Nat)
    (msf : EvmMemorySliceFields off len) :
    Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ 0 = 0 := by
  simp only [Evm.Functions.memory_expansion_cost, memory_high_water_eq]
  rw [if_pos (by simp [memory_word_count_eq])]

open Evm.Functions in
theorem runS_execute_return_zero (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : Nat) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: 0 :: rest).reverse)
    (htop : top.toNat = (x :: 0 :: rest).length)
    (hlim : top.toNat ≤ 1024) :
    runS (Evm.Functions.execute (.RETURN ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          ⟨off, len, msf⟩, g), hs)
        { ss with regs :=
            ss.regs.insert Register.frame_status (returnedStatus 0 0 EMPTY_OUTPUT_SLICE) } := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  have hbound := top.isLt
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hpfx' : l.take ((top.toNat - 1) + 1) = (x :: 0 :: rest).reverse := by
    rw [show top.toNat - 1 + 1 = top.toNat from by omega]
    exact hpfx
  have hpfx1 : l.take (top.toNat - 1) = ((0 : word) :: rest).reverse :=
    take_shrink l _ x _ hpfx' (by simp; omega)
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.RETURN ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, return_dispatch]
  have hbody : runS (Evm.Functions.execute_return top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice), g), hs)
        { ss with regs :=
            ss.regs.insert Register.frame_status (returnedStatus 0 0 EMPTY_OUTPUT_SLICE) } := by
    simp only [Evm.Functions.execute_return]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x ((0 : word) :: rest) hframe hpfx
        htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest (0 : word) rest hframe
        (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
    rw [show Evm.Functions.memory_required_size x (0 : Nat) = 0 from rfl,
      memory_expansion_cost_zero]
    refine runS_bind_ok (runS_charge_ok g 0 hs ss (Nat.zero_le g)) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok (runS_memory_access_zero x hs ss) ?_
    refine runS_bind_ok
      (runS_expand_memory_le off len 0 msf hs ss (Nat.zero_le len)) ?_
    refine runS_bind_ok
      (runS_active_memory_slice_zero off len msf 0 hs ss) ?_
    refine runS_bind_ok (runS_freeze_zero hs ss) ?_
    refine runS_bind_ok (runS_writeReg _ _ _ _) ?_
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
theorem runS_execute_return_ok_grow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y : Nat)
    (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: rest).reverse)
    (htop : top.toNat = (x :: y :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (mfrest : List Evm.MemoryFrame)
    (hmframe : hs.memoryFrames
      = ({ base := off, established := len } : Evm.MemoryFrame) :: mfrest)
    (hy : (y == 0) = false)
    (hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + y)
      ≤ g)
    (hreq : x + y ≤ 2 ^ 32 - 32)
    (hgrow : len < x + y) :
    runS (Evm.Functions.execute (.RETURN ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, x + y, {}⟩ : EvmMemorySlice),
          g - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + y)),
        { hs with
          memoryBytes :=
            zeroMemoryRange hs.memoryBytes (off + len) (x + y - len)
          memoryFrames :=
            ({ base := off, established := x + y } : Evm.MemoryFrame)
              :: mfrest
          outputBytes := (readArrayBytes
            (zeroMemoryRange hs.memoryBytes (off + len) (x + y - len))
            (off + 0 + x) y).toArray })
        { ss with regs :=
            ss.regs.insert Register.frame_status (returnedStatus 0 y (Evm.Functions.output_slice 0 y)) } := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  have hbound := top.isLt
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hpfx' : l.take ((top.toNat - 1) + 1) = (x :: y :: rest).reverse := by
    rw [show top.toNat - 1 + 1 = top.toNat from by omega]
    exact hpfx
  have hpfx1 : l.take (top.toNat - 1) = (y :: rest).reverse :=
    take_shrink l _ x _ hpfx' (by simp; omega)
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.RETURN ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, return_dispatch]
  have hbody : runS (Evm.Functions.execute_return top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, x + y, {}⟩ : EvmMemorySlice),
          g - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + y)),
        { hs with
          memoryBytes :=
            zeroMemoryRange hs.memoryBytes (off + len) (x + y - len)
          memoryFrames :=
            ({ base := off, established := x + y } : Evm.MemoryFrame)
              :: mfrest
          outputBytes := (readArrayBytes
            (zeroMemoryRange hs.memoryBytes (off + len) (x + y - len))
            (off + 0 + x) y).toArray })
        { ss with regs :=
            ss.regs.insert Register.frame_status (returnedStatus 0 y (Evm.Functions.output_slice 0 y)) } := by
    simp only [Evm.Functions.execute_return]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (y :: rest) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest y rest hframe
        (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
    rw [memory_required_size_ne x y hy]
    refine runS_bind_ok (runS_charge_ok g _ hs ss hexp) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_memory_access_ok x y hs ss hy
        (show x ≤ 2 ^ 32 - 1 by omega)
        (show y ≤ 2 ^ 32 - 1 - x by omega)) ?_
    refine runS_bind_ok
      (runS_expand_memory_grow off len (x + y) msf hs ss len mfrest hmframe
        rfl hgrow) ?_
    refine runS_bind_ok
      (runS_active_memory_slice_le off (x + y) x y {} _ ss hy
        (le_refl _)) ?_
    refine runS_bind_ok
      (runS_freeze_ne (off + 0 + x) y _ _ ss hy) ?_
    refine runS_bind_ok (runS_writeReg _ _ _ _) ?_
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
theorem runS_execute_return_ok_nogrow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y : Nat)
    (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: rest).reverse)
    (htop : top.toNat = (x :: y :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hy : (y == 0) = false)
    (hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + y)
      ≤ g)
    (hreq : x + y ≤ 2 ^ 32 - 32)
    (hgrow : x + y ≤ len) :
    runS (Evm.Functions.execute (.RETURN ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice),
          g - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + y)),
        { hs with
          outputBytes := (readArrayBytes hs.memoryBytes
            (off + 0 + x) y).toArray })
        { ss with regs :=
            ss.regs.insert Register.frame_status (returnedStatus 0 y (Evm.Functions.output_slice 0 y)) } := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  have hbound := top.isLt
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hpfx' : l.take ((top.toNat - 1) + 1) = (x :: y :: rest).reverse := by
    rw [show top.toNat - 1 + 1 = top.toNat from by omega]
    exact hpfx
  have hpfx1 : l.take (top.toNat - 1) = (y :: rest).reverse :=
    take_shrink l _ x _ hpfx' (by simp; omega)
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.RETURN ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, return_dispatch]
  have hbody : runS (Evm.Functions.execute_return top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice),
          g - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + y)),
        { hs with
          outputBytes := (readArrayBytes hs.memoryBytes
            (off + 0 + x) y).toArray })
        { ss with regs :=
            ss.regs.insert Register.frame_status (returnedStatus 0 y (Evm.Functions.output_slice 0 y)) } := by
    simp only [Evm.Functions.execute_return]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (y :: rest) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest y rest hframe
        (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
    rw [memory_required_size_ne x y hy]
    refine runS_bind_ok (runS_charge_ok g _ hs ss hexp) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_memory_access_ok x y hs ss hy
        (show x ≤ 2 ^ 32 - 1 by omega)
        (show y ≤ 2 ^ 32 - 1 - x by omega)) ?_
    refine runS_bind_ok
      (runS_expand_memory_le off len (x + y) msf hs ss hgrow) ?_
    refine runS_bind_ok
      (runS_active_memory_slice_le off len x y msf hs ss hy hgrow) ?_
    refine runS_bind_ok
      (runS_freeze_ne (off + 0 + x) y _ hs ss hy) ?_
    refine runS_bind_ok (runS_writeReg _ _ _ _) ?_
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)


theorem toArray_getD (l : List byte) (i : Nat) :
    (l.toArray).getD i 0 = l.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD]

/-! ## The step equivalence -/

open Evm.Functions in
/-- **RETURN, all reachable outcomes**: normal halt with matching output
(zero / grow / in-window) / underflow ×2 / OOG on the expansion charge.
The pc plays no role — both sides discard it at the frame boundary. -/
theorem return_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (off len : Nat)
    (msf : EvmMemorySliceFields off len) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hmem : MemoryRel sRef.evm.memory hs off len)
    (hsafe : MemGasSafe sRef.evm.memory sRef.evm.gasLeft) :
    StepResultRel ReturnPost (runR iReturn sRef)
      (runS (Evm.Functions.execute (.RETURN ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_iReturn_underflow_nil sRef hS,
      runS_execute_return_underflow pc_in top off len g msf hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | [x] =>
    rw [hS] at hpfx htop
    rw [runR_iReturn_underflow_one sRef x hS,
      runS_execute_return_underflow pc_in top off len g msf hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | x :: y :: rest =>
    rw [hS] at hpfx htop hlim hwfS
    have hin2 : 2 ≤ top.toNat := by simp at htop; omega
    have hlim' : top.toNat ≤ 1024 := by simp at htop ⊢; simp at hlim; omega
    obtain ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩ := hmem
    have hrc : returnCost sRef.evm.memory.length x y
        = (calculate_gas_extend_memory sRef.evm.memory.length
            [(x, y)]).cost := Nat.zero_add _
    by_cases hy0 : (y == 0) = true
    · have hyz : y = 0 := by simpa using hy0
      subst hyz
      have h0cost : (calculate_gas_extend_memory sRef.evm.memory.length
          [(x, 0)]).cost = 0 := by
        rw [calc_extend_single]
        rfl
      have h0exp : (calculate_gas_extend_memory sRef.evm.memory.length
          [(x, 0)]).expandBy = 0 := by
        rw [calc_extend_single]
        rfl
      have hgas0 : returnCost sRef.evm.memory.length x 0
          ≤ sRef.evm.gasLeft := by
        rw [hrc, h0cost]
        exact Nat.zero_le _
      rw [runR_iReturn_success sRef x 0 rest hS hgas0,
        runS_execute_return_zero pc_in top off len g msf hs ss l frest x
          rest hframe hpfx htop hlim']
      rw [h0exp, show List.replicate 0 (0x00 : EvmAsm.EL.RLP.Byte) = []
        from rfl, List.append_nil]
      refine StepResultRel.success ?_
      refine ⟨rfl, ?_, by simp [Std.ExtDHashMap.get?_insert]; exact hres, by simp [Std.ExtDHashMap.get?_insert]; exact hsp,
        0, 0, EMPTY_OUTPUT_SLICE, by simp [returnedStatus], ?_, ?_⟩
      · show g = sRef.evm.gasLeft - returnCost sRef.evm.memory.length x 0
        rw [hlive, hrc, h0cost]
        exact (Nat.sub_zero _).symm
      · show (0 : Nat) = (memory_read_bytes sRef.evm.memory x 0).length
        simp [memory_read_bytes]
      · intro i hi
        exact absurd hi (Nat.not_lt_zero i)
    · have hy' : (y == 0) = false := by simpa using hy0
      have hcost' : (calculate_gas_extend_memory sRef.evm.memory.length
          [(x, y)]).cost
          = Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + y) := by
        have h1 := extend_cost_eq sRef.evm.memory off len x y msf haligned
        rwa [memory_required_size_ne x y hy'] at h1
      by_cases hg : sRef.evm.gasLeft < returnCost sRef.evm.memory.length x y
      · rw [runR_iReturn_oog sRef x y rest hS hg]
        have hgg : g < returnCost sRef.evm.memory.length x y := by
          rw [hlive]
          exact hg
        have key : g < ((calculate_gas_extend_memory
            sRef.evm.memory.length [(x, y)]).cost : Nat) := by omega
        have hgasS : g < Evm.Functions.memory_expansion_cost
            ⟨off, len, msf⟩ (Evm.Functions.memory_required_size x y) := by
          rw [memory_required_size_ne x y hy', ← hcost']
          exact key
        rw [runS_execute_return_oog pc_in top off len g msf hs ss l frest x
          y rest hframe hpfx htop hlim' prof sRef.evm.stateGasSpilled msg
          hprof hsp hmsg hfork hgasS]
        exact StepResultRel.halted ErrorRel.outOfGas
          (haltRegs_frame_status ss msg .OutOfGas)
      · push Not at hg
        have hgc : g ≥ returnCost sRef.evm.memory.length x y := by
          rw [hlive]
          exact hg
        have hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
            (x + y) ≤ g := by
          rw [← hcost']
          have key : g ≥ ((calculate_gas_extend_memory
              sRef.evm.memory.length [(x, y)]).cost : Nat) := by omega
          exact key
        have hreq : x + y ≤ 2 ^ 32 - 32 :=
          safe_required_bound sRef.evm.memory off len (x + y) g
            sRef.evm.gasLeft msf haligned hsafe (le_of_eq hlive) hexp
        have hwcM : Evm.Functions.memory_word_count sRef.evm.memory.length
            = Evm.Functions.memory_word_count len := by
          rw [haligned, memory_word_count_eq, memory_word_count_eq]
          omega
        have hexpandBy : ((calculate_gas_extend_memory
            sRef.evm.memory.length [(x, y)]).expandBy : Nat)
            = 32 * Evm.Functions.memory_word_count (x + y)
              - sRef.evm.memory.length := by
          have hiff0 : ∀ a b : Nat, (32 * a ≤ 32 * b) ↔ (a ≤ b) :=
            fun a b => by omega
          have hiff : ((ceil32 (x + y) : Nat)
              ≤ ceil32 sRef.evm.memory.length)
              ↔ (Evm.Functions.memory_word_count (x + y)
                  ≤ Evm.Functions.memory_word_count len) := by
            rw [ceil32_eq, ceil32_eq, hwcM]
            exact hiff0 _ _
          rw [calc_extend_single]
          rw [if_neg (by simp [hy'])]
          by_cases hle : Evm.Functions.memory_word_count (x + y)
              ≤ Evm.Functions.memory_word_count len
          · rw [if_pos (hiff.mpr hle)]
            show (0 : Nat) = _
            have h1 : 32 * Evm.Functions.memory_word_count (x + y)
                ≤ sRef.evm.memory.length := by
              rw [haligned]
              omega
            omega
          · rw [if_neg (fun hc => hle (hiff.mp hc))]
            show ((ceil32 (x + y) : Nat) - ceil32 sRef.evm.memory.length)
              = _
            rw [ceil32_eq, ceil32_eq, hwcM, ← haligned]
        have hgasSpec : returnCost sRef.evm.memory.length x y
            ≤ sRef.evm.gasLeft := hg
        rw [runR_iReturn_success sRef x y rest hS hgasSpec]
        have hMlen : len ≤ sRef.evm.memory.length := by
          have := le_32_wc len
          omega
        by_cases hgrow : len < x + y
        · rw [runS_execute_return_ok_grow pc_in top off len g msf hs ss l
            frest x y rest hframe hpfx htop hlim' mfrest hmframe hy' hexp
            hreq hgrow]
          have hrel' := memoryRel_expand sRef.evm.memory hs off len (x + y)
            mfrest ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩ hgrow
          rw [hexpandBy]
          refine StepResultRel.success ?_
          refine ⟨rfl, ?_, by simp [Std.ExtDHashMap.get?_insert]; exact hres, by simp [Std.ExtDHashMap.get?_insert]; exact hsp,
            0, y, Evm.Functions.output_slice 0 y,
            by simp [returnedStatus], ?_, ?_⟩
          · show g - _ = sRef.evm.gasLeft - returnCost
              sRef.evm.memory.length x y
            rw [hlive, ← hcost']
            have key : ∀ a c : Nat, a - c = a - (0 + c) :=
              fun a c => by omega
            exact key _ _
          · show (y : Nat) = _
            rw [memory_read_bytes_length _ x y (by
              simp only [List.length_append, List.length_replicate]
              have h32 := le_32_wc (x + y)
              have hwc := wc_mono (Nat.le_of_lt hgrow)
              have hal := haligned
              omega)]
          · intro i hi
            rw [show (0 : Nat) + i = i from by omega]
            have h1 : ((readArrayBytes
                (zeroMemoryRange hs.memoryBytes (off + len)
                  (x + y - len)) (off + 0 + x) y).toArray).getD i 0
                = (zeroMemoryRange hs.memoryBytes (off + len)
                    (x + y - len)).getD (off + (x + i)) 0 := by
              rw [toArray_getD, readArrayBytes_getD _ _ _ i hi,
                show off + 0 + x + i = off + (x + i) from by omega]
            have h2 : (zeroMemoryRange hs.memoryBytes (off + len)
                (x + y - len)).getD (off + (x + i)) 0
                = (sRef.evm.memory ++ List.replicate
                    (32 * Evm.Functions.memory_word_count (x + y)
                      - sRef.evm.memory.length) 0x00).getD (x + i) 0 :=
              hrel'.bytes (x + i) (by omega)
            have h3 := memory_read_bytes_getElem
              (sRef.evm.memory ++ List.replicate
                (32 * Evm.Functions.memory_word_count (x + y)
                  - sRef.evm.memory.length) 0x00) x y i hi
            exact h1.trans (h2.trans h3.symm)
        · push Not at hgrow
          rw [runS_execute_return_ok_nogrow pc_in top off len g msf hs ss l
            frest x y rest hframe hpfx htop hlim' hy' hexp hreq hgrow]
          have hzero : (0 : Nat) = (calculate_gas_extend_memory
              sRef.evm.memory.length [(x, y)]).expandBy := by
            rw [hexpandBy]
            have hwc := wc_mono hgrow
            have hal := haligned
            rw [memory_word_count_eq] at hwc hal ⊢
            omega
          rw [← hzero]
          rw [show List.replicate 0 (0x00 : EvmAsm.EL.RLP.Byte) = []
            from rfl, List.append_nil]
          refine StepResultRel.success ?_
          refine ⟨rfl, ?_, by simp [Std.ExtDHashMap.get?_insert]; exact hres, by simp [Std.ExtDHashMap.get?_insert]; exact hsp,
            0, y, Evm.Functions.output_slice 0 y,
            by simp [returnedStatus], ?_, ?_⟩
          · show g - _ = sRef.evm.gasLeft - returnCost
              sRef.evm.memory.length x y
            rw [hlive, ← hcost']
            have key : ∀ a c : Nat, a - c = a - (0 + c) :=
              fun a c => by omega
            exact key _ _
          · show (y : Nat) = _
            rw [memory_read_bytes_length _ x y (by omega)]
          · intro i hi
            rw [show (0 : Nat) + i = i from by omega]
            have h1 : ((readArrayBytes hs.memoryBytes
                (off + 0 + x) y).toArray).getD i 0
                = hs.memoryBytes.getD (off + (x + i)) 0 := by
              rw [toArray_getD, readArrayBytes_getD _ _ _ i hi,
                show off + 0 + x + i = off + (x + i) from by omega]
            have h2 : hs.memoryBytes.getD (off + (x + i)) 0
                = sRef.evm.memory.getD (x + i) 0 :=
              hbytes (x + i) (by omega)
            have h3 := memory_read_bytes_getElem sRef.evm.memory x y i hi
            exact h1.trans (h2.trans h3.symm)

end EvmSpecsVerify
