import EvmSpecsVerify.Opcodes.Return

/-!
# REVERT

The [`RETURN`](Return.lean) harvest, and the first opcode whose outcome is
neither an ordinary success nor an exceptional halt. `iRevert` pops offset
and size, charges the expansion, extends, sets `output` — and then
`throw .revert`. Since `EvmError.isHalt .revert = false`, the frame
teardown keeps the remaining gas and the output instead of discarding
them, so [`StepResultRel.halted`](../Relations/Outcome.lean)'s
"all gas consumed" clause does not apply. The step theorem therefore
targets [`RevertResultRel`](../Relations/Outcome.lean), an additive
wrapper whose `reverted` case carries [`RevertPost`](#RevertPost).

## Where the state-gas refill happens (mismatch ledger MM-9)

The one substantive difference from RETURN: `execute_revert` calls
`refill_frame_state_gas` **inside the handler**, while SpecRef runs the
identical refill at *frame teardown* (`process_message`'s `tryCatch`,
Interpreter.lean:490, which fires on every error — revert included).
`execute_return` performs no refill, and SpecRef's RETURN path raises no
error, so RETURN is unaffected: the asymmetry between the extraction's two
handlers exactly mirrors the asymmetry in SpecRef's control flow.

The consequence is visible at our step boundary and nowhere else: the
extraction's returned live gas is already `gasLeft + stateGasSpilled` and
its two state-gas registers already show the refilled values.
[`refilled`](#refilled) names SpecRef's own teardown transformation, and
[`runR_refill`](#runR_refill) proves it *is* SpecRef's
`refill_frame_state_gas`, so `RevertPost` compares against a SpecRef state
rather than against an invented one.

Reachable outcomes: revert (zero / grow / in-window output windows) /
underflow ×2 / OOG on the expansion charge. `MemGasSafe` (MM-6) discharges
the u32 range check as for RETURN.
-/

open private writeArrayBytes wordBytes zeroMemoryRange readArrayBytes
  from Evm.HostAxioms

set_option maxHeartbeats 4000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- The SpecRef REVERT charge: the expansion cost alone (RETURN adds a
`ZERO` base, which is the same number). -/
def revertCost (msz x y : Nat) : Nat :=
  (calculate_gas_extend_memory msz [(x, y)]).cost

/-- SpecRef's frame-teardown state-gas refill, as a state transformation.
Proved to be SpecRef's own `refill_frame_state_gas` by
[`runR_refill`](#runR_refill). -/
def refilled (s : Machine) : Machine :=
  { s with evm := { s.evm with
      gasLeft := s.evm.gasLeft + s.evm.stateGasSpilled
      stateGasLeft := s.evm.message.stateGasReservoir
      stateGasSpilled := 0 } }

theorem runR_refill (s : Machine) :
    runR EvmAsm.Stateless.SpecRef.refill_frame_state_gas s
      = .ok (.ok (), refilled s) :=
  runR_modifyEvm _ _

/-- The revert post: the extraction's halt kind carries the same output
bytes, and its gas and state-gas registers match SpecRef's frame **after
the teardown refill** (MM-9). A reverted frame's stack, pc, and memory are
not observable past the frame boundary. -/
def RevertPost (sR' : Machine) (step : EvmStep)
    (hs' : Evm.HostState) (ss' : SeqState) : Prop :=
  step.2.2.2 = (refilled sR').evm.gasLeft ∧
  ss'.regs.get? Register.state_gas_remaining
    = some (refilled sR').evm.stateGasLeft ∧
  ss'.regs.get? Register.state_gas_spilled
    = some (refilled sR').evm.stateGasSpilled ∧
  ∃ (oo ol : Nat) (osf : OutputSliceFields oo ol),
    ss'.regs.get? Register.frame_status
      = some (FrameStatus.Halted (HaltKind.HaltRevert ⟨oo, ol, osf⟩)) ∧
    ol = sR'.evm.output.length ∧
    ∀ i, i < ol → hs'.outputBytes.getD (oo + i) 0
      = sR'.evm.output.getD i 0

/-- The frame status a REVERT writes. -/
def revertedStatus (oo ol : Nat) (osf : OutputSliceFields oo ol) :
    FrameStatus :=
  FrameStatus.Halted (HaltKind.HaltRevert ⟨oo, ol, osf⟩)

/-- The register file a REVERT leaves: MM-9's teardown refill folded in,
then the revert halt status. Named so the run shapes below carry no
multi-line structure-update literal. -/
def revertRegs (ss : SeqState) (msg : Evm.Defs.Message) (oo ol : Nat)
    (osf : OutputSliceFields oo ol) :=
  (refillRegs ss msg).insert Register.frame_status (revertedStatus oo ol osf)

theorem revertRegs_frame_status (ss : SeqState) (msg : Evm.Defs.Message)
    (oo ol : Nat) (osf : OutputSliceFields oo ol) :
    (revertRegs ss msg oo ol osf).get? Register.frame_status
      = some (revertedStatus oo ol osf) := by
  simp [revertRegs]

theorem revertRegs_state_gas (ss : SeqState) (msg : Evm.Defs.Message)
    (oo ol : Nat) (osf : OutputSliceFields oo ol) :
    (revertRegs ss msg oo ol osf).get? Register.state_gas_remaining
        = some msg.state_gas_reservoir ∧
      (revertRegs ss msg oo ol osf).get? Register.state_gas_spilled
        = some Evm.Functions.STATE_GAS_SPILL_ZERO := by
  constructor <;> simp [revertRegs, refillRegs, Std.ExtDHashMap.get?_insert]

/-! ## SpecRef run shapes -/

theorem runR_iRevert_underflow_nil (s : Machine)
    (hstack : s.evm.stack = []) :
    runR iRevert s = .ok (.error .stackUnderflow, s) := by
  simp only [iRevert]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_iRevert_underflow_one (s : Machine) (x : U256)
    (hstack : s.evm.stack = [x]) :
    runR iRevert s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with stack := [] } }) := by
  simp only [iRevert]
  refine runR_bind_ok (runR_stackPop_cons s x [] hstack) ?_
  exact runR_bind_err (runR_stackPop_nil _ (by simp))

theorem runR_iRevert_oog (s : Machine) (x y : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: y :: rest)
    (hgas : s.evm.gasLeft < revertCost s.evm.memory.length x y) :
    runR iRevert s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [iRevert]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y rest (by simp)) ?_
  refine runR_bind_ok (runR_getEvm_map _ _) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _
    (by simpa [revertCost] using hgas))

theorem runR_iRevert_success (s : Machine) (x y : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: y :: rest)
    (hgas : revertCost s.evm.memory.length x y ≤ s.evm.gasLeft) :
    runR iRevert s =
      .ok (.error .revert,
        { s with evm := { s.evm with
            stack := rest
            memory := s.evm.memory ++ List.replicate
              (calculate_gas_extend_memory s.evm.memory.length
                [(x, y)]).expandBy 0x00
            output := memory_read_bytes
              (s.evm.memory ++ List.replicate
                (calculate_gas_extend_memory s.evm.memory.length
                  [(x, y)]).expandBy 0x00) x y
            gasLeft := s.evm.gasLeft - revertCost s.evm.memory.length x y
            regularGasUsed :=
              s.evm.regularGasUsed
                + revertCost s.evm.memory.length x y } }) := by
  simp only [iRevert, extendMemory]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y rest (by simp)) ?_
  refine runR_bind_ok (runR_getEvm_map _ _) ?_
  refine runR_bind_ok (runR_charge_gas _ _
    (by simpa [revertCost] using hgas)) ?_
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  exact runR_throw _ _

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for REVERT. -/
theorem revert_dispatch (pc_in : Nat) (top : StackTop) (off len : Nat)
    (msf : EvmMemorySliceFields off len) (g : Nat) :
    Evm.Functions.execute_opcode (.REVERT ()) pc_in top ⟨off, len, msf⟩ g =
      Evm.Functions.execute_revert top ⟨off, len, msf⟩ g >>= fun p =>
        pure (pc_in, p.1, p.2.1, p.2.2) := rfl

open Evm.Functions in
theorem runS_execute_revert_underflow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 2) :
    runS (Evm.Functions.execute (.REVERT ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.REVERT ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 2 0 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_revert_oog (pc_in : Nat) (top : StackTop)
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
    runS (Evm.Functions.execute (.REVERT ()) pc_in top ⟨off, len, msf⟩ g)
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
    show Evm.Functions.opcode_stack_effect (.REVERT ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, revert_dispatch]
  have hbody : runS (Evm.Functions.execute_revert top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_revert]
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
theorem runS_execute_revert_zero (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : Nat) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: 0 :: rest).reverse)
    (htop : top.toNat = (x :: 0 :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1) :
    runS (Evm.Functions.execute (.REVERT ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          ⟨off, len, msf⟩, g + sp), hs)
        { ss with regs := revertRegs ss msg 0 0 EMPTY_OUTPUT_SLICE } := by
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
    show Evm.Functions.opcode_stack_effect (.REVERT ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, revert_dispatch]
  have hbody : runS (Evm.Functions.execute_revert top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice), g + sp), hs)
        { ss with regs := revertRegs ss msg 0 0 EMPTY_OUTPUT_SLICE } := by
    simp only [Evm.Functions.execute_revert]
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
      (runS_refill (g - 0) hs ss prof sp msg hprof hsp hmsg hfork) ?_
    refine runS_bind_ok
      (runS_active_memory_slice_zero off len msf 0 hs _) ?_
    refine runS_bind_ok (runS_freeze_zero hs _) ?_
    refine runS_bind_ok (runS_writeReg _ _ _ _) ?_
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
theorem runS_execute_revert_ok_grow (pc_in : Nat) (top : StackTop)
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
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hy : (y == 0) = false)
    (hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + y) ≤ g)
    (hreq : x + y ≤ 2 ^ 32 - 32)
    (hgrow : len < x + y) :
    runS (Evm.Functions.execute (.REVERT ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, x + y, {}⟩ : EvmMemorySlice),
          g - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + y)
            + sp),
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
            revertRegs ss msg 0 y (Evm.Functions.output_slice 0 y) } := by
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
    show Evm.Functions.opcode_stack_effect (.REVERT ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, revert_dispatch]
  have hbody : runS (Evm.Functions.execute_revert top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, x + y, {}⟩ : EvmMemorySlice),
          g - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + y)
            + sp),
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
            revertRegs ss msg 0 y (Evm.Functions.output_slice 0 y) } := by
    simp only [Evm.Functions.execute_revert]
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
      (runS_refill _ _ ss prof sp msg hprof hsp hmsg hfork) ?_
    refine runS_bind_ok
      (runS_active_memory_slice_le off (x + y) x y {} _ _ hy
        (le_refl _)) ?_
    refine runS_bind_ok
      (runS_freeze_ne (off + 0 + x) y _ _ _ hy) ?_
    refine runS_bind_ok (runS_writeReg _ _ _ _) ?_
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
theorem runS_execute_revert_ok_nogrow (pc_in : Nat) (top : StackTop)
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
    (hy : (y == 0) = false)
    (hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + y) ≤ g)
    (hreq : x + y ≤ 2 ^ 32 - 32)
    (hgrow : x + y ≤ len) :
    runS (Evm.Functions.execute (.REVERT ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice),
          g - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + y)
            + sp),
        { hs with
          outputBytes := (readArrayBytes hs.memoryBytes
            (off + 0 + x) y).toArray })
        { ss with regs :=
            revertRegs ss msg 0 y (Evm.Functions.output_slice 0 y) } := by
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
    show Evm.Functions.opcode_stack_effect (.REVERT ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, revert_dispatch]
  have hbody : runS (Evm.Functions.execute_revert top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice),
          g - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + y)
            + sp),
        { hs with
          outputBytes := (readArrayBytes hs.memoryBytes
            (off + 0 + x) y).toArray })
        { ss with regs :=
            revertRegs ss msg 0 y (Evm.Functions.output_slice 0 y) } := by
    simp only [Evm.Functions.execute_revert]
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
      (runS_refill _ _ ss prof sp msg hprof hsp hmsg hfork) ?_
    refine runS_bind_ok
      (runS_active_memory_slice_le off len x y msf hs _ hy hgrow) ?_
    refine runS_bind_ok
      (runS_freeze_ne (off + 0 + x) y _ hs _ hy) ?_
    refine runS_bind_ok (runS_writeReg _ _ _ _) ?_
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

/-! ## The step equivalence -/

open Evm.Functions in
/-- **REVERT, all reachable outcomes**: the revert itself with matching
output (zero / grow / in-window) / underflow ×2 / OOG on the expansion
charge. The revert case is `RevertResultRel.reverted`, not
`StepResultRel.halted`: `.revert` is not an exceptional halt, so the gas
survives. `hresv` is the message-register tie MM-9's refill needs — the
extraction restores the reservoir from its `message` register, SpecRef
from `evm.message`. -/
theorem revert_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (off len : Nat)
    (msf : EvmMemorySliceFields off len) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hmem : MemoryRel sRef.evm.memory hs off len)
    (hsafe : MemGasSafe sRef.evm.memory sRef.evm.gasLeft)
    (hresv : ∀ msg : Evm.Defs.Message,
      ss.regs.get? Register.message = some msg →
      msg.state_gas_reservoir = sRef.evm.message.stateGasReservoir) :
    RevertResultRel RevertPost (runR iRevert sRef)
      (runS (Evm.Functions.execute (.REVERT ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  have hrv := hresv msg hmsg
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_iRevert_underflow_nil sRef hS,
      runS_execute_revert_underflow pc_in top off len g msf hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact RevertResultRel.exceptional
      (StepResultRel.halted ErrorRel.stackUnderflow
        (haltRegs_frame_status ss msg .StackUnderflow))
  | [x] =>
    rw [hS] at hpfx htop
    rw [runR_iRevert_underflow_one sRef x hS,
      runS_execute_revert_underflow pc_in top off len g msf hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact RevertResultRel.exceptional
      (StepResultRel.halted ErrorRel.stackUnderflow
        (haltRegs_frame_status ss msg .StackUnderflow))
  | x :: y :: rest =>
    rw [hS] at hpfx htop hlim hwfS
    have hin2 : 2 ≤ top.toNat := by simp at htop; omega
    have hlim' : top.toNat ≤ 1024 := by simp at htop ⊢; simp at hlim; omega
    obtain ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩ := hmem
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
      have hgas0 : revertCost sRef.evm.memory.length x 0
          ≤ sRef.evm.gasLeft := by
        rw [revertCost, h0cost]
        exact Nat.zero_le _
      rw [runR_iRevert_success sRef x 0 rest hS hgas0,
        runS_execute_revert_zero pc_in top off len g msf hs ss l frest x
          rest hframe hpfx htop hlim' prof sRef.evm.stateGasSpilled msg
          hprof hsp hmsg hfork]
      rw [h0exp, show List.replicate 0 (0x00 : EvmAsm.EL.RLP.Byte) = []
        from rfl, List.append_nil]
      refine RevertResultRel.reverted ?_
      refine ⟨?_, ?_, ?_, 0, 0, EMPTY_OUTPUT_SLICE,
        revertRegs_frame_status ss msg 0 0 EMPTY_OUTPUT_SLICE, ?_, ?_⟩
      · show g + sRef.evm.stateGasSpilled
          = sRef.evm.gasLeft - revertCost sRef.evm.memory.length x 0
            + sRef.evm.stateGasSpilled
        rw [hlive, revertCost, h0cost]
        omega
      · rw [(revertRegs_state_gas ss msg 0 0 EMPTY_OUTPUT_SLICE).1]
        exact congrArg some hrv
      · exact (revertRegs_state_gas ss msg 0 0 EMPTY_OUTPUT_SLICE).2
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
      by_cases hg : sRef.evm.gasLeft < revertCost sRef.evm.memory.length x y
      · rw [runR_iRevert_oog sRef x y rest hS hg]
        have hgasS : g < Evm.Functions.memory_expansion_cost
            ⟨off, len, msf⟩ (Evm.Functions.memory_required_size x y) := by
          rw [memory_required_size_ne x y hy', ← hcost']
          rw [hlive]
          exact hg
        rw [runS_execute_revert_oog pc_in top off len g msf hs ss l frest x
          y rest hframe hpfx htop hlim' prof sRef.evm.stateGasSpilled msg
          hprof hsp hmsg hfork hgasS]
        exact RevertResultRel.exceptional
          (StepResultRel.halted ErrorRel.outOfGas
            (haltRegs_frame_status ss msg .OutOfGas))
      · push Not at hg
        have hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
            (x + y) ≤ g := by
          rw [← hcost', hlive]
          exact hg
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
        rw [runR_iRevert_success sRef x y rest hS hg]
        have hMlen : len ≤ sRef.evm.memory.length := by
          have := le_32_wc len
          omega
        by_cases hgrow : len < x + y
        · rw [runS_execute_revert_ok_grow pc_in top off len g msf hs ss l
            frest x y rest hframe hpfx htop hlim' mfrest hmframe prof
            sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hy' hexp
            hreq hgrow]
          have hrel' := memoryRel_expand sRef.evm.memory hs off len (x + y)
            mfrest ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩ hgrow
          rw [hexpandBy]
          refine RevertResultRel.reverted ?_
          refine ⟨?_, ?_, ?_, 0, y, Evm.Functions.output_slice 0 y,
            revertRegs_frame_status ss msg 0 y _, ?_, ?_⟩
          · show g - _ + sRef.evm.stateGasSpilled
              = sRef.evm.gasLeft - revertCost sRef.evm.memory.length x y
                + sRef.evm.stateGasSpilled
            rw [hlive, revertCost, hcost']
          · rw [(revertRegs_state_gas ss msg 0 y _).1]
            exact congrArg some hrv
          · exact (revertRegs_state_gas ss msg 0 y _).2
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
          rw [runS_execute_revert_ok_nogrow pc_in top off len g msf hs ss l
            frest x y rest hframe hpfx htop hlim' prof
            sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hy' hexp
            hreq hgrow]
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
          refine RevertResultRel.reverted ?_
          refine ⟨?_, ?_, ?_, 0, y, Evm.Functions.output_slice 0 y,
            revertRegs_frame_status ss msg 0 y _, ?_, ?_⟩
          · show g - _ + sRef.evm.stateGasSpilled
              = sRef.evm.gasLeft - revertCost sRef.evm.memory.length x y
                + sRef.evm.stateGasSpilled
            rw [hlive, revertCost, hcost']
          · rw [(revertRegs_state_gas ss msg 0 y _).1]
            exact congrArg some hrv
          · exact (revertRegs_state_gas ss msg 0 y _).2
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
