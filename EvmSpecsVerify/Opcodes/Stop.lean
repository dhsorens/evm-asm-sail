import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# STOP

The simplest opcode: a free normal halt. SpecRef's `iStop` clears `running`
and advances the pc; the extraction's `execute_stop` writes
`frame_status := Halted (HaltStop ())` and passes the step tuple through
untouched. Neither side charges gas or touches the stack, so the only
reachable outcome is success-as-normal-halt: underflow/overflow are
impossible for 0-in/0-out (`validate_stack 0 0` always passes under the
1024 stack invariant) and there is no gas charge to fail.

`StopPost` mirrors [`ReturnPost`](Return.lean) minus the output clause:
SpecRef's `output` field is untouched by `iStop` (only RETURN/REVERT
assign it), and `HaltStop` carries no output slice — both teardowns read
an empty output for this halt kind, so there is nothing step-level to
relate. A halted frame's stack, pc, and memory are not observable past
the frame boundary.
-/

open private pcAdd from EvmAsm.Stateless.SpecRef.InstructionsCore

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- The success post for STOP: both sides halted normally with the gas and
state-gas registers intact. -/
def StopPost (sR' : Machine) (step : EvmStep)
    (_hs' : Evm.HostState) (ss' : SeqState) : Prop :=
  sR'.evm.running = false ∧
  step.2.2.2 = sR'.evm.gasLeft ∧
  ss'.regs.get? Register.state_gas_remaining
    = some sR'.evm.stateGasLeft ∧
  ss'.regs.get? Register.state_gas_spilled
    = some sR'.evm.stateGasSpilled ∧
  ss'.regs.get? Register.frame_status
    = some (FrameStatus.Halted (HaltKind.HaltStop ()))

/-! ## Run shapes -/

theorem runR_iStop (s : Machine) :
    runR iStop s =
      .ok (.ok (), { s with evm := { s.evm with
        running := false
        pc := s.evm.pc + 1 } }) := by
  simp only [iStop, pcAdd]
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  exact runR_modifyEvm _ _

open Evm.Functions in
/-- The dispatch equation for STOP. -/
theorem stop_dispatch (pc_in : Nat) (top : StackTop) (mem : EvmMemorySlice)
    (g : Nat) :
    Evm.Functions.execute_opcode (.STOP ()) pc_in top mem g =
      Evm.Functions.execute_stop () >>= fun _ =>
        pure (pc_in, top, mem, g) := rfl

/-- The frame status STOP writes (single-token value for the
structure-update literal). -/
def stoppedStatus : FrameStatus :=
  FrameStatus.Halted (HaltKind.HaltStop ())

open Evm.Functions in
theorem runS_execute_stop (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (hlim : top.toNat ≤ 1024) :
    runS (Evm.Functions.execute (.STOP ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, g), hs)
        { ss with regs := ss.regs.insert Register.frame_status stoppedStatus }
        := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.STOP ()) = pure (0, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 0 hs ss (by omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, stop_dispatch]
  refine runS_bind_ok
    (runS_writeReg Register.frame_status stoppedStatus hs ss) ?_
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **STOP, all reachable outcomes** — which is exactly one: the free
normal halt. 0-in/0-out excludes stack faults under the 1024 invariant,
and neither side charges gas. -/
theorem stop_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss) :
    StepResultRel StopPost (runR iStop sRef)
      (runS (Evm.Functions.execute (.STOP ()) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, _, _, _, _⟩ := hrel
  obtain ⟨_, htop, hlim, _⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  rw [runR_iStop sRef,
    runS_execute_stop pc_in top g mem hs ss (by omega)]
  refine StepResultRel.success ⟨rfl, hlive, ?_, ?_, ?_⟩
  · simp only [Std.ExtDHashMap.get?_insert]
    exact hres
  · simp only [Std.ExtDHashMap.get?_insert]
    exact hsp
  · simp [stoppedStatus]

end EvmSpecsVerify
