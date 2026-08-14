import EvmAsmSail.Opcodes.Shapes.Unop

/-!
# ISZERO

Derived through `unop_step_equiv` (`Opcodes/Shapes/Unop.lean`); per-opcode
content is the pure-function lemma and the wf bound. Reachable outcomes:
success / stack underflow / out-of-gas (overflow unreachable for 1-in/1-out).
-/

open private boolPush from EvmAsm.Stateless.SpecRef.InstructionsCore

set_option maxHeartbeats 1000000

namespace EvmAsmSail

open EvmAsm.Stateless.SpecRef
open Evm.Defs

theorem alu_iszero_eq (a : Nat) :
    Evm.Functions.alu_iszero a = boolPush (a == 0) := by
  show (if (a == 0) = true then ((1 : Int)).toNat else ((0 : Int)).toNat)
      = if (a == 0) = true then 1 else 0
  split <;> rfl

open Evm.Functions in
/-- **ISZERO, all reachable outcomes.** -/
theorem iszero_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iIszero sRef)
      (runS (Evm.Functions.execute (.ISZERO ()) pc_in top mem g) hs ss) :=
  unop_step_equiv (.ISZERO ()) G_verylow alu_iszero iIszero
    GasCosts.OPCODE_ISZERO (fun x => boolPush (x == 0)) rfl rfl
    ⟨rfl, fun _ _ _ _ => rfl⟩ (fun x _ => alu_iszero_eq x)
    (fun _ _ => boolPush_wf _) sRef top g hs ss mem pc_in hrel hpc

end EvmAsmSail
