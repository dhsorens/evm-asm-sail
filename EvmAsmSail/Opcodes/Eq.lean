import EvmAsmSail.Opcodes.BinopFamily

/-!
# EQ

Derived through `binop_step_equiv` (`Opcodes/BinopFamily.lean`); per-opcode
content is the pure-function lemma and the wf bound. Reachable outcomes:
success / stack underflow / out-of-gas (overflow unreachable for 2-in/1-out).
-/

open private boolPush from EvmAsm.Stateless.SpecRef.InstructionsCore

set_option maxHeartbeats 1000000

namespace EvmAsmSail

open EvmAsm.Stateless.SpecRef
open Evm.Defs

theorem alu_eq_eq (a b : Nat) :
    Evm.Functions.alu_eq a b = boolPush (a == b) := by
  show (if (a == b) = true then ((1 : Int)).toNat else ((0 : Int)).toNat)
      = if (a == b) = true then 1 else 0
  split <;> rfl

open Evm.Functions in
/-- **EQ, all reachable outcomes.** -/
theorem eq_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iEq sRef)
      (runS (Evm.Functions.execute (.EQ ()) pc_in top mem g) hs ss) :=
  binop_step_equiv (.EQ ()) G_verylow alu_eq iEq GasCosts.OPCODE_EQ
    (fun x y => boolPush (x == y)) rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩
    (fun x y _ _ => alu_eq_eq x y) (fun _ _ _ _ => boolPush_wf _)
    sRef top g hs ss mem pc_in hrel hpc

end EvmAsmSail
