import EvmAsmSail.Opcodes.BinopFamily

/-!
# GT

Derived through `binop_step_equiv` (`Opcodes/BinopFamily.lean`); per-opcode
content is the pure-function lemma and the wf bound. Reachable outcomes:
success / stack underflow / out-of-gas (overflow unreachable for 2-in/1-out).
-/

open private boolPush from EvmAsm.Stateless.SpecRef.InstructionsCore

set_option maxHeartbeats 1000000

namespace EvmAsmSail

open EvmAsm.Stateless.SpecRef
open Evm.Defs

theorem alu_gt_eq (a b : Nat) :
    Evm.Functions.alu_gt a b = boolPush (a > b) := by
  show (if (b < a : Bool) = true then ((1 : Int)).toNat else ((0 : Int)).toNat)
      = if (a > b : Bool) = true then 1 else 0
  split <;> rename_i h <;> simp at h <;> simp [Nat.lt_iff_add_one_le] <;> omega

open Evm.Functions in
/-- **GT, all reachable outcomes.** -/
theorem gt_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iGt sRef)
      (runS (Evm.Functions.execute (.GT ()) pc_in top mem g) hs ss) :=
  binop_step_equiv (.GT ()) G_verylow alu_gt iGt GasCosts.OPCODE_GT
    (fun x y => boolPush (x > y)) rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩
    (fun x y _ _ => alu_gt_eq x y) (fun _ _ _ _ => boolPush_wf _)
    sRef top g hs ss mem pc_in hrel hpc

end EvmAsmSail
