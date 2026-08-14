import EvmSpecsVerify.Opcodes.Slt

/-!
# SGT

Signed greater-than: `word_slt` with the operands swapped on the extraction
side (`alu_sgt`, Prelude.lean:586), the flipped signed order on SpecRef's
(`iSgt`, InstructionsCore.lean:202). Reuses `word_slt_eq`.

Reachable outcomes: success / stack underflow / out-of-gas (overflow
unreachable for 2-in/1-out).
-/

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

open private boolPush from EvmAsm.Stateless.SpecRef.InstructionsCore

theorem alu_sgt_eq (x y : Nat) (hx : WordWf x) (hy : WordWf y) :
    Evm.Functions.alu_sgt x y = boolPush (toSigned x > toSigned y) := by
  rw [Evm.Functions.alu_sgt, word_slt_eq y x hy hx]
  show (if decide (toSigned y < toSigned x) = true
      then ((1 : Int)).toNat else ((0 : Int)).toNat)
    = if decide (toSigned x > toSigned y) = true then 1 else 0
  split <;> rfl

open Evm.Functions in
/-- **SGT, all reachable outcomes.** -/
theorem sgt_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iSgt sRef)
      (runS (Evm.Functions.execute (.SGT ()) pc_in top mem g) hs ss) :=
  binop_step_equiv (.SGT ()) G_verylow alu_sgt iSgt GasCosts.OPCODE_SGT
    (fun x y => boolPush (toSigned x > toSigned y)) rfl rfl
    ⟨rfl, fun _ _ _ _ => rfl⟩
    (fun x y hx hy => alu_sgt_eq x y hx hy)
    (fun _ _ _ _ => boolPush_wf _)
    sRef top g hs ss mem pc_in hrel hpc

end EvmSpecsVerify
