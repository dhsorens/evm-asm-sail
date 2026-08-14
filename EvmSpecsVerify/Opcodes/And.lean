import EvmSpecsVerify.Opcodes.Shapes.Binop
import EvmSpecsVerify.Representation.BitwiseWord

/-!
# AND

Derived through `binop_step_equiv`; the pure lemma goes through the
bitwise-word bridge (`Representation/BitwiseWord.lean`). Reachable outcomes:
success / stack underflow / out-of-gas (overflow unreachable for 2-in/1-out).
-/

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

theorem alu_and_eq (a b : Nat) (ha : WordWf a) (hb : WordWf b) :
    Evm.Functions.alu_and a b = a &&& b := by
  rw [Evm.Functions.alu_and, word_and_eq a b ha hb]

private theorem and_wf (a b : Nat) (hb : WordWf b) :
    WordWf (a &&& b) := Nat.and_lt_two_pow a hb

open Evm.Functions in
/-- **AND, all reachable outcomes.** -/
theorem and_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iAnd sRef)
      (runS (Evm.Functions.execute (.AND ()) pc_in top mem g) hs ss) :=
  binop_step_equiv (.AND ()) G_verylow alu_and iAnd GasCosts.OPCODE_AND
    (fun x y => x &&& y) rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩
    (fun x y hx hy => alu_and_eq x y hx hy)
    (fun x y _ hy => and_wf x y hy)
    sRef top g hs ss mem pc_in hrel hpc

end EvmSpecsVerify
