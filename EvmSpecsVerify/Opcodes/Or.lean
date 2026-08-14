import EvmSpecsVerify.Opcodes.Shapes.Binop
import EvmSpecsVerify.Representation.BitwiseWord

/-!
# OR

Derived through `binop_step_equiv`; the pure lemma goes through the
bitwise-word bridge (`Representation/BitwiseWord.lean`). Reachable outcomes:
success / stack underflow / out-of-gas (overflow unreachable for 2-in/1-out).
-/

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

theorem alu_or_eq (a b : Nat) (ha : WordWf a) (hb : WordWf b) :
    Evm.Functions.alu_or a b = a ||| b := by
  rw [Evm.Functions.alu_or, word_or_eq a b ha hb]

private theorem or_wf (a b : Nat) (ha : WordWf a) (hb : WordWf b) :
    WordWf (a ||| b) := Nat.or_lt_two_pow ha hb

open Evm.Functions in
/-- **OR, all reachable outcomes.** -/
theorem or_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iOr sRef)
      (runS (Evm.Functions.execute (.OR ()) pc_in top mem g) hs ss) :=
  binop_step_equiv (.OR ()) G_verylow alu_or iOr GasCosts.OPCODE_OR
    (fun x y => x ||| y) rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩
    (fun x y hx hy => alu_or_eq x y hx hy)
    (fun x y hx hy => or_wf x y hx hy)
    sRef top g hs ss mem pc_in hrel hpc

end EvmSpecsVerify
