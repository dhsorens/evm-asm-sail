import EvmAsmSail.Opcodes.BinopFamily
import EvmAsmSail.Representation.BitwiseWord

/-!
# XOR

Derived through `binop_step_equiv`; the pure lemma goes through the
bitwise-word bridge (`Representation/BitwiseWord.lean`). Reachable outcomes:
success / stack underflow / out-of-gas (overflow unreachable for 2-in/1-out).
-/

set_option maxHeartbeats 1000000

namespace EvmAsmSail

open EvmAsm.Stateless.SpecRef
open Evm.Defs

theorem alu_xor_eq (a b : Nat) (ha : WordWf a) (hb : WordWf b) :
    Evm.Functions.alu_xor a b = a ^^^ b := by
  rw [Evm.Functions.alu_xor, word_xor_eq a b ha hb]

private theorem xor_wf (a b : Nat) (ha : WordWf a) (hb : WordWf b) :
    WordWf (a ^^^ b) := Nat.xor_lt_two_pow ha hb

open Evm.Functions in
/-- **XOR, all reachable outcomes.** -/
theorem xor_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iXor sRef)
      (runS (Evm.Functions.execute (.XOR ()) pc_in top mem g) hs ss) :=
  binop_step_equiv (.XOR ()) G_verylow alu_xor iXor GasCosts.OPCODE_XOR
    (fun x y => x ^^^ y) rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩
    (fun x y hx hy => alu_xor_eq x y hx hy)
    (fun x y hx hy => xor_wf x y hx hy)
    sRef top g hs ss mem pc_in hrel hpc

end EvmAsmSail
