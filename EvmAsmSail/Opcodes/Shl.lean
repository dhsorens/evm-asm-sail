import EvmAsmSail.Opcodes.Shapes.Binop
import EvmAsmSail.Representation.BitwiseWord

/-!
# SHL

Derived through `binop_step_equiv`; the pure lemma goes through the
bitwise-word bridge (`Representation/BitwiseWord.lean`). Reachable outcomes:
success / stack underflow / out-of-gas (overflow unreachable for 2-in/1-out).
-/

set_option maxHeartbeats 1000000

namespace EvmAsmSail

open EvmAsm.Stateless.SpecRef
open Evm.Defs

theorem alu_shl_eq (s v : Nat) (hv : WordWf v) :
    Evm.Functions.alu_shl s v = (if s < 256 then wrap256 (v <<< s) else 0) := by
  rw [Evm.Functions.alu_shl]
  by_cases hs : s < 256
  · rw [if_pos (by simpa using hs), if_pos hs, word_shift_left_eq v s hv]
    rfl
  · rw [if_neg (by simpa using hs), if_neg hs]
    rfl

private theorem shl_wf (s v : Nat) :
    WordWf (if s < 256 then wrap256 (v <<< s) else 0) := by
  split
  · exact wrap256_wf _
  · exact Nat.two_pow_pos 256

open Evm.Functions in
/-- **SHL, all reachable outcomes.** -/
theorem shl_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iShl sRef)
      (runS (Evm.Functions.execute (.SHL ()) pc_in top mem g) hs ss) :=
  binop_step_equiv (.SHL ()) G_verylow alu_shl iShl GasCosts.OPCODE_SHL
    (fun s v => if s < 256 then wrap256 (v <<< s) else 0) rfl rfl
    ⟨rfl, fun _ _ _ _ => rfl⟩
    (fun x y _ hy => alu_shl_eq x y hy)
    (fun x y _ _ => shl_wf x y)
    sRef top g hs ss mem pc_in hrel hpc

end EvmAsmSail
