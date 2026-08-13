import EvmAsmSail.Opcodes.BinopFamily
import EvmAsmSail.Representation.BitwiseWord

/-!
# SHR

Derived through `binop_step_equiv`; the pure lemma goes through the
bitwise-word bridge (`Representation/BitwiseWord.lean`). Reachable outcomes:
success / stack underflow / out-of-gas (overflow unreachable for 2-in/1-out).
-/

set_option maxHeartbeats 1000000

namespace EvmAsmSail

open EvmAsm.Stateless.SpecRef
open Evm.Defs

theorem alu_shr_eq (s v : Nat) (hv : WordWf v) :
    Evm.Functions.alu_shr s v = (if s < 256 then v >>> s else 0) := by
  rw [Evm.Functions.alu_shr]
  by_cases hs : s < 256
  · rw [if_pos (by simpa using hs), if_pos hs, word_shift_right_eq v s hv]
  · rw [if_neg (by simpa using hs), if_neg hs]
    rfl

private theorem shr_wf (s v : Nat) (hv : WordWf v) :
    WordWf (if s < 256 then v >>> s else 0) := by
  unfold WordWf at hv ⊢
  split
  · calc v >>> s ≤ v := Nat.shiftRight_le v s
      _ < 2 ^ 256 := hv
  · exact Nat.two_pow_pos 256

open Evm.Functions in
/-- **SHR, all reachable outcomes.** -/
theorem shr_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iShr sRef)
      (runS (Evm.Functions.execute (.SHR ()) pc_in top mem g) hs ss) :=
  binop_step_equiv (.SHR ()) G_verylow alu_shr iShr GasCosts.OPCODE_SHR
    (fun s v => if s < 256 then v >>> s else 0) rfl rfl
    ⟨rfl, fun _ _ _ _ => rfl⟩
    (fun x y _ hy => alu_shr_eq x y hy)
    (fun x y _ hy => shr_wf x y hy)
    sRef top g hs ss mem pc_in hrel hpc

end EvmAsmSail
