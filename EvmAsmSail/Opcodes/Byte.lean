import EvmAsmSail.Opcodes.BinopFamily
import EvmAsmSail.Representation.BitwiseWord

/-!
# BYTE

Derived through `binop_step_equiv`; the pure lemma goes through the
bitwise-word bridge (`Representation/BitwiseWord.lean`). Reachable outcomes:
success / stack underflow / out-of-gas (overflow unreachable for 2-in/1-out).
-/

set_option maxHeartbeats 1000000

namespace EvmAsmSail

open EvmAsm.Stateless.SpecRef
open Evm.Defs

theorem alu_byte_eq (i x : Nat) (hx : WordWf x) :
    Evm.Functions.alu_byte i x =
      (if i ≥ 32 then 0 else (x >>> ((31 - i) * 8)) &&& 0xFF) := by
  rw [Evm.Functions.alu_byte]
  by_cases hi : i < 32
  · rw [if_pos (by simpa using hi), if_neg (by omega)]
    have hsh : (((31 - (i : Int)) * 8)).toNat = (31 - i) * 8 := by omega
    show ((Evm.Functions.word_low_byte
        (Evm.Functions.word_shift_right x ((((31 : Int) - i) * 8)).toNat)).toNat : Int).toNat = _
    rw [Int.toNat_natCast, hsh,
      word_shift_right_eq x ((31 - i) * 8) hx, word_low_byte_eq]
    rw [show (0xFF : Nat) = 2 ^ 8 - 1 from by decide,
      Nat.and_two_pow_sub_one_eq_mod]
  · rw [if_neg (by simpa using hi), if_pos (by omega)]
    rfl

private theorem byte_wf (i x : Nat) :
    WordWf (if i ≥ 32 then 0 else (x >>> ((31 - i) * 8)) &&& 0xFF) := by
  unfold WordWf
  split
  · exact Nat.two_pow_pos 256
  · calc (x >>> ((31 - i) * 8)) &&& 0xFF ≤ 0xFF := Nat.and_le_right
      _ < 2 ^ 256 := by decide

open Evm.Functions in
/-- **BYTE, all reachable outcomes.** -/
theorem byte_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iByte sRef)
      (runS (Evm.Functions.execute (.BYTE ()) pc_in top mem g) hs ss) :=
  binop_step_equiv (.BYTE ()) G_verylow alu_byte iByte GasCosts.OPCODE_BYTE
    (fun i x => if i ≥ 32 then 0 else (x >>> ((31 - i) * 8)) &&& 0xFF) rfl rfl
    ⟨rfl, fun _ _ _ _ => rfl⟩
    (fun x y hx hy => alu_byte_eq x y hy)
    (fun x y _ _ => byte_wf x y)
    sRef top g hs ss mem pc_in hrel hpc

end EvmAsmSail
