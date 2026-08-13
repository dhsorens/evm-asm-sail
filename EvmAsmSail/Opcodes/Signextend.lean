import EvmAsmSail.Opcodes.BinopFamily
import EvmAsmSail.Representation.BitwiseWord
import Mathlib.Tactic.Ring

/-!
# SIGNEXTEND

Sign-extension from a byte boundary. The extraction isolates the sign bit
with shifts and builds the result from masks (`alu_signextend`,
Prelude.lean:543); SpecRef phrases the same value with `%`/`2^k` arithmetic
(`iSignextend`, InstructionsCore.lean:187). The bridge facts
(`shiftRight_and_one`, `div_parity_iff`, `or_fill`) exchange the two forms.

Reachable outcomes: success / stack underflow / out-of-gas (overflow
unreachable for 2-in/1-out).
-/

set_option maxHeartbeats 1000000

namespace EvmAsmSail

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- The SpecRef SIGNEXTEND lambda, named for the proofs below. -/
private def signextendSpec (byte_num value : U256) : U256 :=
  if byte_num > 31 then value
  else
    let bits := (byte_num + 1) * 8
    let low := value % 2 ^ bits
    if low < 2 ^ (bits - 1) then low
    else low + (U256_MOD - 2 ^ bits)

theorem alu_signextend_eq (i v : Nat) (hv : WordWf v) :
    Evm.Functions.alu_signextend i v = signextendSpec i v := by
  have hv' := hv
  unfold WordWf at hv'
  simp only [Evm.Functions.alu_signextend, signextendSpec]
  by_cases hi : i < 32
  · rw [if_pos (by simpa using hi), if_neg (show ¬ i > 31 from by omega)]
    -- widths, with the Sail Int arithmetic normalized away
    have hw : ((i : Int) * 8).toNat + 8 = (i + 1) * 8 := by omega
    have hs : ((i : Int) * 8).toNat + 7 = (i + 1) * 8 - 1 := by omega
    have hwle : (i + 1) * 8 ≤ 256 := by omega
    -- the isolated sign bit is the division parity
    have hshift : Evm.Functions.word_shift_right v (((i : Int) * 8).toNat + 7)
        = v >>> ((i + 1) * 8 - 1) := by
      rw [hs, word_shift_right_eq v _ hv]
    have hone : Evm.Functions.WORD_ONE = 1 := by decide
    have hiso : Evm.Functions.word_and (v >>> ((i + 1) * 8 - 1)) 1
        = v / 2 ^ ((i + 1) * 8 - 1) % 2 := by
      rw [word_and_eq _ _ (by
          unfold WordWf
          calc v >>> ((i + 1) * 8 - 1) ≤ v := Nat.shiftRight_le v _
            _ < 2 ^ 256 := hv') (by unfold WordWf; omega), shiftRight_and_one]
    -- the low mask is 2^w - 1 (also at w = 256, via the wrap in word_sub_word)
    have hmaskend : Evm.Functions.word_shift_left 1
        (((i : Int) * 8).toNat + 8) = 2 ^ ((i + 1) * 8) % 2 ^ 256 := by
      rw [hw, word_shift_left_eq 1 _ (by unfold WordWf; omega)]
      congr 1
      rw [Nat.shiftLeft_eq, Nat.one_mul]
    have hmask : Evm.Functions.word_sub_word (2 ^ ((i + 1) * 8) % 2 ^ 256)
        1 = 2 ^ ((i + 1) * 8) - 1 := by
      rw [Evm.Functions.word_sub_word]
      rcases Nat.lt_or_ge ((i + 1) * 8) 256 with hw256 | hw256
      · rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hw256)]
        rw [if_pos (by simp [Nat.one_le_two_pow])]
      · have hweq : (i + 1) * 8 = 256 := by omega
        rw [hweq, Nat.mod_self]
        rw [if_neg (by simp)]
        decide
    have hmwf : WordWf (2 ^ ((i + 1) * 8) - 1) := by
      unfold WordWf
      have : (2 : Nat) ^ ((i + 1) * 8) ≤ 2 ^ 256 :=
        Nat.pow_le_pow_right (by omega) hwle
      omega
    rw [hone, hshift, hiso, hmaskend, hmask]
    -- case on the sign bit, aligning the two sign tests via div_parity_iff
    have hw1 : (i + 1) * 8 - 1 + 1 = (i + 1) * 8 := by omega
    rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ ((i + 1) * 8 - 1)) with hpar | hpar
    · -- sign clear: the masked value on both sides
      rw [hpar, if_neg (show ¬(((0 : Nat) == 1) = true) from by decide),
        word_and_eq v _ hv hmwf, Nat.and_two_pow_sub_one_eq_mod]
      rw [if_pos (by
        by_contra hbad
        rw [Nat.not_lt] at hbad
        have := (div_parity_iff v ((i + 1) * 8 - 1)).mpr (by rw [hw1]; exact hbad)
        omega)]
    · -- sign set: masked value plus the high fill
      rw [hpar, if_pos (show (((1 : Nat) == 1) = true) from by decide)]
      have hvand : Evm.Functions.word_and v (2 ^ ((i + 1) * 8) - 1)
          = v % 2 ^ ((i + 1) * 8) := by
        rw [word_and_eq v _ hv hmwf, Nat.and_two_pow_sub_one_eq_mod]
      have hnot : Evm.Functions.word_not (2 ^ ((i + 1) * 8) - 1)
          = 2 ^ 256 - 2 ^ ((i + 1) * 8) := by
        rw [word_not_eq _ hmwf]
        omega
      have hlowlt : v % 2 ^ ((i + 1) * 8) < 2 ^ ((i + 1) * 8) :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
      have hple : (2 : Nat) ^ ((i + 1) * 8) ≤ 2 ^ 256 :=
        Nat.pow_le_pow_right (by omega) hwle
      rw [hvand, hnot,
        word_or_eq _ _ (by unfold WordWf; omega) (by
          unfold WordWf
          have := Nat.two_pow_pos ((i + 1) * 8)
          omega),
        or_fill _ _ hwle hlowlt]
      rw [if_neg (by
        rw [Nat.not_lt]
        exact (div_parity_iff v ((i + 1) * 8 - 1)).mp hpar |>.trans (by rw [hw1]))]
      rfl
  · rw [if_neg (by simpa using hi), if_pos (show i > 31 from by omega)]

private theorem signextendSpec_wf (i v : Nat) (hv : WordWf v) :
    WordWf (signextendSpec i v) := by
  unfold WordWf at *
  simp only [signextendSpec]
  by_cases hi : i > 31
  · rw [if_pos hi]
    exact hv
  · rw [if_neg hi]
    have hle : (i + 1) * 8 ≤ 256 := by omega
    have h1 : v % 2 ^ ((i + 1) * 8) < 2 ^ ((i + 1) * 8) :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    have h2 : (2 : Nat) ^ ((i + 1) * 8) ≤ 2 ^ 256 :=
      Nat.pow_le_pow_right (by omega) hle
    split
    · omega
    · unfold U256_MOD
      omega

open Evm.Functions in
/-- **SIGNEXTEND, all reachable outcomes.** -/
theorem signextend_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iSignextend sRef)
      (runS (Evm.Functions.execute (.SIGNEXTEND ()) pc_in top mem g) hs ss) :=
  binop_step_equiv (.SIGNEXTEND ()) G_low alu_signextend iSignextend
    GasCosts.OPCODE_SIGNEXTEND (fun i v => signextendSpec i v) rfl rfl
    ⟨rfl, fun _ _ _ _ => rfl⟩
    (fun x y _ hy => alu_signextend_eq x y hy)
    (fun x y _ hy => signextendSpec_wf x y hy)
    sRef top g hs ss mem pc_in hrel hpc

end EvmAsmSail
