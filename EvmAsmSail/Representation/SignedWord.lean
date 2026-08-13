import Evm
import EvmAsm.Stateless.SpecRef
import EvmAsmSail.Relations.Word

/-!
# Signed-word bridge

The extraction reads two's-complement structure off the raw `Nat` through
`BitVec` operations (`word_bit` for the sign, `word_abs`/`word_negate` for
magnitudes — Prelude.lean); SpecRef works with `toSigned : U256 → Int` /
`fromSigned : Int → U256` (InstructionsCore.lean:106-112). This file proves
the correspondence once, for use by every signed opcode (SDIV, SMOD, SLT,
SGT, SIGNEXTEND, SAR).

Implementation note: `omega` does not normalize `Int` powers, so the
canonical forms below (`fromSigned_eq`, `toSigned_eq`) expose `2^256` as an
`Int` numeral (`(115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int)`); all downstream arithmetic is then plain `omega`.
-/

set_option exponentiation.threshold 300

namespace EvmAsmSail

open EvmAsm.Stateless.SpecRef

/-- SpecRef's `fromSigned`, with the modulus in `omega`-normal form. -/
theorem fromSigned_eq (v : Int) : fromSigned v = (v % (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int)).toNat := by
  unfold fromSigned
  rw [show ((U256_MOD : Nat) : Int) = (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) from by decide]

/-- SpecRef's `toSigned`, with the offset in `omega`-normal form. -/
theorem toSigned_eq (a : Nat) :
    toSigned a = if a < 2 ^ 255 then (a : Int) else (a : Int) - (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) := by
  unfold toSigned
  split <;> rename_i h
  · rfl
  · rw [show ((U256_MOD : Nat) : Int) = (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) from by decide]

/-- Sail's generic bit-slice at width 256 on a `Nat` is `BitVec.ofNat`. -/
theorem get_slice_int_256 (a : Nat) :
    Sail.get_slice_int 256 (a : Int) 0 = BitVec.ofNat 256 a := by
  have h : BitVec.ofInt 257 (a : Int) = BitVec.ofNat 257 a := by simp
  apply BitVec.eq_of_toNat_eq
  simp [Sail.get_slice_int, h, BitVec.extractLsb']

/-- `Nat.testBit` at 255, as an arithmetic bound. -/
theorem testBit_255_eq (a : Nat) :
    a.testBit 255 = decide (2 ^ 255 ≤ a % 2 ^ 256) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : 2 ^ 255 ≤ a % 2 ^ 256 <;> simp [h] <;> omega

/-- The sign bit reads as "at or above `2^255`". -/
theorem word_bit_255_iff (a : Nat) (ha : a < 2 ^ 256) :
    Evm.Functions.word_bit a 255 = 1#1 ↔ 2 ^ 255 ≤ a := by
  rw [Evm.Functions.word_bit, get_slice_int_256, Sail.BitVec.access]
  have h255 : (BitVec.ofNat 256 a)[255]! = a.testBit 255 := by
    rw [getElem!_pos _ _ (by omega), BitVec.getElem_eq_testBit_toNat]
    simp only [BitVec.toNat_ofNat]
    congr 1
    omega
  rw [h255, testBit_255_eq, Nat.mod_eq_of_lt ha]
  by_cases h : 2 ^ 255 ≤ a
  · rw [decide_eq_true h]
    simpa using h
  · rw [decide_eq_false h]
    constructor
    · intro hbad
      exact absurd hbad (by decide)
    · intro hle
      exact absurd hle h

/-- The extraction's negation is SpecRef's `fromSigned` of the negated value. -/
theorem word_negate_eq (q : Nat) (hq : q < 2 ^ 256) :
    Evm.Functions.word_negate q = fromSigned (-(q : Int)) := by
  show Evm.Functions.word_sub_word (((0 : Int)).toNat) q = _
  rw [Evm.Functions.word_sub_word, fromSigned_eq]
  show (if (q ≤ (0 : Nat) : Bool) = true then (0 : Nat) - q
    else ((2 : Int) ^ (256 : Nat)).toNat - 1 - (q - 0) + 1) = _
  rw [show ((2 : Int) ^ (256 : Nat)).toNat = 2 ^ 256 from by decide]
  split <;> rename_i h <;> simp at h <;> omega

/-- `fromSigned` on a small non-negative value is the identity. -/
theorem fromSigned_of_nonneg (v : Int) (h0 : 0 ≤ v) (h : v < 2 ^ 256) :
    fromSigned v = v.toNat := by
  rw [show ((2 : Int) ^ (256 : Nat)) = (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) from by decide] at h
  rw [fromSigned_eq]
  exact (by omega : (v % (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int)).toNat = v.toNat)

/-- `fromSigned` of a small negated magnitude wraps once. -/
theorem fromSigned_neg (m : Nat) (h0 : 0 < m) (h : m ≤ 2 ^ 256) :
    fromSigned (-(m : Int)) = 2 ^ 256 - m := by
  rw [fromSigned_eq]
  exact (by omega : ((-(m : Int)) % (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int)).toNat = 2 ^ 256 - m)

theorem toSigned_of_lt (a : Nat) (h : a < 2 ^ 255) : toSigned a = a := by
  rw [toSigned_eq, if_pos h]

theorem toSigned_of_ge (a : Nat) (h : 2 ^ 255 ≤ a) :
    toSigned a = (a : Int) - (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) := by
  rw [toSigned_eq, if_neg (by omega)]

theorem toSigned_neg_iff (a : Nat) (ha : a < 2 ^ 256) :
    toSigned a < 0 ↔ 2 ^ 255 ≤ a := by
  rw [toSigned_eq]
  split <;> omega

theorem toSigned_eq_zero_iff (a : Nat) (ha : a < 2 ^ 256) :
    toSigned a = 0 ↔ a = 0 := by
  rw [toSigned_eq]
  split <;> omega

theorem natAbs_toSigned_le (a : Nat) (ha : a < 2 ^ 256) :
    (toSigned a).natAbs ≤ 2 ^ 255 := by
  rw [toSigned_eq]
  split <;> omega

/-- The extraction's magnitude is `natAbs` of SpecRef's signed reading. -/
theorem word_abs_eq (a : Nat) (ha : a < 2 ^ 256) :
    Evm.Functions.word_abs a = (toSigned a).natAbs := by
  rw [Evm.Functions.word_abs, toSigned_eq]
  by_cases hs : 2 ^ 255 ≤ a
  · have hbit : (Evm.Functions.word_bit a 255 == 1#1) = true :=
      beq_iff_eq.mpr ((word_bit_255_iff a ha).mpr hs)
    rw [if_pos hbit, word_negate_eq a ha, fromSigned_eq, if_neg (by omega)]
    omega
  · have hbit : (Evm.Functions.word_bit a 255 == 1#1) = false := by
      rw [beq_eq_false_iff_ne]
      intro hbad
      exact absurd ((word_bit_255_iff a ha).mp hbad) hs
    rw [if_neg (by simp [hbit]), if_pos (by omega)]
    omega

end EvmAsmSail
