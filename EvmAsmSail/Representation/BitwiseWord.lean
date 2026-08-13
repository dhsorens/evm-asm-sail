import Evm
import Mathlib.Tactic.Ring
import EvmAsm.Stateless.SpecRef
import EvmAsmSail.Representation.SignedWord

/-!
# Bitwise-word bridge

The extraction's bitwise and shift operations round-trip through
`BitVec 256` (`word_and`/`word_or`/`word_xor`/`word_not`/`word_shift_*`,
Prelude.lean:213-373); SpecRef uses `Nat` bitwise operations directly. This
file collapses the round trips to the `Nat` operations for well-formed
words, on top of `get_slice_int_256` from the signed bridge.
-/

namespace EvmAsmSail

open EvmAsm.Stateless.SpecRef

theorem word_and_eq (a b : Nat) (ha : WordWf a) (hb : WordWf b) :
    Evm.Functions.word_and a b = a &&& b := by
  unfold WordWf at ha hb
  simp only [Evm.Functions.word_and, get_slice_int_256]
  show (((BitVec.ofNat 256 a &&& BitVec.ofNat 256 b).toNat : Int)).toNat = a &&& b
  rw [Int.toNat_natCast, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem word_or_eq (a b : Nat) (ha : WordWf a) (hb : WordWf b) :
    Evm.Functions.word_or a b = a ||| b := by
  unfold WordWf at ha hb
  simp only [Evm.Functions.word_or, get_slice_int_256]
  show (((BitVec.ofNat 256 a ||| BitVec.ofNat 256 b).toNat : Int)).toNat = a ||| b
  rw [Int.toNat_natCast, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem word_xor_eq (a b : Nat) (ha : WordWf a) (hb : WordWf b) :
    Evm.Functions.word_xor a b = a ^^^ b := by
  unfold WordWf at ha hb
  simp only [Evm.Functions.word_xor, get_slice_int_256]
  show (((BitVec.ofNat 256 a ^^^ BitVec.ofNat 256 b).toNat : Int)).toNat = a ^^^ b
  rw [Int.toNat_natCast, BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem word_not_eq (a : Nat) (ha : WordWf a) :
    Evm.Functions.word_not a = 2 ^ 256 - 1 - a := by
  unfold WordWf at ha
  simp only [Evm.Functions.word_not, get_slice_int_256]
  show (((~~~BitVec.ofNat 256 a).toNat : Int)).toNat = 2 ^ 256 - 1 - a
  rw [Int.toNat_natCast, BitVec.toNat_not, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha]

theorem word_shift_left_eq (v n : Nat) (hv : WordWf v) :
    Evm.Functions.word_shift_left v n = (v <<< n) % 2 ^ 256 := by
  unfold WordWf at hv
  simp only [Evm.Functions.word_shift_left, get_slice_int_256,
    Evm.Functions.u256]
  show (((BitVec.ofNat 256 v <<< n).toNat : Int)).toNat = (v <<< n) % 2 ^ 256
  rw [Int.toNat_natCast, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hv]

theorem word_shift_right_eq (v n : Nat) (hv : WordWf v) :
    Evm.Functions.word_shift_right v n = v >>> n := by
  unfold WordWf at hv
  simp only [Evm.Functions.word_shift_right, get_slice_int_256]
  show (((BitVec.ofNat 256 v >>> n).toNat : Int)).toNat = v >>> n
  rw [Int.toNat_natCast, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hv]

/-- The low byte, as a mask. -/
theorem word_low_byte_eq (v : Nat) :
    (Evm.Functions.word_low_byte v).toNat = v % 2 ^ 8 := by
  rw [Evm.Functions.word_low_byte]
  have h : Sail.get_slice_int 8 (v : Int) 0 = BitVec.ofNat 8 v := by
    have hofInt : BitVec.ofInt 9 (v : Int) = BitVec.ofNat 9 v := by simp
    apply BitVec.eq_of_toNat_eq
    simp [Sail.get_slice_int, hofInt, BitVec.extractLsb']
  rw [h, BitVec.toNat_ofNat]

/-! ## Disjoint bit ranges and field arithmetic

`SAR` and `SIGNEXTEND` combine a low field with a high fill by `|||`; on the
SpecRef side the same value is written with addition and `%`/`2^k`
arithmetic. The facts below exchange the two forms (generic exponents, so
everything is stated for `Nat.testBit`/division rather than `omega`).
-/

/-- High multiples of `2^w` and values below `2^w` occupy disjoint bits, so
their `|||` is their sum. -/
theorem or_high_low (q w b : Nat) (hb : b < 2 ^ w) :
    (q * 2 ^ w) ||| b = q * 2 ^ w + b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  rcases Nat.lt_or_ge i w with hi | hi
  · -- low bits: the multiple contributes nothing
    have hpow : (2 : Nat) ^ w = 2 ^ i * (2 * 2 ^ (w - i - 1)) := by
      rw [← Nat.pow_succ']
      rw [← Nat.pow_add]
      congr 1
      omega
    have h1 : (q * 2 ^ w).testBit i = false := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      rw [hpow, show q * (2 ^ i * (2 * 2 ^ (w - i - 1)))
          = (q * (2 * 2 ^ (w - i - 1))) * 2 ^ i from by ring,
        Nat.mul_div_cancel _ (Nat.two_pow_pos i),
        show q * (2 * 2 ^ (w - i - 1)) = 2 * (q * 2 ^ (w - i - 1)) from by ring,
        Nat.mul_mod_right]
      decide
    have h2 : (q * 2 ^ w + b).testBit i = b.testBit i := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
      rw [hpow, show q * (2 ^ i * (2 * 2 ^ (w - i - 1))) + b
          = b + (2 * (q * 2 ^ (w - i - 1))) * 2 ^ i from by ring,
        Nat.add_mul_div_right _ _ (Nat.two_pow_pos i),
        show b / 2 ^ i + 2 * (q * 2 ^ (w - i - 1))
          = b / 2 ^ i + (q * 2 ^ (w - i - 1)) * 2 from by ring,
        Nat.add_mul_mod_self_right]
    rw [h1, h2]
    simp
  · -- high bits: the low field contributes nothing
    have h1 : b.testBit i = false :=
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) hi))
    have h2 : (q * 2 ^ w + b).testBit i = (q * 2 ^ w).testBit i := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
      have hsplit : ∀ n : Nat, n / 2 ^ i = n / 2 ^ w / 2 ^ (i - w) := by
        intro n
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
        congr 2
        omega
      rw [hsplit (q * 2 ^ w + b), hsplit (q * 2 ^ w),
        Nat.mul_div_cancel _ (Nat.two_pow_pos w),
        show q * 2 ^ w + b = b + q * 2 ^ w from by ring,
        Nat.add_mul_div_right _ _ (Nat.two_pow_pos w),
        Nat.div_eq_of_lt hb, Nat.zero_add]
    rw [h1, h2]
    simp

/-- The high fill `2^256 - 2^w` absorbs by addition below `2^w`. -/
theorem or_fill (w b : Nat) (hw : w ≤ 256) (hb : b < 2 ^ w) :
    b ||| (2 ^ 256 - 2 ^ w) = b + (2 ^ 256 - 2 ^ w) := by
  have h2 : (2 : Nat) ^ (256 - w) * 2 ^ w = 2 ^ 256 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hfill : (2 : Nat) ^ 256 - 2 ^ w = (2 ^ (256 - w) - 1) * 2 ^ w := by
    rw [Nat.sub_mul, Nat.one_mul, h2]
  rw [hfill, Nat.or_comm, or_high_low _ _ _ hb, Nat.add_comm]

/-- The extraction's isolated sign bit is a division-parity test. -/
theorem shiftRight_and_one (v k : Nat) : (v >>> k) &&& 1 = v / 2 ^ k % 2 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

/-- Division parity at `k` is the `2^k` threshold of `v % 2^(k+1)` — the
form SpecRef's SIGNEXTEND sign test takes. -/
theorem div_parity_iff (v k : Nat) :
    v / 2 ^ k % 2 = 1 ↔ 2 ^ k ≤ v % 2 ^ (k + 1) := by
  have hsplit : v % 2 ^ (k + 1) = v % 2 ^ k + 2 ^ k * (v / 2 ^ k % 2) := by
    rw [Nat.pow_succ, Nat.mod_mul]
  have hA : v % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ k) with h | h <;> rw [h] at hsplit
  · constructor
    · intro hbad
      omega
    · intro hle
      omega
  · constructor
    · intro _
      omega
    · intro _
      exact h

end EvmAsmSail