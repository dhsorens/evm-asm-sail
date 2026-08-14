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

/-! ## Bit length

`CLZ` computes `256 - word_bit_length`: the extraction reads 64-bit limbs
top-down (`word_bit_length`, Prelude.lean:604) and measures the highest
nonzero limb by `BitVec.clz` (`u64_bit_length`); SpecRef writes the same
quantity as `Nat.log2 x + 1` for `x ≠ 0`. The facts below identify the two,
limb by limb.
-/

/-- `get_slice_int` at width 64 and offset `s` of a `Nat` is the 64-bit
field starting at bit `s`. -/
theorem get_slice_int_64 (v s : Nat) :
    Sail.get_slice_int 64 (v : Int) s = BitVec.ofNat 64 (v / 2 ^ s) := by
  have hofInt : BitVec.ofInt (s + 64 + 1) (v : Int)
      = BitVec.ofNat (s + 64 + 1) v := by simp
  apply BitVec.eq_of_toNat_eq
  simp only [Sail.get_slice_int, hofInt, BitVec.extractLsb', BitVec.toNat_ofNat]
  rw [Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ (s + 64 + 1) = 2 ^ s * 2 ^ 65 from by
      rw [← Nat.pow_add],
    Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

/-- `clzAuxRec` scanning down from `n` finds the highest set bit `j ≤ n`. -/
theorem clzAuxRec_eq_of_highest {w : Nat} (x : BitVec w) (j n : Nat)
    (hj : j ≤ n) (hset : x.getLsbD j = true)
    (habove : ∀ i, j < i → x.getLsbD i = false) :
    x.clzAuxRec n = BitVec.ofNat w (w - 1 - j) := by
  induction n with
  | zero =>
    have hj0 : j = 0 := by omega
    subst hj0
    simp [BitVec.clzAuxRec_zero, hset]
  | succ n ih =>
    by_cases hj1 : j = n + 1
    · subst hj1
      simp [BitVec.clzAuxRec_succ, hset]
    · rw [BitVec.clzAuxRec_succ, habove (n + 1) (by omega)]
      simp only [Bool.false_eq_true, if_false]
      exact ih (by omega)

/-- `u64_bit_length` is `Nat.log2`-based bit length on 64-bit values. -/
theorem u64_bit_length_eq (v : Nat) (hv : v < 2 ^ 64) :
    Evm.Functions.u64_bit_length v = if v = 0 then 0 else Nat.log2 v + 1 := by
  simp only [Evm.Functions.u64_bit_length, get_slice_int_64, Nat.pow_zero,
    Nat.div_one, Sail.BitVec.countLeadingZeros]
  by_cases hz : v = 0
  · subst hz
    have hclz : (BitVec.ofNat 64 0).clz = BitVec.ofNat 64 64 :=
      (BitVec.clz_eq_iff_eq_zero (x := BitVec.ofNat 64 0)).mpr rfl
    rw [hclz, if_pos rfl]
    decide
  · have hlog : Nat.log2 v < 64 := (Nat.log2_lt hz).mpr hv
    have hset : (BitVec.ofNat 64 v).getLsbD (Nat.log2 v) = true := by
      show (BitVec.ofNat 64 v).toNat.testBit (Nat.log2 v) = true
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv,
        Nat.testBit_eq_decide_div_mod_eq]
      have h1 : 2 ^ Nat.log2 v ≤ v := Nat.log2_self_le hz
      have h2 : v < 2 ^ (Nat.log2 v + 1) := Nat.lt_log2_self
      rw [Nat.pow_succ] at h2
      have hdiv : v / 2 ^ Nat.log2 v = 1 := by
        have hle : 1 ≤ v / 2 ^ Nat.log2 v :=
          (Nat.one_le_div_iff (Nat.two_pow_pos _)).mpr h1
        have hlt : v / 2 ^ Nat.log2 v < 2 := Nat.div_lt_of_lt_mul h2
        omega
      simp [hdiv]
    have habove : ∀ i, Nat.log2 v < i →
        (BitVec.ofNat 64 v).getLsbD i = false := by
      intro i hi
      show (BitVec.ofNat 64 v).toNat.testBit i = false
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_log2_self
        (Nat.pow_le_pow_right (by omega) (by omega)))
    have hclz : (BitVec.ofNat 64 v).clz = BitVec.ofNat 64 (63 - Nat.log2 v) :=
      clzAuxRec_eq_of_highest _ (Nat.log2 v) 63 (by omega) hset habove
    rw [hclz, if_neg hz, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega

/-- Dividing by `2^k` shifts `Nat.log2` down by `k` (in range). -/
theorem log2_div_pow (v k : Nat) (h : 2 ^ k ≤ v) :
    Nat.log2 v = k + Nat.log2 (v / 2 ^ k) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    show Nat.log2 v = (k + 1) + Nat.log2 (v / 2 ^ (k + 1))
    have hk : (0 : Nat) < 2 ^ k := Nat.two_pow_pos k
    have hs : (2 : Nat) ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ ..
    have hpos : (2 : Nat) ^ k ≤ v / 2 := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      omega
    have h2 : 2 ≤ v := by omega
    rw [Nat.log2_def v, if_pos h2, ih (v / 2) hpos, Nat.div_div_eq_div_mul,
      show (2 : Nat) * 2 ^ k = 2 ^ (k + 1) from by rw [hs, Nat.mul_comm]]
    omega

/-- `word_bit_length` is `Nat.log2`-based bit length on well-formed words. -/
theorem word_bit_length_eq (v : Nat) (hv : WordWf v) :
    Evm.Functions.word_bit_length v = if v = 0 then 0 else Nat.log2 v + 1 := by
  unfold WordWf at hv
  have hdivlt : ∀ s t b : Nat, v < 2 ^ b → s + t = b → v / 2 ^ s < 2 ^ t := by
    intro s t b hb hst
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    calc v < 2 ^ b := hb
      _ = 2 ^ t * 2 ^ s := by rw [← Nat.pow_add]; congr 1; omega
  have hstep : ∀ s : Nat, 2 ^ s ≤ v → v / 2 ^ s ≠ 0 → v ≠ 0 →
      s + (if v / 2 ^ s = 0 then 0 else Nat.log2 (v / 2 ^ s) + 1)
        = if v = 0 then 0 else Nat.log2 v + 1 := by
    intro s hge hne hvne
    rw [if_neg hne, if_neg hvne, log2_div_pow v s hge]
    omega
  have hofNat : ∀ n : Nat, Int.ofNat n = (n : Int) := fun _ => rfl
  simp only [Evm.Functions.word_bit_length, get_slice_int_64,
    Sail.BitVec.toNatInt, BitVec.toNat_ofNat, hofNat, Int.toNat_natCast,
    bne_iff_ne, ne_eq, Int.natCast_eq_zero, ite_not,
    Nat.mod_eq_of_lt (hdivlt 192 64 256 hv rfl)]
  by_cases h192 : v / 2 ^ 192 = 0
  · rw [if_pos h192]
    have hv192 : v < 2 ^ 192 := by
      have h := Nat.div_eq_zero_iff.mp h192; omega
    rw [Nat.mod_eq_of_lt (hdivlt 128 64 192 hv192 rfl)]
    by_cases h128 : v / 2 ^ 128 = 0
    · rw [if_pos h128]
      have hv128 : v < 2 ^ 128 := by
        have h := Nat.div_eq_zero_iff.mp h128; omega
      rw [Nat.mod_eq_of_lt (hdivlt 64 64 128 hv128 rfl)]
      by_cases h64 : v / 2 ^ 64 = 0
      · rw [if_pos h64]
        have hv64 : v < 2 ^ 64 := by
          have h := Nat.div_eq_zero_iff.mp h64; omega
        simp only [Nat.pow_zero, Nat.div_one]
        rw [Nat.mod_eq_of_lt hv64, u64_bit_length_eq v hv64]
      · rw [if_neg h64, u64_bit_length_eq _ (hdivlt 64 64 128 hv128 rfl)]
        exact hstep 64 (by by_contra h; exact h64 (Nat.div_eq_of_lt (by omega)))
          h64 (by rintro rfl; simp at h64)
    · rw [if_neg h128, u64_bit_length_eq _ (hdivlt 128 64 192 hv192 rfl)]
      exact hstep 128 (by by_contra h; exact h128 (Nat.div_eq_of_lt (by omega)))
        h128 (by rintro rfl; simp at h128)
  · rw [if_neg h192, u64_bit_length_eq _ (hdivlt 192 64 256 hv rfl)]
    exact hstep 192 (by by_contra h; exact h192 (Nat.div_eq_of_lt (by omega)))
      h192 (by rintro rfl; simp at h192)

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