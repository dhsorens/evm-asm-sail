import Evm
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

end EvmAsmSail
