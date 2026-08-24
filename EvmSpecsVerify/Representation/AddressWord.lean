import EvmSpecsVerify.Representation.BitwiseWord
import EvmSpecsVerify.Relations.Warm
import Mathlib.Tactic.IntervalCases

/-!
# Address ↔ word codecs

The env family moves 20-byte addresses in and out of 256-bit words on both
sides, with different codecs:

* the extraction's `address_to_word` (Prelude.lean) appends the 20 bytes
  into a `BitVec 160` and takes `toNat` — big-endian by construction;
  SpecRef pushes `bytesBEtoNat` of the address bytes.
* the extraction's `word_to_address` slices 20 bytes out of the word with
  `get_slice_int` (offsets 152 down to 0); SpecRef's `to_address_masked`
  is `natToBytesBE 20 (x % 2^160)`.

This file identifies the two pairs: `address_to_word_eq` (decode) and
`word_to_address_toList` (encode), on top of the byte-slice/roundtrip
arithmetic from `Relations/Warm.lean` and the disjoint-or facts from
`BitwiseWord.lean`.
-/

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef

/-- Appending bitvectors sums their values (the high half's low bits are
zero). -/
theorem append_toNat_sum (m n : Nat) (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, Nat.shiftLeft_eq, or_high_low _ _ _ y.isLt]

/-- Sail's byte slice of a `Nat` at offset `k`. -/
theorem get_slice_int_byte (x k : Nat) :
    Sail.get_slice_int 8 (x : Int) k = BitVec.ofNat 8 (x >>> k) := by
  have hofInt : BitVec.ofInt (k + 8 + 1) (x : Int)
      = BitVec.ofNat (k + 8 + 1) x := by simp
  apply BitVec.eq_of_toNat_eq
  simp only [Sail.get_slice_int, hofInt, BitVec.extractLsb',
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  exact mod_pow_digit x (k + 8 + 1) k (by omega)

/-- A 20-vector's list, elementwise. -/
theorem vector20_toList (v : Vector (BitVec 8) 20) :
    v.toList = [v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9],
      v[10], v[11], v[12], v[13], v[14], v[15], v[16], v[17], v[18],
      v[19]] := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [Vector.getElem_toList]
    have h20 : i < 20 := by simpa using h1
    interval_cases i <;> simp

/-- **Decode**: the extraction's `address_to_word` is SpecRef's
`bytesBEtoNat` of the same bytes. -/
theorem address_to_word_eq (aV : Vector (BitVec 8) 20) :
    Evm.Functions.address_to_word aV = bytesBEtoNat aV.toList := by
  rw [vector20_toList]
  simp only [Evm.Functions.address_to_word, Sail.BitVec.toNatInt]
  show ((aV[0]! ++ (aV[1]! ++ (aV[2]! ++ (aV[3]! ++ (aV[4]! ++ (aV[5]! ++
      (aV[6]! ++ (aV[7]! ++ (aV[8]! ++ (aV[9]! ++ (aV[10]! ++ (aV[11]! ++
      (aV[12]! ++ (aV[13]! ++ (aV[14]! ++ (aV[15]! ++ (aV[16]! ++ (aV[17]! ++
      (aV[18]! ++ aV[19]!))))))))))))))))))).toNat : Int).toNat = _
  rw [Int.toNat_natCast]
  simp only [append_toNat_sum]
  show _ = aV[0].toNat * 256 ^ 19 + (aV[1].toNat * 256 ^ 18 +
    (aV[2].toNat * 256 ^ 17 + (aV[3].toNat * 256 ^ 16 +
    (aV[4].toNat * 256 ^ 15 + (aV[5].toNat * 256 ^ 14 +
    (aV[6].toNat * 256 ^ 13 + (aV[7].toNat * 256 ^ 12 +
    (aV[8].toNat * 256 ^ 11 + (aV[9].toNat * 256 ^ 10 +
    (aV[10].toNat * 256 ^ 9 + (aV[11].toNat * 256 ^ 8 +
    (aV[12].toNat * 256 ^ 7 + (aV[13].toNat * 256 ^ 6 +
    (aV[14].toNat * 256 ^ 5 + (aV[15].toNat * 256 ^ 4 +
    (aV[16].toNat * 256 ^ 3 + (aV[17].toNat * 256 ^ 2 +
    (aV[18].toNat * 256 ^ 1 + (aV[19].toNat * 256 ^ 0 + 0)))))))))))))))))))
  norm_num

/-- The pushed address word is well-formed (20 bytes < 2^160 < 2^256). -/
theorem address_to_word_wf (aV : Vector (BitVec 8) 20) :
    WordWf (Evm.Functions.address_to_word aV) := by
  rw [address_to_word_eq]
  have h := EvmAsm.EL.RLP.Nat.fromBytesBE_lt aV.toList
  have hlen : aV.toList.length = 20 := by simp
  rw [hlen] at h
  unfold WordWf
  calc bytesBEtoNat aV.toList < 256 ^ 20 := h
    _ < 2 ^ 256 := by norm_num

/-- SpecRef's address mask is the plain 20-byte encoder: the mod is
absorbed by digit stability. -/
theorem to_address_masked_eq (x : Nat) :
    to_address_masked x = natToBytesBE 20 x := by
  unfold EvmAsm.Stateless.SpecRef.to_address_masked
  rw [show (2 : Nat) ^ 160 = 256 ^ 20 from by norm_num, natToBytesBE_mod]

/-- A 32-vector's list, elementwise. -/
theorem vector32_toList (v : Vector (BitVec 8) 32) :
    v.toList = [v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11], v[12], v[13], v[14], v[15], v[16], v[17], v[18], v[19], v[20], v[21], v[22], v[23], v[24], v[25], v[26], v[27], v[28], v[29], v[30], v[31]] := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [Vector.getElem_toList]
    have h32 : i < 32 := by simpa using h1
    interval_cases i <;> simp

/-- **Decode**: the extraction's `hash_to_word` is SpecRef's
`bytesBEtoNat` of the same 32 bytes (the BLOCKHASH value codec). -/
theorem hash_to_word_eq (hV : Vector (BitVec 8) 32) :
    Evm.Functions.hash_to_word hV = bytesBEtoNat hV.toList := by
  rw [vector32_toList]
  simp only [Evm.Functions.hash_to_word, Sail.BitVec.toNatInt]
  show (((hV[0]! ++ (hV[1]! ++ (hV[2]! ++ (hV[3]! ++ (hV[4]! ++ (hV[5]! ++ (hV[6]! ++ (hV[7]! ++ (hV[8]! ++ (hV[9]! ++ (hV[10]! ++ (hV[11]! ++ (hV[12]! ++ (hV[13]! ++ (hV[14]! ++ (hV[15]! ++ (hV[16]! ++ (hV[17]! ++ (hV[18]! ++ (hV[19]! ++ (hV[20]! ++ (hV[21]! ++ (hV[22]! ++ (hV[23]! ++ (hV[24]! ++ (hV[25]! ++ (hV[26]! ++ (hV[27]! ++ (hV[28]! ++ (hV[29]! ++ (hV[30]! ++ (hV[31]!)))))))))))))))))))))))))))))))) : BitVec 256).toNat : Int).toNat = _
  rw [Int.toNat_natCast]
  simp only [append_toNat_sum]
  show _ = hV[0].toNat * 256 ^ 31 + (hV[1].toNat * 256 ^ 30 + (hV[2].toNat * 256 ^ 29 + (hV[3].toNat * 256 ^ 28 + (hV[4].toNat * 256 ^ 27 + (hV[5].toNat * 256 ^ 26 + (hV[6].toNat * 256 ^ 25 + (hV[7].toNat * 256 ^ 24 + (hV[8].toNat * 256 ^ 23 + (hV[9].toNat * 256 ^ 22 + (hV[10].toNat * 256 ^ 21 + (hV[11].toNat * 256 ^ 20 + (hV[12].toNat * 256 ^ 19 + (hV[13].toNat * 256 ^ 18 + (hV[14].toNat * 256 ^ 17 + (hV[15].toNat * 256 ^ 16 + (hV[16].toNat * 256 ^ 15 + (hV[17].toNat * 256 ^ 14 + (hV[18].toNat * 256 ^ 13 + (hV[19].toNat * 256 ^ 12 + (hV[20].toNat * 256 ^ 11 + (hV[21].toNat * 256 ^ 10 + (hV[22].toNat * 256 ^ 9 + (hV[23].toNat * 256 ^ 8 + (hV[24].toNat * 256 ^ 7 + (hV[25].toNat * 256 ^ 6 + (hV[26].toNat * 256 ^ 5 + (hV[27].toNat * 256 ^ 4 + (hV[28].toNat * 256 ^ 3 + (hV[29].toNat * 256 ^ 2 + (hV[30].toNat * 256 ^ 1 + (hV[31].toNat * 256 ^ 0 + 0)))))))))))))))))))))))))))))))
  norm_num

/-- The pushed hash word is well-formed (32 bytes, exactly the word
width). -/
theorem hash_to_word_wf (hV : Vector (BitVec 8) 32) :
    WordWf (Evm.Functions.hash_to_word hV) := by
  rw [hash_to_word_eq]
  have h := EvmAsm.EL.RLP.Nat.fromBytesBE_lt hV.toList
  have hlen : hV.toList.length = 32 := by simp
  rw [hlen] at h
  unfold WordWf
  calc bytesBEtoNat hV.toList < 256 ^ 32 := h
    _ = 2 ^ 256 := by norm_num

set_option maxRecDepth 4000 in
set_option exponentiation.threshold 400 in
/-- The zero hash decodes to the zero word (BLOCKHASH's out-of-window
push). -/
theorem hash_to_word_zero :
    Evm.Functions.hash_to_word Evm.Functions.ZERO_HASH = 0 := by decide

private theorem vector_set!_eq {α : Type} {n : Nat} (v : Vector α n)
    (i : Nat) (a : α) : v.set! i a = v.setIfInBounds i a := rfl

/-- **Encode**: the extraction's `word_to_address`, as bytes, is SpecRef's
`to_address_masked`. -/
theorem word_to_address_toList (x : Nat) :
    (Evm.Functions.word_to_address x).toList = to_address_masked x := by
  rw [to_address_masked_eq,
    show natToBytesBE 20 x
      = [BitVec.ofNat 8 (x >>> 152), BitVec.ofNat 8 (x >>> 144),
         BitVec.ofNat 8 (x >>> 136), BitVec.ofNat 8 (x >>> 128),
         BitVec.ofNat 8 (x >>> 120), BitVec.ofNat 8 (x >>> 112),
         BitVec.ofNat 8 (x >>> 104), BitVec.ofNat 8 (x >>> 96),
         BitVec.ofNat 8 (x >>> 88), BitVec.ofNat 8 (x >>> 80),
         BitVec.ofNat 8 (x >>> 72), BitVec.ofNat 8 (x >>> 64),
         BitVec.ofNat 8 (x >>> 56), BitVec.ofNat 8 (x >>> 48),
         BitVec.ofNat 8 (x >>> 40), BitVec.ofNat 8 (x >>> 32),
         BitVec.ofNat 8 (x >>> 24), BitVec.ofNat 8 (x >>> 16),
         BitVec.ofNat 8 (x >>> 8), BitVec.ofNat 8 (x >>> 0)] from by
      simp [EvmAsm.Stateless.SpecRef.natToBytesBE, List.range_succ]]
  simp [Evm.Functions.word_to_address, Sail.vectorInit, Sail.vectorUpdate,
    Evm.Functions.Address, vector_set!_eq, Vector.toList_setIfInBounds,
    Vector.toList_replicate, List.replicate, get_slice_int_byte]

end EvmSpecsVerify
