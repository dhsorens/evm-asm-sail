import EvmSpecsVerify.Relations.State
import EvmSpecsVerify.Relations.Memory
import EvmSpecsVerify.Opcodes.Push
import Batteries.Tactic.OpenPrivate

/-!
# Calldata relation

SpecRef keeps the frame's calldata inline (`message.data : Bytes`); the
extraction keeps it behind the `calldata` register — for the stateless top
frame an `InputCalldata` window into the host's `inputBytes` arena, for
nested frames a `MemoryCalldata` window into the parent's memory.

`CalldataRel` covers **both** constructors: whichever window the register
holds reads back SpecRef's data byte-for-byte. What remains for the CALL
family is only *establishing* the `MemoryCalldata` case at frame entry
(CALL must set up a window that reads back the child's `message.data`);
the read path is closed here.

The payoff lemma is `calldataRel_load_word`: the extraction's
`calldata_slice_load_word_offset` (zero past the slice end, `spanWord`
inside) computes exactly SpecRef's `bytesBEtoNat (buffer_read data x 32)`
for **every** popped offset word `x` — both sides zero-pad reads past the
end, so no range hypothesis is needed.
-/

open private readArrayBytes bytesToWord spanWord inputBytesOf
  memoryBytesOf from Evm.HostAxioms

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- The `calldata` register's window reads back SpecRef's `message.data`:
an input-arena window for the stateless top frame, a parent-memory window
for nested frames. -/
def CalldataRel (D : Bytes) (hs : Evm.HostState) (cd : CalldataSlice) :
    Prop :=
  (∃ (off len : Nat) (f : StatelessInputSliceFields off len),
    cd = .InputCalldata ⟨off, len, f⟩ ∧
    len = D.length ∧
    ∀ i, i < len → hs.inputBytes.getD (off + i) 0 = D.getD i 0) ∨
  (∃ (off len : Nat) (f : EvmMemorySliceFields off len),
    cd = .MemoryCalldata ⟨off, len, f⟩ ∧
    len = D.length ∧
    ∀ i, i < len → hs.memoryBytes.getD (off + i) 0 = D.getD i 0)

/-! ## `buffer_read`, elementwise -/

/-- SpecRef's zero-padded buffer read, one byte at a time. -/
theorem buffer_read_getD (buf : Bytes) (p size i : Nat) (hi : i < size) :
    (buffer_read buf p size).getD i 0 = buf.getD (p + i) 0 := by
  simp only [buffer_read]
  rw [list_getD_append]
  by_cases hin : i < ((buf.drop p).take size).length
  · rw [if_pos hin]
    simp only [List.length_take, List.length_drop, lt_min_iff] at hin
    simp only [List.getD, List.getElem?_take_of_lt hin.1,
      List.getElem?_drop]
  · rw [if_neg hin, list_getD_replicate]
    have hlen : ((buf.drop p).take size).length
        = min size (buf.length - p) := by simp
    rw [hlen] at hin
    have hout : buf.length ≤ p + i := by
      rcases Nat.lt_or_ge (buf.length - p) size with hc | hc
      · omega
      · omega
    symm
    simp only [List.getD, List.getElem?_eq_none (by omega), Option.getD_none]

/-- Decoding all-zero padding gives zero. -/
theorem bytesBEtoNat_replicate_zero (n : Nat) :
    bytesBEtoNat (List.replicate n (0x00 : BitVec 8)) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ,
      show bytesBEtoNat ((0x00 : BitVec 8) :: List.replicate m (0x00 : BitVec 8))
        = (0x00 : BitVec 8).toNat
            * 256 ^ (List.replicate m (0x00 : BitVec 8)).length
          + bytesBEtoNat (List.replicate m (0x00 : BitVec 8)) from rfl,
      ih]
    simp

/-- A fully out-of-range buffer read decodes to zero. -/
theorem buffer_read_past_end (buf : Bytes) (p size : Nat)
    (hp : buf.length ≤ p) :
    bytesBEtoNat (buffer_read buf p size) = 0 := by
  have hdrop : buf.drop p = [] := List.drop_eq_nil_of_le hp
  simp only [buffer_read, hdrop, List.take_nil, List.nil_append,
    List.length_nil, Nat.sub_zero]
  exact bytesBEtoNat_replicate_zero size

/-! ## The load-word agreement -/

/-- The shared elementwise core: a byte-window that reads back `D`
decodes, via `spanWord`, to SpecRef's zero-padded 32-byte read. -/
private theorem spanWord_window (arr : Array Evm.Defs.byte) (off len : Nat)
    (D : Bytes) (x : Nat) (hlen : len = D.length)
    (hbytes : ∀ i, i < len → arr.getD (off + i) 0 = D.getD i 0) :
    spanWord (readArrayBytes arr off len) x 32
      = bytesBEtoNat (buffer_read D x 32) := by
  unfold spanWord
  rw [bytesToWord_eq]
  congr 1
  apply List.ext_getElem
  · rw [buffer_read_length]
    simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    have hb : (buffer_read D x 32).getD i 0 = D.getD (x + i) 0 :=
      buffer_read_getD D x 32 i h1
    simp only [List.getD, List.getElem?_eq_getElem h2,
      Option.getD_some] at hb
    rw [hb]
    show (readArrayBytes arr off len).getD (x + i) 0 = D.getD (x + i) 0
    unfold readArrayBytes
    by_cases hxi : x + i < len
    · have : ((List.range len).map fun index =>
          arr.getD (off + index) 0).getD (x + i) 0
          = arr.getD (off + (x + i)) 0 := by
        simp only [List.getD, List.getElem?_map,
          List.getElem?_range hxi, Option.map_some, Option.getD_some]
      rw [this, hbytes (x + i) hxi]
    · have hnone : ((List.range len).map fun index =>
          arr.getD (off + index) 0)[x + i]? = none := by
        rw [List.getElem?_eq_none]
        simpa using hxi
      have hout : D.length ≤ x + i := hlen ▸ Nat.le_of_not_lt hxi
      simp only [List.getD, hnone, Option.getD_none]
      symm
      rw [List.getElem?_eq_none hout]
      rfl

open Evm.Functions in
/-- The extraction's calldata word read is SpecRef's zero-padded 32-byte
read, for every offset word and **either** window constructor. -/
theorem calldataRel_load_word (D : Bytes) (hs : Evm.HostState)
    (ss : SeqState) (cd : CalldataSlice) (x : Nat)
    (hrel : CalldataRel D hs cd) :
    runS (Evm.Functions.calldata_slice_load_word_offset cd x) hs ss =
      .ok (bytesBEtoNat (buffer_read D x 32), hs) ss := by
  rcases hrel with ⟨off, len, f, hcd, hlen, hbytes⟩ |
    ⟨off, len, f, hcd, hlen, hbytes⟩ <;> subst hcd
  · simp only [Evm.Functions.calldata_slice_load_word_offset,
      Evm.Functions.stateless_input_slice_load_word_offset,
      Evm.Functions.stateless_input_slice_load,
      Evm.Functions.stateless_input_load_word,
      StatelessInputSliceFields.len]
    by_cases hx : x < len
    · rw [if_pos (by simpa using hx), if_pos (by simpa using hx)]
      simp only [runS_bind, runS_get, runS_pure]
      congr 2
      show spanWord (inputBytesOf hs ⟨off, len, f⟩) x 32
        = bytesBEtoNat (buffer_read D x 32)
      exact spanWord_window hs.inputBytes off len D x hlen hbytes
    · rw [if_neg (by simpa using hx)]
      simp only [runS_pure]
      rw [buffer_read_past_end D x 32 (by omega),
        show Evm.Functions.ZERO_WORD = 0 from rfl]
  · simp only [Evm.Functions.calldata_slice_load_word_offset,
      Evm.Functions.memory_slice_load_word_offset,
      Evm.Functions.memory_slice_load,
      Evm.Functions.memory_slice_load_word,
      EvmMemorySliceFields.len]
    by_cases hx : x < len
    · rw [if_pos (by simpa using hx), if_pos (by simpa using hx)]
      simp only [runS_bind, runS_get, runS_pure]
      congr 2
      show spanWord (memoryBytesOf hs ⟨off, len, f⟩) x 32
        = bytesBEtoNat (buffer_read D x 32)
      exact spanWord_window hs.memoryBytes off len D x hlen hbytes
    · rw [if_neg (by simpa using hx)]
      simp only [runS_pure]
      rw [buffer_read_past_end D x 32 (by omega),
        show Evm.Functions.ZERO_WORD = 0 from rfl]

end EvmSpecsVerify
