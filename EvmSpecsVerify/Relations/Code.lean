import EvmSpecsVerify.Relations.Calldata

/-!
# Code relation

SpecRef keeps the frame's running code inline (`Evm.code : Bytes`); the
extraction keeps it behind the `frame_code` register — a `CodeFields`
slice whose indices window the host's immutable `codeBytes` region
(`code_bytes` erases the jump table into a `CodeRegionSliceFields` with
the same indices).

`CodeRel` bundles the register read with the byte agreement, the way
`JumpdestRel` bundles the jump-table read: the register holds a slice
whose window reads back SpecRef's `evm.code` byte-for-byte. The payoff
lemma is `codeRel_copy` — the extraction's `code_slice_copy_word_offset`
splices exactly SpecRef's zero-padded `buffer_read` (both sides zero-pad
past the code end, so no source-range hypothesis), reusing the calldata
window lemmas. Code regions are immutable witness bytes, so unlike the
nested-frame calldata window there is no separation concern with the
current frame's memory writes.
-/

open private readArrayBytes inputBytesOf codeBytesOf writeArrayBytes
  copySpanIntoMemory copyIntoMemory establishMemory from Evm.HostAxioms

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- The `frame_code` register's slice windows SpecRef's `evm.code`:
register read + length tie + byte agreement over the host code region. -/
def CodeRel (C : Bytes) (hs : Evm.HostState) (ss : SeqState) : Prop :=
  ∃ (off len : Nat) (cf : CodeFields off len),
    ss.regs.get? Register.frame_code = some ⟨off, len, cf⟩ ∧
    len = C.length ∧
    ∀ i, i < len → hs.codeBytes.getD (off + i) 0 = C.getD i 0

open Evm.Functions in
/-- The extraction's code copy is `writeArrayBytes` of SpecRef's
zero-padded `buffer_read`, for every source offset word, provided the
destination range is inside the established window (guaranteed
post-expansion). Stated over the raw window agreement so it applies at
the post-expansion host state (which shares `codeBytes`). -/
theorem codeRel_copy (C : Bytes) (hs : Evm.HostState) (ss : SeqState)
    (off len : Nat) (crf : CodeRegionSliceFields off len)
    (dst src size : Nat)
    (fr : Evm.MemoryFrame) (mfrest : List Evm.MemoryFrame)
    (hframe : hs.memoryFrames = fr :: mfrest)
    (hest : dst + size ≤ fr.established)
    (hlen : len = C.length)
    (hbytes : ∀ i, i < len → hs.codeBytes.getD (off + i) 0 = C.getD i 0) :
    runS (Evm.Functions.code_slice_copy_word_offset ⟨off, len, crf⟩
        dst src size) hs ss =
      .ok ((),
        { hs with
          memoryBytes := writeArrayBytes hs.memoryBytes (fr.base + dst)
            (buffer_read C src size) }) ss := by
  simp only [Evm.Functions.code_slice_copy_word_offset,
    Evm.Functions.code_slice_copy, CodeRegionSliceFields.len]
  by_cases hx : src < len
  · rw [if_pos (by simpa using hx)]
    unfold Evm.Functions.code_region_copy_to_memory
    refine runS_bind_ok (runS_get hs ss) ?_
    unfold copySpanIntoMemory copyIntoMemory
    simp only [codeBytesOf, CodeRegionSliceFields.bytes,
      CodeRegionSliceFields.len]
    rw [window_pad_eq hs.codeBytes off len C src size hlen hbytes]
    refine runS_bind_ok
      (runS_establishMemory_le _ hs ss fr mfrest hframe
        (by rw [buffer_read_length]; exact hest)) ?_
    exact runS_modify _ _ _
  · rw [if_neg (by simpa using hx)]
    unfold Evm.Functions.stateless_input_copy_to_memory
    refine runS_bind_ok (runS_get hs ss) ?_
    unfold copySpanIntoMemory copyIntoMemory
    simp only [inputBytesOf, StatelessInputSliceFields.bytes,
      StatelessInputSliceFields.len]
    rw [window_empty_eq hs.inputBytes C src size (by omega)]
    refine runS_bind_ok
      (runS_establishMemory_le _ hs ss fr mfrest hframe
        (by rw [buffer_read_length]; exact hest)) ?_
    exact runS_modify _ _ _

end EvmSpecsVerify
