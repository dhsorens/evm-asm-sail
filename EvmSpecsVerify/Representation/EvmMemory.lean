import EvmSpecsVerify.Representation.EvmMonad
import EvmSpecsVerify.Relations.Word
import EvmAsm.Stateless.SpecRef
import Mathlib.Tactic.Ring
import Batteries.Tactic.OpenPrivate

/-!
# The extraction's frame memory, characterized

`HostState` keeps EVM memory as one byte array (`memoryBytes`) shared by a
stack of frames (`memoryFrames`, head = active; each frame owns
`[base, base + established)`). Bytes past the high-water mark read as zero
(`mem_read_byte` / `mem_load_word`); `establishMemory` zero-fills and raises
the mark. The live `EvmMemorySlice` cursor carries `(base, established)` as
its two Sigma indices — `EvmMemorySliceFields` itself is fieldless.

This file gives the byte-array helpers `getD` characterizations, identifies
the host byte codecs with SpecRef's (`bytesToWord` ↔ `bytesBEtoNat`,
`wordBytes` ↔ `natToBytesBE 32`), and provides `runS` shapes for the memory
host operations the MLOAD/MSTORE/RETURN slices step through.
-/

open private ensureArraySize writeArrayByte writeArrayBytes readArrayBytes
  bytesToWord wordBytes currentMemoryFrame replaceCurrentMemoryFrame
  zeroMemoryRange establishMemory memoryBytesOf from Evm.HostAxioms

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef (Bytes bytesBEtoNat natToBytesBE)
open Evm.Defs

/-! ## Byte-array helpers -/

theorem ensureArraySize_size (a : Array byte) (n : Nat) :
    (ensureArraySize a n).size = max a.size n := by
  unfold ensureArraySize
  split <;> simp <;> omega

theorem ensureArraySize_getD (a : Array byte) (n i : Nat) :
    (ensureArraySize a n).getD i 0 = a.getD i 0 := by
  unfold ensureArraySize
  split
  · rfl
  · rename_i h
    simp only [Array.getD_eq_getD_getElem?]
    by_cases hi : i < a.size
    · rw [Array.getElem?_append_left hi]
    · rw [Array.getElem?_append_right (by omega), Array.getElem?_replicate,
        show a[i]? = none from Array.getElem?_eq_none (by omega)]
      by_cases hi2 : i - a.size < n - a.size <;> simp [hi2]

theorem writeArrayByte_size (a : Array byte) (p : Nat) (v : byte) :
    (writeArrayByte a p v).size = max a.size (p + 1) := by
  unfold writeArrayByte
  simp [ensureArraySize_size]

theorem writeArrayByte_getD_eq (a : Array byte) (p : Nat) (v : byte) :
    (writeArrayByte a p v).getD p 0 = v := by
  unfold writeArrayByte
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_setIfInBounds_self_of_lt
    (by rw [ensureArraySize_size]; omega)]
  rfl

theorem writeArrayByte_getD_ne (a : Array byte) (p : Nat) (v : byte)
    (i : Nat) (h : i ≠ p) :
    (writeArrayByte a p v).getD i 0 = a.getD i 0 := by
  unfold writeArrayByte
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_setIfInBounds_ne (by omega)]
  have hens := ensureArraySize_getD a (p + 1) i
  simp only [Array.getD_eq_getD_getElem?] at hens
  exact hens

/-- Index alignment for the `writeArrayBytes` fold: starting the index
count one later is starting the base one later. -/
private theorem writeArrayBytes_shift (vs : List byte) (p n : Nat)
    (b : Array byte) :
    (vs.zipIdx (n + 1)).foldl
      (fun r pair => writeArrayByte r (p + pair.2) pair.1) b
    = (vs.zipIdx n).foldl
      (fun r pair => writeArrayByte r (p + 1 + pair.2) pair.1) b := by
  induction vs generalizing n b with
  | nil => rfl
  | cons w ws ihw =>
    simp only [List.zipIdx_cons, List.foldl_cons]
    rw [ihw]
    rw [show p + (n + 1) = p + 1 + n from by omega]

/-- The `writeArrayBytes` fold, characterized index-wise. -/
theorem writeArrayBytes_getD (vs : List byte) (a : Array byte) (p i : Nat) :
    (writeArrayBytes a p vs).getD i 0 =
      if p ≤ i ∧ i < p + vs.length then vs.getD (i - p) 0
      else a.getD i 0 := by
  induction vs generalizing a p with
  | nil =>
    unfold writeArrayBytes
    simp
  | cons v vs ih =>
    have hstep : writeArrayBytes a p (v :: vs)
        = writeArrayBytes (writeArrayByte a p v) (p + 1) vs := by
      unfold writeArrayBytes
      rw [show (v :: vs).zipIdx = (v, 0) :: vs.zipIdx 1 from by
        simp [List.zipIdx]]
      simp only [List.foldl_cons, Nat.add_zero]
      exact writeArrayBytes_shift vs p 0 _
    rw [hstep, ih]
    by_cases hi : p + 1 ≤ i ∧ i < p + 1 + vs.length
    · rw [if_pos hi, if_pos (by simp only [List.length_cons]; omega)]
      rw [show i - p = (i - (p + 1)) + 1 from by omega]
      rfl
    · rw [if_neg hi]
      by_cases hip : i = p
      · subst hip
        rw [if_pos (by simp only [List.length_cons]; omega),
          writeArrayByte_getD_eq]
        simp
      · rw [if_neg (by simp only [List.length_cons]; omega),
          writeArrayByte_getD_ne _ _ _ _ hip]

theorem zeroFold_size (count : Nat) (b : Array byte) (start : Nat) :
    ((List.range count).foldl (fun r j => r.set! (start + j) 0) b).size
      = b.size := by
  induction count generalizing b with
  | zero => rfl
  | succ c ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil,
      Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    exact ih b

theorem zeroFold_getD (count : Nat) (b : Array byte) (start i : Nat)
    (hsz : start + count ≤ b.size) :
    ((List.range count).foldl (fun r j => r.set! (start + j) 0) b).getD i 0
      = if start ≤ i ∧ i < start + count then 0 else b.getD i 0 := by
  induction count generalizing i with
  | zero => simp
  | succ c ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have hsz' : start + c
        < ((List.range c).foldl (fun r j => r.set! (start + j) 0) b).size := by
      rw [zeroFold_size]; omega
    rw [Array.set!_eq_setIfInBounds]
    simp only [Array.getD_eq_getD_getElem?]
    by_cases hic : i = start + c
    · subst hic
      rw [Array.getElem?_setIfInBounds_self_of_lt hsz']
      rw [if_pos (by omega)]
      rfl
    · rw [Array.getElem?_setIfInBounds_ne (by omega)]
      have hihi := ih i (by omega)
      simp only [Array.getD_eq_getD_getElem?] at hihi
      rw [hihi]
      by_cases h1 : start ≤ i ∧ i < start + c
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]

theorem zeroMemoryRange_getD (a : Array byte) (start count i : Nat) :
    (zeroMemoryRange a start count).getD i 0 =
      if start ≤ i ∧ i < start + count then 0 else a.getD i 0 := by
  unfold zeroMemoryRange
  rw [zeroFold_getD count _ start i (by rw [ensureArraySize_size]; omega)]
  by_cases h : start ≤ i ∧ i < start + count
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, ensureArraySize_getD]

/-! ## Byte codecs: host ↔ SpecRef -/

/-- The host fold agrees with the RLP model's big-endian decoder. -/
theorem bytesToWord_eq (bs : List byte) :
    bytesToWord bs = bytesBEtoNat bs := by
  have hgen : ∀ (acc : Nat),
      bs.foldl (fun result value => result * 256 + value.toNat) acc
        = acc * 256 ^ bs.length + bytesBEtoNat bs := by
    induction bs with
    | nil => intro acc; simp [bytesBEtoNat, EvmAsm.EL.RLP.Nat.fromBytesBE]
    | cons b tl ih =>
      intro acc
      simp only [List.foldl_cons, ih, List.length_cons]
      show (acc * 256 + b.toNat) * 256 ^ tl.length + bytesBEtoNat tl
        = acc * 256 ^ (tl.length + 1)
          + (b.toNat * 256 ^ tl.length + bytesBEtoNat tl)
      ring
  unfold bytesToWord
  rw [hgen 0]
  simp

/-- The host word encoder is SpecRef's fixed-width big-endian encoder. -/
theorem wordBytes_eq (v : Nat) : wordBytes v = natToBytesBE 32 v := by
  unfold wordBytes
  unfold EvmAsm.Stateless.SpecRef.natToBytesBE
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_reverse,
      List.length_range]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have h32 : 32 - 1 - i = 31 - i := by omega
    rw [h32, show (2 : Nat) ^ 8 = 256 from by decide,
      Nat.mod_mod_of_dvd _ dvd_rfl]

/-! ## `runS` shapes for the memory host operations -/

theorem memory_high_water_eq (off len : Nat) (msf : EvmMemorySliceFields off len) :
    Evm.Functions.memory_high_water ⟨off, len, msf⟩ = len := rfl

theorem runS_establishMemory_le (required : Nat) (hs : Evm.HostState)
    (ss : SeqState) (fr : Evm.MemoryFrame) (frest : List Evm.MemoryFrame)
    (hframe : hs.memoryFrames = fr :: frest)
    (h : required ≤ fr.established) :
    runS (establishMemory required) hs ss = .ok (fr, hs) ss := by
  unfold establishMemory
  refine runS_bind_ok (runS_get hs ss) ?_
  rw [show currentMemoryFrame hs = fr from by
    unfold currentMemoryFrame; rw [hframe]; rfl]
  rw [if_pos h]
  exact runS_pure _ _ _

theorem runS_establishMemory_grow (required : Nat) (hs : Evm.HostState)
    (ss : SeqState) (base est : Nat) (frest : List Evm.MemoryFrame)
    (hframe : hs.memoryFrames = { base := base, established := est } :: frest)
    (h : est < required) :
    runS (establishMemory required) hs ss =
      .ok (({ base := base, established := required } : Evm.MemoryFrame),
        { hs with
          memoryBytes :=
            zeroMemoryRange hs.memoryBytes (base + est) (required - est)
          memoryFrames :=
            { base := base, established := required } :: frest }) ss := by
  unfold establishMemory
  refine runS_bind_ok (runS_get hs ss) ?_
  rw [show currentMemoryFrame hs
      = ({ base := base, established := est } : Evm.MemoryFrame) from by
    unfold currentMemoryFrame; rw [hframe]; rfl]
  rw [if_neg (by show ¬(required ≤ est); omega)]
  refine runS_bind_ok (runS_set _ _ _) ?_
  show runS (pure _) _ _ = _
  rw [runS_pure]
  unfold replaceCurrentMemoryFrame
  rw [hframe]
  rfl

theorem runS_mem_load_word (pos : Nat) (hs : Evm.HostState) (ss : SeqState)
    (fr : Evm.MemoryFrame) (frest : List Evm.MemoryFrame)
    (hframe : hs.memoryFrames = fr :: frest) :
    runS (Evm.Functions.mem_load_word pos) hs ss =
      .ok (bytesToWord ((List.range 32).map fun i =>
        if pos + i < fr.established then
          hs.memoryBytes.getD (fr.base + pos + i) 0
        else 0), hs) ss := by
  unfold Evm.Functions.mem_load_word
  refine runS_bind_ok (runS_get hs ss) ?_
  rw [show currentMemoryFrame hs = fr from by
    unfold currentMemoryFrame; rw [hframe]; rfl]
  exact runS_pure _ _ _

theorem runS_mem_store_word (pos v : Nat) (hs : Evm.HostState)
    (ss : SeqState) (fr : Evm.MemoryFrame) (frest : List Evm.MemoryFrame)
    (hframe : hs.memoryFrames = fr :: frest)
    (hle : pos + 32 ≤ fr.established) :
    runS (Evm.Functions.mem_store_word pos v) hs ss =
      .ok ((), { hs with
        memoryBytes :=
          writeArrayBytes hs.memoryBytes (fr.base + pos) (wordBytes v) }) ss := by
  unfold Evm.Functions.mem_store_word
  refine runS_bind_ok
    (runS_establishMemory_le (pos + 32) hs ss fr frest hframe hle) ?_
  exact runS_modify _ _ _

theorem runS_mem_expand_grow (required : Nat) (hs : Evm.HostState)
    (ss : SeqState) (base est : Nat) (frest : List Evm.MemoryFrame)
    (hframe : hs.memoryFrames = { base := base, established := est } :: frest)
    (h : est < required) :
    runS (Evm.Functions.mem_expand required) hs ss =
      .ok ((⟨base, required, {}⟩ : EvmMemorySlice),
        { hs with
          memoryBytes :=
            zeroMemoryRange hs.memoryBytes (base + est) (required - est)
          memoryFrames :=
            { base := base, established := required } :: frest }) ss := by
  unfold Evm.Functions.mem_expand
  refine runS_bind_ok
    (runS_establishMemory_grow required hs ss base est frest hframe h) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_expand_memory_le (off len req : Nat)
    (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (h : req ≤ len) :
    runS (Evm.Functions.expand_memory ⟨off, len, msf⟩ req) hs ss =
      .ok ((⟨off, len, msf⟩ : EvmMemorySlice), hs) ss := by
  simp only [Evm.Functions.expand_memory, Evm.Functions.memory_expand_to]
  rw [dif_neg (by simp only [EvmMemorySliceFields.len]; simpa using
    Nat.not_lt.mpr h)]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_expand_memory_grow (off len req : Nat)
    (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (est : Nat) (frest : List Evm.MemoryFrame)
    (hframe : hs.memoryFrames = { base := off, established := est } :: frest)
    (hlen : est = len)
    (h : len < req) :
    runS (Evm.Functions.expand_memory ⟨off, len, msf⟩ req) hs ss =
      .ok ((⟨off, req, {}⟩ : EvmMemorySlice),
        { hs with
          memoryBytes :=
            zeroMemoryRange hs.memoryBytes (off + est) (req - est)
          memoryFrames :=
            { base := off, established := req } :: frest }) ss := by
  subst hlen
  simp only [Evm.Functions.expand_memory, Evm.Functions.memory_expand_to]
  rw [dif_pos (by simp only [EvmMemorySliceFields.len]; simpa using h)]
  refine runS_bind_ok (runS_bind_ok
    (runS_mem_expand_grow req hs ss off est frest hframe h)
    (runS_pure _ _ _)) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_memory_access_ok (start size : Nat) (hs : Evm.HostState)
    (ss : SeqState)
    (h0 : (size == 0) = false)
    (hstart : start ≤ 2 ^ 32 - 1)
    (hsize : size ≤ 2 ^ 32 - 1 - start) :
    runS (Evm.Functions.memory_access start size) hs ss =
      .ok ((⟨start, size, start + size,
        { range := Evm.Functions.memory_range start size }⟩ :
          MemoryAccess), hs) ss := by
  unfold Evm.Functions.memory_access
  rw [dif_neg (by simp only [h0]; decide)]
  rw [dif_pos (by simpa using hstart)]
  rw [dif_pos (by simpa using hsize)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_memory_access_zero (start : Nat) (hs : Evm.HostState)
    (ss : SeqState) :
    runS (Evm.Functions.memory_access start 0) hs ss =
      .ok ((⟨0, 0, 0, Evm.Functions.EMPTY_MEMORY_ACCESS⟩ : MemoryAccess),
        hs) ss := by
  unfold Evm.Functions.memory_access
  rw [dif_pos (by decide)]
  exact runS_pure _ _ _

end EvmSpecsVerify
