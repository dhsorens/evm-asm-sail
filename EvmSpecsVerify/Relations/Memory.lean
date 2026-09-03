import EvmSpecsVerify.Relations.State
import EvmSpecsVerify.Relations.Base
import EvmSpecsVerify.Representation.EvmMemory

/-!
# Memory relation

SpecRef frame memory is `Evm.memory : Bytes`, grown in ceil32-sized steps by
the gas-metered `extendMemory` (its length is always a multiple of 32). The
extraction keeps one shared byte array with per-frame `(base, established)`
windows and grows `established` to the **exact** requested byte
(`establishMemory`); reads past the mark are zero. The faithful relation is
therefore prefix-correspondence up to the mark plus a zero tail up to
SpecRef's 32-aligned length:

* `aligned` — `M.length = ceil32 established` (as `32 * memory_word_count`);
* `bytes` — the established window matches `M`;
* `tail` — `M`'s alignment padding is zero;
* `cap` — the window respects the extraction's u32 memory space.

`MemGasSafe` is the **MM-6** budget hypothesis: the frame can never afford
the word count that would push `established` into the last u32 page, where
`memory_access` fatal-errors (a spec abort) while SpecRef would extend
happily. Real gas budgets sit ~8 orders of magnitude below the bound; see
the mismatch ledger and `Assumptions.lean`.
-/

open private writeArrayBytes readArrayBytes bytesToWord wordBytes zeroMemoryRange
  from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- SpecRef frame memory vs the extraction's active window
(`off` = frame base, `len` = established high-water mark). -/
structure MemoryRel (M : Bytes) (hs : Evm.HostState) (off len : Nat) :
    Prop where
  frame : ∃ frest, hs.memoryFrames
    = ({ base := off, established := len } : Evm.MemoryFrame) :: frest
  aligned : M.length = 32 * Evm.Functions.memory_word_count len
  bytes : ∀ i, i < len → hs.memoryBytes.getD (off + i) 0 = M.getD i 0
  tail : ∀ i, len ≤ i → i < M.length → M.getD i 0 = 0

/-- **MM-6 budget**: the frame's gas cannot pay for the word count
(`2^27`) at which `memory_access`'s u32 range check becomes reachable.
`mem_cost (2^27) = 35\,184\,774\,742\,016` — about eight orders of magnitude
above real block gas limits. Threaded, ledgered in `Assumptions.lean`. -/
def MemGasSafe (M : Bytes) (gasLeft : Nat) : Prop :=
  gasLeft + Evm.Functions.mem_cost
      (Evm.Functions.memory_word_count M.length)
    < Evm.Functions.mem_cost (2 ^ 27)

/-- Success post for the memory family: `StateRel` on the returned live
values, the ALU pc convention, and the returned memory cursor related to
the SpecRef post-memory. -/
def MemPost (sR' : Machine) (step : EvmStep)
    (hs' : Evm.HostState) (ss' : SeqState) : Prop :=
  StateRel sR' step.2.1 step.2.2.2 hs' ss' ∧
  step.1 = sR'.evm.pc ∧
  ∃ (off len : Nat) (msf : EvmMemorySliceFields off len),
    step.2.2.1 = ⟨off, len, msf⟩ ∧
    MemoryRel sR'.evm.memory hs' off len ∧
    MemGasSafe sR'.evm.memory sR'.evm.gasLeft

/-! ## Arithmetic bridges: `ceil32` / word counts / costs -/

/-- The 32-byte required size, in the `u256`-literal spelling the
word-family handlers produce (MLOAD/MSTORE). -/
theorem memory_required_size_32 (x : Nat) :
    Evm.Functions.memory_required_size x (Evm.Functions.u256 32)
      = x + 32 := rfl

theorem memory_word_count_eq (n : Nat) :
    Evm.Functions.memory_word_count n = (n + 31) / 32 := by
  have h : Evm.Functions.memory_word_count n
      = if n % 32 = 0 then n / 32 else n / 32 + 1 := by
    simp only [Evm.Functions.memory_word_count]
    split <;> rename_i hb <;> simp only [beq_iff_eq] at hb
    · rw [if_pos (show n % 32 = 0 from hb)]
      rfl
    · rw [if_neg (show ¬n % 32 = 0 from hb)]
      rfl
  rw [h]
  split <;> rename_i hb <;> omega

theorem ceil32_eq (n : Nat) :
    (ceil32 n : Nat) = 32 * Evm.Functions.memory_word_count n := by
  rw [memory_word_count_eq]
  have h : (ceil32 n : Nat)
      = if n % 32 = 0 then n else n + 32 - n % 32 := by
    simp only [ceil32]
    split <;> rename_i hb <;> simp only [beq_iff_eq] at hb
    · rw [if_pos (show n % 32 = 0 from hb)]
    · rw [if_neg (show ¬n % 32 = 0 from hb)]
  rw [h]
  have key : (if n % 32 = 0 then n else n + 32 - n % 32)
      = 32 * ((n + 31) / 32) := by
    split <;> rename_i hb <;> omega
  exact key

theorem mem_cost_eq (w : Nat) :
    Evm.Functions.mem_cost w = 3 * w + w * w / 512 := by
  show (((3 : Int) * (w : Int)).toNat + ((w : Int) * (w : Int)).toNat / 512)
    = 3 * w + w * w / 512
  rw [← Int.natCast_mul, Int.toNat_natCast]
  omega

theorem mem_cost_mono {w1 w2 : Nat} (h : w1 ≤ w2) :
    Evm.Functions.mem_cost w1 ≤ Evm.Functions.mem_cost w2 := by
  rw [mem_cost_eq, mem_cost_eq]
  have h1 : w1 * w1 ≤ w2 * w2 := Nat.mul_le_mul h h
  have h2 : w1 * w1 / 512 ≤ w2 * w2 / 512 := Nat.div_le_div_right h1
  omega

theorem calculate_memory_gas_cost_eq (n : Nat) :
    calculate_memory_gas_cost n
      = Evm.Functions.mem_cost (Evm.Functions.memory_word_count n) := by
  have h : calculate_memory_gas_cost n
      = (ceil32 n / 32) * GasCosts.MEMORY_PER_WORD
        + (ceil32 n / 32) ^ 2 / 512 := rfl
  rw [h, mem_cost_eq, ceil32_eq]
  have key : ∀ w : Nat, (32 * w / 32) * 3 + (32 * w / 32) ^ 2 / 512
      = 3 * w + w * w / 512 := by
    intro w
    have h32 : 32 * w / 32 = w := by omega
    rw [h32, Nat.pow_two]
    omega
  exact key _

/-- `calculate_gas_extend_memory` over a single extension, closed form. -/
theorem calc_extend_single (msz start size : Nat) :
    calculate_gas_extend_memory msz [(start, size)] =
      if size == 0 then { cost := 0, expandBy := 0 }
      else if ceil32 (start + size) ≤ ceil32 msz then
        { cost := 0, expandBy := 0 }
      else
        { cost := calculate_memory_gas_cost (ceil32 (start + size))
            - calculate_memory_gas_cost (ceil32 msz)
          expandBy := ceil32 (start + size) - ceil32 msz } := by
  simp only [calculate_gas_extend_memory, Id.run, List.forIn_cons,
    List.forIn_nil]
  by_cases h0 : (size == 0) = true
  · rw [if_pos h0]
    simp only [h0, if_true]
    rfl
  · rw [if_neg h0]
    simp only [h0, Bool.false_eq_true, if_false]
    by_cases hle : ceil32 (start + size) ≤ ceil32 msz
    · rw [if_pos hle]
      simp only [hle, if_true]
      rfl
    · rw [if_neg hle]
      simp only [hle, if_false]
      simp
      rfl

/-- **The expansion charges agree** (single extension, aligned SpecRef
memory): SpecRef's `calculate_gas_extend_memory` cost equals the
extraction's `memory_expansion_cost` for the same request. -/
theorem extend_cost_eq (M : Bytes) (off len start size : Nat)
    (msf : EvmMemorySliceFields off len)
    (haligned : M.length = 32 * Evm.Functions.memory_word_count len) :
    (calculate_gas_extend_memory M.length [(start, size)]).cost
      = Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
          (Evm.Functions.memory_required_size start size) := by
  rw [calc_extend_single]
  simp only [Evm.Functions.memory_expansion_cost,
    Evm.Functions.memory_required_size, memory_high_water_eq]
  have hwcM : Evm.Functions.memory_word_count M.length
      = Evm.Functions.memory_word_count len := by
    rw [haligned, memory_word_count_eq, memory_word_count_eq]
    omega
  by_cases h0 : (size == 0) = true
  · simp only [h0, if_true]
    simp [memory_word_count_eq]
  · have h0' : (size == 0) = false := by simpa using h0
    simp only [h0', Bool.false_eq_true, if_false]
    have hwc32 : ∀ x : Nat,
        Evm.Functions.memory_word_count
          (32 * Evm.Functions.memory_word_count x)
        = Evm.Functions.memory_word_count x := by
      intro x
      rw [memory_word_count_eq, memory_word_count_eq]
      omega
    have hcmgc : ∀ x : Nat, calculate_memory_gas_cost (ceil32 x)
        = Evm.Functions.mem_cost (Evm.Functions.memory_word_count x) := by
      intro x
      rw [calculate_memory_gas_cost_eq, ceil32_eq, hwc32]
    have hcmgcM : calculate_memory_gas_cost (ceil32 M.length)
        = Evm.Functions.mem_cost (Evm.Functions.memory_word_count len) := by
      rw [calculate_memory_gas_cost_eq, ceil32_eq, hwc32, hwcM]
    have hiff0 : ∀ a b : Nat, (32 * a ≤ 32 * b) ↔ (a ≤ b) :=
      fun a b => by omega
    have hiff : ((ceil32 (start + size) : Nat) ≤ ceil32 M.length)
        ↔ (Evm.Functions.memory_word_count (start + size)
            ≤ Evm.Functions.memory_word_count len) := by
      rw [ceil32_eq, ceil32_eq, hwcM]
      exact hiff0 _ _
    by_cases hle : Evm.Functions.memory_word_count (start + size)
        ≤ Evm.Functions.memory_word_count len
    · rw [if_pos (hiff.mpr hle), if_pos (by simpa using hle)]
    · rw [if_neg (fun hc => hle (hiff.mp hc)), if_neg (by simpa using hle)]
      show calculate_memory_gas_cost (ceil32 (start + size))
          - calculate_memory_gas_cost (ceil32 M.length) = _
      rw [hcmgc (start + size), hcmgcM]


/-- `calculate_memory_gas_cost` is monotone (via the extraction's
`mem_cost`, which is monotone in the word count). -/
theorem calculate_memory_gas_cost_mono {a b : Nat} (h : a ≤ b) :
    calculate_memory_gas_cost a ≤ calculate_memory_gas_cost b := by
  rw [calculate_memory_gas_cost_eq, calculate_memory_gas_cost_eq]
  exact mem_cost_mono (by
    rw [memory_word_count_eq, memory_word_count_eq]
    exact Nat.div_le_div_right (by omega))

theorem ceil32_idem (n : Nat) : (ceil32 (ceil32 n) : Nat) = ceil32 n := by
  have h : ∀ w : Nat, (32 * w + 31) / 32 = w := by intro w; omega
  rw [ceil32_eq, ceil32_eq, memory_word_count_eq, memory_word_count_eq, h]

theorem ceil32_mono {a b : Nat} (h : a ≤ b) :
    (ceil32 a : Nat) ≤ ceil32 b := by
  rw [ceil32_eq, ceil32_eq, memory_word_count_eq, memory_word_count_eq]
  exact Nat.mul_le_mul_left 32 (Nat.div_le_div_right (by omega))

theorem sub_add_sub_telescope {x y w : Nat} (h1 : x ≤ y) (h2 : y ≤ w) :
    y - x + (w - y) = w - x := by omega
/-- **Two extensions of the same size collapse to their upper range.**
MCOPY is the only handler that requests two ranges
(`[(source, len), (destination, len)]`), and the fold telescopes: the
intermediate `current_size` cancels, so the pair is indistinguishable
from the single extension at `max source destination`. This is what lets
the MCOPY slice reuse `calc_extend_single` / `extend_cost_eq` unchanged. -/
theorem calc_extend_pair_eq_single (msz a b z : Nat) :
    calculate_gas_extend_memory msz [(a, z), (b, z)]
      = calculate_gas_extend_memory msz [(max a b, z)] := by
  by_cases h0 : (z == 0) = true
  · rw [calc_extend_single, if_pos h0]
    simp only [calculate_gas_extend_memory, Id.run, List.forIn_cons,
      List.forIn_nil]
    simp only [h0, if_true]
    rfl
  by_cases hA : (ceil32 (a + z) : Nat) ≤ ceil32 msz
  · -- the source range is already covered; only the destination can extend
    have hLHS : calculate_gas_extend_memory msz [(a, z), (b, z)]
        = calculate_gas_extend_memory msz [(b, z)] := by
      simp only [calculate_gas_extend_memory, Id.run, List.forIn_cons,
        List.forIn_nil]
      simp only [h0, Bool.false_eq_true, if_false]
      rw [if_pos hA]
      rfl
    rw [hLHS, calc_extend_single, calc_extend_single]
    simp only [h0, Bool.false_eq_true, if_false]
    by_cases hB : (ceil32 (b + z) : Nat) ≤ ceil32 msz
    · rw [if_pos hB,
        if_pos (show (ceil32 (max a b + z) : Nat) ≤ ceil32 msz from by
          rcases Nat.le_total a b with h | h
          · rw [show max a b = b from by omega]; exact hB
          · rw [show max a b = a from by omega]; exact hA)]
    · have hab : max a b = b := by
        by_contra hc
        exact hB (le_trans (ceil32_mono (show b + z ≤ a + z by omega)) hA)
      rw [hab, if_neg hB]
  · rw [calc_extend_single]
    simp only [calculate_gas_extend_memory, Id.run, List.forIn_cons,
      List.forIn_nil]
    simp only [h0, Bool.false_eq_true, if_false]
    rw [if_neg hA]
    simp only [pure_bind, bind_assoc]
    rw [ceil32_idem]
    by_cases hB : (ceil32 (b + z) : Nat) ≤ ceil32 (a + z)
    · rw [if_pos hB]
      have hmax : (ceil32 (max a b + z) : Nat) = ceil32 (a + z) := by
        rcases Nat.le_total (a + z) (b + z) with h | h
        · rw [show max a b + z = b + z from by omega]
          exact Nat.le_antisymm hB (ceil32_mono h)
        · rw [show max a b + z = a + z from by omega]
      rw [hmax, if_neg hA]
      simp only [pure_bind]
      show (⟨_, _⟩ : ExtendMemory) = ⟨_, _⟩
      congr 1 <;> show (_ : Nat) = _ <;> omega
    · rw [if_neg hB]
      have hmA : (ceil32 msz : Nat) < ceil32 (a + z) := Nat.lt_of_not_le hA
      have hAB : (ceil32 (a + z) : Nat) < ceil32 (b + z) := Nat.lt_of_not_le hB
      have halt : a < b := by
        by_contra hc
        exact hB (ceil32_mono (show b + z ≤ a + z by omega))
      rw [show max a b + z = b + z from by omega,
        if_neg (Nat.not_le.mpr (lt_trans hmA hAB))]
      have hle : calculate_memory_gas_cost (ceil32 msz)
          ≤ calculate_memory_gas_cost (ceil32 (a + z)) :=
        calculate_memory_gas_cost_mono (Nat.le_of_lt hmA)
      have hle2 : calculate_memory_gas_cost (ceil32 (a + z))
          ≤ calculate_memory_gas_cost (ceil32 (b + z)) :=
        calculate_memory_gas_cost_mono (Nat.le_of_lt hAB)
      simp only [pure_bind]
      show (⟨_, _⟩ : ExtendMemory) = ⟨_, _⟩
      congr 1
      · show 0 + _ + _ = _
        rw [Nat.zero_add]
        exact sub_add_sub_telescope hle hle2
      · show 0 + _ + _ = _
        rw [Nat.zero_add]
        exact sub_add_sub_telescope (Nat.le_of_lt hmA) (Nat.le_of_lt hAB)

theorem wc_mono {a b : Nat} (h : a ≤ b) :
    Evm.Functions.memory_word_count a ≤ Evm.Functions.memory_word_count b := by
  rw [memory_word_count_eq, memory_word_count_eq]
  exact Nat.div_le_div_right (by omega)

theorem le_32_wc (n : Nat) : n ≤ 32 * Evm.Functions.memory_word_count n := by
  rw [memory_word_count_eq]
  omega

/-- **MM-6 discharge**: an affordable expansion stays clear of the u32
range check in `memory_access`. -/
theorem safe_required_bound (M : Bytes) (off len req g gLeft : Nat)
    (msf : EvmMemorySliceFields off len)
    (haligned : M.length = 32 * Evm.Functions.memory_word_count len)
    (hsafe : MemGasSafe M gLeft)
    (hg : g ≤ gLeft)
    (hafford : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ req ≤ g) :
    req ≤ 2 ^ 32 - 32 := by
  by_contra hcon
  push Not at hcon
  have hwcreq : 2 ^ 27 ≤ Evm.Functions.memory_word_count req := by
    rw [memory_word_count_eq]
    omega
  have hwlen : Evm.Functions.memory_word_count M.length
      = Evm.Functions.memory_word_count len := by
    rw [haligned, memory_word_count_eq, memory_word_count_eq]
    omega
  unfold MemGasSafe at hsafe
  rw [hwlen] at hsafe
  have hlenlt : Evm.Functions.memory_word_count len < 2 ^ 27 := by
    by_contra hc
    push Not at hc
    have := mem_cost_mono hc
    omega
  have hcost : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ req
      = Evm.Functions.mem_cost (Evm.Functions.memory_word_count req)
        - Evm.Functions.mem_cost (Evm.Functions.memory_word_count len) := by
    simp only [Evm.Functions.memory_expansion_cost, memory_high_water_eq]
    rw [if_neg (by simpa using Nat.not_le.mpr (by omega :
      Evm.Functions.memory_word_count len
        < Evm.Functions.memory_word_count req))]
  rw [hcost] at hafford
  have hmono := mem_cost_mono hwcreq
  omega

/-! ## List-side read/write characterizations -/

theorem list_getD_append (l1 l2 : Bytes) (i : Nat) :
    (l1 ++ l2).getD i 0 =
      if i < l1.length then l1.getD i 0 else l2.getD (i - l1.length) 0 := by
  simp only [List.getD]
  by_cases h : i < l1.length
  · rw [if_pos h, List.getElem?_append_left h]
  · rw [if_neg h, List.getElem?_append_right (by omega)]

theorem list_getD_replicate (n : Nat) (i : Nat) :
    (List.replicate n (0x00 : byte)).getD i 0 = 0 := by
  simp only [List.getD, List.getElem?_replicate]
  by_cases h : i < n <;> simp [h]

theorem memory_read_bytes_length (M : Bytes) (pos size : Nat)
    (h : pos + size ≤ M.length) :
    (memory_read_bytes M pos size).length = size := by
  simp only [memory_read_bytes, List.length_take, List.length_drop]
  omega

theorem memory_read_bytes_getElem (M : Bytes) (pos size i : Nat)
    (hi : i < size) :
    (memory_read_bytes M pos size).getD i 0 = M.getD (pos + i) 0 := by
  simp only [memory_read_bytes, List.getD]
  rw [List.getElem?_take_of_lt hi, List.getElem?_drop]

/-- Byte lists of equal length agreeing at every `getD` are equal. -/
theorem list_eq_of_getD (l1 l2 : Bytes) (hlen : l1.length = l2.length)
    (h : ∀ i, i < l1.length → l1.getD i 0 = l2.getD i 0) : l1 = l2 := by
  apply List.ext_getElem hlen
  intro i h1 h2
  have hi := h i h1
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2] using hi

open Evm.Functions in
/-- **The bulk read agrees.** Inside the established window, the host's
`readArrayBytes` off the shared array is SpecRef's `memory_read_bytes`.
MCOPY is the first handler whose *source* is memory itself, so this is
the read direction of `memoryRel_write`. -/
theorem memoryRel_read (M : Bytes) (hs : Evm.HostState)
    (off len src l : Nat)
    (hrel : MemoryRel M hs off len) (hin : src + l ≤ len) :
    readArrayBytes hs.memoryBytes (off + src) l = memory_read_bytes M src l := by
  obtain ⟨-, haligned, hbytes, -⟩ := hrel
  have hlenM : len ≤ M.length := by
    have := le_32_wc len
    omega
  refine list_eq_of_getD _ _ ?_ ?_
  · rw [readArrayBytes_length, memory_read_bytes_length M src l (by omega)]
  · intro i hi
    rw [readArrayBytes_length] at hi
    rw [readArrayBytes_getD _ _ _ _ hi,
      memory_read_bytes_getElem M src l i hi,
      show off + src + i = off + (src + i) from by omega]
    exact hbytes (src + i) (by omega)

theorem memory_write_length (M val : Bytes) (pos : Nat)
    (h : pos + val.length ≤ M.length) :
    (memory_write M pos val).length = M.length := by
  simp only [memory_write, List.length_append, List.length_take,
    List.length_drop]
  omega

theorem memory_write_getD (M val : Bytes) (pos i : Nat)
    (h : pos + val.length ≤ M.length) :
    (memory_write M pos val).getD i 0 =
      if pos ≤ i ∧ i < pos + val.length then val.getD (i - pos) 0
      else M.getD i 0 := by
  have hlt : (List.take pos M).length = pos := by simp; omega
  simp only [memory_write, List.getD, List.append_assoc]
  by_cases h1 : i < pos
  · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt h1,
      if_neg (by omega)]
  · rw [List.getElem?_append_right (by rw [hlt]; omega), hlt]
    by_cases h2 : i < pos + val.length
    · rw [List.getElem?_append_left (by omega), if_pos (by omega)]
    · rw [List.getElem?_append_right (by omega), if_neg (by omega),
        List.getElem?_drop,
        show pos + val.length + (i - pos - val.length) = i from by omega]

/-! ## Relation preservation -/

private theorem hostState_set_memoryBytes (hs : Evm.HostState)
    (a : Array byte) :
    ({ hs with memoryBytes := a } : Evm.HostState).memoryBytes = a := rfl

open Evm.Functions in
/-- Expansion preserves the relation: SpecRef appends its ceil32-sized zero
block while the host zero-fills `[len, req)` and raises the mark. Covers
the `expandBy = 0` case (`wc req = wc len`) with an empty append. -/
theorem memoryRel_expand (M : Bytes) (hs : Evm.HostState)
    (off len req : Nat) (frest : List Evm.MemoryFrame)
    (hrel : MemoryRel M hs off len)
    (hgrow : len < req) :
    MemoryRel
      (M ++ List.replicate
        (32 * Evm.Functions.memory_word_count req - M.length) 0x00)
      { hs with
        memoryBytes := zeroMemoryRange hs.memoryBytes (off + len) (req - len)
        memoryFrames :=
          ({ base := off, established := req } : Evm.MemoryFrame) :: frest }
      off req := by
  obtain ⟨_, haligned, hbytes, htail⟩ := hrel
  have hML : M.length = 32 * Evm.Functions.memory_word_count len := haligned
  have hwcle : Evm.Functions.memory_word_count len
      ≤ Evm.Functions.memory_word_count req := wc_mono (by omega)
  have hreq32 : req ≤ 32 * Evm.Functions.memory_word_count req := le_32_wc req
  have hlen32 : len ≤ 32 * Evm.Functions.memory_word_count len := le_32_wc len
  refine ⟨⟨frest, rfl⟩, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate]
    omega
  · intro i hi
    show (zeroMemoryRange hs.memoryBytes (off + len) (req - len)).getD
        (off + i) 0 = _
    rw [zeroMemoryRange_getD, list_getD_append]
    by_cases hlt : i < len
    · rw [if_neg (by omega), if_pos (by omega)]
      exact hbytes i hlt
    · rw [if_pos (by omega)]
      by_cases hM : i < M.length
      · rw [if_pos hM, htail i (by omega) hM]
      · rw [if_neg hM, list_getD_replicate]
  · intro i hge hi
    simp only [List.length_append, List.length_replicate] at hi
    rw [list_getD_append]
    by_cases hM : i < M.length
    · rw [if_pos hM]
      exact htail i (by omega) hM
    · rw [if_neg hM, list_getD_replicate]

open Evm.Functions in
/-- The zero-padded host word read is SpecRef's in-range memory read. -/
theorem memoryRel_read_word (M : Bytes) (hs : Evm.HostState)
    (off len pos : Nat)
    (hrel : MemoryRel M hs off len)
    (h32 : pos + 32 ≤ len) :
    bytesToWord ((List.range 32).map fun i =>
        if pos + i < len then hs.memoryBytes.getD (off + pos + i) 0 else 0)
      = bytesBEtoNat (memory_read_bytes M pos 32) := by
  obtain ⟨_, haligned, hbytes, _⟩ := hrel
  have hlenM : len ≤ M.length := by
    have := le_32_wc len
    omega
  rw [bytesToWord_eq]
  congr 1
  apply List.ext_getElem
  · rw [memory_read_bytes_length M pos 32 (by omega)]
    simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    rw [if_pos (by omega)]
    have hrd := memory_read_bytes_getElem M pos 32 i h1
    simp only [List.getD] at hrd
    rw [List.getElem?_eq_getElem h2] at hrd
    simp only [Option.getD_some] at hrd
    rw [hrd]
    have hb := hbytes (pos + i) (by omega)
    rw [show off + pos + i = off + (pos + i) from by omega, hb]
    rfl

set_option maxRecDepth 4000 in
open Evm.Functions in
/-- An in-established word store preserves the relation, with SpecRef's
`memory_write` of the 32-byte big-endian encoding on the other side. -/
theorem memoryRel_store (M : Bytes) (hs : Evm.HostState)
    (off len pos v : Nat)
    (hrel : MemoryRel M hs off len)
    (h32 : pos + 32 ≤ len) :
    MemoryRel (memory_write M pos (toBeBytes32 v))
      { hs with memoryBytes :=
          writeArrayBytes hs.memoryBytes (off + pos) (wordBytes v) }
      off len := by
  obtain ⟨⟨frest, hframe⟩, haligned, hbytes, htail⟩ := hrel
  have hval32 : (toBeBytes32 v).length = 32 := by
    simp [EvmAsm.Stateless.SpecRef.toBeBytes32,
      EvmAsm.Stateless.SpecRef.natToBytesBE]
  have hlenM : len ≤ M.length := by
    have := le_32_wc len
    omega
  have hwl : pos + (toBeBytes32 v).length ≤ M.length := by omega
  refine ⟨⟨frest, hframe⟩, ?_, ?_, ?_⟩
  · rw [memory_write_length M _ pos hwl]
    exact haligned
  · intro i hi
    rw [hostState_set_memoryBytes (hs := hs), writeArrayBytes_getD,
      memory_write_getD M _ pos i hwl]
    have hwb : (wordBytes v).length = 32 := by
      rw [wordBytes_eq]
      simp [EvmAsm.Stateless.SpecRef.natToBytesBE]
    rw [hwb, hval32]
    by_cases hin : pos ≤ i ∧ i < pos + 32
    · rw [if_pos (by omega), if_pos (by omega)]
      rw [show off + i - (off + pos) = i - pos from by omega, wordBytes_eq]
      rfl
    · rw [if_neg (by omega), if_neg (by omega)]
      exact hbytes i hi
  · intro i hge hi
    rw [memory_write_length M _ pos hwl] at hi
    rw [memory_write_getD M _ pos i hwl, if_neg (by omega)]
    exact htail i hge hi


/-- A zero-length splice is a no-op at every position. -/
theorem memory_write_nil (M : Bytes) (pos : Nat) :
    memory_write M pos [] = M := by
  simp [memory_write]

open Evm.Functions in
/-- An in-established bulk write preserves the relation: the **same** byte
list spliced by SpecRef's `memory_write` and by the host's
`writeArrayBytes`. (`memoryRel_store` is the 32-byte word instance.) -/
theorem memoryRel_write (M : Bytes) (hs : Evm.HostState)
    (off len pos : Nat) (val : Bytes)
    (hrel : MemoryRel M hs off len)
    (hin : pos + val.length ≤ len) :
    MemoryRel (memory_write M pos val)
      { hs with memoryBytes :=
          writeArrayBytes hs.memoryBytes (off + pos) val }
      off len := by
  obtain ⟨⟨frest, hframe⟩, haligned, hbytes, htail⟩ := hrel
  have hlenM : len ≤ M.length := by
    have := le_32_wc len
    omega
  have hwl : pos + val.length ≤ M.length := by omega
  refine ⟨⟨frest, hframe⟩, ?_, ?_, ?_⟩
  · rw [memory_write_length M _ pos hwl]
    exact haligned
  · intro i hi
    rw [hostState_set_memoryBytes (hs := hs), writeArrayBytes_getD,
      memory_write_getD M _ pos i hwl]
    by_cases hband : pos ≤ i ∧ i < pos + val.length
    · rw [if_pos (by omega), if_pos (by omega),
        show off + i - (off + pos) = i - pos from by omega]
    · rw [if_neg (by omega), if_neg (by omega)]
      exact hbytes i hi
  · intro i hge hi
    rw [memory_write_length M _ pos hwl] at hi
    rw [memory_write_getD M _ pos i hwl, if_neg (by omega)]
    exact htail i hge hi

theorem memGasSafe_mono_gas (M : Bytes) {g g' : Nat} (h : g' ≤ g)
    (hsafe : MemGasSafe M g) : MemGasSafe M g' := by
  unfold MemGasSafe at hsafe ⊢
  omega

open Evm.Functions in
/-- The MM-6 budget survives a charged expansion: the gas paid covers
exactly the cost increase of the larger memory. -/
theorem memGasSafe_after_expand (M : Bytes) (off len req gasLeft chg : Nat)
    (msf : EvmMemorySliceFields off len)
    (haligned : M.length = 32 * Evm.Functions.memory_word_count len)
    (hsafe : MemGasSafe M gasLeft)
    (hchg : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ req ≤ chg)
    (hcharge : chg ≤ gasLeft) :
    MemGasSafe
      (M ++ List.replicate
        (32 * Evm.Functions.memory_word_count req - M.length) 0x00)
      (gasLeft - chg) := by
  have hwlen : Evm.Functions.memory_word_count M.length
      = Evm.Functions.memory_word_count len := by
    rw [haligned, memory_word_count_eq, memory_word_count_eq]
    omega
  unfold MemGasSafe at hsafe ⊢
  rw [hwlen] at hsafe
  have hlenM : M.length ≤ 32 * Evm.Functions.memory_word_count req
      ∨ 32 * Evm.Functions.memory_word_count req ≤ M.length := by omega
  have hML' : (M ++ List.replicate
      (32 * Evm.Functions.memory_word_count req - M.length) 0x00).length
      = max M.length (32 * Evm.Functions.memory_word_count req) := by
    simp only [List.length_append, List.length_replicate]
    omega
  rw [hML']
  simp only [Evm.Functions.memory_expansion_cost, memory_high_water_eq]
    at hchg
  by_cases hle : Evm.Functions.memory_word_count req
      ≤ Evm.Functions.memory_word_count len
  · -- no cost; the new high water's words don't exceed the old count
    have hmaxwc : Evm.Functions.memory_word_count
        (max M.length (32 * Evm.Functions.memory_word_count req))
        = Evm.Functions.memory_word_count len := by
      by_cases hm : 32 * Evm.Functions.memory_word_count req ≤ M.length
      · rw [Nat.max_eq_left hm, hwlen]
      · have : max M.length (32 * Evm.Functions.memory_word_count req)
            = 32 * Evm.Functions.memory_word_count req := by omega
        rw [this, memory_word_count_eq, memory_word_count_eq] at *
        omega
    rw [hmaxwc]
    omega
  · rw [if_neg (by simpa using hle)] at hchg
    have hgt : Evm.Functions.memory_word_count len
        < Evm.Functions.memory_word_count req := by omega
    have hmax : max M.length (32 * Evm.Functions.memory_word_count req)
        = 32 * Evm.Functions.memory_word_count req := by
      rw [haligned]
      omega
    rw [hmax]
    have hwc32 : Evm.Functions.memory_word_count
        (32 * Evm.Functions.memory_word_count req)
        = Evm.Functions.memory_word_count req := by
      rw [memory_word_count_eq, memory_word_count_eq]
      omega
    rw [hwc32]
    have hmono := mem_cost_mono (Nat.le_of_lt hgt)
    omega

end EvmSpecsVerify
