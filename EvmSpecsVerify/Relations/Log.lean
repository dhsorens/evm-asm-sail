import EvmSpecsVerify.Relations.Memory

/-!
# Log relation

SpecRef keeps a frame's emitted logs inline: `Evm.logs : List Log`, each
`Log` carrying its `address`, a `List Hash32` of topics and a `Bytes`
payload. The extraction keeps a **block-lifetime** store instead —
`HostState.logs : Array LogRecordRow`, where a row holds the address, the
topics as raw `word`s, and only the *span* `(dataOffset, dataLength)` of
its payload inside the shared `logBytes` arena (HostAxioms.lean:1080).

So the relation is a suffix correspondence, indexed by a `base`: the rows
from `base` onward decode to SpecRef's frame-local list. The base is not
cosmetic — SpecRef's `logs` is reset per frame and merged into the parent
on success, while the host array only ever grows within a transaction, so
a frame-local relation cannot pin `logs.size` to the list length alone.

Three encoding steps are folded into the row fields:

* the address is the host's `Vector (BitVec 8) 20` read as a byte list
  (the `haddr` tie ADDRESS/SLOAD already use);
* topics are raw words host-side and 32-byte big-endian strings
  SpecRef-side, so `toBeBytes32` bridges them;
* the payload is `readArrayBytes` over the arena span, which for a
  `LOG` emitted out of memory reduces through
  [`memoryRel_read`](Memory.lean) to SpecRef's `memory_read_bytes`.

`logAppend` names the net effect of the extraction's three-call emission
(`log_begin`, then the topics, then the payload) and `logRel_append`
proves the relation survives it. Consumers: the LOG family.
-/

open private modifyLastLog appendLogData readArrayBytes
  memoryBytesOf from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## Array helpers for the log store -/

/-- Writing the slot a `push` just created is the same as pushing the new
value. `modifyLastLog` always writes exactly that slot. -/
theorem push_set_last {α : Type} [Inhabited α] (a : Array α) (x y : α) :
    (a.push x).set! a.size y = a.push y := by
  simp only [Array.set!, Array.setIfInBounds]
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.size_push] at h2
    by_cases h : i = a.size
    · subst h
      simp
    · have hi : i < a.size := by omega
      simp [Array.getElem_set, Array.getElem_push, hi]
      intro hc
      exact absurd hc.symm h

theorem getD_push_last {α : Type} [Inhabited α] (a : Array α) (x : α) :
    (a.push x).getD a.size default = x := by simp

/-! ## The host log store, addressed -/

/-- Row `i` of the host log store. -/
def logRow (hs : Evm.HostState) (i : Nat) : Evm.LogRecordRow :=
  hs.logs.getD i default

/-- The payload bytes of row `i`, read out of the shared arena. -/
def logRowData (hs : Evm.HostState) (i : Nat) : List byte :=
  readArrayBytes hs.logBytes (logRow hs i).dataOffset (logRow hs i).dataLength

/-- SpecRef's frame-local log list vs the host store's rows from `base`.
`bounded` is what makes the relation stable under further emission: an
earlier row's span must already lie inside the arena, so appending bytes
cannot change what it reads back. -/
structure LogRel (L : List Log) (hs : Evm.HostState) (base : Nat) : Prop where
  count : hs.logs.size = base + L.length
  address : ∀ i, (h : i < L.length) →
    (logRow hs (base + i)).address.toList = L[i].address
  topics : ∀ i, (h : i < L.length) →
    (logRow hs (base + i)).topics.map toBeBytes32 = L[i].topics
  data : ∀ i, (h : i < L.length) → logRowData hs (base + i) = L[i].data
  bounded : ∀ i, i < L.length →
    (logRow hs (base + i)).dataOffset + (logRow hs (base + i)).dataLength
      ≤ hs.logBytes.size

/-! ## Appending one record -/

/-- The net effect of the extraction's `k_log`: one row appended, its
payload appended to the arena, its span pointing at the payload. -/
def logAppend (hs : Evm.HostState) (a : Evm.Defs.address) (ts : List word)
    (d : List byte) : Evm.HostState :=
  { hs with
      logs := hs.logs.push
        { address := a
          topics := ts
          dataOffset := hs.logBytes.size
          dataLength := d.length }
      logBytes := hs.logBytes ++ d.toArray }

/-- The row an emission appends. -/
def logRowOf (hs : Evm.HostState) (a : Evm.Defs.address) (ts : List word)
    (d : List byte) : Evm.LogRecordRow :=
  { address := a
    topics := ts
    dataOffset := hs.logBytes.size
    dataLength := d.length }

/-- `modifyLastLog` on a state whose store was just pushed rewrites that
row in place. -/
theorem modifyLastLog_push (st : Evm.HostState)
    (arr : Array Evm.LogRecordRow) (r : Evm.LogRecordRow)
    (f : Evm.LogRecordRow → Evm.LogRecordRow)
    (hlogs : st.logs = arr.push r) :
    modifyLastLog st f = { st with logs := arr.push (f r) } := by
  unfold modifyLastLog
  rw [hlogs]
  rw [if_neg (by simp)]
  simp only [Array.size_push, Nat.add_sub_cancel]
  rw [getD_push_last, push_set_last]

/-- The in-progress row: address fixed, `ws` topics so far, span still
empty at the arena's current end. `log_begin` produces the `ws = []` case
and each `log_add_topic` extends `ws`, so every intermediate state of an
emission is in this shape. -/
def logRowTopics (hs : Evm.HostState) (a : Evm.Defs.address)
    (ws : List word) : Evm.LogRecordRow :=
  { address := a
    topics := ws
    dataOffset := hs.logBytes.size
    dataLength := 0 }

/-- The state after `log_begin` / after `k` topic operands. -/
def logPending (hs : Evm.HostState) (a : Evm.Defs.address)
    (ws : List word) : Evm.HostState :=
  { hs with logs := hs.logs.push (logRowTopics hs a ws) }

theorem runS_log_begin (a : Evm.Defs.address) (hs : Evm.HostState)
    (ss : SeqState) :
    runS (Evm.Functions.log_begin a) hs ss =
      .ok ((), logPending hs a []) ss := runS_modify _ _ _

theorem runS_log_add_topic (t : word) (a : Evm.Defs.address)
    (ws : List word) (hs : Evm.HostState) (ss : SeqState) :
    runS (Evm.Functions.log_add_topic t) (logPending hs a ws) ss =
      .ok ((), logPending hs a (ws ++ [t])) ss := by
  unfold Evm.Functions.log_add_topic
  rw [runS_modify,
    modifyLastLog_push (logPending hs a ws) hs.logs (logRowTopics hs a ws) _
      rfl]
  simp [logPending, logRowTopics]

theorem runS_log_add_data_memory (s : EvmMemorySlice) (d : List byte)
    (a : Evm.Defs.address) (ws : List word)
    (hs : Evm.HostState) (ss : SeqState)
    (hd : memoryBytesOf hs s = d) :
    runS (Evm.Functions.log_add_data_memory s) (logPending hs a ws) ss =
      .ok ((), logAppend hs a ws d) ss := by
  unfold Evm.Functions.log_add_data_memory
  refine runS_bind_ok (runS_get _ ss) ?_
  rw [show memoryBytesOf (logPending hs a ws) s = d from hd]
  unfold appendLogData
  rw [runS_modify,
    modifyLastLog_push
      { logPending hs a ws with
          logBytes := (logPending hs a ws).logBytes ++ d.toArray }
      hs.logs (logRowTopics hs a ws) _ rfl]
  simp [logPending, logRowTopics, logAppend]

/-- The topic operands as a list, in emission order. -/
def topicWords : LogTopics → List word
  | .LogTopics0 () => []
  | .LogTopics1 t0 => [t0]
  | .LogTopics2 (t0, t1) => [t0, t1]
  | .LogTopics3 (t0, t1, t2) => [t0, t1, t2]
  | .LogTopics4 (t0, t1, t2, t3) => [t0, t1, t2, t3]

open Evm.Functions in
/-- **One emission**: `k_log` appends exactly one row, whose span points at
the payload it just appended to the arena. -/
theorem runS_k_log_memory (a : Evm.Defs.address) (ts : LogTopics)
    (s : EvmMemorySlice) (d : List byte)
    (hs : Evm.HostState) (ss : SeqState)
    (hd : memoryBytesOf hs s = d) :
    runS (Evm.Functions.k_log a ts (.LogDataMemory s)) hs ss =
      .ok ((), logAppend hs a (topicWords ts) d) ss := by
  unfold Evm.Functions.k_log
  refine runS_bind_ok (runS_log_begin a hs ss) ?_
  unfold Evm.Functions.k_log_topics Evm.Functions.k_log_data
  cases ts with
  | LogTopics0 u =>
    refine runS_bind_ok (runS_pure _ _ _) ?_
    exact runS_log_add_data_memory s d a [] hs ss hd
  | LogTopics1 t0 =>
    refine runS_bind_ok (runS_log_add_topic t0 a [] hs ss) ?_
    exact runS_log_add_data_memory s d a [t0] hs ss hd
  | LogTopics2 p =>
    obtain ⟨t0, t1⟩ := p
    refine runS_bind_ok
      (runS_bind_ok (runS_log_add_topic t0 a [] hs ss)
        (runS_log_add_topic t1 a [t0] hs ss)) ?_
    exact runS_log_add_data_memory s d a [t0, t1] hs ss hd
  | LogTopics3 p =>
    obtain ⟨t0, t1, t2⟩ := p
    refine runS_bind_ok
      (runS_bind_ok (runS_log_add_topic t0 a [] hs ss)
        (runS_bind_ok (runS_log_add_topic t1 a [t0] hs ss)
          (runS_log_add_topic t2 a [t0, t1] hs ss))) ?_
    exact runS_log_add_data_memory s d a [t0, t1, t2] hs ss hd
  | LogTopics4 p =>
    obtain ⟨t0, t1, t2, t3⟩ := p
    refine runS_bind_ok
      (runS_bind_ok (runS_log_add_topic t0 a [] hs ss)
        (runS_bind_ok (runS_log_add_topic t1 a [t0] hs ss)
          (runS_bind_ok (runS_log_add_topic t2 a [t0, t1] hs ss)
            (runS_log_add_topic t3 a [t0, t1, t2] hs ss)))) ?_
    exact runS_log_add_data_memory s d a [t0, t1, t2, t3] hs ss hd

/-! ## Arena and store stability -/

theorem getD_push_lt {α : Type} [Inhabited α] (a : Array α) (x : α)
    (j : Nat) (hj : j < a.size) :
    (a.push x).getD j default = a.getD j default := by
  simp [Array.getD, hj, Array.getElem_push]
  intro h
  omega

theorem array_append_getD_lt (arr b : Array byte) (i : Nat)
    (hi : i < arr.size) : (arr ++ b).getD i 0 = arr.getD i 0 := by
  simp [Array.getD, hi, Array.size_append,
    show i < arr.size + b.size from by omega]

theorem array_append_getD_ge (arr : Array byte) (d : List byte) (i : Nat)
    (h1 : arr.size ≤ i) (h2 : i < arr.size + d.length) :
    (arr ++ d.toArray).getD i 0 = d.getD (i - arr.size) 0 := by
  simp [Array.getD, Array.getElem_append, h2,
    show ¬ i < arr.size from by omega, List.getD,
    List.getElem?_eq_getElem (show i - arr.size < d.length from by omega)]

/-- Bytes already inside the arena read back unchanged after an append. -/
theorem readArrayBytes_append_lt (arr b : Array byte) (off len : Nat)
    (h : off + len ≤ arr.size) :
    readArrayBytes (arr ++ b) off len = readArrayBytes arr off len := by
  refine list_eq_of_getD _ _ (by rw [readArrayBytes_length,
    readArrayBytes_length]) ?_
  intro i hi
  rw [readArrayBytes_length] at hi
  rw [readArrayBytes_getD _ _ _ _ hi, readArrayBytes_getD _ _ _ _ hi]
  exact array_append_getD_lt arr b (off + i) (by omega)

/-- The freshly appended span reads back as exactly what was appended. -/
theorem readArrayBytes_append_exact (arr : Array byte) (d : List byte) :
    readArrayBytes (arr ++ d.toArray) arr.size d.length = d := by
  refine list_eq_of_getD _ _ (by rw [readArrayBytes_length]) ?_
  intro i hi
  rw [readArrayBytes_length] at hi
  rw [readArrayBytes_getD _ _ _ _ hi,
    array_append_getD_ge arr d (arr.size + i) (by omega) (by omega),
    show arr.size + i - arr.size = i from by omega]

/-! ## The relation survives an emission -/

/-- The SpecRef log record an emission produces. -/
def logOf (a : Evm.Defs.address) (ts : List word) (d : List byte) : Log :=
  { address := a.toList
    topics := ts.map toBeBytes32
    data := d }

theorem logAppend_logBytes (hs : Evm.HostState) (a : Evm.Defs.address)
    (ts : List word) (d : List byte) :
    (logAppend hs a ts d).logBytes = hs.logBytes ++ d.toArray := rfl

theorem logAppend_logs_size (hs : Evm.HostState) (a : Evm.Defs.address)
    (ts : List word) (d : List byte) :
    (logAppend hs a ts d).logs.size = hs.logs.size + 1 := by
  simp [logAppend]

theorem logAppend_logBytes_size (hs : Evm.HostState) (a : Evm.Defs.address)
    (ts : List word) (d : List byte) :
    (logAppend hs a ts d).logBytes.size = hs.logBytes.size + d.length := by
  simp [logAppend]

/-- Rows the emission did not touch read back unchanged. -/
theorem logRow_logAppend_lt (hs : Evm.HostState) (a : Evm.Defs.address)
    (ts : List word) (d : List byte) (j : Nat) (hj : j < hs.logs.size) :
    logRow (logAppend hs a ts d) j = logRow hs j := by
  simp only [logRow, logAppend]
  exact getD_push_lt hs.logs _ j hj

theorem logRow_logAppend_last (hs : Evm.HostState) (a : Evm.Defs.address)
    (ts : List word) (d : List byte) :
    logRow (logAppend hs a ts d) hs.logs.size = logRowOf hs a ts d := by
  simp only [logRow, logAppend, logRowOf]
  exact getD_push_last hs.logs _

theorem logRowData_logAppend_lt (hs : Evm.HostState) (a : Evm.Defs.address)
    (ts : List word) (d : List byte) (j : Nat) (hj : j < hs.logs.size)
    (hb : (logRow hs j).dataOffset + (logRow hs j).dataLength
      ≤ hs.logBytes.size) :
    logRowData (logAppend hs a ts d) j = logRowData hs j := by
  simp only [logRowData, logRow_logAppend_lt hs a ts d j hj,
    logAppend_logBytes]
  exact readArrayBytes_append_lt _ _ _ _ hb

theorem logRowData_logAppend_last (hs : Evm.HostState)
    (a : Evm.Defs.address) (ts : List word) (d : List byte) :
    logRowData (logAppend hs a ts d) hs.logs.size = d := by
  simp only [logRowData, logRow_logAppend_last, logAppend_logBytes, logRowOf]
  exact readArrayBytes_append_exact hs.logBytes d

/-- **`LogRel` is stable under one emission.** The `bounded` field is what
carries the earlier rows across the arena append: their spans already lie
inside the arena, so appending cannot change what they read back. -/
theorem logRel_append (L : List Log) (hs : Evm.HostState) (base : Nat)
    (a : Evm.Defs.address) (ts : List word) (d : List byte)
    (hrel : LogRel L hs base) :
    LogRel (L ++ [logOf a ts d]) (logAppend hs a ts d) base := by
  obtain ⟨hcount, haddr, htop, hdata, hbound⟩ := hrel
  have hlast : base + L.length = hs.logs.size := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [logAppend_logs_size]
    simp only [List.length_append, List.length_singleton]
    omega
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < L.length
    · rw [logRow_logAppend_lt hs a ts d (base + i) (by omega),
        List.getElem_append_left hlt]
      exact haddr i hlt
    · have hie : i = L.length := by omega
      subst hie
      rw [hlast, logRow_logAppend_last]
      simp [logRowOf, logOf]
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < L.length
    · rw [logRow_logAppend_lt hs a ts d (base + i) (by omega),
        List.getElem_append_left hlt]
      exact htop i hlt
    · have hie : i = L.length := by omega
      subst hie
      rw [hlast, logRow_logAppend_last]
      simp [logRowOf, logOf]
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < L.length
    · rw [logRowData_logAppend_lt hs a ts d (base + i) (by omega)
        (hbound i hlt), List.getElem_append_left hlt]
      exact hdata i hlt
    · have hie : i = L.length := by omega
      subst hie
      rw [hlast, logRowData_logAppend_last]
      simp [logOf]
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < L.length
    · rw [logRow_logAppend_lt hs a ts d (base + i) (by omega),
        logAppend_logBytes_size]
      exact Nat.le_trans (hbound i hlt) (Nat.le_add_right _ _)
    · have hie : i = L.length := by omega
      subst hie
      rw [hlast, logRow_logAppend_last, logAppend_logBytes_size]
      simp [logRowOf]

/-- An emission touches neither memory frames nor memory bytes, so the
memory relation survives it (LOG observes both stores at once). -/
theorem memoryRel_logAppend (M : Bytes) (hs : Evm.HostState)
    (off len : Nat) (a : Evm.Defs.address) (ts : List word)
    (d : List byte) (hrel : MemoryRel M hs off len) :
    MemoryRel M (logAppend hs a ts d) off len := by
  obtain ⟨hframe, haligned, hbytes, htail⟩ := hrel
  exact ⟨hframe, haligned, hbytes, htail⟩

/-- A memory expansion touches neither the log store nor the arena, so the
relation is preserved verbatim (LOG expands before emitting). -/
theorem logRel_expandedHost (L : List Log) (hs : Evm.HostState)
    (base off len req : Nat) (mfrest : List Evm.MemoryFrame)
    (hrel : LogRel L hs base) :
    LogRel L (expandedHost hs off len req mfrest) base := by
  obtain ⟨hcount, haddr, htop, hdata, hbound⟩ := hrel
  exact ⟨hcount, haddr, htop, hdata, hbound⟩

/-! ## The success post for the LOG family -/

/-- The memory-family post plus the log-store correspondence. LOG is the
first opcode whose observation includes the log store, so its `Post` is
`MemPost` conjoined with `LogRel` at the frame's base index. -/
def LogPost (base : Nat) (sR' : Machine) (step : EvmStep)
    (hs' : Evm.HostState) (ss' : SeqState) : Prop :=
  MemPost sR' step hs' ss' ∧ LogRel sR'.evm.logs hs' base

end EvmSpecsVerify
