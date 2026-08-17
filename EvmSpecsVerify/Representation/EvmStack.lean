import Evm
import Batteries.Tactic.OpenPrivate
import EvmSpecsVerify.Representation.EvmMonad

/-!
# The `Evm` host operand stack, abstracted

The extraction's operand stack is `HostState.stackFrames.head` — a
**bottom-indexed** `List word` — addressed through a `StackTop : BitVec 64`
cursor whose reference reading is the frame height (HostAxioms.lean:1846).
Key semantic fact: `pop` only retreats the cursor; the popped entry stays in
the list as inaccessible scratch until a later `push` overwrites it. The
faithful abstraction is therefore *prefix-up-to-cursor*:

    (currentStack hs).take top.toNat = S.reverse

for a SpecRef-style head-is-top stack `S`. This file proves the
representation lemmas that let opcode proofs treat `pop`/`push_word`/`peek`/
`stack_height` as operations on `S`, given:

  * `hframe : hs.stackFrames = l :: rest`
  * `hpfx   : l.take top.toNat = S.reverse`
  * `hlen   : top.toNat ≤ l.length`
  * `htop   : top.toNat = S.length`
  * a cursor headroom bound (`S.length < 2^64 − 1`, supplied by the 1024
    stack limit in the state relation)

Cursor arithmetic is wrapping `BitVec 64` and slot positions use truncating
`Nat` subtraction — the hypotheses above are exactly what keeps both honest.
-/

namespace EvmSpecsVerify

open Evm (HostState)
open Evm.Defs (StackTop word)

open private currentStack replaceCurrentStack replaceListAt writeListAt
  stackSlotPosition from Evm.HostAxioms

/-! ## Pure characterizations of the private helpers -/

theorem currentStack_eq (hs : HostState) :
    currentStack hs = hs.stackFrames.head?.getD [] := rfl

theorem replaceCurrentStack_eq (hs : HostState) (stack : List word) :
    replaceCurrentStack hs stack =
      { hs with stackFrames := stack :: hs.stackFrames.drop 1 } := rfl

theorem stackSlotPosition_eq (top : StackTop) (index : Nat) :
    stackSlotPosition top index = top.toNat - 1 - index := rfl

theorem replaceListAt_nil (index : Nat) (value : α) :
    replaceListAt ([] : List α) index value = [] := rfl

theorem replaceListAt_cons_zero (head : α) (rest : List α) (value : α) :
    replaceListAt (head :: rest) 0 value = value :: rest := rfl

theorem replaceListAt_cons_succ (head : α) (rest : List α) (index : Nat)
    (value : α) :
    replaceListAt (head :: rest) (index + 1) value =
      head :: replaceListAt rest index value := rfl

/-- `replaceListAt` preserves length. -/
theorem length_replaceListAt (values : List α) (index : Nat) (value : α) :
    (replaceListAt values index value).length = values.length := by
  induction values generalizing index with
  | nil => rfl
  | cons head rest ih =>
    cases index with
    | zero => simp [replaceListAt_cons_zero]
    | succ i => simp [replaceListAt_cons_succ, ih]

/-- In-range `replaceListAt` splits as take/set/drop around the index. -/
theorem take_replaceListAt (values : List α) (index : Nat) (value : α) :
    (replaceListAt values index value).take index = values.take index := by
  induction values generalizing index with
  | nil => simp [replaceListAt_nil]
  | cons head rest ih =>
    cases index with
    | zero => simp
    | succ i => simp [replaceListAt_cons_succ, ih]

theorem getElem?_replaceListAt_self (values : List α) (index : Nat) (value : α)
    (h : index < values.length) :
    (replaceListAt values index value)[index]? = some value := by
  induction values generalizing index with
  | nil => simp at h
  | cons head rest ih =>
    cases index with
    | zero => simp [replaceListAt_cons_zero]
    | succ i =>
      simp only [replaceListAt_cons_succ, List.getElem?_cons_succ]
      exact ih i (by simpa using h)

/-- Writing one past the end of an exactly-one-padded list appends. -/
theorem replaceListAt_pad_append (l : List word) (w : word) :
    replaceListAt (l ++ [default]) l.length w = l ++ [w] := by
  induction l with
  | nil => rfl
  | cons head rest ih =>
    simpa [replaceListAt_cons_succ] using ih

/-- The single write the ALU family performs: writing at the cursor position
`p` with `p ≤ l.length` yields a list whose `p+1`-prefix is `l.take p ++ [w]`.
Both `writeListAt` branches (in-place replace / pad-and-append) satisfy it. -/
theorem take_writeListAt (l : List word) (p : Nat) (w : word) (hp : p ≤ l.length) :
    (writeListAt l p w).take (p + 1) = l.take p ++ [w] := by
  unfold writeListAt
  split
  · -- in place: p < l.length
    rename_i hlt
    have htklen : (l.take p).length = p := by simp; omega
    apply List.ext_getElem?
    intro i
    rcases Nat.lt_trichotomy i p with hi | rfl | hi
    · rw [List.getElem?_take_of_lt (by omega),
        List.getElem?_append_left (by omega)]
      have h1 : ((replaceListAt l p w).take p)[i]? = (l.take p)[i]? := by
        rw [take_replaceListAt]
      rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi] at h1
      rw [h1, List.getElem?_take_of_lt hi]
    · rw [List.getElem?_take_of_lt (Nat.lt_succ_self i),
        getElem?_replaceListAt_self l i w hlt,
        List.getElem?_append_right (by omega), htklen]
      simp
    · rw [List.getElem?_take_eq_none (by omega), Eq.comm, List.getElem?_eq_none]
      simp only [List.length_append, List.length_cons, List.length_nil, htklen]
      omega
  · -- pad and append: p = l.length (given hp)
    rename_i hge
    have hpe : p = l.length := by omega
    subst hpe
    simp only [Nat.add_sub_cancel_left, List.replicate_one,
      replaceListAt_pad_append]
    rw [List.take_of_length_le (by simp), List.take_length]

/-- `writeListAt` grows the list exactly to cover the write position. -/
theorem length_writeListAt (l : List word) (p : Nat) (w : word) :
    (writeListAt l p w).length = max l.length (p + 1) := by
  unfold writeListAt
  split
  · rw [length_replaceListAt]; omega
  · rw [length_replaceListAt]; simp; omega

/-- Truncating a one-longer reversed-stack prefix drops the top element:
the list-geometry step each `pop` takes on the prefix relation. -/
theorem take_shrink (l S : List word) (a : word) (k : Nat)
    (hpfx : l.take (k + 1) = (a :: S).reverse) (hS : S.length = k) :
    l.take k = S.reverse := by
  have hview : l.take k = (l.take (k + 1)).take k := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  rw [hview, hpfx]
  have hrl : S.reverse.length = k := by simp [hS]
  calc ((a :: S).reverse).take k = (S.reverse ++ [a]).take k := by simp
    _ = S.reverse := by
        rw [List.take_append_of_le_length (by omega), ← hrl, List.take_length]

/-- Record-update projection (whnf-safe `rfl` mini-lemma). -/
theorem hostState_set_stackFrames_frames (h : HostState)
    (f : List (List word)) :
    ({ h with stackFrames := f } : HostState).stackFrames = f := rfl

/-! ## Reads through the cursor -/

/-- Reading slot `i` below cursor `top` returns the `i`-th element (from the
top) of the abstract stack: with the prefix relation and `top.toNat = S.length`,
slot `i` addresses `S[i]`. -/
theorem currentStack_read (l : List word) (S : List word) (top : StackTop)
    (i : Nat) (hpfx : l.take top.toNat = S.reverse) (htop : top.toNat = S.length)
    (hi : i < S.length) :
    l.getD (stackSlotPosition top i) default = S.getD i default := by
  rw [stackSlotPosition_eq]
  have hpos : top.toNat - 1 - i < top.toNat := by omega
  have hlt : top.toNat - 1 - i < S.reverse.length := by simp; omega
  calc l.getD (top.toNat - 1 - i) default
      = (l.take top.toNat).getD (top.toNat - 1 - i) default := by
        simp only [List.getD]
        rw [List.getElem?_take_of_lt hpos]
    _ = S.reverse.getD (top.toNat - 1 - i) default := by rw [hpfx]
    _ = S.getD i default := by
        have hidx : S.length - 1 - (top.toNat - 1 - i) = i := by omega
        simp only [List.getD]
        rw [List.getElem?_reverse (by simpa using hlt), hidx]

/-! ## Cursor arithmetic (wrapping `BitVec 64`, kept honest by bounds) -/

theorem cursor_advance_toNat (top : StackTop) (h : top.toNat + 1 < 2 ^ 64) :
    (top + BitVec.ofNat 64 1).toNat = top.toNat + 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  simp [Nat.mod_eq_of_lt h]

theorem cursor_retreat_toNat (top : StackTop) (h : 1 ≤ top.toNat) :
    (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have htop := top.isLt
  simp only [Nat.pow_succ] at *
  omega

/-! ## Machine-level stack operations, run

The hypotheses shared by this block (`hframe`/`hpfx`/`htop`) are the raw form
of the stack relation; `Relations/Stack.lean` packages them.
-/

theorem runS_stack_height (top : StackTop) (hs : HostState) (ss : SeqState) :
    runS (Evm.Functions.stack_height top) hs ss = .ok (top.toNat, hs) ss := rfl

theorem runS_stack_slot_read (top : StackTop) (i : Nat) (hs : HostState)
    (ss : SeqState) :
    runS (Evm.Functions.stack_slot_read top i) hs ss =
      .ok ((currentStack hs).getD (stackSlotPosition top i) default, hs) ss := rfl

theorem currentStack_of_frame (hs : HostState) (l : List word)
    (rest : List (List word)) (hframe : hs.stackFrames = l :: rest) :
    currentStack hs = l := by
  simp [currentStack_eq, hframe]

theorem runS_peek (top : StackTop) (i : Nat) (hs : HostState) (ss : SeqState)
    (l : List word) (rest : List (List word)) (S : List word)
    (hframe : hs.stackFrames = l :: rest)
    (hpfx : l.take top.toNat = S.reverse) (htop : top.toNat = S.length)
    (hi : i < S.length) :
    runS (Evm.Functions.peek top i) hs ss = .ok (S.getD i default, hs) ss := by
  show runS (Evm.Functions.stack_slot_read top i) hs ss = _
  rw [runS_stack_slot_read, currentStack_of_frame hs l rest hframe,
    currentStack_read l S top i hpfx htop hi]

/-- `pop` returns the top element and retreats the cursor; the host state is
untouched (the entry becomes inaccessible scratch above the new cursor). -/
theorem runS_pop (top : StackTop) (hs : HostState) (ss : SeqState)
    (l : List word) (rest : List (List word)) (x : word) (S' : List word)
    (hframe : hs.stackFrames = l :: rest)
    (hpfx : l.take top.toNat = (x :: S').reverse)
    (htop : top.toNat = (x :: S').length) :
    runS (Evm.Functions.pop top) hs ss =
      .ok ((x, top - BitVec.ofNat 64 1), hs) ss := by
  have hx : (x :: S').getD 0 default = x := rfl
  simp only [Evm.Functions.pop, Evm.Functions.stack_top_retreat]
  simp only [runS_bind, runS_stack_slot_read,
    currentStack_of_frame hs l rest hframe,
    currentStack_read l (x :: S') top 0 hpfx htop (by simp), hx, runS_pure]

/-- `push_word` advances the cursor and writes at the new cursor's slot 0 —
i.e. at position `top.toNat` of the bottom-indexed list. The new list's
`top.toNat + 1`-prefix is `(w :: S).reverse` (`take_writeListAt`). -/
theorem runS_push_word (top : StackTop) (w : word) (hs : HostState)
    (ss : SeqState) (l : List word) (rest : List (List word))
    (hframe : hs.stackFrames = l :: rest)
    (hbound : top.toNat + 1 < 2 ^ 64) :
    runS (Evm.Functions.push_word top w) hs ss =
      .ok (top + BitVec.ofNat 64 1,
        { hs with stackFrames := writeListAt l top.toNat w :: rest }) ss := by
  have hpos : stackSlotPosition (top + BitVec.ofNat 64 1) 0 = top.toNat := by
    rw [stackSlotPosition_eq, cursor_advance_toNat top hbound]
    omega
  simp only [Evm.Functions.push_word, Evm.Functions.stack_top_advance,
    Evm.Functions.stack_slot_write]
  simp only [runS_bind, runS_pure, runS_modify]
  rw [currentStack_of_frame hs l rest hframe, hpos, replaceCurrentStack_eq,
    hframe]
  rfl

end EvmSpecsVerify
