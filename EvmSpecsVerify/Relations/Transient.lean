import EvmSpecsVerify.Relations.Warm
import EvmSpecsVerify.Relations.Base
import Batteries.Tactic.OpenPrivate

/-!
# Transient storage relation (EIP-1153)

SpecRef keeps transient storage in the transaction state as a dictionary,
`TransactionState.transientStorage : List ((Address × Bytes32) × U256)`,
read with `getTransientStorage` and written with `setTransientStorage`.
The extraction keeps `HostState.transient : List (StorageKey × word)`,
read with `transient_load` and written with `transient_store`
(HostAxioms.lean:2009).

The two writers do **not** agree on representation: SpecRef *deletes* the
row when the new value is zero, the extraction stores the zero. Both
readers return zero for an absent key, so the difference is invisible
through the reads — and nothing on either side enumerates the map (frame
checkpoint/restore copies it wholesale on both sides), which is what makes
a **pointwise** relation the right one here rather than a structural one.
Mismatch ledger MM-13 records the divergence and why it is unobservable.

`TransientRel` therefore reads: at every host-side key (address vector ×
slot word), the extraction's read equals SpecRef's read of the
corresponding `(aV.toList, toBeBytes32 w)` pair. Preservation under a
write needs `toBeBytes32` and `Vector.toList` to be injective, exactly as
[`WarmRel`](Warm.lean) does.
-/

open private assocGet assocPut from Evm.HostAxioms

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## The two sides' reads and writes, as functions -/

/-- SpecRef's transient read (`getTransientStorage`, StateTracker.lean:203)
as a function of the transaction state. -/
def transientReadOf (ts : TransactionState) (a : Address) (k : Bytes32) :
    U256 :=
  ((ts.transientStorage.find? (·.1 == (a, k))).map (·.2)).getD 0

theorem runTx_getTransientStorage (ts : TransactionState) (a : Address)
    (k : Bytes32) :
    (getTransientStorage a k).run ts = .ok (transientReadOf ts a k, ts) :=
  rfl

/-- SpecRef's transient write. The zero case **removes** the row. -/
def transientWriteOf (ts : TransactionState) (a : Address) (k : Bytes32)
    (v : U256) : TransactionState :=
  if v == 0 then
    { ts with
        transientStorage :=
          ts.transientStorage.filter (·.1 != (a, k)) }
  else
    { ts with
        transientStorage := dictSet ts.transientStorage (a, k) v }

theorem runTx_setTransientStorage (ts : TransactionState) (a : Address)
    (k : Bytes32) (v : U256) :
    (setTransientStorage a k v).run ts
      = .ok ((), transientWriteOf ts a k v) := by
  unfold setTransientStorage transientWriteOf
  split <;> rfl

/-- The extraction's transient read. -/
def hostTransientRead (hs : Evm.HostState) (aV : Evm.Defs.address)
    (x : Nat) : Nat :=
  (assocGet hs.transient ({ addr := aV, slot := x } : Evm.Defs.StorageKey)).getD
    default

/-- The extraction's transient write. The zero case **stores** the zero. -/
def hostTransientWrite (hs : Evm.HostState) (aV : Evm.Defs.address)
    (x v : Nat) : Evm.HostState :=
  { hs with
      transient :=
        assocPut hs.transient ({ addr := aV, slot := x } : Evm.Defs.StorageKey) v }

theorem runS_k_tload (aV : Evm.Defs.address) (x : Nat) (hs : Evm.HostState)
    (ss : SeqState) :
    runS (Evm.Functions.k_tload aV x) hs ss
      = .ok (hostTransientRead hs aV x, hs) ss := by
  unfold hostTransientRead
  exact runS_bind_ok (runS_get _ _) (runS_pure _ _ _)

theorem runS_k_tstore (aV : Evm.Defs.address) (x v : Nat)
    (hs : Evm.HostState) (ss : SeqState) :
    runS (Evm.Functions.k_tstore aV x v) hs ss
      = .ok ((), hostTransientWrite hs aV x v) ss := by
  unfold hostTransientWrite
  exact runS_modify _ _ _

/-! ## The relation -/

/-- SpecRef's transient dictionary vs the extraction's, pointwise. -/
structure TransientRel (ts : TransactionState) (hs : Evm.HostState) :
    Prop where
  rel : ∀ (aV : Evm.Defs.address) (w : Nat), WordWf w →
    hostTransientRead hs aV w
      = transientReadOf ts aV.toList (toBeBytes32 w)
  /-- Every stored value is a well-formed word — the transient analogue
  of `StackRel.wf`, and what lets a *read* be pushed back onto the stack
  (`tloadAgree_of_transientRel`). Both sides only ever store operands. -/
  wf : ∀ (aV : Evm.Defs.address) (w : Nat), WordWf w →
    WordWf (hostTransientRead hs aV w)

/-! ## SpecRef dictionary characterization -/

private theorem find?_filter_ne {κ ν : Type} [BEq κ] [LawfulBEq κ]
    (d : List (κ × ν)) (k k' : κ) (h : k' ≠ k) :
    (d.filter (·.1 != k)).find? (·.1 == k') = d.find? (·.1 == k') := by
  induction d with
  | nil => rfl
  | cons e es ih =>
    by_cases he : e.1 = k
    · rw [List.filter_cons_of_neg (by simpa using he),
        List.find?_cons_of_neg (by simp [he]; exact fun hc => h hc.symm)]
      exact ih
    · rw [List.filter_cons_of_pos (by simpa using he)]
      by_cases hk' : e.1 = k'
      · rw [List.find?_cons_of_pos (by simpa using hk'),
          List.find?_cons_of_pos (by simpa using hk')]
      · rw [List.find?_cons_of_neg (by simpa using hk'),
          List.find?_cons_of_neg (by simpa using hk')]
        exact ih

private theorem find?_filter_self {κ ν : Type} [BEq κ] [LawfulBEq κ]
    (d : List (κ × ν)) (k : κ) :
    (d.filter (·.1 != k)).find? (·.1 == k) = none := by
  rw [List.find?_eq_none]
  intro p hp
  have hmem := List.mem_of_mem_filter hp
  have hne : p.1 != k := by
    have := List.of_mem_filter hp
    simpa using this
  simpa using hne

/-- The hit branch of `dictSet` rewrites the matching row in place. -/
private theorem find?_map_set_self {κ ν : Type} [BEq κ] [LawfulBEq κ]
    (k : κ) (v : ν) :
    ∀ d : List (κ × ν), d.any (·.1 == k) = true →
      ((d.map (fun p => if p.1 == k then (k, v) else p)).find?
        (·.1 == k)).map (·.2) = some v := by
  intro d
  induction d with
  | nil => intro h; simp at h
  | cons e es ih =>
    intro h
    by_cases he : e.1 = k
    · rw [List.map_cons, if_pos (by simpa using he),
        List.find?_cons_of_pos (by simp)]
      rfl
    · rw [List.map_cons, if_neg (by simpa using he),
        List.find?_cons_of_neg (by simpa using he)]
      refine ih ?_
      simp only [List.any_cons, Bool.or_eq_true, beq_iff_eq] at h
      exact h.resolve_left he

/-- The hit branch leaves every other key's row alone. -/
private theorem find?_map_set_ne {κ ν : Type} [BEq κ] [LawfulBEq κ]
    (k k' : κ) (v : ν) (h : k' ≠ k) :
    ∀ d : List (κ × ν),
      ((d.map (fun p => if p.1 == k then (k, v) else p)).find?
        (·.1 == k')).map (·.2) = (d.find? (·.1 == k')).map (·.2) := by
  intro d
  induction d with
  | nil => rfl
  | cons e es ih =>
    by_cases he : e.1 = k
    · rw [List.map_cons, if_pos (by simpa using he),
        List.find?_cons_of_neg (by simpa using Ne.symm h),
        List.find?_cons_of_neg (by simp [he]; exact fun hc => h hc.symm)]
      exact ih
    · rw [List.map_cons, if_neg (by simpa using he)]
      by_cases hk' : e.1 = k'
      · rw [List.find?_cons_of_pos (by simpa using hk'),
          List.find?_cons_of_pos (by simpa using hk')]
      · rw [List.find?_cons_of_neg (by simpa using hk'),
          List.find?_cons_of_neg (by simpa using hk')]
        exact ih

private theorem find?_dictSet_self {κ ν : Type} [BEq κ] [LawfulBEq κ]
    (d : List (κ × ν)) (k : κ) (v : ν) :
    ((dictSet d k v).find? (·.1 == k)).map (·.2) = some v := by
  unfold dictSet
  by_cases hany : d.any (·.1 == k) = true
  · rw [if_pos hany]
    exact find?_map_set_self k v d hany
  · rw [if_neg (by simpa using hany)]
    have hnone : d.find? (·.1 == k) = none := by
      rw [List.find?_eq_none]
      intro p hp hc
      simp only [List.any_eq_true] at hany
      exact hany ⟨p, hp, hc⟩
    rw [List.find?_append, hnone]
    simp

private theorem find?_dictSet_ne {κ ν : Type} [BEq κ] [LawfulBEq κ]
    (d : List (κ × ν)) (k k' : κ) (v : ν) (h : k' ≠ k) :
    ((dictSet d k v).find? (·.1 == k')).map (·.2)
      = (d.find? (·.1 == k')).map (·.2) := by
  unfold dictSet
  by_cases hany : d.any (·.1 == k) = true
  · rw [if_pos hany]
    exact find?_map_set_ne k k' v h d
  · rw [if_neg (by simpa using hany), List.find?_append]
    cases hf : d.find? (fun p => p.1 == k') with
    | some p => simp
    | none => simp [Ne.symm h]

/-! ## SpecRef's write, through its read -/

/-- The written slot reads back as the value written — including the zero
case, where SpecRef stores no row at all. -/
private theorem transientReadOf_write_self (ts : TransactionState)
    (a : Address) (k : Bytes32) (v : U256) :
    transientReadOf (transientWriteOf ts a k v) a k = v := by
  unfold transientWriteOf transientReadOf
  by_cases hv : v = 0
  · subst hv
    rw [if_pos (by simp)]
    dsimp only
    rw [find?_filter_self]
    rfl
  · rw [if_neg (by simpa using hv)]
    dsimp only
    rw [find?_dictSet_self]
    rfl

/-- Every other slot is untouched. -/
private theorem transientReadOf_write_ne (ts : TransactionState)
    (a a' : Address) (k k' : Bytes32) (v : U256)
    (h : (a', k') ≠ (a, k)) :
    transientReadOf (transientWriteOf ts a k v) a' k'
      = transientReadOf ts a' k' := by
  unfold transientWriteOf transientReadOf
  by_cases hv : v = 0
  · subst hv
    rw [if_pos (by simp)]
    dsimp only
    rw [find?_filter_ne _ _ _ h]
  · rw [if_neg (by simpa using hv)]
    dsimp only
    rw [find?_dictSet_ne _ _ _ _ h]

/-! ## The write preserves the relation -/

/-- **`TransientRel` is stable under one TSTORE.** The two writers differ
on the zero case (SpecRef deletes, the extraction stores — MM-13), which
is exactly where the two branches of this proof meet: an absent row and a
row holding zero read back the same. -/
theorem transientRel_write (ts : TransactionState) (hs : Evm.HostState)
    (aV : Evm.Defs.address) (x v : Nat) (hx : WordWf x) (hv : WordWf v)
    (hrel : TransientRel ts hs) :
    TransientRel (transientWriteOf ts aV.toList (toBeBytes32 x) v)
      (hostTransientWrite hs aV x v) := by
  -- the two key-inequalities every "some other slot" case needs
  have hne : ∀ (bV : Evm.Defs.address) (w : Nat), WordWf w →
      ¬(bV = aV ∧ w = x) →
      ({ addr := bV, slot := w } : Evm.Defs.StorageKey)
          ≠ { addr := aV, slot := x }
        ∧ ((bV.toList, toBeBytes32 w) : Address × Bytes32)
            ≠ (aV.toList, toBeBytes32 x) := by
    intro bV w hw hkey
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · injection hc with h1 h2
      exact hkey ⟨h1, h2⟩
    · injection hc with h1 h2
      exact hkey ⟨Vector.toList_inj.mp h1, toBeBytes32_inj hw hx h2⟩
  constructor
  · intro bV w hw
    by_cases hkey : bV = aV ∧ w = x
    · obtain ⟨rfl, rfl⟩ := hkey
      rw [hostTransientRead, hostTransientWrite, assocGet_put_self,
        transientReadOf_write_self]
      rfl
    · obtain ⟨h1, h2⟩ := hne bV w hw hkey
      rw [hostTransientRead, hostTransientWrite, assocGet_put_ne _ _ _ _ h1,
        transientReadOf_write_ne _ _ _ _ _ _ h2]
      exact hrel.rel bV w hw
  · intro bV w hw
    by_cases hkey : bV = aV ∧ w = x
    · obtain ⟨rfl, rfl⟩ := hkey
      rw [hostTransientRead, hostTransientWrite, assocGet_put_self]
      exact hv
    · obtain ⟨h1, _⟩ := hne bV w hw hkey
      rw [hostTransientRead, hostTransientWrite, assocGet_put_ne _ _ _ _ h1]
      exact hrel.wf bV w hw

/-! ## The success post for the transient writers -/

/-- The base post plus the transient-store correspondence. TSTORE's whole
observable effect is the write, so `BasePost` alone would say nothing
about it. -/
def TransientPost (mem : EvmMemorySlice) (sR' : Machine) (step : EvmStep)
    (hs' : Evm.HostState) (ss' : SeqState) : Prop :=
  BasePost mem sR' step hs' ss' ∧ TransientRel sR'.txState hs'

end EvmSpecsVerify
