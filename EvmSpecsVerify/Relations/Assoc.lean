import EvmSpecsVerify.Relations.Warm

/-!
# The association-list layer

Both specifications represent their maps as association lists, and three
relations now bridge them: [`WarmRel`](Warm.lean) (epoch stamps),
[`TransientRel`](Transient.lean) (EIP-1153 storage) and
[`StorageRel`](Storage.lean) (persistent storage). The extraction's side
is `assocGet`/`assocPut` (characterized in Warm.lean, whose
`LawfulBEq StorageKey` instance the keys need); SpecRef's side is
`dictGet?`/`dictSet`/`dictDel` over `List (κ × ν)`, and this file is what
those lemmas say.

`dictSet` has two branches — rewrite the matching row in place, or append
— so each of its laws needs both. `dictDel`/`filter` is the zero-value
deletion path (mismatch ledger MM-13).
-/

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef

/-! ## `find?` under deletion and `dictSet` -/

theorem find?_filter_ne {κ ν : Type} [BEq κ] [LawfulBEq κ]
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

theorem find?_filter_self {κ ν : Type} [BEq κ] [LawfulBEq κ]
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
theorem find?_map_set_self {κ ν : Type} [BEq κ] [LawfulBEq κ]
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
theorem find?_map_set_ne {κ ν : Type} [BEq κ] [LawfulBEq κ]
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

theorem find?_dictSet_self {κ ν : Type} [BEq κ] [LawfulBEq κ]
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

theorem find?_dictSet_ne {κ ν : Type} [BEq κ] [LawfulBEq κ]
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

/-! ## The same laws under SpecRef's `dictGet?` spelling -/

theorem dictGet?_dictSet_self {κ ν : Type} [BEq κ] [LawfulBEq κ]
    (d : List (κ × ν)) (k : κ) (v : ν) :
    dictGet? (dictSet d k v) k = some v := find?_dictSet_self d k v

theorem dictGet?_dictSet_ne {κ ν : Type} [BEq κ] [LawfulBEq κ]
    (d : List (κ × ν)) (k k' : κ) (v : ν) (h : k' ≠ k) :
    dictGet? (dictSet d k v) k' = dictGet? d k' :=
  find?_dictSet_ne d k k' v h

end EvmSpecsVerify
