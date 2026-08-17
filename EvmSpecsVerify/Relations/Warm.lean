import EvmSpecsVerify.Relations.State
import EvmSpecsVerify.Representation.EvmMemory
import Batteries.Tactic.OpenPrivate

/-!
# Warm storage-key relation

SpecRef tracks EIP-2929 warmth as a plain set,
`Evm.accessedStorageKeys : List (Address × Bytes32)` (keys are 32-byte
big-endian encodings). The extraction stamps epochs:
`HostState.warmSlots : List (StorageKey × block_access_index)` with a slot
warm iff its last stamp is at or after `warmEpoch` (`storage_is_warm`), so
entries from earlier transactions go stale without being removed.

`WarmRel` quantifies over host-side keys (address vector × slot word): the
SpecRef pair `(aV.toList, toBeBytes32 w)` is in the set exactly when the
stamp is current. Preservation of the cold-path update
(`setAdd` vs `assocPut … warmEpoch`) needs `toBeBytes32` to be injective on
well-formed words, which follows from the big-endian decode roundtrip
proven here.
-/

open private assocGet assocPut from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## Fixed-width big-endian roundtrip and injectivity -/

/-- Extracting byte `k` commutes with truncation to `m ≥ k + 8` bits. -/
theorem mod_pow_digit (x m k : Nat) (h : k + 8 ≤ m) :
    (x % 2 ^ m) / 2 ^ k % 2 ^ 8 = x / 2 ^ k % 2 ^ 8 := by
  have hsplit : (2 : Nat) ^ m = 2 ^ k * 2 ^ (m - k) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hsplit, Nat.mod_mul_right_div_self]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

/-- The fixed-width encoder only reads the low `8w` bits. -/
theorem natToBytesBE_mod (w x : Nat) :
    natToBytesBE w (x % 256 ^ w) = natToBytesBE w x := by
  unfold EvmAsm.Stateless.SpecRef.natToBytesBE
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_reverse, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_reverse, List.length_range,
      List.getElem_range]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [show (256 : Nat) ^ w = 2 ^ (8 * w) from by
      rw [show (256 : Nat) = 2 ^ 8 from by decide, ← Nat.pow_mul]]
    exact mod_pow_digit x (8 * w) (8 * (w - 1 - i)) (by omega)

/-- Big-endian decode of the fixed-width encode is the identity below
`256^w`. -/
theorem bytesBEtoNat_natToBytesBE (w : Nat) :
    ∀ x, x < 256 ^ w → bytesBEtoNat (natToBytesBE w x) = x := by
  induction w with
  | zero =>
    intro x hx
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    rfl
  | succ w ih =>
    intro x hx
    have hcons : natToBytesBE (w + 1) x
        = BitVec.ofNat 8 (x >>> (8 * w)) :: natToBytesBE w x := by
      unfold EvmAsm.Stateless.SpecRef.natToBytesBE
      rw [List.range_succ, List.reverse_append]
      rfl
    rw [hcons]
    show (BitVec.ofNat 8 (x >>> (8 * w))).toNat
        * 256 ^ (natToBytesBE w x).length
        + bytesBEtoNat (natToBytesBE w x) = x
    have hlen : (natToBytesBE w x).length = w := by
      simp [EvmAsm.Stateless.SpecRef.natToBytesBE]
    rw [hlen]
    have hlow : bytesBEtoNat (natToBytesBE w x) = x % 256 ^ w := by
      rw [← natToBytesBE_mod]
      exact ih _ (Nat.mod_lt _ (Nat.pow_pos (by omega)))
    rw [hlow]
    simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have hdivlt : x / 2 ^ (8 * w) < 2 ^ 8 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega))]
      calc x < 256 ^ (w + 1) := hx
        _ = 2 ^ 8 * 2 ^ (8 * w) := by
            rw [show (256 : Nat) = 2 ^ 8 from by decide, ← Nat.pow_add,
              ← Nat.pow_mul]
            congr 1
            omega
    rw [Nat.mod_eq_of_lt hdivlt,
      show (256 : Nat) ^ w = 2 ^ (8 * w) from by
        rw [show (256 : Nat) = 2 ^ 8 from by decide, ← Nat.pow_mul]]
    have := Nat.div_add_mod x (2 ^ (8 * w))
    have hcomm : x / 2 ^ (8 * w) * 2 ^ (8 * w)
        = 2 ^ (8 * w) * (x / 2 ^ (8 * w)) := Nat.mul_comm _ _
    omega

/-- `toBeBytes32` is injective on well-formed words. -/
theorem toBeBytes32_inj {a b : Nat} (ha : WordWf a) (hb : WordWf b)
    (h : toBeBytes32 a = toBeBytes32 b) : a = b := by
  have h256 : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  have hc := congrArg bytesBEtoNat h
  rwa [show toBeBytes32 a = natToBytesBE 32 a from rfl,
    show toBeBytes32 b = natToBytesBE 32 b from rfl,
    bytesBEtoNat_natToBytesBE 32 a (by rw [h256]; exact ha),
    bytesBEtoNat_natToBytesBE 32 b (by rw [h256]; exact hb)] at hc

/-! ## The relation -/

/-- SpecRef's warm storage-key set vs the extraction's epoch stamps. -/
structure WarmRel (sRef : Machine) (hs : Evm.HostState) : Prop where
  rel : ∀ (aV : Evm.Defs.address) (w : Nat), WordWf w →
    (sRef.evm.accessedStorageKeys.contains (aV.toList, toBeBytes32 w) = true
      ↔ hs.warmEpoch
          ≤ (assocGet hs.warmSlots
              ({ addr := aV, slot := w } : Evm.Defs.StorageKey)).getD 0)

/-! ## `assocGet` / `assocPut` characterization -/

/-- The derived `BEq` on `StorageKey` compares fields. -/
private theorem storageKey_beq_eq (k k' : Evm.Defs.StorageKey) :
    (k == k') = (k.addr == k'.addr && k.slot == k'.slot) := rfl

instance : LawfulBEq Evm.Defs.StorageKey where
  eq_of_beq {a b} h := by
    cases a
    cases b
    simp only [storageKey_beq_eq, Bool.and_eq_true, beq_iff_eq] at h
    simp only [Evm.Defs.StorageKey.mk.injEq]
    exact h
  rfl {a} := by
    rw [storageKey_beq_eq]
    simp

theorem assocGet_put_self {κ ν : Type} [BEq κ] [LawfulBEq κ]
    (s : List (κ × ν)) (k : κ) (v : ν) :
    assocGet (assocPut s k v) k = some v := by
  unfold assocGet assocPut
  simp

theorem assocGet_put_ne {κ ν : Type} [BEq κ] [LawfulBEq κ]
    (s : List (κ × ν)) (k k' : κ) (v : ν) (h : k' ≠ k) :
    assocGet (assocPut s k v) k' = assocGet s k' := by
  unfold assocGet assocPut
  rw [List.find?_cons_of_neg (by simpa using Ne.symm h)]
  congr 1
  induction s with
  | nil => rfl
  | cons e es ihs =>
    by_cases he : e.1 = k
    · rw [List.filter_cons_of_neg (by simpa using he)]
      rw [List.find?_cons_of_neg (by simp [he]; exact fun hc => h hc.symm)]
      exact ihs
    · rw [List.filter_cons_of_pos (by simpa using he)]
      by_cases hk' : e.1 = k'
      · rw [List.find?_cons_of_pos (by simpa using hk'),
          List.find?_cons_of_pos (by simpa using hk')]
      · rw [List.find?_cons_of_neg (by simpa using hk'),
          List.find?_cons_of_neg (by simpa using hk')]
        exact ihs

/-- The cold-path update preserves the relation: SpecRef `setAdd` vs the
extraction's fresh epoch stamp. -/
theorem warm_after_mark (keys : List (Address × Bytes32))
    (slots : List (Evm.Defs.StorageKey × Nat)) (epoch : Nat)
    (aV : Evm.Defs.address) (x : Nat) (hx : WordWf x)
    (h : ∀ (bV : Evm.Defs.address) (w : Nat), WordWf w →
      (keys.contains (bV.toList, toBeBytes32 w) = true
        ↔ epoch ≤ (assocGet slots
            ({ addr := bV, slot := w } : Evm.Defs.StorageKey)).getD 0)) :
    ∀ (bV : Evm.Defs.address) (w : Nat), WordWf w →
      ((setAdd keys (aV.toList, toBeBytes32 x)).contains
          (bV.toList, toBeBytes32 w) = true
        ↔ epoch ≤ (assocGet
            (assocPut slots ({ addr := aV, slot := x } : Evm.Defs.StorageKey) epoch)
            ({ addr := bV, slot := w } : Evm.Defs.StorageKey)).getD 0) := by
  intro bV w hw
  by_cases hkey : bV = aV ∧ w = x
  · obtain ⟨rfl, rfl⟩ := hkey
    rw [assocGet_put_self]
    simp only [Option.getD_some, le_refl, iff_true]
    unfold EvmAsm.Stateless.SpecRef.setAdd
    split
    · rename_i hc
      exact hc
    · simp
  · have hne : ({ addr := bV, slot := w } : Evm.Defs.StorageKey)
        ≠ ({ addr := aV, slot := x } : Evm.Defs.StorageKey) := by
      intro hc
      injection hc with h1 h2
      exact hkey ⟨h1, h2⟩
    have hpairne : (bV.toList, toBeBytes32 w)
        ≠ (aV.toList, toBeBytes32 x) := by
      intro hc
      injection hc with h1 h2
      refine hkey ⟨?_, toBeBytes32_inj hw hx h2⟩
      exact Vector.toList_inj.mp h1
    rw [assocGet_put_ne _ _ _ _ hne]
    rw [show (setAdd keys (aV.toList, toBeBytes32 x)).contains
        (bV.toList, toBeBytes32 w)
        = keys.contains (bV.toList, toBeBytes32 w) from by
      unfold EvmAsm.Stateless.SpecRef.setAdd
      split
      · rfl
      · rw [List.contains_append]
        simp [hpairne]]
    exact h bV w hw

end EvmSpecsVerify
