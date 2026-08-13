import EvmAsmSail.Opcodes.BinopFamily
import EvmAsmSail.Representation.SignedWord
import Mathlib.Tactic.Push

/-!
# SDIV

Signed division, truncating toward zero. The extraction computes over
magnitudes and the sign bit (`alu_sdiv`, Prelude.lean:453); SpecRef divides
the `natAbs` of the signed readings and re-signs by the product's sign
(`iSdiv`, InstructionsCore.lean:144). The correspondence goes through the
signed-word bridge (`Representation/SignedWord.lean`).

SpecRef carries an explicit `-2^255 / -1` special case; on the extraction
side that case needs no special handling (the magnitude quotient `2^255`
re-wraps to itself), so the pure lemma discharges it by computation.

Reachable outcomes: success / stack underflow / out-of-gas (overflow
unreachable for 2-in/1-out).
-/

set_option maxHeartbeats 1000000

namespace EvmAsmSail

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- The SpecRef SDIV lambda, named for the proofs below. -/
private def sdivSpec (x y : U256) : U256 :=
  let a := toSigned x
  let b := toSigned y
  if b == 0 then 0
  else if a == -(2 ^ 255 : Int) && b == -1 then fromSigned (-(2 ^ 255 : Int))
  else
    let q : Int := (if a * b < 0 then -1 else 1) * ((a.natAbs / b.natAbs : Nat) : Int)
    fromSigned q

/-- Sign-product characterization, in the bridge's arithmetic vocabulary. -/
private theorem mul_neg_iff' (a b : Int) :
    a * b < 0 ↔ (a < 0 ∧ 0 < b) ∨ (0 < a ∧ b < 0) := by
  constructor
  · intro h
    rcases lt_trichotomy a 0 with ha | ha | ha
    · rcases lt_trichotomy b 0 with hb | hb | hb
      · exact absurd (Int.mul_pos_of_neg_of_neg ha hb) (by omega)
      · simp [hb] at h
      · exact Or.inl ⟨ha, hb⟩
    · simp [ha] at h
    · rcases lt_trichotomy b 0 with hb | hb | hb
      · exact Or.inr ⟨ha, hb⟩
      · simp [hb] at h
      · exact absurd (Int.mul_pos ha hb) (by omega)
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact Int.mul_neg_of_neg_of_pos ha hb
    · exact Int.mul_neg_of_pos_of_neg ha hb

theorem alu_sdiv_eq (x y : Nat) (hx : WordWf x) (hy : WordWf y) :
    Evm.Functions.alu_sdiv x y = sdivSpec x y := by
  unfold WordWf at hx hy
  simp only [Evm.Functions.alu_sdiv, sdivSpec]
  have hz : Evm.Functions.word_is_zero y = (y == 0) := by
    rw [Evm.Functions.word_is_zero]; rfl
  by_cases hy0 : y = 0
  · subst hy0
    rw [hz]
    have ht0 : toSigned 0 = 0 := toSigned_of_lt 0 (by omega)
    simp [ht0]
    rfl
  · have hB0 : toSigned y ≠ 0 := by
      rw [Ne, toSigned_eq_zero_iff y hy]; exact hy0
    rw [hz, show ((y == 0) : Bool) = false by simp [hy0],
      if_neg (show ¬((false : Bool) = true) from by decide),
      show ((toSigned y == 0) : Bool) = false by
        rw [beq_eq_false_iff_ne]; exact hB0,
      if_neg (show ¬((false : Bool) = true) from by decide)]
    -- the magnitude quotient, through the bridge
    have hdiv : Evm.Functions.word_div_word (Evm.Functions.word_abs x)
        (Evm.Functions.word_abs y)
        = (toSigned x).natAbs / (toSigned y).natAbs := by
      rw [word_abs_eq x hx, word_abs_eq y hy, Evm.Functions.word_div_word]
      rw [show (((toSigned y).natAbs == 0) : Bool) = false by
        rw [beq_eq_false_iff_ne, Ne, Int.natAbs_eq_zero]; exact hB0]
      rw [if_neg (show ¬((false : Bool) = true) from by decide)]
      rfl
    have hqle : (toSigned x).natAbs / (toSigned y).natAbs ≤ 2 ^ 255 :=
      Nat.le_trans (Nat.div_le_self _ _) (natAbs_toSigned_le x hx)
    -- sign bits as sign predicates
    have hsx : (Evm.Functions.word_bit x 255 == 1#1) = decide (toSigned x < 0) := by
      by_cases hneg : 2 ^ 255 ≤ x
      · rw [beq_iff_eq.mpr ((word_bit_255_iff x hx).mpr hneg),
          decide_eq_true ((toSigned_neg_iff x hx).mpr hneg)]
      · rw [show (Evm.Functions.word_bit x 255 == 1#1) = false by
            rw [beq_eq_false_iff_ne]
            intro hbad
            exact hneg ((word_bit_255_iff x hx).mp hbad),
          decide_eq_false (by rw [toSigned_neg_iff x hx]; exact hneg)]
    have hsy : (Evm.Functions.word_bit y 255 == 1#1) = decide (toSigned y < 0) := by
      by_cases hneg : 2 ^ 255 ≤ y
      · rw [beq_iff_eq.mpr ((word_bit_255_iff y hy).mpr hneg),
          decide_eq_true ((toSigned_neg_iff y hy).mpr hneg)]
      · rw [show (Evm.Functions.word_bit y 255 == 1#1) = false by
            rw [beq_eq_false_iff_ne]
            intro hbad
            exact hneg ((word_bit_255_iff y hy).mp hbad),
          decide_eq_false (by rw [toSigned_neg_iff y hy]; exact hneg)]
    rw [hdiv, hsx, hsy]
    by_cases hxneg : toSigned x < 0 <;> by_cases hyneg : toSigned y < 0
    · -- both negative: signs equal; SpecRef's -2^255 / -1 case sits here
      rw [decide_eq_true hxneg, decide_eq_true hyneg,
        show Evm.Functions.neq_bool true true = false from by decide,
        if_neg (show ¬((false : Bool) = true) from by decide)]
      by_cases hsp : toSigned x = -(2 ^ 255 : Int) ∧ toSigned y = -1
      · rw [hsp.1, hsp.2]
        decide
      · rw [if_neg (show ¬((toSigned x == -(2 ^ 255 : Int)
              && toSigned y == -1) = true) from by
            rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]; exact hsp)]
        rw [if_neg (by rw [mul_neg_iff']; omega), Int.one_mul,
          fromSigned_of_nonneg _ (by omega) (by
            rw [show ((2:Int) ^ (256:Nat)) = (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) from by decide]
            omega)]
        omega
    · -- x negative, y non-negative: signs differ, quotient re-signed
      rw [decide_eq_true hxneg, decide_eq_false hyneg,
        show Evm.Functions.neq_bool true false = true from by decide,
        if_pos (show ((true : Bool) = true) from rfl),
        word_negate_eq _ (by omega)]
      rw [if_neg (show ¬((toSigned x == -(2 ^ 255 : Int)
            && toSigned y == -1) = true) from by
          rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
          rintro ⟨h1, h2⟩
          rw [h2] at hyneg
          exact hyneg (by decide))]
      rw [if_pos (by rw [mul_neg_iff']; omega)]
      congr 1
      omega
    · -- x non-negative, y negative: signs differ
      rw [decide_eq_false hxneg, decide_eq_true hyneg,
        show Evm.Functions.neq_bool false true = true from by decide,
        if_pos (show ((true : Bool) = true) from rfl),
        word_negate_eq _ (by omega)]
      rw [if_neg (show ¬((toSigned x == -(2 ^ 255 : Int)
            && toSigned y == -1) = true) from by
          rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
          rintro ⟨h1, h2⟩
          rw [h1] at hxneg
          exact absurd (by decide : -((2:Int) ^ 255) < 0) hxneg)]
      by_cases hA0 : toSigned x = 0
      · have hq0 : (toSigned x).natAbs / (toSigned y).natAbs = 0 := by
          simp [Int.natAbs_eq_zero.mpr hA0]
        rw [hq0, if_neg (by simp [hA0])]
        simp [fromSigned_eq]
      · rw [if_pos (by rw [mul_neg_iff']; omega)]
        congr 1
        omega
    · -- both non-negative: signs equal
      rw [decide_eq_false hxneg, decide_eq_false hyneg,
        show Evm.Functions.neq_bool false false = false from by decide,
        if_neg (show ¬((false : Bool) = true) from by decide)]
      rw [if_neg (show ¬((toSigned x == -(2 ^ 255 : Int)
            && toSigned y == -1) = true) from by
          rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
          rintro ⟨h1, h2⟩
          rw [h1] at hxneg
          exact hxneg (by decide))]
      rw [if_neg (by rw [mul_neg_iff']; omega), Int.one_mul,
        fromSigned_of_nonneg _ (by omega) (by
          rw [show ((2:Int) ^ (256:Nat)) = (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) from by decide]
          omega)]
      omega

private theorem sdivSpec_wf (x y : Nat) :
    WordWf (sdivSpec x y) := by
  unfold WordWf
  rw [sdivSpec]
  split
  · omega
  · split
    · rw [fromSigned_eq]; omega
    · rw [fromSigned_eq]; omega

open Evm.Functions in
/-- **SDIV, all reachable outcomes.** -/
theorem sdiv_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iSdiv sRef)
      (runS (Evm.Functions.execute (.SDIV ()) pc_in top mem g) hs ss) :=
  binop_step_equiv (.SDIV ()) G_low alu_sdiv iSdiv GasCosts.OPCODE_SDIV
    (fun x y => sdivSpec x y) rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩
    (fun x y hx hy => alu_sdiv_eq x y hx hy)
    (fun x y _ _ => sdivSpec_wf x y)
    sRef top g hs ss mem pc_in hrel hpc

end EvmAsmSail
