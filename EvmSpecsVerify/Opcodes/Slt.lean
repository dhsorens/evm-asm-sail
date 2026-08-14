import EvmSpecsVerify.Opcodes.Sdiv

/-!
# SLT

Signed less-than. The extraction decides by sign bits, falling back to the
unsigned order when they agree (`word_slt`, Prelude.lean:410); SpecRef
compares the signed readings directly (`iSlt`, InstructionsCore.lean:201).
`word_slt_eq` is the bridge fact, shared with SGT.

Reachable outcomes: success / stack underflow / out-of-gas (overflow
unreachable for 2-in/1-out).
-/

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

open private boolPush from EvmAsm.Stateless.SpecRef.InstructionsCore

/-- The extraction's sign-case comparison agrees with the signed order. -/
theorem word_slt_eq (x y : Nat) (hx : WordWf x) (hy : WordWf y) :
    Evm.Functions.word_slt x y = decide (toSigned x < toSigned y) := by
  unfold WordWf at hx hy
  simp only [Evm.Functions.word_slt, Evm.Functions.word_ult]
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
  rw [hsx, hsy]
  by_cases hxneg : toSigned x < 0 <;> by_cases hyneg : toSigned y < 0
  · -- both negative: unsigned order coincides with the signed order
    rw [decide_eq_true hxneg, decide_eq_true hyneg,
      if_pos (show ((true : Bool) = true) from rfl),
      if_pos (show ((true : Bool) = true) from rfl)]
    have htx := toSigned_of_ge x ((toSigned_neg_iff x hx).mp hxneg)
    have hty := toSigned_of_ge y ((toSigned_neg_iff y hy).mp hyneg)
    by_cases hlt : x < y
    · rw [decide_eq_true hlt, decide_eq_true (by omega)]
    · rw [decide_eq_false hlt, decide_eq_false (by omega)]
  · -- x negative, y non-negative: strictly below
    rw [decide_eq_true hxneg, decide_eq_false hyneg,
      if_pos (show ((true : Bool) = true) from rfl),
      if_neg (show ¬((false : Bool) = true) from by decide)]
    have htx := toSigned_of_ge x ((toSigned_neg_iff x hx).mp hxneg)
    have hty := toSigned_of_lt y (by
      by_contra hge
      exact hyneg ((toSigned_neg_iff y hy).mpr (by omega)))
    exact (decide_eq_true (by omega)).symm
  · -- x non-negative, y negative: strictly above
    rw [decide_eq_false hxneg, decide_eq_true hyneg,
      if_neg (show ¬((false : Bool) = true) from by decide),
      if_pos (show ((true : Bool) = true) from rfl)]
    have htx := toSigned_of_lt x (by
      by_contra hge
      exact hxneg ((toSigned_neg_iff x hx).mpr (by omega)))
    have hty := toSigned_of_ge y ((toSigned_neg_iff y hy).mp hyneg)
    exact (decide_eq_false (by omega)).symm
  · -- both non-negative: unsigned order coincides
    rw [decide_eq_false hxneg, decide_eq_false hyneg,
      if_neg (show ¬((false : Bool) = true) from by decide),
      if_neg (show ¬((false : Bool) = true) from by decide)]
    have htx := toSigned_of_lt x (by
      by_contra hge
      exact hxneg ((toSigned_neg_iff x hx).mpr (by omega)))
    have hty := toSigned_of_lt y (by
      by_contra hge
      exact hyneg ((toSigned_neg_iff y hy).mpr (by omega)))
    by_cases hlt : x < y
    · rw [decide_eq_true hlt, decide_eq_true (by omega)]
    · rw [decide_eq_false hlt, decide_eq_false (by omega)]

theorem alu_slt_eq (x y : Nat) (hx : WordWf x) (hy : WordWf y) :
    Evm.Functions.alu_slt x y = boolPush (toSigned x < toSigned y) := by
  rw [Evm.Functions.alu_slt, word_slt_eq x y hx hy]
  show (if decide (toSigned x < toSigned y) = true
      then ((1 : Int)).toNat else ((0 : Int)).toNat)
    = if decide (toSigned x < toSigned y) = true then 1 else 0
  split <;> rfl

open Evm.Functions in
/-- **SLT, all reachable outcomes.** -/
theorem slt_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iSlt sRef)
      (runS (Evm.Functions.execute (.SLT ()) pc_in top mem g) hs ss) :=
  binop_step_equiv (.SLT ()) G_verylow alu_slt iSlt GasCosts.OPCODE_SLT
    (fun x y => boolPush (toSigned x < toSigned y)) rfl rfl
    ⟨rfl, fun _ _ _ _ => rfl⟩
    (fun x y hx hy => alu_slt_eq x y hx hy)
    (fun _ _ _ _ => boolPush_wf _)
    sRef top g hs ss mem pc_in hrel hpc

end EvmSpecsVerify
