import EvmAsmSail.Opcodes.Sdiv

/-!
# SMOD

Signed remainder, with the sign of the dividend. The extraction takes the
magnitude remainder and re-signs by the dividend's sign bit (`alu_smod`,
Prelude.lean:471); SpecRef computes `natAbs`-remainders of the signed
readings (`iSmod`, InstructionsCore.lean:156). The correspondence goes
through the signed-word bridge.

Reachable outcomes: success / stack underflow / out-of-gas (overflow
unreachable for 2-in/1-out).
-/

set_option maxHeartbeats 1000000

namespace EvmAsmSail

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- The SpecRef SMOD lambda, named for the proofs below. -/
private def smodSpec (x y : U256) : U256 :=
  let a := toSigned x
  let b := toSigned y
  if b == 0 then 0
  else fromSigned ((if a < 0 then -1 else 1) * ((a.natAbs % b.natAbs : Nat) : Int))

theorem alu_smod_eq (x y : Nat) (hx : WordWf x) (hy : WordWf y) :
    Evm.Functions.alu_smod x y = smodSpec x y := by
  unfold WordWf at hx hy
  simp only [Evm.Functions.alu_smod, smodSpec]
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
    have hmod : Evm.Functions.word_mod_word (Evm.Functions.word_abs x)
        (Evm.Functions.word_abs y)
        = (toSigned x).natAbs % (toSigned y).natAbs := by
      rw [word_abs_eq x hx, word_abs_eq y hy, Evm.Functions.word_mod_word]
      rw [show (((toSigned y).natAbs == 0) : Bool) = false by
        rw [beq_eq_false_iff_ne, Ne, Int.natAbs_eq_zero]; exact hB0]
      rw [if_neg (show ¬((false : Bool) = true) from by decide)]
      rfl
    have hrle : (toSigned x).natAbs % (toSigned y).natAbs ≤ 2 ^ 255 :=
      Nat.le_trans (Nat.mod_le _ _) (natAbs_toSigned_le x hx)
    have hsx : (Evm.Functions.word_bit x 255 == 1#1) = decide (toSigned x < 0) := by
      by_cases hneg : 2 ^ 255 ≤ x
      · rw [beq_iff_eq.mpr ((word_bit_255_iff x hx).mpr hneg),
          decide_eq_true ((toSigned_neg_iff x hx).mpr hneg)]
      · rw [show (Evm.Functions.word_bit x 255 == 1#1) = false by
            rw [beq_eq_false_iff_ne]
            intro hbad
            exact hneg ((word_bit_255_iff x hx).mp hbad),
          decide_eq_false (by rw [toSigned_neg_iff x hx]; exact hneg)]
    rw [hmod, hsx]
    by_cases hxneg : toSigned x < 0
    · -- negative dividend: re-signed remainder on both sides
      rw [decide_eq_true hxneg, if_pos (show ((true : Bool) = true) from rfl),
        word_negate_eq _ (by omega), if_pos hxneg]
      congr 1
      omega
    · -- non-negative dividend: plain remainder on both sides
      rw [decide_eq_false hxneg, if_neg (show ¬((false : Bool) = true) from by decide),
        if_neg hxneg, Int.one_mul,
        fromSigned_of_nonneg _ (by omega) (by
          rw [show ((2:Int) ^ (256:Nat)) =
            (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int)
            from by decide]
          omega)]
      omega

private theorem smodSpec_wf (x y : Nat) (hx : WordWf x) (hy : WordWf y) :
    WordWf (smodSpec x y) := by
  unfold WordWf at *
  rw [smodSpec]
  split
  · omega
  · rw [fromSigned_eq]; omega

open Evm.Functions in
/-- **SMOD, all reachable outcomes.** -/
theorem smod_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iSmod sRef)
      (runS (Evm.Functions.execute (.SMOD ()) pc_in top mem g) hs ss) :=
  binop_step_equiv (.SMOD ()) G_low alu_smod iSmod GasCosts.OPCODE_SMOD
    (fun x y => smodSpec x y) rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩
    (fun x y hx hy => alu_smod_eq x y hx hy)
    (fun x y hx hy => smodSpec_wf x y hx hy)
    sRef top g hs ss mem pc_in hrel hpc

end EvmAsmSail
