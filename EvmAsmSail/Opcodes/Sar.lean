import EvmAsmSail.Opcodes.BinopFamily
import EvmAsmSail.Representation.BitwiseWord
import Mathlib.Tactic.Ring

/-!
# SAR

Arithmetic (sign-propagating) right shift. The extraction ORs a sign fill
over the logical shift (`word_arithmetic_shift_right`, Prelude.lean:373);
SpecRef floor-divides the signed reading (`Int.fdiv`, `iSar`,
InstructionsCore.lean:223). The two meet through `or_fill` and the identity
`fdiv (v − 2^256) 2^s = v/2^s − 2^(256−s)`.

Reachable outcomes: success / stack underflow / out-of-gas (overflow
unreachable for 2-in/1-out).
-/

set_option maxHeartbeats 1000000

namespace EvmAsmSail

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- The SpecRef SAR lambda, named for the proofs below. -/
private def sarSpec (shift value : U256) : U256 :=
  let sv := toSigned value
  if shift < 256 then fromSigned (Int.fdiv sv (2 ^ shift))
  else if sv ≥ 0 then 0 else U256_MAX

theorem alu_sar_eq (s v : Nat) (hv : WordWf v) :
    Evm.Functions.alu_sar s v = sarSpec s v := by
  have hv' := hv
  unfold WordWf at hv'
  simp only [Evm.Functions.alu_sar, Evm.Functions.word_arithmetic_shift_right,
    sarSpec]
  -- the sign bit as a bound
  have hsgn : (Evm.Functions.word_bit v 255 == 1#1) = decide (2 ^ 255 ≤ v) := by
    by_cases hneg : 2 ^ 255 ≤ v
    · rw [beq_iff_eq.mpr ((word_bit_255_iff v hv').mpr hneg), decide_eq_true hneg]
    · rw [show (Evm.Functions.word_bit v 255 == 1#1) = false by
          rw [beq_eq_false_iff_ne]
          intro hbad
          exact hneg ((word_bit_255_iff v hv').mp hbad),
        decide_eq_false hneg]
  have hall : Evm.Functions.WORD_ALL_ONES = 2 ^ 256 - 1 := by decide
  by_cases hs : s < 256
  · rw [if_pos (show ((s < 256 : Bool) = true) from by simpa using hs),
      if_pos hs, hsgn]
    -- both quotient forms
    have hshift : Evm.Functions.word_shift_right v s = v / 2 ^ s := by
      rw [word_shift_right_eq v s hv, Nat.shiftRight_eq_div_pow]
    have hqlt : v / 2 ^ s < 2 ^ (256 - s) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s), ← Nat.pow_add]
      rw [show 256 - s + s = 256 from by omega]
      exact hv'
    have hMle : (2 : Nat) ^ (256 - s) ≤ 2 ^ 256 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    -- fdiv → ediv → Nat division, plus the wrap identity for the sign fill
    have hfdiv0 : ∀ a : Int, a.fdiv ((2 : Int) ^ s) = a / 2 ^ s := fun a =>
      Int.fdiv_eq_ediv_of_nonneg a (by positivity)
    by_cases hneg : 2 ^ 255 ≤ v
    · -- negative reading: shifted value plus the sign fill
      rw [decide_eq_true hneg, if_pos (show ((true : Bool) = true) from rfl)]
      -- the fill value
      have hfill : Evm.Functions.word_shift_left Evm.Functions.WORD_ALL_ONES
          (256 - s) = 2 ^ 256 - 2 ^ (256 - s) := by
        rw [hall, word_shift_left_eq _ _ (by unfold WordWf; omega),
          Nat.shiftLeft_eq]
        -- (2^256 − 1) · 2^(256−s) = (2^(256−s) − 1) · 2^256 + (2^256 − 2^(256−s))
        have hA1 : 1 ≤ (2 : Nat) ^ (256 - s) := Nat.one_le_two_pow
        have hprod : (2 ^ 256 - 1) * 2 ^ (256 - s)
            = (2 ^ (256 - s) - 1) * 2 ^ 256 + (2 ^ 256 - 2 ^ (256 - s)) := by
          have e1 : (2 ^ 256 - 1) * 2 ^ (256 - s)
              = 2 ^ 256 * 2 ^ (256 - s) - 2 ^ (256 - s) := by
            rw [Nat.sub_mul, Nat.one_mul]
          have e2 : (2 ^ (256 - s) - 1) * 2 ^ 256
              = 2 ^ 256 * 2 ^ (256 - s) - 2 ^ 256 := by
            rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm]
          have hBC : (2 : Nat) ^ 256 ≤ 2 ^ 256 * 2 ^ (256 - s) :=
            Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
          have hAC : (2 : Nat) ^ (256 - s) ≤ 2 ^ 256 * 2 ^ (256 - s) := by
            calc (2 : Nat) ^ (256 - s) ≤ 2 ^ 256 := hMle
              _ ≤ 2 ^ 256 * 2 ^ (256 - s) := hBC
          omega
        rw [hprod, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      rw [hfill, hshift,
        word_or_eq _ _ (by unfold WordWf; omega) (by
          unfold WordWf
          have := Nat.one_le_two_pow (n := 256 - s)
          omega),
        or_fill (256 - s) _ (by omega) hqlt]
      -- SpecRef side: fdiv of the negative reading
      rw [toSigned_of_ge v hneg, hfdiv0]
      have hpow : ((2 ^ (256 - s) : Nat) : Int) * ((2 ^ s : Nat) : Int)
          = (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) := by
        push_cast
        rw [← pow_add, show 256 - s + s = 256 from by omega]
        decide
      have hcast : ((v : Int) -
          (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int))
          = (v : Int) + (-((2 ^ (256 - s) : Nat) : Int)) * ((2 ^ s : Nat) : Int) := by
        rw [neg_mul, hpow]
        ring
      rw [hcast]
      rw [show ((2 : Int) ^ s) = ((2 ^ s : Nat) : Int) from by push_cast; ring,
        Int.add_mul_ediv_right _ _ (by positivity),
        show ((v : Int) / ((2 ^ s : Nat) : Int)) = ((v / 2 ^ s : Nat) : Int)
          from (Int.natCast_ediv v (2 ^ s)).symm,
        fromSigned_eq]
      have hq := hqlt
      have hM := hMle
      exact (by omega :
        v / 2 ^ s + (2 ^ 256 - 2 ^ (256 - s)) =
        ((((v / 2 ^ s : Nat) : Int) + -((2 ^ (256 - s) : Nat) : Int)) %
          (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int)).toNat)
    · -- non-negative reading: plain logical shift
      rw [decide_eq_false hneg, if_neg (show ¬((false : Bool) = true) from by decide)]
      rw [hshift, toSigned_of_lt v (by omega), hfdiv0,
        show ((2 : Int) ^ s) = ((2 ^ s : Nat) : Int) from by push_cast; ring,
        show ((v : Int) / ((2 ^ s : Nat) : Int)) = ((v / 2 ^ s : Nat) : Int)
          from (Int.natCast_ediv v (2 ^ s)).symm,
        fromSigned_of_nonneg _ (by positivity) (by
          rw [show ((2 : Int) ^ (256 : Nat)) =
            (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int)
            from by decide]
          have := hqlt
          have := hMle
          omega)]
      omega
  · rw [if_neg (show ¬((s < 256 : Bool) = true) from by simpa using hs),
      if_neg hs, hsgn, hall]
    by_cases hneg : 2 ^ 255 ≤ v
    · rw [decide_eq_true hneg, if_pos (show ((true : Bool) = true) from rfl),
        if_neg (by
          intro hge
          have := (toSigned_neg_iff v hv').mpr hneg
          omega)]
      decide
    · rw [decide_eq_false hneg, if_neg (show ¬((false : Bool) = true) from by decide),
        if_pos (by
          have h1 : ¬ toSigned v < 0 := (toSigned_neg_iff v hv').not.mpr hneg
          omega)]
      decide

private theorem sarSpec_wf (s v : Nat) :
    WordWf (sarSpec s v) := by
  unfold WordWf
  simp only [sarSpec]
  split
  · rw [fromSigned_eq]
    omega
  · split
    · exact Nat.two_pow_pos 256
    · unfold U256_MAX
      omega

open Evm.Functions in
/-- **SAR, all reachable outcomes.** -/
theorem sar_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iSar sRef)
      (runS (Evm.Functions.execute (.SAR ()) pc_in top mem g) hs ss) :=
  binop_step_equiv (.SAR ()) G_verylow alu_sar iSar GasCosts.OPCODE_SAR
    (fun s v => sarSpec s v) rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩
    (fun x y _ hy => alu_sar_eq x y hy)
    (fun x y _ _ => sarSpec_wf x y)
    sRef top g hs ss mem pc_in hrel hpc

end EvmAsmSail
