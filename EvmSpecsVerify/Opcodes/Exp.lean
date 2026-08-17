import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas
import EvmSpecsVerify.Representation.BitwiseWord
import EvmSpecsVerify.Representation.SignedWord
import Mathlib.Data.Nat.ModEq

/-!
# EXP

Not a `binOp` harvest: gas is exponent-dependent on both sides, and both
sides pop **before** charging (SpecRef pops in `iExp` itself; the extraction's
`execute_exp` pops to read the exponent for `exp_gas`). The `Evm` ALU is the
fuelled square-and-multiply loop `alu_exp` (`whileFuelM`, fuel = bit length);
SpecRef pushes `powMod`. The bridge:

* `exp_gas_eq` — the EIP-160 byte count agrees with SpecRef's
  `log2`-derived `exponent_bytes` (via `word_bit_length_eq`).
* `runS_alu_exp` — the loop runs pure (`runS_whileFuelM` +
  `whileFuelPure_exp`) and computes `powMod` exactly.

Reachable outcomes: success / stack underflow / out-of-gas (overflow
unreachable for 2-in/1-out).
-/

open private pcAdd from EvmAsm.Stateless.SpecRef.InstructionsCore
open private writeListAt from Evm.HostAxioms

set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs
open EvmAsm.Rv64.Accel (powMod powModAux)

/-! ## The gas formula -/

/-- SpecRef's `exponent_bytes` (`iExp`): significant bytes of the exponent. -/
def expBytes (e : Nat) : Nat :=
  if e == 0 then 0 else (Nat.log2 (max e 1) + 1 + 7) / 8

/-- SpecRef's EXP charge (EIP-160). -/
def expCost (e : Nat) : Nat :=
  GasCosts.OPCODE_EXP_BASE + GasCosts.OPCODE_EXP_PER_BYTE * expBytes e

/-- The extraction's `exp_gas` is SpecRef's charge. -/
theorem exp_gas_eq (e : Nat) (he : WordWf e) :
    Evm.Functions.exp_gas e = expCost e := by
  simp only [Evm.Functions.exp_gas, Evm.Functions.word_byte_length,
    word_bit_length_eq e he, expCost, expBytes]
  rcases eq_or_ne e 0 with rfl | h
  · rfl
  · have hmax : max e 1 = e := Nat.max_eq_left (by omega)
    simp only [hmax, beq_iff_eq, h, if_false]
    show 50 * ((Nat.log2 e + 1 + 7) / 8) + 10 = 10 + 50 * ((Nat.log2 e + 1 + 7) / 8)
    omega

/-! ## Word primitives of the loop body -/

theorem word_mul_word_eq (a b : Nat) :
    Evm.Functions.word_mul_word a b = a * b % 2 ^ 256 := by
  show ((a : Int) * (b : Int)).toNat % ((2 : Int) ^ (256 : Nat)).toNat = _
  rw [two_pow_toNat, ← Int.natCast_mul, Int.toNat_natCast]

theorem word_shift_right_one_eq (v : Nat) :
    Evm.Functions.word_shift_right_one v = v / 2 := rfl

/-- The low bit reads as parity (words are < `2^256`). -/
theorem word_bit_zero_eq (a : Nat) (ha : a < 2 ^ 256) :
    (Evm.Functions.word_bit a 0 == 1#1) = decide (a % 2 = 1) := by
  rw [Evm.Functions.word_bit, get_slice_int_256, Sail.BitVec.access]
  have h0 : (BitVec.ofNat 256 a)[0]! = a.testBit 0 := by
    rw [getElem!_pos _ _ (by omega), BitVec.getElem_eq_testBit_toNat]
    simp only [BitVec.toNat_ofNat]
    congr 1
    omega
  rw [h0, Nat.testBit_zero]
  cases hpar : decide (a % 2 = 1) <;> simp_all

/-! ## SpecRef's accelerator `powMod` is modular exponentiation -/

theorem powModAux_eq (m : Nat) :
    ∀ (fuel : Nat) (b e : Nat), e < 2 ^ fuel →
      powModAux m fuel b e = b ^ e % m := by
  intro fuel
  induction fuel with
  | zero =>
    intro b e he
    have : e = 0 := by omega
    subst this
    simp [powModAux]
  | succ n ih =>
    intro b e he
    rcases eq_or_ne e 0 with rfl | h0
    · simp [powModAux]
    · rw [show powModAux m (n + 1) b e =
          (if e = 0 then 1 % m else
            if e % 2 = 1
            then powModAux m n (b * b % m) (e / 2) * (b % m) % m
            else powModAux m n (b * b % m) (e / 2)) from rfl,
        if_neg h0]
      have hdiv : e / 2 < 2 ^ n := by
        have : (2 : Nat) ^ (n + 1) = 2 ^ n * 2 := by ring
        omega
      have hpow2 : (b * b) ^ (e / 2) = b ^ (2 * (e / 2)) := by
        rw [Nat.pow_mul]; ring
      have hesplit : b ^ e = b ^ (2 * (e / 2)) * b ^ (e % 2) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      by_cases hpar : e % 2 = 1
      · rw [if_pos hpar, ih (b * b % m) (e / 2) hdiv]
        have h2 : (b * b) ^ (e / 2) * b = b ^ e := by
          rw [hesplit, hpar, pow_one, hpow2]
        have hx : (b * b % m) ^ (e / 2) % m * (b % m)
            ≡ (b * b) ^ (e / 2) * b [MOD m] :=
          Nat.ModEq.mul
            ((Nat.mod_modEq _ _).trans (Nat.ModEq.pow _ (Nat.mod_modEq _ _)))
            (Nat.mod_modEq _ _)
        rw [← h2]
        exact hx
      · rw [if_neg hpar, ih (b * b % m) (e / 2) hdiv]
        have h0' : e % 2 = 0 := by omega
        have h2 : (b * b) ^ (e / 2) = b ^ e := by
          rw [hesplit, h0', pow_zero, Nat.mul_one, hpow2]
        have hx : (b * b % m) ^ (e / 2) ≡ (b * b) ^ (e / 2) [MOD m] :=
          Nat.ModEq.pow _ (Nat.mod_modEq _ _)
        rw [← h2]
        exact hx

theorem powMod_eq (b e m : Nat) (he : e < 2 ^ 512) :
    powMod b e m = b ^ e % m := by
  rw [powMod, powModAux_eq m 512 (b % m) e he, ← Nat.pow_mod]

theorem powMod_wf (b e : Nat) (he : WordWf e) :
    WordWf (powMod b e U256_MOD) := by
  rw [powMod_eq b e U256_MOD
    (lt_of_lt_of_le he (Nat.pow_le_pow_right (by omega) (by omega)))]
  exact Nat.mod_lt _ (Nat.two_pow_pos 256)

/-! ## The fuelled loop runs pure -/

/-- Pure model of `whileFuelM`'s recursion. -/
def whileFuelPure (c : α → Bool) (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => if c x then whileFuelPure c f n (f x) else x

/-- A `whileFuelM` whose condition and body run pure runs pure. -/
theorem runS_whileFuelM (c : α → Bool) (f : α → α)
    (condM : α → Evm.SailM Bool) (bodyM : α → Evm.SailM α)
    (hc : ∀ x hs ss, runS (condM x) hs ss = .ok (c x, hs) ss)
    (hf : ∀ x hs ss, runS (bodyM x) hs ss = .ok (f x, hs) ss)
    (fuel : Nat) (x : α) (hs : Evm.HostState) (ss : SeqState) :
    runS (whileFuelM fuel condM x bodyM) hs ss =
      .ok (whileFuelPure c f fuel x, hs) ss := by
  show runS (whileFuelM.go condM bodyM x fuel) hs ss = _
  induction fuel generalizing x hs ss with
  | zero => exact runS_pure x hs ss
  | succ n ih =>
    show runS (condM x >>= fun b =>
      if b then bodyM x >>= fun y => whileFuelM.go condM bodyM y n
      else pure x) hs ss = _
    refine runS_bind_ok (hc x hs ss) ?_
    by_cases hcx : c x
    · rw [if_pos hcx]
      refine runS_bind_ok (hf x hs ss) ?_
      rw [ih]
      simp [whileFuelPure, hcx]
    · rw [if_neg hcx]
      simp [whileFuelPure, hcx]

/-- The loop condition of `alu_exp`, purely. -/
def expCond (x : Nat × Nat × Nat × Nat) : Bool := x.2.2.1 >b 0

/-- One `alu_exp` loop iteration, purely: multiply on a set low bit,
square (except on the last round), halve, decrement. -/
def expStep (x : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat :=
  let (b, e, remaining, result) := x
  let result := if Evm.Functions.word_bit e 0 == 1#1
    then Evm.Functions.word_mul_word result b else result
  let b := if remaining >b 1 then Evm.Functions.word_mul_word b b else b
  let e := Evm.Functions.word_shift_right_one e
  let remaining := if remaining >b 0 then remaining - 1 else 0
  (b, e, remaining, result)

/-- The loop invariant: with `e < 2^n` and fuel `n` (`n ≤ 256` keeps the
low-bit read faithful), the accumulator lands on `res * b^e mod 2^256`. -/
theorem whileFuelPure_exp :
    ∀ (n : Nat), n ≤ 256 → ∀ (b e res : Nat), e < 2 ^ n → res < 2 ^ 256 →
      (whileFuelPure expCond expStep n (b, e, n, res)).2.2.2
        = res * b ^ e % 2 ^ 256 := by
  intro n
  induction n with
  | zero =>
    intro _ b e res he hres
    have : e = 0 := by omega
    subst this
    simp only [whileFuelPure, Nat.pow_zero, Nat.mul_one]
    exact (Nat.mod_eq_of_lt hres).symm
  | succ n ih =>
    intro hn b e res he hres
    have he256 : e < 2 ^ 256 :=
      lt_of_lt_of_le he (Nat.pow_le_pow_right (by omega) hn)
    have hcond : expCond (b, e, n + 1, res) = true := by
      simp [expCond]
    have hstep : expStep (b, e, n + 1, res) =
        (if n + 1 > 1 then b * b % 2 ^ 256 else b, e / 2, n,
          if e % 2 = 1 then res * b % 2 ^ 256 else res) := by
      simp only [expStep, word_bit_zero_eq e he256, word_mul_word_eq,
        word_shift_right_one_eq]
      have h0 : ((n + 1 >b 0)) = true := by simp
      simp only [h0, if_true]
      by_cases hpar : e % 2 = 1 <;> simp [hpar]
    have hdiv : e / 2 < 2 ^ n := by
      have : (2 : Nat) ^ (n + 1) = 2 ^ n * 2 := by ring
      omega
    have hres' : (if e % 2 = 1 then res * b % 2 ^ 256 else res) < 2 ^ 256 := by
      split
      · exact Nat.mod_lt _ (Nat.two_pow_pos 256)
      · exact hres
    show (whileFuelPure expCond expStep (n + 1) (b, e, n + 1, res)).2.2.2 = _
    rw [whileFuelPure, if_pos hcond, hstep]
    cases n with
    | zero =>
      -- last round: no squaring, `e ∈ {0, 1}`, loop exits with the result
      simp only [Nat.lt_irrefl, if_false, whileFuelPure]
      have : e = 0 ∨ e = 1 := by omega
      rcases this with rfl | rfl
      · rw [if_neg (by omega), Nat.pow_zero, Nat.mul_one]
        exact (Nat.mod_eq_of_lt hres).symm
      · simp
    | succ m =>
      rw [if_pos (by omega)]
      rw [ih (by omega) (b * b % 2 ^ 256) (e / 2)
        (if e % 2 = 1 then res * b % 2 ^ 256 else res) hdiv hres']
      -- `res' * (b²%M)^(e/2) ≡ res * b^e  (mod M)`
      have hpow2 : (b * b) ^ (e / 2) = b ^ (2 * (e / 2)) := by
        rw [Nat.pow_mul]; ring
      have hesplit : b ^ e = b ^ (2 * (e / 2)) * b ^ (e % 2) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      by_cases hpar : e % 2 = 1
      · rw [if_pos hpar]
        have h2 : res * b * (b * b) ^ (e / 2) = res * b ^ e := by
          rw [hesplit, hpar, pow_one, hpow2]
          ring
        have hx : (res * b % 2 ^ 256) * ((b * b % 2 ^ 256) ^ (e / 2))
            ≡ res * b * (b * b) ^ (e / 2) [MOD 2 ^ 256] :=
          Nat.ModEq.mul (Nat.mod_modEq _ _)
            (Nat.ModEq.pow _ (Nat.mod_modEq _ _))
        rw [← h2]
        exact hx
      · rw [if_neg hpar]
        have h0' : e % 2 = 0 := by omega
        have h2 : res * (b * b) ^ (e / 2) = res * b ^ e := by
          rw [hesplit, h0', pow_zero, Nat.mul_one, hpow2]
        have hx : res * ((b * b % 2 ^ 256) ^ (e / 2))
            ≡ res * (b * b) ^ (e / 2) [MOD 2 ^ 256] :=
          Nat.ModEq.mul (Nat.ModEq.refl res)
            (Nat.ModEq.pow _ (Nat.mod_modEq _ _))
        rw [← h2]
        exact hx

/-- **`alu_exp` computes `powMod`** (and runs pure: no host/register
traffic). -/
theorem runS_alu_exp (a e : Nat) (he : WordWf e)
    (hs : Evm.HostState) (ss : SeqState) :
    runS (Evm.Functions.alu_exp a e) hs ss =
      .ok (powMod a e U256_MOD, hs) ss := by
  have hval : (whileFuelPure expCond expStep (Evm.Functions.word_bit_length e)
      (a, e, Evm.Functions.word_bit_length e, Evm.Functions.WORD_ONE)).2.2.2
      = powMod a e U256_MOD := by
    have hone : Evm.Functions.WORD_ONE = 1 := by decide
    have he512 : e < 2 ^ 512 :=
      lt_of_lt_of_le he (Nat.pow_le_pow_right (by omega) (by omega))
    rw [hone, word_bit_length_eq e he]
    rcases eq_or_ne e 0 with rfl | h0
    · rw [if_pos rfl, powMod_eq a 0 U256_MOD he512]
      show (1 : Nat) = 1 % 2 ^ 256
      decide
    · rw [if_neg (by simpa using h0)]
      have heR : e < 2 ^ (Nat.log2 e + 1) :=
        (Nat.log2_lt h0).mp (Nat.lt_succ_self _)
      have hR256 : Nat.log2 e + 1 ≤ 256 := by
        have := (Nat.log2_lt h0).mpr he
        omega
      rw [whileFuelPure_exp (Nat.log2 e + 1) hR256 a e 1 heR (by decide),
        Nat.one_mul, powMod_eq a e U256_MOD he512]
      rfl
  simp only [Evm.Functions.alu_exp]
  refine runS_bind_ok (runS_bind_ok
    (runS_whileFuelM expCond expStep _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (Evm.Functions.word_bit_length e)
      (a, e, Evm.Functions.word_bit_length e, Evm.Functions.WORD_ONE) hs ss)
    (runS_pure _ _ _)) ?_
  show EStateM.Result.ok
    ((whileFuelPure expCond expStep (Evm.Functions.word_bit_length e)
      (a, e, Evm.Functions.word_bit_length e,
        Evm.Functions.WORD_ONE)).2.2.2, hs) ss = _
  rw [hval]

/-! ## SpecRef run shapes -/

theorem runR_iExp_success (s : Machine) (x y : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: y :: rest)
    (hgas : expCost y ≤ s.evm.gasLeft)
    (hlim : s.evm.stack.length ≤ 1024) :
    runR iExp s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := powMod x y U256_MOD :: rest
            gasLeft := s.evm.gasLeft - expCost y
            regularGasUsed := s.evm.regularGasUsed + expCost y
            pc := s.evm.pc + 1 } }) := by
  have hlen : rest.length ≠ 1024 := by
    rw [hstack] at hlim; simp at hlim; omega
  simp only [iExp, pcAdd, expCost, expBytes]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y rest (by simp)) ?_
  refine runR_bind_ok (runR_charge_gas _ _
    (by simpa [expCost, expBytes] using hgas)) ?_
  refine runR_bind_ok (runR_stackPush _ _ (by simpa using hlen)) ?_
  exact runR_modifyEvm _ _

theorem runR_iExp_underflow_nil (s : Machine) (hstack : s.evm.stack = []) :
    runR iExp s = .ok (.error .stackUnderflow, s) := by
  simp only [iExp]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_iExp_underflow_one (s : Machine) (x : U256)
    (hstack : s.evm.stack = [x]) :
    runR iExp s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with stack := [] } }) := by
  simp only [iExp]
  refine runR_bind_ok (runR_stackPop_cons s x [] hstack) ?_
  exact runR_bind_err (runR_stackPop_nil _ (by simp))

theorem runR_iExp_oog (s : Machine) (x y : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: y :: rest)
    (hgas : s.evm.gasLeft < expCost y) :
    runR iExp s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [iExp]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y rest (by simp)) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _
    (by simpa [expCost, expBytes] using hgas))

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for EXP. -/
theorem exp_dispatch (pc_in : Nat) (top : StackTop) (mem : EvmMemorySlice)
    (g : Nat) :
    Evm.Functions.execute_opcode (.EXP ()) pc_in top mem g =
      Evm.Functions.execute_exp top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
theorem runS_exp_body_ok (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: rest).reverse)
    (htop : top.toNat = (x :: y :: rest).length)
    (hy : WordWf y)
    (hgas : Evm.Functions.exp_gas y ≤ g) :
    runS (Evm.Functions.execute_exp top g) hs ss =
      .ok ((top - BitVec.ofNat 64 1, g - Evm.Functions.exp_gas y),
        { hs with stackFrames :=
            writeListAt l (top.toNat - 2) (powMod x y U256_MOD) :: frest })
        ss := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  have hbound := top.isLt
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hret2 : (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1).toNat
      = top.toNat - 2 := by
    rw [cursor_retreat_toNat _ (by rw [hret1]; omega), hret1]
    omega
  have hpfx' : l.take ((top.toNat - 1) + 1) = (x :: y :: rest).reverse := by
    rw [show top.toNat - 1 + 1 = top.toNat from by omega]; exact hpfx
  have hpfx1 : l.take (top.toNat - 1) = (y :: rest).reverse :=
    take_shrink l _ x _ hpfx' (by simp; omega)
  simp only [Evm.Functions.execute_exp]
  refine runS_bind_ok
    (runS_pop top hs ss l frest x (y :: rest) hframe hpfx htop) ?_
  refine runS_bind_ok
    (runS_pop _ hs ss l frest y rest hframe
      (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
  refine runS_bind_ok (runS_charge_ok g (exp_gas y) hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_alu_exp x y hy hs ss) ?_
  refine runS_bind_ok
    (runS_push_word _ (powMod x y U256_MOD) hs ss l frest
      hframe (by rw [hret2]; omega)) ?_
  have hc : top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1 + BitVec.ofNat 64 1
      = top - BitVec.ofNat 64 1 := by
    rw [BitVec.sub_add_cancel]
  rw [hc, hret2]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_exp_body_oog (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: rest).reverse)
    (htop : top.toNat = (x :: y :: rest).length)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < Evm.Functions.exp_gas y) :
    runS (Evm.Functions.execute_exp top g) hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  have hbound := top.isLt
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hpfx' : l.take ((top.toNat - 1) + 1) = (x :: y :: rest).reverse := by
    rw [show top.toNat - 1 + 1 = top.toNat from by omega]; exact hpfx
  have hpfx1 : l.take (top.toNat - 1) = (y :: rest).reverse :=
    take_shrink l _ x _ hpfx' (by simp; omega)
  simp only [Evm.Functions.execute_exp]
  refine runS_bind_ok
    (runS_pop top hs ss l frest x (y :: rest) hframe hpfx htop) ?_
  refine runS_bind_ok
    (runS_pop _ hs ss l frest y rest hframe
      (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
  refine runS_bind_ok
    (runS_charge_oog g (exp_gas y) hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_exp_success (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: rest).reverse)
    (htop : top.toNat = (x :: y :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hy : WordWf y)
    (hgas : Evm.Functions.exp_gas y ≤ g) :
    runS (Evm.Functions.execute (.EXP ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1, mem, g - Evm.Functions.exp_gas y),
        { hs with stackFrames :=
            writeListAt l (top.toNat - 2) (powMod x y U256_MOD) :: frest })
        ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.EXP ()) = pure (2, 1) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 1 hs ss (by simp at htop; omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, exp_dispatch]
  refine runS_bind_ok
    (runS_exp_body_ok top g hs ss l frest x y rest hframe hpfx htop hy
      hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_exp_underflow (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 2) :
    runS (Evm.Functions.execute (.EXP ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.EXP ()) = pure (2, 1) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 2 1 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_exp_oog (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: rest).reverse)
    (htop : top.toNat = (x :: y :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < Evm.Functions.exp_gas y) :
    runS (Evm.Functions.execute (.EXP ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1, mem, GAS_ZERO),
          hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.EXP ()) = pure (2, 1) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 1 hs ss (by simp at htop; omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, exp_dispatch]
  refine runS_bind_ok
    (runS_exp_body_oog top g hs ss l frest x y rest hframe hpfx htop prof sp
      msg hprof hsp hmsg hfork hgas) ?_
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **EXP, all reachable outcomes.** -/
theorem exp_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (BasePost mem) (runR iExp sRef)
      (runS (Evm.Functions.execute (.EXP ()) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_iExp_underflow_nil sRef hS,
      runS_execute_exp_underflow pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | [x] =>
    rw [hS] at hpfx htop
    rw [runR_iExp_underflow_one sRef x hS,
      runS_execute_exp_underflow pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | x :: y :: rest =>
    rw [hS] at hpfx htop hlim hwfS
    have hwx : WordWf x := hwfS x (by simp)
    have hwy : WordWf y := hwfS y (by simp)
    have hlim' : top.toNat ≤ 1024 := by simp at htop ⊢; simp at hlim; omega
    have hcost : Evm.Functions.exp_gas y = expCost y := exp_gas_eq y hwy
    by_cases hg : sRef.evm.gasLeft < expCost y
    · rw [runR_iExp_oog sRef x y rest hS hg,
        runS_execute_exp_oog pc_in top g mem hs ss l frest x y rest hframe
          hpfx htop hlim' prof sRef.evm.stateGasSpilled msg hprof hsp hmsg
          hfork (by rw [hlive, hcost]; exact hg)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
    · push Not at hg
      have hn : top.toNat = rest.length + 2 := by simpa using htop
      rw [runR_iExp_success sRef x y rest hS hg (by rw [hS]; exact hlim),
        runS_execute_exp_success pc_in top g mem hs ss l frest x y rest
          hframe hpfx htop hlim' hwy (by rw [hlive, hcost]; exact hg)]
      have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
        cursor_retreat_toNat top (by omega)
      refine StepResultRel.success ?_
      refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
        ⟨msg, hmsg⟩⟩, by simp [hpc], rfl⟩
      · have hpfx2 : l.take (top.toNat - 2) = rest.reverse := by
          have hview : l.take (top.toNat - 2) =
              (l.take top.toNat).take (top.toNat - 2) := by
            rw [List.take_take, Nat.min_eq_left (by omega)]
          rw [hview, hpfx]
          have hrl : rest.reverse.length = top.toNat - 2 := by simp; omega
          calc ((x :: y :: rest).reverse).take (top.toNat - 2)
              = (rest.reverse ++ [y, x]).take (top.toNat - 2) := by simp
            _ = rest.reverse := by
                rw [List.take_append_of_le_length (by omega), ← hrl,
                  List.take_length]
        refine ⟨⟨writeListAt l (top.toNat - 2)
            (powMod x y U256_MOD),
          frest, rfl, ?_, ?_⟩, ?_, ?_, ?_⟩
        · rw [hret1]
          have hstep : top.toNat - 1 = (top.toNat - 2) + 1 := by omega
          rw [hstep, take_writeListAt l (top.toNat - 2) _ (by omega)]
          rw [hpfx2]
          simp
        · rw [hret1, length_writeListAt]
          omega
        · rw [hret1]; simp; omega
        · simp; simp at hlim; omega
        · intro w hw
          rcases List.mem_cons.mp hw with hw | hw
          · subst hw
            exact powMod_wf x y hwy
          · exact hwfS w (by simp [hw])
      · exact ⟨by rw [hlive, hcost], hres, hsp⟩

end EvmSpecsVerify
