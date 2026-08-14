import EvmSpecsVerify.Opcodes.Shapes.Ternop

/-!
# MULMOD

Derived through `ternop_step_equiv` (`Opcodes/Shapes/Ternop.lean`);
per-opcode content is the pure-function lemma and the wf bound. Reachable
outcomes: success / stack underflow / out-of-gas (overflow unreachable for
3-in/1-out).
-/

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

theorem alu_mulmod_eq (a b n : Nat) :
    Evm.Functions.alu_mulmod a b n = if n == 0 then 0 else (a * b) % n := by
  show (if (n == 0) = true then ((0 : Int)).toNat
      else ((a : Int) * (b : Int)).toNat % n)
      = if (n == 0) = true then 0 else (a * b) % n
  rw [← Int.natCast_mul, Int.toNat_natCast]
  split <;> rfl

theorem mulmod_wf (a b n : Nat) (hn : WordWf n) :
    WordWf (if n == 0 then 0 else (a * b) % n) := by
  unfold WordWf at hn ⊢
  split
  · exact Nat.two_pow_pos 256
  · rename_i h
    have : n ≠ 0 := by simpa using h
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)

open Evm.Functions in
/-- **MULMOD, all reachable outcomes.** -/
theorem mulmod_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iMulmod sRef)
      (runS (Evm.Functions.execute (.MULMOD ()) pc_in top mem g) hs ss) :=
  ternop_step_equiv (.MULMOD ()) G_mid alu_mulmod iMulmod
    GasCosts.OPCODE_MULMOD (fun x y z => if z == 0 then 0 else (x * y) % z)
    rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩
    (fun x y z _ _ _ => alu_mulmod_eq x y z)
    (fun x y z _ _ hz => mulmod_wf x y z hz)
    sRef top g hs ss mem pc_in hrel hpc

end EvmSpecsVerify
