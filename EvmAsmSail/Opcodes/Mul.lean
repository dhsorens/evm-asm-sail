import EvmAsmSail.Opcodes.BinopFamily

/-!
# MUL

Derived through `binop_step_equiv` (`Opcodes/BinopFamily.lean`); per-opcode
content is the pure-function lemma and the wf bound. Reachable outcomes:
success / stack underflow / out-of-gas (overflow unreachable for 2-in/1-out).
-/

set_option maxHeartbeats 1000000

namespace EvmAsmSail

open EvmAsm.Stateless.SpecRef
open Evm.Defs

theorem alu_mul_eq (a b : Nat) :
    Evm.Functions.alu_mul a b = wrap256 (a * b) := by
  show ((a : Int) * (b : Int)).toNat % ((2 : Int) ^ (256 : Nat)).toNat
      = (a * b) % 2 ^ 256
  rw [two_pow_toNat, ← Int.natCast_mul, Int.toNat_natCast]

open Evm.Functions in
/-- **MUL, all reachable outcomes.** -/
theorem mul_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iMul sRef)
      (runS (Evm.Functions.execute (.MUL ()) pc_in top mem g) hs ss) :=
  binop_step_equiv (.MUL ()) G_low alu_mul iMul GasCosts.OPCODE_MUL
    (fun x y => wrap256 (x * y)) rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩
    (fun x y _ _ => alu_mul_eq x y) (fun _ _ _ _ => wrap256_wf _)
    sRef top g hs ss mem pc_in hrel hpc

end EvmAsmSail
