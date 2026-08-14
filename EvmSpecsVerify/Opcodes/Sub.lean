import EvmSpecsVerify.Opcodes.Shapes.Binop

/-!
# SUB

Derived through `binop_step_equiv` (`Opcodes/Shapes/Binop.lean`); per-opcode
content is the pure-function lemma and the wf bound. Reachable outcomes:
success / stack underflow / out-of-gas (overflow unreachable for 2-in/1-out).
-/

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

theorem alu_sub_eq (a b : Nat) (ha : WordWf a) (hb : WordWf b) :
    Evm.Functions.alu_sub a b = wrap256 (U256_MOD + a - b) := by
  show (if (b ≤ a : Bool) = true then a - b
      else ((2 : Int) ^ (256 : Nat)).toNat - 1 - (b - a) + 1)
      = (U256_MOD + a - b) % U256_MOD
  rw [two_pow_toNat]
  unfold WordWf at ha hb
  unfold U256_MOD
  split <;> rename_i h <;> simp at h <;> omega

open Evm.Functions in
/-- **SUB, all reachable outcomes.** -/
theorem sub_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iSub sRef)
      (runS (Evm.Functions.execute (.SUB ()) pc_in top mem g) hs ss) :=
  binop_step_equiv (.SUB ()) G_verylow alu_sub iSub GasCosts.OPCODE_SUB
    (fun x y => wrap256 (U256_MOD + x - y)) rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩
    (fun x y hx hy => alu_sub_eq x y hx hy) (fun _ _ _ _ => wrap256_wf _)
    sRef top g hs ss mem pc_in hrel hpc

end EvmSpecsVerify
