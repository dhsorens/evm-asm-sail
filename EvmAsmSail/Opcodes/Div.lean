import EvmAsmSail.Opcodes.BinopFamily

/-!
# DIV

Derived through `binop_step_equiv` (`Opcodes/BinopFamily.lean`); per-opcode
content is the pure-function lemma and the wf bound. Reachable outcomes:
success / stack underflow / out-of-gas (overflow unreachable for 2-in/1-out).
-/

set_option maxHeartbeats 1000000

namespace EvmAsmSail

open EvmAsm.Stateless.SpecRef
open Evm.Defs

theorem alu_div_eq (a b : Nat) :
    Evm.Functions.alu_div a b = (if b == 0 then 0 else a / b) := by
  show (if (b == 0) = true then ((0 : Int)).toNat else a / b)
      = if b == 0 then 0 else a / b
  split <;> rfl

theorem div_wf (x y : Nat) (hx : WordWf x) :
    WordWf (if y == 0 then 0 else x / y) := by
  unfold WordWf at hx ⊢
  split
  · exact Nat.two_pow_pos 256
  · exact Nat.lt_of_le_of_lt (Nat.div_le_self x _) hx

open Evm.Functions in
/-- **DIV, all reachable outcomes.** -/
theorem div_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iDiv sRef)
      (runS (Evm.Functions.execute (.DIV ()) pc_in top mem g) hs ss) :=
  binop_step_equiv (.DIV ()) G_low alu_div iDiv GasCosts.OPCODE_DIV
    (fun x y => if y == 0 then 0 else x / y) rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩
    (fun x y _ _ => alu_div_eq x y) (fun x y hx _ => div_wf x y hx)
    sRef top g hs ss mem pc_in hrel hpc

end EvmAsmSail
