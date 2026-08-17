import EvmSpecsVerify.Opcodes.Shapes.Binop

/-!
# ADD

The archetype ALU binop, derived through `binop_step_equiv`
(`Opcodes/Shapes/Binop.lean`). Per-opcode content: the pure-function
equivalence `alu_add_eq_wrap256` and the wf bound; everything else is `rfl`.

Reachable outcomes: success / stack underflow / out-of-gas. Stack overflow is
unreachable (2-in/1-out; see `validate_stack`'s bound in the family lemma).
-/

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- ADD's pure function is SpecRef's: both wrap the `Nat` sum mod `2^256`. -/
theorem alu_add_eq_wrap256 (a b : Nat) :
    Evm.Functions.alu_add a b = wrap256 (a + b) := by
  -- lean-sail's `HPow Int Int Int` is `x ^ n.toNat` (Sail.lean:860), so the
  -- Sail modulus `2 ^i 256` is definitionally `((2 : Int) ^ (256 : Nat)).toNat`.
  have h : ((2 : Int) ^ (256 : Nat)).toNat = 2 ^ 256 := by decide
  show (a + b) % ((2 : Int) ^ (256 : Nat)).toNat = (a + b) % 2 ^ 256
  rw [h]

/-- **ADD, all reachable outcomes** (success / underflow / OOG; overflow
unreachable for 2-in/1-out). -/
theorem add_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (BasePost mem) (runR iAdd sRef)
      (runS (Evm.Functions.execute (.ADD ()) pc_in top mem g) hs ss) :=
  binop_step_equiv (.ADD ()) Evm.Functions.G_verylow Evm.Functions.alu_add
    iAdd GasCosts.OPCODE_ADD (fun x y => wrap256 (x + y))
    rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩
    (fun x y _ _ => alu_add_eq_wrap256 x y)
    (fun _ _ _ _ => Nat.mod_lt _ (Nat.two_pow_pos 256))
    sRef top g hs ss mem pc_in hrel hpc

end EvmSpecsVerify
