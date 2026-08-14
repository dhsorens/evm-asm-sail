import EvmSpecsVerify.Relations.Alu
import Batteries.Tactic.OpenPrivate

/-!
# Shared ALU harvest facts

Well-formedness lemmas every ALU opcode file uses when instantiating a
shape. The success Post is [`AluPost`](../../Relations/Alu.lean) (re-exported
by this import).

Shape files ([`Binop`](Binop.lean) / [`Unop`](Unop.lean) /
[`Ternop`](Ternop.lean)) import **this** module, never each other.
-/

open private boolPush from EvmAsm.Stateless.SpecRef.InstructionsCore

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef

/-- lean-sail's `HPow Int Int Int` is `x ^ n.toNat` (Sail.lean:860), so
Sail's `2 ^i 256` is definitionally `((2 : Int) ^ (256 : Nat)).toNat`. -/
theorem two_pow_toNat : ((2 : Int) ^ (256 : Nat)).toNat = 2 ^ 256 := by
  decide

theorem wrap256_wf (n : Nat) : WordWf (wrap256 n) :=
  Nat.mod_lt _ (Nat.two_pow_pos 256)

theorem boolPush_wf (b : Bool) : WordWf (boolPush b) := by
  unfold WordWf
  show (if b = true then 1 else 0) < 2 ^ 256
  split <;> decide

end EvmSpecsVerify
