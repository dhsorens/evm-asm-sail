import Evm
import EvmAsm.Stateless.SpecRef

/-!
# Word relation

Both sides represent EVM words as `Nat` (SpecRef `U256 := Nat`, Types.lean:26;
`Evm` `word := Nat`, Defs.lean:51), so the relation is equality — carried as a
definition anyway so every use-site names its abstraction level, and so the
well-formedness bound (`< 2^256`, which neither side states type-level) has
one home.
-/

namespace EvmAsmSail

/-- A `Nat` is a well-formed EVM word. Neither side enforces this in types;
every SpecRef handler re-establishes it by wrapping, and the `Evm` ALU
maintains it (`u256`-reduction). The state relation carries it for every
stack entry. -/
def WordWf (x : Nat) : Prop := x < 2 ^ 256

/-- Word relation: representations coincide (both `Nat`). -/
def WordRel (x : EvmAsm.Stateless.SpecRef.U256) (w : Evm.Defs.word) : Prop :=
  x = w

theorem WordRel.refl (x : Nat) : WordRel x x := rfl

end EvmAsmSail
