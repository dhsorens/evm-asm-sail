import EvmSpecsVerify.Representation.EvmMonad
import EvmAsm.Stateless.SpecRef

/-!
# Gas relation

Both sides carry Amsterdam's two-dimensional gas. SpecRef holds all three
quantities in the frame (`gasLeft`, `stateGasLeft`, `stateGasSpilled`,
Vm.lean:192-207). The extraction threads the **live execution gas** as the
`g` argument of `execute` (state-passing convention; the `gas_remaining`
register is authoritative only at frame boundaries) and keeps the state-gas
reservoir/spill in registers.
-/

namespace EvmSpecsVerify

open Evm (HostState)

/-- The extraction's gas state (live argument + registers) represents
SpecRef's frame gas. `g` is the carried live gas of the current step. -/
structure GasRel (evmRef : EvmAsm.Stateless.SpecRef.Evm) (g : Nat)
    (ss : SeqState) : Prop where
  live : g = evmRef.gasLeft
  reservoir : ss.regs.get? Evm.Defs.Register.state_gas_remaining =
    some evmRef.stateGasLeft
  spilled : ss.regs.get? Evm.Defs.Register.state_gas_spilled =
    some evmRef.stateGasSpilled

end EvmSpecsVerify
