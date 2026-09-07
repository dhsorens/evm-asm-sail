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

/-! ## Frame-level gas effects

The three `Evm`-record updates SpecRef's gas primitives perform, named so
that a step theorem can compose them and project the fields afterwards
rather than carrying nested record literals. `charge_gas` and
`charge_state_gas` are the charges; `credit_state_gas_refund` is
`charge_state_gas`'s LIFO inverse. -/

open EvmAsm.Stateless.SpecRef in
/-- `charge_gas`. -/
def chargeEvm (e : Evm) (amount : Uint) : Evm :=
  { e with
      gasLeft := e.gasLeft - amount
      regularGasUsed := e.regularGasUsed + amount }

open EvmAsm.Stateless.SpecRef in
/-- `charge_state_gas`: reservoir first, then spill out of execution gas. -/
def chargeStateEvm (e : Evm) (amount : Uint) : Evm :=
  if amount ≤ e.stateGasLeft then
    { e with stateGasLeft := e.stateGasLeft - amount }
  else
    { e with
        stateGasLeft := 0
        gasLeft := e.gasLeft - (amount - e.stateGasLeft)
        stateGasSpilled :=
          e.stateGasSpilled + (amount - e.stateGasLeft) }

open EvmAsm.Stateless.SpecRef in
/-- `credit_state_gas_refund`, LIFO: execution gas up to the recorded
spill, then the reservoir. Guarded, since every caller so far applies it
conditionally. -/
def creditEvm (e : Evm) (cond : Bool) (amount : Uint) : Evm :=
  if cond then
    { e with
        gasLeft := e.gasLeft + min amount e.stateGasSpilled
        stateGasSpilled := e.stateGasSpilled - min amount e.stateGasSpilled
        stateGasLeft :=
          e.stateGasLeft + (amount - min amount e.stateGasSpilled) }
  else e

open EvmAsm.Stateless.SpecRef in
/-- `pcAdd 1`. -/
def pcBump (e : Evm) : Evm := { e with pc := e.pc + 1 }

end EvmSpecsVerify
