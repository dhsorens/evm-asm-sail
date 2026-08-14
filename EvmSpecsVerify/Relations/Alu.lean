import EvmSpecsVerify.Relations.State
import EvmSpecsVerify.Relations.Outcome

/-!
# ALU success post-relation

The `Post` argument of [`StepResultRel`](Outcome.lean) for constant-gas ALU
shapes (binop / unop / ternop). Not an arity skeleton — those live in
[`Opcodes/Shapes/`](../Opcodes/Shapes/README.md) and import this file.

Future non-ALU slices get their own Post here (`MemPost`, …), not a field
on this one.
-/

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef (Machine)
open Evm (HostState)
open Evm.Defs

/-- Success post-relation for the ALU slice: [`StateRel`](State.lean) holds
on the returned live values, the returned pc is the SpecRef post-pc (step
boundaries re-align; mismatch ledger MM-4), and memory is a pass-through. -/
def AluPost (mem : EvmMemorySlice) (sR' : Machine) (step : EvmStep)
    (hs' : HostState) (ss' : SeqState) : Prop :=
  StateRel sR' step.2.1 step.2.2.2 hs' ss' ∧
  step.1 = sR'.evm.pc ∧ step.2.2.1 = mem

end EvmSpecsVerify
