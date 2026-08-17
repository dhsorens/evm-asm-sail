import EvmSpecsVerify.Relations.State
import EvmSpecsVerify.Relations.Outcome

/-!
# Base success post-relation

The `Post` argument of [`StepResultRel`](Outcome.lean) for every opcode
whose observable footprint is stack + gas + pc with memory passed through
untouched — the ALU shapes (binop / unop / ternop), the stack family
(POP/PUSH/DUP), and the env pushers/readers. Formerly named `AluPost`,
before the footprint outgrew the family.

Opcodes that relate more get their own Post built on top (`JumpiPost`,
`MemPost`, `ReturnPost`, `SloadPost`, `BalancePost`), never extra fields
on this one. Arity skeletons live in
[`Opcodes/Shapes/`](../Opcodes/Shapes/README.md) and import this file.
-/

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef (Machine)
open Evm (HostState)
open Evm.Defs

/-- The base success post: [`StateRel`](State.lean) holds on the returned
live values, the returned pc is the SpecRef post-pc (step boundaries
re-align; mismatch ledger MM-4), and memory is a pass-through. -/
def BasePost (mem : EvmMemorySlice) (sR' : Machine) (step : EvmStep)
    (hs' : HostState) (ss' : SeqState) : Prop :=
  StateRel sR' step.2.1 step.2.2.2 hs' ss' ∧
  step.1 = sR'.evm.pc ∧ step.2.2.1 = mem

end EvmSpecsVerify
