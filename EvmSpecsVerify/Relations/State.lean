import EvmSpecsVerify.Relations.Word
import EvmSpecsVerify.Relations.Stack
import EvmSpecsVerify.Relations.Gas
import EvmSpecsVerify.Relations.Outcome

/-!
# The state relation (ALU slice)

The minimal relation the arithmetic/stack opcode family needs: stack, gas,
status, and the register hypotheses that make the extraction's exceptional
path computable (`exc_halt` reads the profile, spill, and message
registers). Grows monotonically as more machinery enters scope — components
already have rows in `docs/comparison-matrix.md`.

Step-boundary convention (mismatch ledger MM-4): the extraction advances
`pc` past the opcode in `fetch`, *before* `execute`; SpecRef handlers
advance it themselves. The ALU-slice theorems therefore take
`pc_in = sRef.evm.pc + 1` and conclude the returned pc equals the SpecRef
post-state's pc — the pcs coincide at step boundaries.
-/

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef (Machine)
open Evm (HostState)
open Evm.Defs

/-- The Amsterdam-configuration hypothesis: the profile register holds a
profile whose fork is Amsterdam-or-later. (The comparison is fixed-fork;
this is threaded, never eliminated.) -/
def AmsterdamProfile (prof : ExecutionProfile) : Prop :=
  Evm.Functions.Amsterdam ≤ prof.1

/-- The ALU-slice state relation: SpecRef `Machine` vs the extraction's
live step arguments (`top`, `g`) + host state + register state. -/
structure StateRel (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : HostState) (ss : SeqState) : Prop where
  stack : StackRel sRef.evm.stack hs top
  gas : GasRel sRef.evm g ss
  /-- Both frames are running (the step theorems' precondition). -/
  runningRef : sRef.evm.running = true ∧ sRef.evm.error = none
  runningEvm : ss.regs.get? Register.frame_status =
    some (FrameStatus.Running ())
  /-- Register reads `exc_halt` needs, tied to the profile hypothesis. -/
  profile : ∃ prof, ss.regs.get? Register.k_execution_profile = some prof ∧
    AmsterdamProfile prof
  message : ∃ msg, ss.regs.get? Register.message = some msg

end EvmSpecsVerify
