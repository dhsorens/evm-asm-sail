import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# INVALID (`0xfe`) — and every other undefined byte

Neither side gives this byte a named handler.

**SpecRef.** `opImplementation` (Interpreter.lean:319-360) matches the
defined bytes, then falls through to a catch-all that tests the three
immediate-carrying ranges and otherwise throws:

```
| op =>
    if 0x5F ≤ op && op ≤ 0x7F then iPushN (op - 0x5F)
    else if 0x80 ≤ op && op ≤ 0x8F then iDupN (op - 0x80)
    else if 0x90 ≤ op && op ≤ 0x9F then iSwapN (op - 0x8F)
    else throw (.invalidOpcode op)
```

(The two offsets differ for a reason: `iDupN`'s position is 0-indexed
from the top, `iSwapN`'s names the position to swap *with*, so `SWAP1`
must arrive as `1`.)

`throw (.invalidOpcode op)` is a total expression: it names no member of
the `partial mutual` block it sits in, so it can be run and proven about
even though `opImplementation` itself cannot. That expression is what
`runR_invalid` targets, exactly as the other opcode slices target their
handler `def`. Which bytes reach it — the complement of the defined set
and of the three ranges above — is a fact about the dispatch match, and
the byte-to-handler link is unproven for **every** opcode (MM-3), not
specially for this one.

**The extraction.** The decoder's own catch-all,
`| _ => (pure (INVALID ()))` (Interpreter.lean:241), sends every byte
with no `ast` constructor to one node, so `.INVALID ()` stands for the
whole undefined range rather than for `0xfe` alone. `execute_invalid`
(Execute.lean:1837) is two lines:

```
def execute_invalid (g : Nat) : SailM Nat := do
  let consumed := (gas_sub g g)
  (exc_halt consumed InvalidOpcode)
```

`gas_sub g g` is `0` (`gas_sub_self`), and `exc_halt` (Machine.lean:152) discards its
gas argument anyway — it returns `GAS_ZERO` after refilling state gas and
writing `frame_status := Exceptional InvalidOpcode`. The argument is not
entirely dead on the way there: `refill_frame_state_gas`
(Machine.lean:127) adds it to the recorded spill, so passing `0` is what
keeps the refilled figure equal to the spill. `exc_halt` then drops that
figure, which is why `runS_exc_halt` needs no hypothesis about it.

**One outcome, and the hoisted check provably cannot fire.**
`opcode_stack_effect (.INVALID ()) = pure (0, 0)` (Execute.lean:2983), so
`execute`'s hoisted `validate_stack 0 0` passes on every state satisfying
the 1024 invariant. This is the one member of the halting family where
that is *provable* rather than a case split: MM-5's and MM-14's double
faults both arise from `validate_stack` firing ahead of a handler's own
guard, and here there is nothing for it to fire on. SpecRef reads no
state and charges nothing before throwing, so the two sides agree on the
single reachable outcome — `InvalidOpcode`, all gas consumed — through
the plain `halted` constructor.

The post relation is universally quantified: `StepResultRel`'s success
branch is unreachable here, so the pairing holds for any `Post`.
-/

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## SpecRef's side -/

/-- The undefined-byte arm of `opImplementation`'s catch-all. It reads no
state and charges nothing, so the machine is returned untouched. -/
theorem runR_invalid (op : Nat) (s : Machine) :
    runR (throw (.invalidOpcode op) : EvmM Unit) s =
      .ok (.error (.invalidOpcode op), s) :=
  runR_throw _ _

/-! ## The extraction's side -/

/-- `execute_invalid`'s `consumed`: nothing was afforded, so nothing is
subtracted. -/
theorem gas_sub_self (g : Nat) : Evm.Functions.gas_sub g g = 0 := by
  simp [Evm.Functions.gas_sub]

open Evm.Functions in
/-- The dispatch equation for the undefined byte. -/
theorem invalid_dispatch (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_opcode (.INVALID ()) pc_in top mem g =
      Evm.Functions.execute_invalid g >>= fun g' =>
        pure (pc_in, top, mem, g') := rfl

open Evm.Functions in
/-- `execute_invalid` is `exc_halt` on a zero charge. -/
theorem runS_execute_invalid_body (g : Nat) (hs : Evm.HostState)
    (ss : SeqState) (prof : ExecutionProfile) (sp : state_gas_spill)
    (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Evm.Functions.Amsterdam ≤ prof.1) :
    runS (Evm.Functions.execute_invalid g) hs ss =
      .ok (0, hs)
        { ss with regs := haltRegs ss msg .InvalidOpcode } := by
  simp only [Evm.Functions.execute_invalid, gas_sub_self]
  exact runS_exc_halt 0 .InvalidOpcode hs ss prof sp msg hprof hsp hmsg hfork

open Evm.Functions in
/-- **The extraction's only outcome for an undefined byte.** The hoisted
`validate_stack 0 0` passes under the 1024 invariant, so no state reaches
`execute` without reaching `exc_halt`. -/
theorem runS_execute_invalid (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Evm.Functions.Amsterdam ≤ prof.1)
    (hlim : top.toNat ≤ 1024) :
    runS (Evm.Functions.execute (.INVALID ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, 0), hs)
        { ss with regs := haltRegs ss msg .InvalidOpcode } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.INVALID ()) = pure (0, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 0 hs ss (by omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, invalid_dispatch]
  refine runS_bind_ok
    (runS_execute_invalid_body g hs ss prof sp msg hprof hsp hmsg hfork) ?_
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **Every undefined opcode byte, its one reachable outcome.** SpecRef's
`throw (.invalidOpcode op)` and the extraction's
`exc_halt 0 InvalidOpcode` are the same exceptional halt: same kind, all
gas consumed, no state read on either side.

`Post` is arbitrary because the success branch cannot fire. The byte is
quantified: the pairing is the same for `0xfe` and for every other byte
outside the defined set and the PUSH/DUP/SWAP ranges, since the
extraction's decoder maps them all to one node. Selecting this arm on
either side is the dispatch link, unproven for every opcode (MM-3). -/
theorem invalid_step_equiv
    {Post : Machine → EvmStep → Evm.HostState → SeqState → Prop}
    (op : Nat) (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss) :
    StepResultRel Post
      (runR (throw (.invalidOpcode op) : EvmM Unit) sRef)
      (runS (Evm.Functions.execute (.INVALID ()) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, _, _, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨_, htop, hlim, _⟩ := hstackR
  obtain ⟨_, _, hsp⟩ := hgasR
  rw [runR_invalid op sRef,
    runS_execute_invalid pc_in top g mem hs ss prof
      sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
  exact StepResultRel.halted (ErrorRel.invalidOpcode op)
    (haltRegs_frame_status ss msg .InvalidOpcode)

end EvmSpecsVerify
