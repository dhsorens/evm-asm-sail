import EvmSpecsVerify.Coverage.Registry
import EvmSpecsVerify.Opcodes.Add
import EvmSpecsVerify.Opcodes.Addmod
import EvmSpecsVerify.Opcodes.And
import EvmSpecsVerify.Opcodes.Byte
import EvmSpecsVerify.Opcodes.Clz
import EvmSpecsVerify.Opcodes.Div
import EvmSpecsVerify.Opcodes.Eq
import EvmSpecsVerify.Opcodes.Exp
import EvmSpecsVerify.Opcodes.Gt
import EvmSpecsVerify.Opcodes.Iszero
import EvmSpecsVerify.Opcodes.Jumpdest
import EvmSpecsVerify.Opcodes.Lt
import EvmSpecsVerify.Opcodes.Mod
import EvmSpecsVerify.Opcodes.Mul
import EvmSpecsVerify.Opcodes.Mulmod
import EvmSpecsVerify.Opcodes.Not
import EvmSpecsVerify.Opcodes.Or
import EvmSpecsVerify.Opcodes.Pop
import EvmSpecsVerify.Opcodes.Sar
import EvmSpecsVerify.Opcodes.Sdiv
import EvmSpecsVerify.Opcodes.Sgt
import EvmSpecsVerify.Opcodes.Shl
import EvmSpecsVerify.Opcodes.Shr
import EvmSpecsVerify.Opcodes.Signextend
import EvmSpecsVerify.Opcodes.Slt
import EvmSpecsVerify.Opcodes.Smod
import EvmSpecsVerify.Opcodes.Sub
import EvmSpecsVerify.Opcodes.Xor

/-!
# The exhaustive step theorem, first tranche

Every opcode theorem so far names its own AST constructor *and* its own
SpecRef handler, in a statement a human wrote. Nothing checks that the
pair is the right pair: `add_step_equiv` would be just as green if it
related `iMul` to `.ADD ()`, because the two sides are only ever brought
together by the theorem statement itself. `docs/opcode-coverage.md`
records the intended pairing in a table nothing reads.

This file makes the pairing an object. `baseHandler` is the table, and
`baseHandler_step_equiv` is one theorem, quantified over
`Evm.Defs.ast`, that discharges every opcode in it — so a wrong pair is
a failed `exact`, not a green theorem about the wrong opcode.

## What this does **not** close: MM-3

The theorem relates `runR (baseHandler op)` to `runS (execute op …)`.
It does **not** say that SpecRef's dispatch sends `op` to
`baseHandler op`. It cannot: `opImplementation` is a `partial def`
inside a `mutual` block, so it has no equation lemmas and
`opImplementation … 0x01 = iAdd` is unprovable (mismatch ledger MM-3).

So `baseHandler` is a *transcription* of `opImplementation`'s arms,
checked by reading, and that reading is the assumption. What changes is
that the assumption is now one reviewable table in one place instead of
28 separate statements — see `DispatchFidelity` in
`EvmSpecsVerify/Assumptions.lean`.

## The tranche

The 28 opcodes whose step theorem needs nothing beyond `StateRel` and
the MM-4 pc convention, and whose post-state is `BasePost`: the ALU core
(binops, unops, ternops, EXP), `POP` and `JUMPDEST`.

The other 53 `full` opcodes are excluded by *signature*, not by doubt —
each needs hypotheses this statement does not carry (register ties,
`MemGasSafe`, decode fidelity, the `*Agree` world-read assumptions) or
lands in a different post (`MemPost`, `ControlPost`, `StopPost`, …).
Widening the tranche means an opcode-indexed pre/post family, which is
the next installment rather than this one. `baseCount` and
`baseHandler_full` keep the two facts honest meanwhile: how many are in,
and that everything in is `full` in the registry.

## Why the catch-all is safe here

`baseHandler` closes with `| _ => none`, unlike
[`astStatus`](Registry.lean), which spells out all 88 constructors so a
new one fails to compile. The asymmetry is deliberate: this function's
catch-all defaults to **not claiming** an opcode, so a constructor added
upstream silently leaves the tranche rather than silently joining it.
Claiming requires writing the constructor down. The totality discipline
stays where it bites — `astStatus`, which `baseHandler_full` ties this
table to.
-/

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs
open EvmSpecsVerify.Coverage

/-- SpecRef's handler for each opcode in the base tranche, transcribed
from `opImplementation`'s dispatch arms
(`EvmAsm/Stateless/SpecRef/Interpreter.lean`). `none` means "not claimed
by this tranche", which covers both the opcodes proven elsewhere with
richer hypotheses and the six MM-3-blocked ones. -/
def baseHandler : ast → Option (EvmM Unit)
  | .ADD _ => some iAdd
  | .MUL _ => some iMul
  | .SUB _ => some iSub
  | .DIV _ => some iDiv
  | .SDIV _ => some iSdiv
  | .MOD _ => some iMod
  | .SMOD _ => some iSmod
  | .ADDMOD _ => some iAddmod
  | .MULMOD _ => some iMulmod
  | .EXP _ => some iExp
  | .SIGNEXTEND _ => some iSignextend
  | .LT _ => some iLt
  | .GT _ => some iGt
  | .SLT _ => some iSlt
  | .SGT _ => some iSgt
  | .EQ _ => some iEq
  | .ISZERO _ => some iIszero
  | .AND _ => some iAnd
  | .OR _ => some iOr
  | .XOR _ => some iXor
  | .NOT _ => some iNot
  | .BYTE _ => some iByte
  | .SHL _ => some iShl
  | .SHR _ => some iShr
  | .SAR _ => some iSar
  | .CLZ _ => some iClz
  | .POP _ => some iPop
  | .JUMPDEST _ => some iJumpdest
  | _ => none

/-- **Every opcode in the base tranche, in one theorem.** For any `op`
the table claims, SpecRef's handler for it and the extraction's
`execute` at that constructor agree on every reachable outcome.

The quantifier is the point: the 28 per-opcode theorems each assert a
pairing that only their own statement asserts, and this one derives all
28 from a single table, so a mistranscribed arm fails to elaborate.
What it still assumes is that the table *is* SpecRef's dispatch —
MM-3, ledgered as `DispatchFidelity`. -/
theorem baseHandler_step_equiv (op : ast) (h : EvmM Unit)
    (hop : baseHandler op = some h)
    (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (BasePost mem) (runR h sRef)
      (runS (Evm.Functions.execute op pc_in top mem g) hs ss) := by
  cases op <;> simp only [baseHandler, Option.some.injEq, reduceCtorEq] at hop
  all_goals subst hop
  · exact add_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact mul_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact sub_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact div_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact sdiv_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact mod_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact smod_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact addmod_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact mulmod_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact exp_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact signextend_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact lt_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact gt_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact slt_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact sgt_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact eq_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact iszero_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact and_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact or_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact xor_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact not_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact byte_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact shl_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact shr_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact sar_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact clz_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact pop_step_equiv sRef top g hs ss mem pc_in hrel hpc
  · exact jumpdest_step_equiv sRef top g hs ss mem pc_in hrel hpc

/-! ## What the tranche is, checked rather than asserted -/

/-- The constructors the table claims, drawn from the registry's verified
enumeration so the list cannot drift from the AST. -/
def baseOps : List ast := astCtors.filter fun a => (baseHandler a).isSome

/-- The tranche has 28 members. Computed from `astCtors`, not transcribed:
this is what stops the docstring's "28" from becoming a stale number, and
what makes `baseHandler_step_equiv` visibly non-vacuous. -/
theorem baseOps_length : baseOps.length = 28 := by rfl

/-- Nothing is claimed here that the coverage registry does not already
call `full`. The tranche is a *subset* of the proven opcodes, so this
direction is the one that matters: it cannot quietly promote a row. -/
theorem baseHandler_full (a : ast) (h : EvmM Unit) (hop : baseHandler a = some h) :
    astStatus a = .full := by
  cases a <;> simp only [baseHandler, Option.some.injEq, reduceCtorEq] at hop <;> rfl

end EvmSpecsVerify
