# Opcode shapes

Shared **step-skeleton** proofs for SpecRef ↔ `Evm` handlers that differ only
in gas cost and a pure `alu_*` function. Per-opcode files under
[`../`](../) instantiate these theorems.

"Shape" is the coverage-matrix term
([`docs/opcode-coverage.md`](../../../docs/opcode-coverage.md)): how many
pops, when gas is charged, how the stack cursor moves, which failures are
reachable. It is not the ALU arithmetic, and it is not the Yellow-Paper
"ALU family" grouping of opcodes.

| Shape | Arity | Step theorem |
| --- | --- | --- |
| [`Binop.lean`](Binop.lean) | 2-in/1-out | [`binop_step_equiv`](Binop.lean#L293) |
| [`Unop.lean`](Unop.lean) | 1-in/1-out | [`unop_step_equiv`](Unop.lean#L230) |
| [`Ternop.lean`](Ternop.lean) | 3-in/1-out | [`ternop_step_equiv`](Ternop.lean#L308) |

Each harvested [`Opcodes/<Op>.lean`](../) file is `rfl` dispatch + `aluF = fSpec` + [`WordWf`](../../Relations/Word.lean#L20).

| File | SpecRef | `Evm` | Instantiations |
| --- | --- | --- | --- |
| [`Binop.lean`](Binop.lean) | `binOp cost f` | [`binopShape`](Binop.lean#L114) | [`ADD`](../Add.lean) [`MUL`](../Mul.lean) [`SUB`](../Sub.lean) [`DIV`](../Div.lean) [`SDIV`](../Sdiv.lean) [`MOD`](../Mod.lean) [`SMOD`](../Smod.lean) [`SIGNEXTEND`](../Signextend.lean) [`LT`](../Lt.lean) [`GT`](../Gt.lean) [`SLT`](../Slt.lean) [`SGT`](../Sgt.lean) [`EQ`](../Eq.lean) [`AND`](../And.lean) [`OR`](../Or.lean) [`XOR`](../Xor.lean) [`BYTE`](../Byte.lean) [`SHL`](../Shl.lean) [`SHR`](../Shr.lean) [`SAR`](../Sar.lean) |
| [`Unop.lean`](Unop.lean) | `unOp cost f` | [`unopShape`](Unop.lean#L78) | [`ISZERO`](../Iszero.lean) [`NOT`](../Not.lean) [`CLZ`](../Clz.lean) |
| [`Ternop.lean`](Ternop.lean) | [`ternOp`](Ternop.lean#L55) (named here; SpecRef has no combinator) | [`ternopShape`](Ternop.lean#L127) | [`ADDMOD`](../Addmod.lean); MULMOD residual |

[`Unop.lean`](Unop.lean) and [`Ternop.lean`](Ternop.lean) import
[`Binop.lean`](Binop.lean) for the shared success post-relation
[`AluPost`](Binop.lean#L40) (and [`wrap256_wf`](Binop.lean#L52) /
[`boolPush_wf`](Binop.lean#L55)). That coupling is real, not a leftover
path: all three close the same ALU observation boundary (live
[`StateRel`](../../Relations/State.lean#L36), MM-4 pc re-align, memory
pass-through).

## What a harvest supplies

Each opcode file is an application of `*_step_equiv` with:

1. `rfl` that the SpecRef handler is the shape combinator at the right cost
2. `rfl` `*Dispatch` — [`BinopDispatch`](Binop.lean#L206) /
   [`UnopDispatch`](Unop.lean#L143) /
   [`TernopDispatch`](Ternop.lean#L220)
   (`opcode_stack_effect` arity + `execute_opcode` reduces to `*Shape`)
3. a pure lemma `aluF = fSpec`
4. a [`WordWf`](../../Relations/Word.lean#L20) bound on the result

Do not extract a new shape file until a **second** opcode proves the
duplication is real. Do not put EXP here (pops first, data-dependent gas).
Future candidates (env pushers, DUP/SWAP, memory copies) belong in this
directory only if they share a byte-identical skeleton the way ADD/SUB do.

Package map: [`../../README.md`](../../README.md). Harvest ritual:
[`opcode-slice`](../../../.claude/skills/opcode-slice/SKILL.md).
