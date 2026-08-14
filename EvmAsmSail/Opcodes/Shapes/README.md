# Opcode shapes

Shared **step-skeleton** proofs for SpecRef ↔ `Evm` handlers that differ only
in gas cost and a pure `alu_*` function. Per-opcode files under
[`../`](../) instantiate these theorems.

"Shape" is the coverage-matrix term (`docs/opcode-coverage.md`): how many
pops, when gas is charged, how the stack cursor moves, which failures are
reachable. It is not the ALU arithmetic, and it is not the Yellow-Paper
"ALU family" grouping of opcodes.

```text
  Shapes/Binop.lean     2-in/1-out   binop_step_equiv
  Shapes/Unop.lean      1-in/1-out   unop_step_equiv
  Shapes/Ternop.lean    3-in/1-out   ternop_step_equiv
           │
           ▼
  Opcodes/<Op>.lean     rfl dispatch + aluF = fSpec + WordWf
```

| File | SpecRef | `Evm` | Arity | Instantiations |
| --- | --- | --- | --- | --- |
| [`Binop.lean`](Binop.lean) | `binOp cost f` | `binopShape` / `execute_add` | (2, 1) | ADD MUL SUB DIV SDIV MOD SMOD SIGNEXTEND LT GT SLT SGT EQ AND OR XOR BYTE SHL SHR SAR |
| [`Unop.lean`](Unop.lean) | `unOp cost f` | `unopShape` / `execute_iszero` | (1, 1) | ISZERO NOT CLZ |
| [`Ternop.lean`](Ternop.lean) | `ternOp` (named here; SpecRef has no combinator) | `ternopShape` / `execute_addmod` | (3, 1) | ADDMOD; MULMOD residual |

Unop and ternop import binop for the shared success post-relation `AluPost`
(and `wrap256_wf` / `boolPush_wf`). That coupling is real, not a leftover
path: all three close the same ALU observation boundary (live `StateRel`,
MM-4 pc re-align, memory pass-through).

## What a harvest supplies

Each opcode file is an application of `*_step_equiv` with:

1. `rfl` that the SpecRef handler is the shape combinator at the right cost
2. `rfl` `*Dispatch` (`opcode_stack_effect` arity + `execute_opcode` reduces
   to `*Shape`)
3. a pure lemma `aluF = fSpec`
4. a `WordWf` bound on the result

Do not extract a new shape file until a **second** opcode proves the
duplication is real. Do not put EXP here (pops first, data-dependent gas).
Future candidates (env pushers, DUP/SWAP, memory copies) belong in this
directory only if they share a byte-identical skeleton the way ADD/SUB do.

Package map: [`../../README.md`](../../README.md). Harvest ritual:
[`opcode-slice`](../../../.claude/skills/opcode-slice/SKILL.md).
