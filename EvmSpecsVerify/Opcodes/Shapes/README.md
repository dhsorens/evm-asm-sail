# Opcode shapes

Shared **step-skeleton** proofs for SpecRef ↔ `Evm` handlers that differ only
in gas cost and a pure `alu_*` function. Per-opcode files under
[`../`](../) instantiate these theorems.

"Shape" is the coverage-matrix term
([`docs/opcode-coverage.md`](../../../docs/opcode-coverage.md)): how many
pops, when gas is charged, how the stack cursor moves, which failures are
reachable. It is not the ALU arithmetic, and it is not the Yellow-Paper
"ALU family" grouping of opcodes.

## Dependency rule

**A shape file never imports a sibling.** Shared facts go down:

```text
Relations/State.lean     StateRel          (pre)
Relations/Alu.lean       AluPost           (ALU success Post)
        │
        ▼
Opcodes/Shapes/Alu.lean  wrap256_wf, boolPush_wf, two_pow_toNat
        │
        ├──────────────┬──────────────┐
        ▼              ▼              ▼
     Binop.lean     Unop.lean     Ternop.lean
      (2,1)          (1,1)          (3,1)
```

Future slices copy this: a new Post in [`Relations/`](../../Relations/)
(`MemPost`, …), harvest helpers in `Shapes/<Slice>.lean` if needed, then
one arity file that imports **that** layer — never Binop/Unop/Ternop.

## ALU shapes

| Layer | File | Role |
| --- | --- | --- |
| Post | [`Relations/Alu.lean`](../../Relations/Alu.lean) | [`AluPost`](../../Relations/Alu.lean#L24) |
| Helpers | [`Alu.lean`](Alu.lean) | [`wrap256_wf`](Alu.lean#L26), [`boolPush_wf`](Alu.lean#L29), [`two_pow_toNat`](Alu.lean#L23) |
| (2,1) | [`Binop.lean`](Binop.lean) | [`binopShape`](Binop.lean#L85), [`binop_step_equiv`](Binop.lean#L264) |
| (1,1) | [`Unop.lean`](Unop.lean) | [`unopShape`](Unop.lean#L74), [`unop_step_equiv`](Unop.lean#L226) |
| (3,1) | [`Ternop.lean`](Ternop.lean) | [`ternopShape`](Ternop.lean#L122), [`ternop_step_equiv`](Ternop.lean#L303) |

Each harvested [`Opcodes/<Op>.lean`](../) file is `rfl` dispatch + `aluF = fSpec` + [`WordWf`](../../Relations/Word.lean#L20).

| File | SpecRef | `Evm` | Instantiations |
| --- | --- | --- | --- |
| [`Binop.lean`](Binop.lean) | `binOp cost f` | [`binopShape`](Binop.lean#L85) | [`ADD`](../Add.lean) [`MUL`](../Mul.lean) [`SUB`](../Sub.lean) [`DIV`](../Div.lean) [`SDIV`](../Sdiv.lean) [`MOD`](../Mod.lean) [`SMOD`](../Smod.lean) [`SIGNEXTEND`](../Signextend.lean) [`LT`](../Lt.lean) [`GT`](../Gt.lean) [`SLT`](../Slt.lean) [`SGT`](../Sgt.lean) [`EQ`](../Eq.lean) [`AND`](../And.lean) [`OR`](../Or.lean) [`XOR`](../Xor.lean) [`BYTE`](../Byte.lean) [`SHL`](../Shl.lean) [`SHR`](../Shr.lean) [`SAR`](../Sar.lean) |
| [`Unop.lean`](Unop.lean) | `unOp cost f` | [`unopShape`](Unop.lean#L74) | [`ISZERO`](../Iszero.lean) [`NOT`](../Not.lean) [`CLZ`](../Clz.lean) |
| [`Ternop.lean`](Ternop.lean) | [`ternOp`](Ternop.lean#L50) (named here; SpecRef has no combinator) | [`ternopShape`](Ternop.lean#L122) | [`ADDMOD`](../Addmod.lean); MULMOD residual |

## Shape-file template

Every `Shapes/Foo.lean` (and future Env/Memory/…):

1. Import [`Alu.lean`](Alu.lean) (or the relevant Post) plus
   [`EvmGas`](../../Representation/EvmGas.lean) /
   [`SpecRefLemmas`](../../Representation/SpecRefLemmas.lean). **Not** a sibling shape.
2. SpecRef combinator + `runR_*` for each reachable outcome.
3. `fooShape` — extracted handler body.
4. `FooDispatch` — `rfl` arity + `execute_opcode` reduces to `fooShape`.
5. `runS_fooShape_*` and `runS_execute_foo_*` per outcome.
6. `foo_step_equiv` : [`StateRel`](../../Relations/State.lean) →
   [`StepResultRel`](../../Relations/Outcome.lean) [`AluPost`](../../Relations/Alu.lean)
   (or that slice's Post).

Do not extract a new shape file until a **second** opcode proves the
duplication is real. Do not put EXP here (pops first, data-dependent gas).

Package map: [`../../README.md`](../../README.md). Harvest ritual:
[`opcode-slice`](../../../.claude/skills/opcode-slice/SKILL.md).
