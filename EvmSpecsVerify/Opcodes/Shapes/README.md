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
Relations/Base.lean       BasePost           (ALU success Post)
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
| Post | [`Relations/Base.lean`](../../Relations/Base.lean) | [`BasePost`](../../Relations/Base.lean#L24) |
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

## Pusher shapes (0-in/1-out, charge-first)

Two shapes, split by *where the pushed word comes from*. Both are
charge-first on the SpecRef side, so both inherit mismatch-ledger MM-5 on
double-fault states (full stack ∧ out of gas).

| File | SpecRef combinator | `Evm` side | Instantiations |
| --- | --- | --- | --- |
| [`EnvPusher.lean`](EnvPusher.lean) | [`pushConstOf`](EnvPusher.lean#L38) — reads the machine **before** charging | [`envPushShape`](EnvPusher.lean#L86) via [`EnvPushDispatch`](EnvPusher.lean#L98), value from a `k_env` field | [`COINBASE`/`TIMESTAMP`/`NUMBER`/`PREVRANDAO`/`GASLIMIT`/`CHAINID`/`BASEFEE`/`SLOTNUM`](../BlockEnv.lean) |
| [`LivePusher.lean`](LivePusher.lean) | [`livePushOf`](LivePusher.lean#L54) — reads the machine **after** charging ([`chargedEvm`](LivePusher.lean#L44)) | [`LivePushDispatch`](LivePusher.lean#L118) over the handler body, value from the live step state | [`PC`](../Pc.lean) [`GAS`](../Gas.lean); [`MSIZE`](../Msize.lean) reuses the SpecRef half only (its handler threads the memory slice) |

The read-order distinction is not cosmetic: GAS pushes `gasLeft - 2`
precisely because its read follows the charge. Step theorems:
[`envPush_step_equiv`](EnvPusher.lean#L203),
[`livePush_step_equiv`](LivePusher.lean#L197).

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
   [`StepResultRel`](../../Relations/Outcome.lean) [`BasePost`](../../Relations/Base.lean)
   (or that slice's Post).

Do not extract a new shape file until a **second** opcode proves the
duplication is real. Do not put EXP here (pops first, data-dependent gas).

Package map: [`../../README.md`](../../README.md). Harvest ritual:
[`opcode-slice`](../../../.claude/skills/opcode-slice/SKILL.md).
