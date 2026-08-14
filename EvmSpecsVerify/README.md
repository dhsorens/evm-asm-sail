# EvmSpecsVerify

Lean proofs that SpecRef (from **evm-asm**) and the Lean extraction of
**evm-sail** (`Evm`) agree on observable EVM behavior.

## Layout

| Directory | Role |
| --- | --- |
| [`Representation/`](Representation/README.md) | **How each side runs** — [`runR`](Representation/SpecRefLemmas.lean#L24) / [`runS`](Representation/EvmMonad.lean#L32), stack/gas/word characterizations |
| [`Relations/`](Relations/README.md) | **When the sides correspond** — [`StateRel`](Relations/State.lean#L36), [`StepResultRel`](Relations/Outcome.lean#L53), [`AluPost`](Relations/Alu.lean#L24), … |
| [`Opcodes/`](Opcodes/) | Per-opcode simulation theorems — start from [`Add.lean`](Opcodes/Add.lean) |
| [`Opcodes/Shapes/`](Opcodes/Shapes/README.md) | Shared step-skeleton proofs ([`binop_step_equiv`](Opcodes/Shapes/Binop.lean#L264), …) |
| [`Assumptions.lean`](Assumptions.lean) | Explicit trust base / deferred hypotheses |

```text
  SpecRef                         Evm extraction
     │                                  │
     └──────── Representation/ ─────────┘
                    │
                    ▼
              Relations/          ←  StateRel, AluPost, StepResultRel, …
                    │
                    ▼
               Opcodes/           ←  per-opcode StepResultRel
                 Shapes/          ←  Alu helpers; sibling binop / unop / ternop
```

**Representation** = facts about one model's definitions (rewritable run
shapes, BitVec↔Nat, host stack prefix, …) — see
[`Representation/README.md`](Representation/README.md).  
**Relations** = predicates between models (the comparison boundary) — see
[`Relations/README.md`](Relations/README.md).

Living coverage: [`docs/opcode-coverage.md`](../docs/opcode-coverage.md),
[`docs/comparison-matrix.md`](../docs/comparison-matrix.md). Standing rules:
[`AGENTS.md`](../AGENTS.md).
