# EvmAsmSail

Lean proofs that SpecRef (from **evm-asm**) and the Lean extraction of
**evm-sail** (`Evm`) agree on observable EVM behavior.

## Layout

| Directory | Role |
| --- | --- |
| [`Representation/`](Representation/) | **How each side runs** — `runR` / `runS`, stack/gas/word characterizations |
| [`Relations/`](Relations/) | **When the sides correspond** — `StateRel`, `StepResultRel`, … |
| `Opcodes/` | Per-opcode (or family) simulation theorems |
| `Assumptions.lean` | Explicit trust base / deferred hypotheses |

```text
  SpecRef                         Evm extraction
     │                                  │
     └──────── Representation/ ─────────┘
                    │
                    ▼
              Relations/          ←  StateRel, StepResultRel, …
                    │
                    ▼
               Opcodes/           ←  full StepResultRel theorems
```

**Representation** = facts about one model's definitions (rewritable run
shapes, BitVec↔Nat, host stack prefix, …).  
**Relations** = predicates between models (the comparison boundary).

Read those two READMEs before extending the bridge. Living coverage:
[`docs/opcode-coverage.md`](../docs/opcode-coverage.md),
[`docs/comparison-matrix.md`](../docs/comparison-matrix.md). Standing rules:
[`AGENTS.md`](../AGENTS.md).
