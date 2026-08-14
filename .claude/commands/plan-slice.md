# Plan opcode / relation slices

You are a **planner** for this repo. Create a small set of atomic next work
items — do **not** implement them in this session unless the user explicitly
asks to continue into execution.

## Orient

1. Read `PROGRESS.md` (current milestone).
2. Read `docs/opcode-coverage.md` — prefer `unstated` rows in the active shape
   class (after ADD: ALU binops / unops, then `PROGRESS.md` M2 validators).
3. Skim `docs/comparison-matrix.md` and `docs/mismatches.md` for blockers.
4. Skim recent theorem files under `EvmAsmSail/Opcodes/` and `Relations/`.

## Sizing rules

Each work item must be **one logical concern**, ideally:

- ≤ ~2 primary Lean files touched for proofs
- Full `StepResultRel` for **one** opcode, **or** one representation/relation
  prerequisite that unblocks a named opcode
- Never span multiple `PROGRESS.md` milestones in one item

When in doubt, split. Harvesting a binop member is one item per opcode until a
shared shape lemma exists (`Opcodes/Shapes/Binop.lean`) — then "instantiate OP
via shape lemma + coverage row" is one item.

## Issue / task body template

For each item write:

```markdown
### Title
<opcode or relation slice — specific>

### Current state
- Coverage row status, relevant theorems, mismatch ids

### Deliverables
1. …
2. …
3. …   # max 3

### Context
- SpecRef handler / Evm execute symbol
- Shape class; MM-* to respect
- Files to read first

### Verification
- `lake build` green
- Named `StepResultRel` theorem (if opcode)
- `docs/opcode-coverage.md` (+ matrix if needed) updated
- `python3 scripts/refresh-proof-coverage-canvas.py`
```

## How many

Default: **1–3** items, ordered by dependency (relation before opcode when
needed). Prefer the next shape validators listed in `PROGRESS.md` M1/M2.

Do not plan work that edits upstream `evm-sail` / `EvmAsm` checkouts.

## Output

Present the planned items in chat (and write them to GitHub issues only if the
user asks). End with the single recommended **first** item to execute via the
`opcode-slice` skill.
