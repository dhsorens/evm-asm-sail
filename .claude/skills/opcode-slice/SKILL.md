---
name: opcode-slice
description: >
  End-to-end ritual for landing one SpecRef ↔ Evm opcode (or one shape-class
  member) with full StepResultRel coverage. Use when proving a new opcode,
  harvesting a binop/unop/ternop member from an existing pattern, or when the
  user asks to do the next vertical slice / next opcode.
---

# Opcode vertical slice

One coherent unit of work: a single opcode (or one harvested member of an
already-proven shape class) with full-outcome equivalence, matrix updates, and
a green build. Template: `EvmSpecsVerify/Opcodes/Add.lean` (`add_step_equiv`).

For relation design and observation-boundary questions, also read
`evm-spec-comparison`. For known traps, read `evm-bridge-gotchas`.

## Preconditions

- Know the **shape class** (binop / unop / ternop / stack / memory / control /
  …) from `docs/opcode-coverage.md`. ALU skeletons live in `Opcodes/Shapes/`
  (siblings: they import `Shapes/Alu.lean`, never each other).
- Prefer harvesting within a proven class (e.g. next ALU binop after ADD) over
  inventing a new relation shape mid-slice.
- If the slice needs a new observable component in `StateRel`, update
  `docs/comparison-matrix.md` and define the relation **before** the opcode
  theorem.

## Ritual

### 1. Orient

1. Read the SpecRef handler and the `Evm` `execute_*` (or shared helper) —
   inspect, do not guess names.
2. Read the opcode row in `docs/opcode-coverage.md` and any related mismatch
   entries (`MM-1`, `MM-4`, …).
3. Skim `Assumptions.lean` for fork / scope hypotheses you must thread.
4. List reachable outcomes (success + failures). Note unreachable ones
   (e.g. overflow for 2-in/1-out) for the docstring / registry.

### 2. Run-shape lemmas (both sides)

Prove concrete `runR_*` / `runS_*` (or equivalent) lemmas for each reachable
outcome under raw hypotheses, following `Opcodes/Add.lean`:

- success
- each underflow / overflow / OOG / … case that can fire

Reuse `Representation/` lemmas. Keep each lemma small and compiling.

### 3. Step equivalence

State a single top-level theorem of the form:

```lean
theorem <op>_step_equiv
    (h : StateRel …) (-- plus live pc/top/mem/g threading as in ADD)
    : StepResultRel (runR iOp sRef) (runS (execute (.OP …) …) …)
```

Requirements:

- **Name any structure-update field value that won't fit on one physical
  line as a `def` BEFORE writing the statement** (`returnedStatus`,
  `stoppedStatus`, `wsAfterMark`, `cdWord`). Multi-line values inside
  `{ x with field := … }` do not parse (see evm-bridge-gotchas), and this
  keeps getting rediscovered one parse error at a time — pre-empt it at
  drafting time.
- Full inductive `StepResultRel` — not success-only.
- Thread `AmsterdamProfile` / register hypotheses as in existing `StateRel` /
  `StepRel` usage.
- Respect MM-1 (halt observation) and MM-4 (pc convention) for ALU-like ops;
  revisit both for JUMP/PUSH/memory.

### 4. Verify

```sh
lake build
```

Fix errors **and warnings** in touched files before docs. Unused hypotheses /
simp args mean the statement or proof is loose — tighten (drop unused
assumptions) rather than `set_option linter… false`. No new `axiom`s. No
`sorry` destined for `main`.

### 5. Coverage hygiene

1. Set the opcode row status to `full` (or honest intermediate: never leave
   success-only as the final claimed status). The theorem name in the status
   column must be a markdown link to the `theorem` line — see
   `coverage-hygiene`.
2. Update comparison-matrix rows if this slice newly preserves a component.
3. Add or update mismatch entries if you discovered a new disagreement.
4. Run:

```sh
python3 scripts/refresh-proof-coverage-canvas.py
```

5. Update `PROGRESS.md` checkboxes / notes if the milestone list mentions this
   opcode or shape class.

See `coverage-hygiene` for the full artifact rules.

### 6. Stop conditions

- **Statement / infrastructure problem** (unsound goal, missing bridge,
  relation bug, upstream `partial`): stop. Write concrete evidence into
  `docs/mismatches.md` or `PROGRESS.md`. Do **not** weaken the theorem, and do
  **not** send it to Aleph — fix or restate first.
- **Stuck after real attempts**: before more tactics or Aleph, run a short
  falsification pass — could the property be false on a reachable state? is
  `StateRel` / the observation boundary wrong? is this MM-* material? If yes,
  record and stop. If the statement still looks sound and `lake build` accepts
  a compiling `sorry`, then dispatch via **`/prove`** (read
  `.claude/commands/prove.md`). After Aleph applies a proof, re-run
  `lake build` and continue from step 5. Requires `PROVER_API_KEY`.
- **Slice too large** (new memory model + opcode + gas schedule): split —
  representation/relation PR first, opcode theorem second. Prefer
  `/plan-slice` sizing.

## Shape harvest (binop / unop / ternop)

When ADD (or another archetype) is `full` and the next op shares the shape:

1. Extract shared structure only when the second instance proves the
   duplication is real ([`Opcodes/Shapes/`](../../../EvmSpecsVerify/Opcodes/Shapes/README.md);
   new files import `Shapes/Alu.lean`, not a sibling arity).
2. Each harvested opcode still gets its own coverage-row update to `full`.
3. Do not mark a whole shape class `full` from a generic lemma until every
   member is instantiated or an exhaustive registry says so.

## Done checklist

- [ ] Both-side run shapes for every reachable outcome
- [ ] Top-level `StepResultRel` theorem compiles
- [ ] `lake build` green **without warnings** in touched modules
- [ ] `docs/opcode-coverage.md` updated
- [ ] Comparison matrix / mismatches updated if needed
- [ ] Coverage refresh script run
- [ ] No new axioms; assumptions threaded or ledgered
