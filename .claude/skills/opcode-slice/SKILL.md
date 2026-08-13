---
name: opcode-slice
description: >
  End-to-end ritual for landing one SpecRef ↔ Evm opcode (or one shape-family
  member) with full StepResultRel coverage. Use when proving a new opcode,
  harvesting a binop/unop family member from an existing pattern, or when the
  user asks to do the next vertical slice / next opcode.
---

# Opcode vertical slice

One coherent unit of work: a single opcode (or one harvested member of an
already-proven shape class) with full-outcome equivalence, matrix updates, and
a green build. Template: `EvmAsmSail/Opcodes/Add.lean` (`add_step_equiv`).

For relation design and observation-boundary questions, also read
`evm-spec-comparison`. For known traps, read `evm-bridge-gotchas`.

## Preconditions

- Know the **shape class** (binop / unop / ternop / stack / memory / control /
  …) from `docs/opcode-coverage.md`.
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

- Full inductive `StepResultRel` — not success-only.
- Thread `AmsterdamProfile` / register hypotheses as in existing `StateRel` /
  `StepRel` usage.
- Respect MM-1 (halt observation) and MM-4 (pc convention) for ALU-like ops;
  revisit both for JUMP/PUSH/memory.

### 4. Verify

```sh
lake build
```

Fix errors before touching docs. No new `axiom`s. No `sorry` destined for
`main`.

### 5. Coverage hygiene

1. Set the opcode row status to `full` (or honest intermediate: never leave
   success-only as the final claimed status).
2. Update comparison-matrix rows if this slice newly preserves a component.
3. Add or update mismatch entries if you discovered a new disagreement.
4. Run:

```sh
python3 scripts/refresh-proof-coverage-canvas.py
```

5. Update `PROGRESS.md` checkboxes / notes if the milestone list mentions this
   opcode or family.

See `coverage-hygiene` for the full artifact rules.

### 6. Stop conditions

- **Statement / infrastructure problem** (unsound goal, missing bridge,
  relation bug, upstream `partial`): stop. Write concrete evidence into
  `docs/mismatches.md` or `PROGRESS.md`. Do **not** weaken the theorem, and do
  **not** send it to Aleph — fix or restate first.
- **Proof is tactically hard** (statement looks right; `lake build` accepts the
  `sorry`; 3+ failed proof approaches): leave a compiling `sorry`, then
  dispatch that theorem via **`/prove`** — read and follow
  `.claude/commands/prove.md` (Aleph Prover). After Aleph applies a proof,
  re-run `lake build` and continue from step 5. Requires `PROVER_API_KEY`.
- **Slice too large** (new memory model + opcode + gas schedule): split —
  representation/relation PR first, opcode theorem second. Prefer
  `/plan-slice` sizing.

## Family harvest (binop / unop)

When ADD (or another archetype) is `full` and the next op shares the shape:

1. Extract shared structure only when the second instance proves the
   duplication is real (`Opcodes/BinopFamily.lean` direction in `PROGRESS.md`).
2. Each harvested opcode still gets its own coverage-row update to `full`.
3. Do not mark a whole family `full` from a generic lemma until every member
   is instantiated or an exhaustive registry says so.

## Done checklist

- [ ] Both-side run shapes for every reachable outcome
- [ ] Top-level `StepResultRel` theorem compiles
- [ ] `lake build` green
- [ ] `docs/opcode-coverage.md` updated
- [ ] Comparison matrix / mismatches updated if needed
- [ ] Coverage refresh script run
- [ ] No new axioms; assumptions threaded or ledgered
