---
name: evm-spec-comparison
description: >
  Guide rigorous formal comparison between evm-asm SpecRef and the evm-sail Lean
  extraction (package Evm). Use when designing, extending, reviewing, or proving
  semantic equivalence/refinement between SpecRef and Evm. Prioritize explicit
  state relations, complete semantic coverage, mechanically checkable theorem
  structure, and careful treatment of exceptional, environmental, gas, and
  representation behavior.
---

# EVM specification comparison

Related skills: `evm-bridge-gotchas` (failure modes), `opcode-slice` (one-opcode
ritual), `coverage-hygiene` (matrices / refresh). Standing rules: `AGENTS.md`.

## Objective

Compare **SpecRef** (evm-asm's internal Lean EVM semantics) and **`Evm`** (the
committed Lean extraction of evm-sail) as two formal semantic systems.

Do not treat this primarily as a source-code diff.

The core goal is a correspondence between states and observations, then proofs
that corresponding executions remain corresponding:

```lean
StateRel : SpecRef.State → Evm.State → Prop

theorem execution_equiv
    (hrel : StateRel sRef sEvm)
    (hvalid : ValidInitialState sRef sEvm) :
    ObservablyEquivalent (runSpecRef sRef) (runEvm sEvm)
```

Prefer **refinement** when strict structural equality would force irrelevant
implementation detail into the relation. Inspect existing datatypes before
naming or inventing replacements — do not guess shapes or theorem names.

### Repo facts

- Proofs live in `EvmAsmSail/`; living coverage docs in `docs/`.
- `EvmAsm` is a Lake git dep; `evm` is a path dep into the `extraction/evm-sail` submodule.
- Primary bridge in this repo: SpecRef ↔ `Evm`. RISC-V / macro representation is
  upstream of SpecRef unless you deliberately lower the comparison boundary.
- See `PROGRESS.md` and `README.md` for toolchain pins and milestone status.

## Living coverage artifacts

Keep these updated — they are the project's primary coverage documents, not skill
content:

| artifact | path |
| --- | --- |
| Master comparison matrix | [`docs/comparison-matrix.md`](../../../docs/comparison-matrix.md) — update in place |
| Opcode coverage matrix | [`docs/opcode-coverage.md`](../../../docs/opcode-coverage.md) — update in place |
| Proof coverage canvas | Cursor canvas `proof-coverage.canvas.tsx` (beside chat) — **view only**; markdown wins on conflict |
| Coverage site (source) | [`docs/index.html`](../../../docs/index.html) — generated; same DATA as the canvas; Pages `/docs` entry |
| Coverage site (live) | [https://derekhsorensen.com/evm-asm-sail/](https://derekhsorensen.com/evm-asm-sail/) — published from `docs/index.html` on `main` |

Every semantically relevant field or behavior should eventually have both-side
representations, a relation, invariants, proof coverage, and a status. Add rows rather
than hiding concepts in prose. Prefer generating opcode rows from the opcode
datatype when practical.

### Coverage canvas refresh ritual

After any edit to either matrix (or at the end of a proof session that changes
statuses):

1. Update the markdown matrices in place (source of truth).
2. Refresh canvas + site source from the matrices (one DATA snapshot for both):
   `python3 scripts/refresh-proof-coverage-canvas.py`
   (writes `docs/index.html` and, if present, the Cursor canvas DATA).
3. Commit and push `docs/index.html` on `main` so the live site updates.
4. Keep the proof-coverage canvas open beside chat so the next slice and filters
   stay honest. Expand opcode rows to inspect theorem links (`openFile` into
   `EvmAsmSail/…`); verify claims against the named `StepResultRel` theorem.

Do not invent progress in chat that is not reflected in the matrices. Do not edit
the canvas or `docs/index.html` by hand — always regenerate via the refresh script.

## Working principles

1. Define observational equivalence before proving opcode equivalence.
2. Separate representation proofs from semantic proofs.
3. Make all assumptions explicit.
4. Treat exceptional paths as first-class semantics.
5. Use finite datatypes and exhaustive pattern matching for mechanical coverage.
6. Do not silently restrict the relation until both implementations happen to agree.
7. Record every discovered mismatch, including deliberate differences.
8. Prefer small compositional lemmas feeding a small number of top-level simulation theorems.
9. Keep the living matrices current.
10. When adding an assumption, ask whether it is an EVM invariant or only avoids a hard case.
11. Treat proof attempts as bug-finding: a failed theorem, counterexample, or
    specification flaw can beat a completed proof of a weakened statement.
12. Keep layers distinct — upstream SpecRef/`Evm`, bridge relations, stated
    observation property, Lean proof — and audit 1–3 explicitly; Lean only
    certifies layer 4.

## Crown-jewel properties (this project)

Prioritize by semantic impact, not ease of proof. For SpecRef ↔ `Evm`, the
catastrophic failures to prevent in the bridge are roughly:

- observably different halt / error kinds (underflow, OOG, invalid jump, …);
- gas or PC disagreement at the observation boundary;
- stack / memory / storage content that should be related but is not;
- silently restricted `StateRel` that excludes reachable EVM states;
- fork / profile mix-ups (Amsterdam pin vs accidental Cancun/Prague);
- treating SpecRef `partial` dispatch as proved (MM-3);
- unverified gas-schedule disagreement on storage/account ops (MM-2).

For each, prefer a mismatch ledger entry or an honest "unknown" over a green
but vacuous theorem.

## What “the same” means

Before opcode proofs, fix the observation boundary. Typical observables: final
machine state, stack, memory (contents/size), storage, world state, gas, return
data, logs, creates, call outcomes, halt/revert/error, host requests, traces.

Do not require equality of SpecRef- or implementation-internal scratch unless it
is semantically observable. Decompose with explicit relations, e.g. `WordRel`,
`StackRel`, `MemoryRel`, `StorageRel`, `EnvRel`, `WorldRel`, `ResultRel`,
`ErrorRel`, `ObservationRel`, aggregated as `StateRel`.

## Proof layering

Organize Lean under a semantic decomposition (not a mirror of either upstream
tree), roughly:

```text
EvmAsmSail/
  Relations/ Representation/ SpecRef/ Evm/
  Opcodes/ Simulation/ Coverage/ TopLevel/
  Assumptions.lean   # ledger
  Mismatches.lean    # or docs/mismatches.md
```

| layer | focus |
| --- | --- |
| 1 Representation | encodings / well-formedness; no opcode cases unless unavoidable |
| 2 Semantic components | reusable ops (`add_word_equiv`, gas charge, jumpdest, …) |
| 3 Opcode theorems | full `StepResultRel` (success **and** failure), not success-only |
| 4 Step simulation | one SpecRef step ↔ one `Evm` step (or explicit stuttering if lowered) |
| 5 Execution | lift to `ResultRel` / `TraceRel`; gas often gives the measure |

Ideal opcode shape:

```lean
theorem add_equiv (h : StateRel sRef sEvm) :
    StepResultRel (runSpecRefOpcode .ADD sRef) (runEvmOpcode .ADD sEvm)
```

Critically examine every added precondition. Prefer inductive `StepResultRel`
covering success / revert / OOG / exceptional over “if both succeed, agree.”

## Symmetry vs refinement

Do not assume the final relation is symmetric. Full equivalence only where both
sides share an abstraction level. A failed equivalence proof is often the most
useful project output — treat it as a potential semantic mismatch first.

## Assumptions ledger

Keep one explicit ledger (Lean file or doc) of every assumption used by the final
theorem. Categorize: EVM validity, fork/config, representation invariant,
host/env, crypto primitive, external theorem, unproved implementation, deliberate
scope restriction.

For each: why required, who guarantees it, reachable violation?, part of intended
statement?, eliminable by proving?

## Mismatch ledger

When specs disagree, do not “fix the proof” first. Record area, both behaviors,
triggering state, expected EVM behavior + source, fork, reachability, severity,
likely cause, disposition (`evm-asm` / `evm-sail` / extraction / relation / fork /
intentional abstraction / unreachable / ambiguity / needs investigation).

## Claiming completeness

Never claim equivalence from “many opcode lemmas.” Prefer mechanically checkable
stories:

- **Opcodes** — `SupportedOpcode` (or support predicate) + exhaustive
  `all_supported_opcodes_equiv`.
- **State** — every observable field in `StateRel` (or explicitly linked).
- **Outcomes** — success, STOP, RETURN, REVERT, OOG, invalid op/jump, stack
  under/overflow, static violation, call/create failure, other exceptional halts.
- **Fork** — theorem identifies configuration; never Cancun-vs-Prague by accident.
- **Dependencies** — extraction trust, Keccak/precompile/host models, external
  arith; state relative completeness explicitly.

## Recommended work order

Narrow vertical slice; do not speculate the whole abstraction before one real
opcode proof:

1. Inspect both state models.
2. Fill [`docs/comparison-matrix.md`](../../../docs/comparison-matrix.md).
3. `WordRel` → `StackRel` → minimal `StateRel` for ADD.
4. Prove ADD (gas, PC, stack, exceptional paths); refactor what felt awkward.
5. Pure/stack-local ops → memory → control → env → storage/world → calls/creation.
6. Exhaustive opcode theorem → execution equivalence.

Early shape validators: `ADD`, `PUSHn`, `DUPn`, `MLOAD`, `JUMPI`, `SLOAD`, `RETURN`.
`ADD` alone is too weak.

## Review checklist

Before accepting an equivalence theorem:

- [ ] Success and failure correspond
- [ ] Gas, EVM PC, modified stack, memory expansion, return data, world rollback covered where relevant
- [ ] Fork-dependent semantics accounted for
- [ ] Implementation-only effects irrelevant or behind the abstraction
- [ ] Assumptions visible; `StateRel` not vacuously restrictive
- [ ] Reachable EVM states can meet stated preconditions
- [ ] Relation does not identify observably different states
- [ ] Opcode constructors mechanically accounted for; unsupported cases enumerated
- [ ] Proof difficulty was checked for semantic signal (bug / mismatch / bad
      statement) before proof-engineering or Aleph

## Interaction style

- Be concise. Prefer theorem sketches, tables, invariants, concrete decompositions.
- Inspect definitions before proposing replacements; do not guess names/shapes.
- Label clearly: discovered facts / proposed architecture / assumptions / open questions.
- Ask short targeted questions when they unblock a design decision (abstraction
  boundary of existing theorems, exact extracted state type, fork targets,
  exceptional-halt encoding, host/precompile model, gas in SpecRef specs,
  malformed-state quantification, intentional unobservables).
- Awkward proofs: question the relation before adding tactics or assumptions.

Ultimate target: for an explicitly stated EVM configuration, every supported
execution from related states has corresponding observable behavior in SpecRef
and `Evm`, with trusted assumptions, excluded cases, and intentional differences
explicitly accounted for — not merely “many matching lemmas.”
