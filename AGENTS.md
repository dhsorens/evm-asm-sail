# Agent conventions — evm-asm-sail

Standing rules for LLM agents working in this repository. Methodology for SpecRef
↔ `Evm` comparison lives in `.claude/skills/evm-spec-comparison/`; living coverage
docs live in `docs/`. Read those for design; this file is operational doctrine.

## Project facts

- Proofs live in `EvmAsmSail/`. Coverage matrices and the mismatch ledger live in
  `docs/`. Status and milestones live in `PROGRESS.md`.
- `EvmAsm` is a Lake git dependency; `evm` is a path dep into
  `extraction/evm-sail` (submodule). Do not edit either checkout except via
  upstream PRs.
- Primary bridge: SpecRef ↔ extracted `Evm`. See `README.md` for toolchain pins.

## Lean

- Build with `lake build`, not `lean` directly. Check diagnostics after every
  coherent step; do not continue past errors **or leave new warnings**. Treat
  `unused variable` / `unused simp argument` / deprecated tactics as build
  debt to clear before claiming the slice done — especially unused hypotheses,
  which usually mean the theorem is not tight (drop the hyp or use it).
- Never introduce an `axiom`. This includes converting a broken `theorem` into
  an `axiom`. Unfinished proofs use `sorry` (grep-able, warned). `axiom` is silent.
- No `sorry` merged to `main`; unfinished obligations belong in a registry or
  stay on a branch.
- No `native_decide` / `bv_decide` in anything we hope to upstream (evm-asm CI
  bans them).
- Prefer short verb-noun names (`add_step_equiv`, `StackRel`). Names with 5+
  defensive qualifiers are tech debt — rename them.
- Inspect both-side definitions before inventing types, relations, or theorem
  names. Do not guess shapes.

## Proof hygiene

Optimize for real SpecRef ↔ `Evm` assurance, not theorem count. Prefer, in order:
discovering a real semantic disagreement; showing an intended guarantee is false
or vacuous; recording a model/relation blind spot; proving a meaningful theorem
with an explicit trust base; clearly stating what remains unknown.

Keep four layers distinct: (1) upstream SpecRef / `Evm` behavior, (2) our Lean
bridge model and relations, (3) the stated observation / `StepResultRel`
property, (4) the Lean proof. A green proof of a weak or mis-aimed statement
is not progress.

- Success-only opcode theorems are not acceptable. Target full inductive
  `StepResultRel` (success and every reachable failure).
- Do not silently weaken a relation or add a vacuous precondition to make a
  proof go through. Record discovered disagreements in `docs/mismatches.md`
  **before** adjusting the proof. "I cannot prove this without assuming X" is
  better than silently assuming X — ledger it in `Assumptions.lean`.
- Prefer properties about reachable EVM states. Do not assume the invariant you
  claim to establish (e.g. `(hInv : Invariant s) → Safe s` with no reachability
  story).
- When a plan or issue asks for a theorem whose statement looks unsound or
  unsupported by current infrastructure: stop, write concrete evidence
  (counterexample, missing bridge, wrong observation boundary), and leave the
  work claimable for a revised statement. Do not invent `sorry`/`axiom` to bash
  through.
- Awkward or stuck proofs: first ask whether the property is false, the relation
  is wrong, or a mismatch is hiding — **then** try more tactics or `/prove`.
  Do not send unsound goals to Aleph.

## Coverage artifacts (source of truth)

| artifact | path |
| --- | --- |
| Comparison matrix | `docs/comparison-matrix.md` |
| Opcode coverage | `docs/opcode-coverage.md` |
| Mismatch ledger | `docs/mismatches.md` |
| Assumptions ledger | `EvmAsmSail/Assumptions.lean` |
| Coverage site source | `docs/index.html` (generated) |
| Refresh script | `scripts/refresh-proof-coverage-canvas.py` |

After any matrix status change (or end of a proof session that changes
statuses): update the markdown matrices, then run
`python3 scripts/refresh-proof-coverage-canvas.py`. Do not hand-edit
`docs/index.html` or the Cursor canvas DATA. Do not claim progress in chat that
is not reflected in the matrices.

## Style

- Don't add research-journal timestamps, "session completed" meta-commentary, or
  process history into design docs. Git history tracks that. Matrices and
  `PROGRESS.md` hold current state.
- Be concise in chat. Prefer theorem sketches, tables, and concrete
  decompositions over long prose.
- Label clearly: discovered facts / proposed architecture / assumptions / open
  questions.
- In `EvmAsmSail/**/README.md` (and other design markdown), every file path and
  named Lean definition is a clickable markdown link. Files:
  ``[`Foo.lean`](Foo.lean)``. Definitions: ``[`thm`](Foo.lean#L12)`` pointing at
  the `def`/`theorem` line. Exemplar: [`EvmAsmSail/Representation/README.md`](EvmAsmSail/Representation/README.md).
  Do not leave bare `` `Foo.lean` `` or unlinked theorem names in those docs.
  Code fences cannot hold links — lift file names out of fences into a table
  or list.
- In `docs/opcode-coverage.md`, every named theorem in the **status** column is
  a markdown link to its `theorem` line
  (``[`add_step_equiv`](../EvmAsmSail/Opcodes/Add.lean#L30)``). See
  `coverage-hygiene`.

## Skills and commands

Project skills live under `.claude/skills/`. Prefer them over reinventing
workflows:

| skill | when |
| --- | --- |
| `evm-spec-comparison` | designing / reviewing SpecRef ↔ `Evm` relations and theorems |
| `evm-bridge-gotchas` | proving lemmas, stuck on a simulation, about to add a `StateRel` precondition |
| `opcode-slice` | landing one opcode (or shape-class member) end-to-end |
| `coverage-hygiene` | updating matrices / regenerating the coverage site or canvas |
| `acquiring-skills` | creating or updating skills after real friction |

Commands under `.claude/commands/`: `/work` (default contribute entrypoint —
branch, slice, coverage hygiene, **open a PR**, then `/reflect`),
`/plan-slice`, `/reflect`, `/prove` (Aleph Prover for hard closed-form proofs).
`/work` does not commit slice work on `main`; include regenerated
`docs/index.html` in the PR (live site updates on merge).

When a theorem statement is sound but the proof is tactically hard after real
attempts: first check for a false property / bad relation / mismatch; only then
leave a compiling `sorry` and follow `.claude/commands/prove.md`
(`PROVER_API_KEY` required). Do not send unsound goals to Aleph; do not replace
a stuck proof with an `axiom`.

## Off-limits

- Do not modify upstream trees under `extraction/evm-sail` or Lake's `EvmAsm`
  package checkout as part of "making the proof work."
- Do not regenerate the Sail→Lean extraction here (`make extract-lean` is
  upstream's business).
