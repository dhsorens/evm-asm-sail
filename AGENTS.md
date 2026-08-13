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
  coherent step; do not continue past errors.
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

- Success-only opcode theorems are not acceptable. Target full inductive
  `StepResultRel` (success and every reachable failure).
- Do not silently weaken a relation or add a vacuous precondition to make a
  proof go through. Record discovered disagreements in `docs/mismatches.md`
  **before** adjusting the proof.
- When a plan or issue asks for a theorem whose statement looks unsound or
  unsupported by current infrastructure: stop, write concrete evidence
  (counterexample, missing bridge, wrong observation boundary), and leave the
  work claimable for a revised statement. Do not invent `sorry`/`axiom` to bash
  through.
- Awkward proofs: question the relation before adding tactics or assumptions.

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

## Skills and commands

Project skills live under `.claude/skills/`. Prefer them over reinventing
workflows:

| skill | when |
| --- | --- |
| `evm-spec-comparison` | designing / reviewing SpecRef ↔ `Evm` relations and theorems |
| `evm-bridge-gotchas` | proving lemmas, stuck on a simulation, about to add a `StateRel` precondition |
| `opcode-slice` | landing one opcode (or shape-family member) end-to-end |
| `coverage-hygiene` | updating matrices / regenerating the coverage site or canvas |
| `acquiring-skills` | creating or updating skills after real friction |

Commands under `.claude/commands/`: `/reflect`, `/plan-slice`.

## Off-limits

- Do not modify upstream trees under `extraction/evm-sail` or Lake's `EvmAsm`
  package checkout as part of "making the proof work."
- Do not regenerate the Sail→Lean extraction here (`make extract-lean` is
  upstream's business).
