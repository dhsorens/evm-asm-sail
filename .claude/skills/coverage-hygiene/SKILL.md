---
name: coverage-hygiene
description: >
  Keep SpecRef ↔ Evm living coverage artifacts honest. Use when updating proof
  status, editing docs/comparison-matrix.md or docs/opcode-coverage.md,
  regenerating the coverage site or Cursor canvas, claiming progress, or ending
  a proof session that changed theorem coverage.
---

# Coverage hygiene

Markdown matrices are the source of truth. Generated HTML and the Cursor canvas
are projections. Chat is not a coverage document.

## Artifacts

| role | path |
| --- | --- |
| Comparison matrix (edit) | `docs/comparison-matrix.md` |
| Opcode coverage (edit) | `docs/opcode-coverage.md` |
| Mismatch ledger (edit) | `docs/mismatches.md` |
| Assumptions ledger (edit) | `EvmAsmSail/Assumptions.lean` |
| Site + canvas DATA (generated) | `docs/index.html` (+ canvas if present) |
| Regenerator | `scripts/refresh-proof-coverage-canvas.py` |
| Live site | https://derekhsorensen.com/evm-asm-sail/ (from `docs/index.html` on `main`) |

## Ritual after status changes

1. Update the relevant markdown matrix **in place** (and mismatches /
   assumptions if the session discovered any).
2. Regenerate:

```sh
python3 scripts/refresh-proof-coverage-canvas.py
```

3. Commit generated `docs/index.html` together with the matrix edits when
   publishing; push to `main` to update the live site.
4. Keep the proof-coverage canvas open beside chat when doing slice work so the
   next opcode filter stays honest.

## Rules

- **Do not hand-edit** `docs/index.html` or canvas DATA blocks. Always
  regenerate.
- **Do not claim** `full` / `proven-*` in chat or `PROGRESS.md` unless the
  matrix row says so and the named theorem exists.
- Opcode statuses: `unstated` · `stated` · `success-proven` (not acceptable as
  final) · `full` · `n/a` (+ reason). Prefer `full` only for complete
  `StepResultRel`.
- Comparison-matrix statuses: `unrelated` · `related` · `proven-<scope>` ·
  `n/a`. Add rows rather than hiding components in prose.
- When markdown and canvas disagree, **markdown wins** — regenerate.

## Minimal status edit pattern

For an opcode that just landed `full`:

1. In `docs/opcode-coverage.md`, set the row status to
   `**full** (\`<theorem>\`, path — outcomes…)`.
2. Run the refresh script.
3. If the theorem newly ties a machine-frame component, bump that row in
   `docs/comparison-matrix.md` to `proven-<scope>` with the theorem name.

## End-of-session gate

Before ending a proof session that touched theorems:

- [ ] Matrices match reality
- [ ] Refresh script run if matrices changed
- [ ] Mismatches / assumptions updated if new disagreements or hypotheses appeared
- [ ] No progress claimed beyond the matrices
