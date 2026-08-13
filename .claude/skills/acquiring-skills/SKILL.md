---
name: acquiring-skills
description: >
  Create or update Claude / Cursor project skills. Use when creating a new
  SKILL.md, updating an existing skill, consolidating repeated agent friction,
  or when /reflect or /meditate asks for skill changes.
---

# Writing skills

## Practice first

Before writing `SKILL.md`, perform the workflow manually (or finish the session
that hit the friction). Theoretical skills miss edge cases. Ground every rule
in something that already failed or succeeded in this repo.

## Location and layout

```text
.claude/skills/<skill-name>/
  SKILL.md           # required
  scripts/           # optional helpers
  templates/         # optional
```

Match existing skills under `.claude/skills/`. Standing doctrine belongs in
`AGENTS.md`, not in every skill.

## YAML frontmatter

```yaml
---
name: skill-name
description: >
  One-line trigger. Use when [specific situation]. Also use when [other
  situation].
---
```

- **name**: Match the directory name (lowercase, hyphens).
- **description**: This is the **trigger**, not a summary. Write conditions
  under which the agent should load the skill.

### Good vs bad descriptions

Good:

- "Use when proving SpecRef↔Evm lemmas or about to add a StateRel precondition."
- "Use when updating docs/opcode-coverage.md or regenerating the coverage site."

Bad:

- "A skill for Lean proofs" (when does it fire?)
- "Handles coverage stuff" (too broad)

## Body guidelines

- Keep skills procedural and concrete: commands, file paths, stop conditions.
- Do **not** restate living docs (`docs/*.md`, `PROGRESS.md`). Link them.
- Do **not** journal research history into skills. Git tracks that.
- Prefer short bullets and tables over essays.
- Cross-link sibling skills instead of duplicating (`evm-spec-comparison` vs
  `evm-bridge-gotchas` vs `opcode-slice`).

## Helper scripts

If a workflow repeats shell multi-step operations, add an executable helper
next to `SKILL.md` and reference it from the project root, e.g.
`.claude/skills/my-skill/helper.sh`.

## Iterate on friction

When a skill is wrong or incomplete mid-task:

1. Stop and fix the skill now — do not only work around it.
2. Commit the skill improvement with or right after the work that revealed it.

A used, updated skill beats a perfect one written once.

## Reflect filter

Only promote struggles that:

1. Caused real problems or user correction
2. Would be prevented by clearer prompting
3. Are likely to recur

Successful exploration does not need a skill entry. Avoid prompt bloat.
