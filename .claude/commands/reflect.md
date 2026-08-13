# Self-reflection

Review the current conversation and identify where you **genuinely struggled**
and where additional prompting would have prevented the issue.

Distinguish:

- **Successful adaptation** — figured it out and finished effectively
- **Actual struggles** — repeated mistakes, user correction, or failed expectations

## Areas to consider

- Lean build / diagnostics / heartbeat / `open private` patterns in this repo
- SpecRef ↔ `Evm` observation boundary, relations, MM-* mismatches
- Coverage matrix honesty and refresh ritual
- Following `AGENTS.md` and project skills
- Tool usage and efficiency

## For each ACTUAL struggle

Only propose additions if:

1. The struggle caused real problems or required user intervention
2. Clearer prompting would have prevented it
3. The issue is likely to recur without guidance

Then:

1. Explain what happened and why it was problematic
2. Decide: project doctrine (`AGENTS.md`) vs skill (`.claude/skills/`) vs command
3. Propose a **specific, concise** addition — prefer extending
   `evm-bridge-gotchas` or `opcode-slice` over new skills when the topic fits

Read `acquiring-skills` before writing or heavily editing a skill.

## Recognize success

If you adapted cleanly:

- Acknowledge what went well
- Note that no additional prompting is needed
- **Do not** propose changes just to document everything

Avoid prompt bloat.
