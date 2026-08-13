---
description: Submit a Lean theorem to Aleph Prover and apply the proof
allowed-tools: Bash(uvx:*)
---

# Aleph Prover Skill

Submit a Lean theorem to the Aleph Prover API using the `alephprover` CLI.

## Arguments

The user provides the theorem name and file path. Examples:
- `/prove mul_left_cancel in Mathlib/Algebra/Group/Basic.lean`
- `/prove my_theorem in MyProject/Basic.lean with hint: try induction on n`

Parse the user's message to extract:
- `theorem_name` (required): the theorem to prove
- `file_path` (required): path to the Lean file containing the theorem
- `hints` (optional): any hints or guidance after "with hint:" or "hint:"

If the theorem name or file path is unclear, ask the user to clarify before proceeding.

## Configuration

**Required:** `PROVER_API_KEY` environment variable (starts with `sk-aleph-`)

**Optional:** `PROVER_API_URL` environment variable (defaults to `https://alephprover.logicalintelligence.com`)

## Run

```bash
uvx alephprover prove <file_path> <theorem_name> [--hints "..."] [--time-budget <minutes>] [--cost-budget <credits>] [-v]
```

Use `timeout=3700000` (just over 60 min) for the command since polling can take up to 60 minutes.

## Fallback: --all-files

If the proof attempt fails with a build error (e.g. missing imports, unresolved dependencies, or files not found during compilation), retry with `--all-files`:

```bash
uvx alephprover prove <file_path> <theorem_name> --all-files [--hints "..."] [--time-budget <minutes>] [--cost-budget <credits>] [-v]
```

This includes all project files (excluding `.git/`, `.lake/`, and `.gitignore` patterns) instead of only Lake-discovered source paths. Use this when the default archive is missing files needed for the build.

## After completion

1. Show whether the proof was applied successfully
2. Show which files were modified (`git diff --stat`)
3. Read the modified theorem from the file and show the proof to the user

## Other commands

The CLI also supports these commands. Use them when the user asks to check status, continue a previous request, etc.

```bash
# Check request status and stages
uvx alephprover status <request_id>

# List recent proof requests
uvx alephprover list [--search "..."] [--limit N]

# Continue a partial/cancelled request with new budget
uvx alephprover continue <request_id> [--time-budget <minutes>] [--cost-budget <credits>] [--hints "additional hints"]

# Cancel a running request
uvx alephprover cancel <request_id>

# Download results or specific artifacts
uvx alephprover download <request_id> [--artifact <id>] [-o output.zip]
```

Examples of user requests that should use these commands:
- "continue that proof request" → `uvx alephprover continue <id>`
- "what's the status of my proof?" → `uvx alephprover status <id>`
- "list my recent proofs" → `uvx alephprover list`
- "cancel that request" → `uvx alephprover cancel <id>`
