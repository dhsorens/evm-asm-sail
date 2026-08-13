---
name: evm-bridge-gotchas
description: >
  Hard-won SpecRef ↔ Evm bridge pitfalls. Use when proving or debugging
  SpecRef↔Evm simulation lemmas, failing StepResultRel goals, stuck stack/gas/pc
  relations, SailM/HostState run shapes, or before adding a precondition to
  StateRel / StackRel / GasRel. Also use when an opcode proof seems to require
  silently restricting the relation.
---

# SpecRef ↔ Evm bridge gotchas

Living document of failure modes discovered while proving SpecRef ↔ extracted
`Evm` equivalence. Add an entry when a session burns time on a recurring trap.
Methodology stays in `evm-spec-comparison`; coverage status stays in `docs/`.

## Words and arithmetic

- **Both sides use `Nat` for EVM words** (SpecRef `U256`, `Evm` `word`). Pure
  arithmetic does not need a `BitVec` bridge. Bitwise / shift ops on the `Evm`
  side still involve `BitVec` at the API edge — relate through `WordRel` /
  wrapping lemmas, do not invent a second word type.
- SpecRef re-establishes `< 2^256` by wrapping (`wrap256`); the extraction uses
  `u256` reduction. `StackRel.wf` is an EVM invariant, not a free lunch — do not
  drop it from hypotheses without a plan to prove preservation.

- **`omega` fails on goals typed at `U256`/`word` abbrevs and on `Int` powers.**
  Trigger: an equality whose `Eq` lives at `U256` (SpecRef) or `word` (`Evm`) —
  omega matches types syntactically and won't see the `Nat` underneath; likewise
  `(2 : Int) ^ 256` in a hypothesis or goal is opaque to omega (Nat powers are
  fine). Wrong move: fight the goal with `unfold`/`simp` roulette. Right move:
  `exact (by omega : <same statement ascribed at Nat>)` for the abbrev case;
  rewrite `Int` powers to numerals via `show (2:Int)^(256:Nat) = <numeral> from
  by decide` first (see `Representation/SignedWord.lean`, `fromSigned_eq`).

## Stack geometry

- SpecRef stack is **head = top** (`List U256`). Host stack is **bottom-indexed**
  with a `StackTop` cursor; popped entries linger above the cursor as scratch.
  Faithful relation is **prefix-up-to-cursor = SpecRef.reverse**, plus
  `top.toNat = S.length` and the 1024 limit. See `Relations/Stack.lean` and
  `Representation/EvmStack.lean`.
- Do not equate full host frame lists with SpecRef stacks. Cursor-prefix only.
- Private host helpers (`writeListAt`, …) are characterized via
  `open private` + run-shape lemmas — inspect existing representation lemmas
  before rewriting stack ops ad hoc.

## Gas and exceptional halt (MM-1)

- SpecRef ALU `binOp`: pop ×2 → charge → push. On OOG the machine may already
  have lost operands.
- `Evm`: `validate_stack` then charge-before-pop. On failure `exc_halt` zeroes
  gas, refills state gas, sets `frame_status := Exceptional k`; operands may
  still sit on the host stack.
- **Observation boundary**: halted-frame stack/pc/memory are not observable.
  Relate halt **kind** + zeroed gas via `StepResultRel` / `ErrorRel`, not
  full post-state equality on failure. ADD already proves this shape
  (`add_step_equiv`).
- Do not "fix" MM-1 by forcing identical intermediate stacks. Record or cite
  the mismatch ledger.

## PC convention (MM-4)

- SpecRef handlers advance `pc` themselves (`pcAdd`).
- `Evm` `fetch` advances past the opcode before `execute`; ALU handlers return
  `pc_in` unchanged.
- Statement shape for ALU: hypothesis `pc_in = sRef.evm.pc + 1`, conclusion
  ties returned pc to SpecRef post-pc (`AluPost`-style). JUMP / JUMPI / PUSH will
  need extra care — do not copy the ALU pc hypothesis blindly.

## Monads and run shapes

- SpecRef: `EvmM` / `runR` — inner `.error e` is exceptional halt with mutated
  machine; outer `.error` is spec abort (exclude by hypothesis).
- `Evm`: `SailM` / `runS` of state-passing `execute` — failure is encoded in
  registers (`exc_halt`), success returns `(pc', top', mem', g')`.
- Prefer existing `Representation/` run-shape lemmas (`runR_bind_ok`,
  `runS` algebra, `charge`/`validate_stack` forms) over unfolding the whole
  handler in one `simp`.
- Heartbeats: large step theorems may need `set_option maxHeartbeats …`
  (see `Opcodes/Add.lean`). Raise deliberately; do not hide nontermination.

## Dispatch and scope (MM-3)

- SpecRef `opImplementation` / interpreter loop is `partial` — no equation
  lemmas. Theorems target **handler `def`s** (`iAdd`, …) directly, not
  dispatch.
- Do not claim step-loop or `opImplementation 0x01 = iAdd` equivalence until
  upstream de-partials (or a total wrapper exists).

## Gas vocabularies (MM-2)

- SpecRef uses `GasCosts.OPCODE_*`; `Evm` uses classic `G_*` plus Amsterdam
  `G_amsterdam_*`. ALU constants verified equal for the current tranche.
- Storage / account schedules are **not** yet verified equal once both gas
  dimensions are summed — investigate before claiming SLOAD/SSTORE equivalence.

## Assumptions and trust

- Comparison pinned to Amsterdam (`AmsterdamProfile` / `pinnedFork`). Thread
  the hypothesis; do not silently mix forks.
- Extraction fidelity and `nativeAccelerateBytes` opacity are trust assumptions
  (`Assumptions.lean`). Do not regenerate Sail→Lean here to "fix" a proof.
- Never edit `extraction/evm-sail` or the Lake `EvmAsm` checkout to make a
  bridge theorem hold.

## Tactic traps

- **`if_pos`/`if_neg`/`rw` with inferred conditions bind the leftmost `if`.**
  Trigger: goals with `if`s on both sides of an equality (extraction LHS,
  SpecRef RHS) — the side-condition tactic elaborates against whichever `if`
  comes first, producing baffling "pattern not found" or wrong-branch errors.
  Right move: pin every conditional rewrite (`if_pos (show c from …)`,
  `show`-typed `decide` proofs), and eliminate the LHS `if` before touching
  the RHS's. See any `Opcodes/S*.lean` sign-case block.
- **`lake env lean <file>` checks against *stale imported oleans*.**
  Trigger: editing a `Representation/` file and immediately checking a
  dependent opcode file — phantom "unknown identifier" errors for lemmas you
  just added. Right move: `lake build <module>` the edited dependency first.

## Anti-patterns (stop and record)

| temptation | do this instead |
| --- | --- |
| Success-only theorem "for now" | Inductive `StepResultRel` covering reachable failures; mark unreachable cases in the docstring / registry |
| Restrict `StateRel` until both sides agree | Ask whether the restriction is an EVM invariant; else mismatch ledger |
| Add `axiom` for a stuck lemma | Compiling `sorry`, then `/prove` (Aleph) if the statement is sound; else decompose / restate. Never silent axioms |
| Send a bad / incomplete statement to Aleph | Fix the relation or record a mismatch first; Aleph is for hard proofs of goals that already typecheck |
| Equate SpecRef and host stacks structurally | Use `StackRel` (cursor-prefix refinement) |
| Prove against `opImplementation` | Prove against the handler `def` |
| Hand-edit `docs/index.html` after a status change | Update markdown matrices → run refresh script |

## How to extend this skill

When you lose >15 minutes to a bridge-specific trap that isn't listed:

1. Write a short bullet under the right section (trigger → wrong move → right move).
2. Link the file/theorem or mismatch id if one exists.
3. Commit the skill update with the proof work when practical.

See `acquiring-skills` for format rules.
