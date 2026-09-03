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

- **`omega` is blind to any comparison/arithmetic NODE whose type argument is
  an abbrev (`U256`/`word`/`Uint`/`gas_constant`), and to raw
  `Nat.le`/`Nat.lt`/`Nat.div`/`Nat.mod` spellings (the extraction emits the
  latter; `rw` patterns written with `/`/`%` also fail to match them — bridge
  with a defeq `show` in `/`/`%` spelling first).** The node's instance is fixed at *elaboration* of whatever
  statement introduced it; abbrev-typed operands can drag the whole binop to
  the abbrev even with a `Nat` operand present, and `(x : Nat)` ascriptions on
  variables do NOT reliably rescue it. Atoms of abbrev type *inside* an
  ℕ-node are fine. The playbook (hard-won in the memory tranche):
  1. Prefer inline `(by omega)` at a lemma-application site — the goal's node
     comes from the lemma's ℕ-typed signature, so it parses.
  2. Otherwise prove a ∀-quantified all-`Nat`-variable "key" clone
     (`have key : ∀ a c : Nat, a - 3 - c = a - (3 + c) := fun a c => by omega`)
     and close with `exact key _ _` — `exact` bridges defeq constants
     (`G_verylow ≡ 3`, `mloadCost ≡ 3 + cost`) that omega cannot.
  3. When restating a polluted hypothesis, lead the relation with a genuinely
     ℕ-typed term and ascribe abbrev projections
     (`g < 3 + ((… ).cost : Nat)`), or flip to `≥`/`=` with the ℕ side first;
     verify by whether the atom shows up in omega's counterexample dump.
  4. Never `rw [hlive]`-substitute a `Uint` projection INTO a goal you will
     still omega — convert the hypothesis instead and bridge with `exact`.
  `Int` powers: rewrite `(2:Int)^(256:Nat)` to a numeral via `decide` first
  (see `Representation/SignedWord.lean`, `fromSigned_eq`).
- Instantiating a generic shape theorem (Binop/EnvPusher style) leaves goals
  with un-reduced beta-redexes (`WordWf ((fun e => …) sRef.evm)`), which `rw`
  cannot see into — `show` the beta-reduced statement first, then rewrite.
- `omega` also ignores **disjunction hypotheses** and can't split a `¬(A ∨ B)`
  goal — `rcases h with h | h <;> omega` for the former, `simp only [not_or]`
  + per-conjunct `omega` for the latter. And when operands are match-bound
  abbrev variables (`x : U256` from a stack match) or struct projections,
  skip the ascription attempt entirely — go straight to the ∀-Nat key-clone
  remedy; `(e : Nat)` ascriptions do not change the elaborated instance.
- A multi-line `by` block inside `rw [… (by tac₁\n tac₂) …]` fails to parse
  mid-bracket — keep in-`rw` proofs single-line (`by tac₁; tac₂`) or hoist a
  `have` above the `rw`.

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
  ties returned pc to SpecRef post-pc (`BasePost`-style). JUMP / JUMPI / PUSH will
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
- **`SailME.run do …` handlers** (`k_sload`, `execute_sstore`) are an
  `ExceptT (Sail.Error ⊕ α)` early return: a `Sum.inr` is a deliberate
  *value*, a `Sum.inl` a real error. Handing that to `simp` loops on the
  `liftM`/`ExceptT`/`bindCont` unfolding (maxRecDepth). Use
  `Representation/EvmSailME.lean` (`runE_bind_ok` / `runE_bind_throw` /
  `runE_lift` / `runS_sailME_ok`/`_throw`); an arm that throws is reached
  as `runE_bind_ok … (runE_bind_throw (runE_throw …))`, because the
  statement-position `match` is bound and its continuation dropped.
- When a fused run-shape lemma's own proof needs its hypothesis, `refine
  runS_bind_ok h ?_` beats `rw [runS_bind, h]`: after a `show`, the goal's
  `runE`-style **abbrev is already unfolded**, so `rw` cannot find the
  pattern, while `refine`/`exact` unify up to `whnf` (this also
  zeta-reduces the do-elaborator's `have key := …` / `__do_jp` prelude).
- SpecRef's `TxM` is `StateT _ (Except _)`: after the `StateT.run_*` lemmas
  the base bind reads `Except.ok a >>= f`, which `pure_bind` does **not**
  match. Add a one-line `rfl` bridge (`except_ok_bind`,
  `Relations/Storage.lean`) rather than fighting simp.

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
- **Ledgered agree-hypotheses that carry data must be `∃`-packed `def`s, not
  `Prop` structures.** A `structure … : Prop` rejects non-proof fields
  (witness values, post-states, `hostAfter` functions) with "field must be a
  proof". Write `def XAgree … : Prop := ∃ v ts' …, … ∧ …` and `obtain` at the
  use site (pattern: `SloadAgree`, Opcodes/Sload.lean).

## Tactic traps

- **`if_pos`/`if_neg`/`rw` with inferred conditions bind the leftmost `if`.**
  Trigger: goals with `if`s on both sides of an equality (extraction LHS,
  SpecRef RHS) — the side-condition tactic elaborates against whichever `if`
  comes first, producing baffling "pattern not found" or wrong-branch errors.
  Right move: pin every conditional rewrite (`if_pos (show c from …)`,
  `show`-typed `decide` proofs), and eliminate the LHS `if` before touching
  the RHS's. See any `Opcodes/S*.lean` sign-case block.
- **Sail's `Int.ofNat` spelling evades `Nat.cast` simp lemmas.**
  Trigger: simping a goal containing `Sail.BitVec.toNatInt` (or other
  extraction code that writes `Int.ofNat n` literally) with cast lemmas like
  `Int.natCast_eq_zero` / `Int.toNat_natCast` — they never fire (different
  discrimination-tree key, though the terms are defeq), and the failure
  surfaces later as a baffling `rw` "pattern not found". Right move: add a
  local `have hofNat : ∀ n : Nat, Int.ofNat n = (n : Int) := fun _ => rfl`
  to the simp set first; see `word_bit_length_eq`
  (`Representation/BitwiseWord.lean`).
- **`omega` won't reduce tuple projections in `StepResultRel` post-state goals.**
  Trigger: after `refine StepResultRel.success ?_`, `BasePost`/`StateRel` goals
  mention the step tuple's projections (`(pc_in, top', mem, g').2.1.toNat`),
  which omega treats as atoms distinct from `top'.toNat` — "could not prove"
  with a baffling counterexample naming the projection. Right move: `show` the
  defeq-reduced statement (or `simp` projections away) before `omega`; see the
  `show top.toNat ≤ _` bullet in `unop_step_equiv` (`Opcodes/Shapes/Unop.lean`).
- **Nested `runS_bind_ok (runS_bind_ok … ?_) ?_` with holes fails to elaborate.**
  Trigger: chaining binds by nesting `runS_bind_ok` where the inner call still
  has a `?_` continuation — "don't know how to synthesize implicit argument
  `a`/`hs'`/`ss'`" because the intermediate result is a metavariable. Right
  move: prove a named body-level lemma for the handler's inner do-block first
  (the `runS_ternopShape_ok` pattern), then compose linearly with sequential
  `refine runS_bind_ok … ?_` steps. Nesting is fine only when the inner
  application is fully concrete (no holes); see `runS_pop_body_ok`
  (`Opcodes/Pop.lean`).
- **A structure-instance field value must fit on ONE physical line.**
  Trigger: any `{ x with field := v }` where `v` spans two lines — whether
  it starts inline after `:=` or on its own continuation line — dies with
  `unexpected token '('; expected '}'`. (Earlier wording claimed an
  own-continuation-line value is safe; STOP's `ss.regs.insert R\n (v…)`
  disproved it — only a value that also ENDS on that one line parses.)
  Right move: make the value a single token/line — shorten with
  `open … (name)` or a small named `def` (`returnedStatus`,
  `Opcodes/Return.lean`; `stoppedStatus`, `Opcodes/Stop.lean`). See also
  `runS_exp_body_ok`.
- **Sigma-packed extraction values (`Code`, `EvmMemorySlice`) leak `.2.2`
  projection atoms that omega/simp can't merge.**
  Trigger: stating a relation or lemma hypothesis over a whole sigma value
  (`c : Code` with `c.2.2.len` in the statement) — downstream goals mix the
  projection spelling with the destructured index, and omega treats them as
  distinct atoms ("possible counterexample" naming both). Right move:
  destructure in the *statement* — quantify the indices and fields separately
  (`(off len : Nat) (cf : CodeFields off len)`, register value
  `some ⟨off, len, cf⟩`) so no goal ever carries a projection. See
  `JumpdestRel` (`Relations/Jumpdest.lean`). The memory tranche will face the
  same choice with `EvmMemorySlice`.
- **`simp [h]` misses Bool `contains`/`decide` hypotheses because it
  normalizes the goal past them.**
  Trigger: an `if`-condition goal like `¬((!l.contains x) = true)` with
  `h : l.contains x = true` — plain `simp [h]` first rewrites the goal to
  `x ∈ l` membership form, then `h` (still in Bool form) never fires and is
  reported unused. Right move: `simpa using h` (normalizes both to the same
  form), or `simp only` with the targeted lemmas
  (`Bool.and_eq_true, decide_eq_true_eq`) and `exact`. See the `if` rewrites
  in `Opcodes/Jumpi.lean`.
- **`show` on a record-update projection can whnf-timeout; a `rfl` mini-lemma
  cannot.** Trigger: `show ({hs with memoryBytes := X} : HostState).memoryBytes
  .getD … = _` (or the equivalent goal restatement) hits a deterministic
  `whnf` heartbeat timeout on the 31-field `HostState`. Right move: prove the
  projection once as a top-level `rfl` lemma
  (`private theorem hostState_set_memoryBytes … := rfl`) and `rw` with it —
  instant. See `Relations/Memory.lean` / `Opcodes/Mload.lean`.
- **`lake env lean <file>` checks against *stale imported oleans*.**
  Trigger: editing a `Representation/` file and immediately checking a
  dependent opcode file — phantom "unknown identifier" errors for lemmas you
  just added. Right move: `lake build <module>` the edited dependency first.

- **No `show runS … = _ from …` placeholders inside `refine runS_bind_ok`
  chains.** The `_` becomes an unassigned metavariable ("unknown metavariable
  `?_uniq.N`"). State the RHS explicitly, or rely on the chain's defeq
  unification: thin kernel wrappers (`k_slot_mark_warm` ≡
  `storage_mark_warm`, pair-projection arguments like `(x, top-1).1`) unify
  with the underlying lemma at `refine` without any `show`.

- **SpecRef helper defs that are do-blocks need their own `runR` lemmas.**
  Trigger: simp-inlining a helper (`accessGasCost`) into its caller's chain —
  the nested bind structure no longer matches `runR_bind_ok`'s outer-bind
  pattern and the chain stalls with a huge un-normalized do goal. Right
  move: one `runR_<helper>_<case>` lemma per outcome, then chain the caller
  through those (pattern: `runR_accessGasCost_warm/cold`,
  `Opcodes/Balance.lean`). Conversely, INLINE `(← readReg r).field`
  expressions are flattened by the do elaborator — chain
  `runS_readReg`/`runS_pure` directly; a compound `show`-lemma over-groups
  the binds and fails to unify (`execute_caller`, `Opcodes/Caller.lean`).
- **Extraction types with derived `BEq` have no `LawfulBEq`** — `beq_iff_eq`
  / `bne_iff_ne` / assoc-list lemmas stall with "failed to synthesize
  LawfulBEq". Add a local instance: structures via field `beq_iff_eq`
  (`StorageKey`, Relations/Warm.lean); enums via
  `cases a <;> cases b <;> first | rfl | exact absurd h (by decide)`
  (`PrecompileId`, Relations/WarmAddr.lean).
- **Never `rfl`/whnf through a chain of `Vector.set!`s** (extraction
  builders like `word_to_address`): 20 sets time out at any heartbeat
  budget. Right move: the simp set `vector_set!_eq` (a local
  `set! = setIfInBounds` rfl bridge) + `Vector.toList_setIfInBounds` +
  `Vector.toList_replicate` + `List.replicate` reduces the whole builder's
  `toList` to a literal list in milliseconds
  (`Representation/AddressWord.lean`).

## Anti-patterns (stop and record)

| temptation | do this instead |
| --- | --- |
| Success-only theorem "for now" | Inductive `StepResultRel` covering reachable failures; mark unreachable cases in the docstring / registry |
| Restrict `StateRel` until both sides agree | Ask whether the restriction is an EVM invariant; else mismatch ledger |
| Add `axiom` for a stuck lemma | Compiling `sorry`, then `/prove` (Aleph) if the statement is sound; else decompose / restate. Never silent axioms |
| Leave `unused variable` / unused-hyp warnings | Tighten the statement (drop the hyp) — unused assumptions mean the theorem is not tight; do not disable the linter |
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
