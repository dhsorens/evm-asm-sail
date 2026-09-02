# Mismatch ledger

Every discovered disagreement between SpecRef and `Evm`, including deliberate
differences. Per the comparison methodology: when the specs disagree, the entry is
written **before** any proof is adjusted around it.

Fields: area · SpecRef behavior · `Evm` behavior · triggering state · expected EVM
behavior (+ source) · fork · reachability · severity · likely cause · disposition
(`evm-asm` / `evm-sail` / extraction / relation / fork / intentional abstraction /
unreachable / ambiguity / needs investigation).

---

## MM-1: Operation order in ALU handlers (pop-then-charge vs validate-charge-then-pop)

- **Area**: every ALU-family opcode handler.
- **SpecRef**: `binOp` pops both operands, *then* charges gas, then pushes
  (InstructionsCore.lean:121; matches Python execution-specs statement order). An OOG
  throw therefore leaves a `Machine` whose stack has already lost its operands.
- **`Evm`**: `execute` runs `validate_stack` (underflow/overflow, Machine.lean:168)
  before the handler; the handler charges (`charge`, Gas.lean:536) *before* popping.
  On failure `exc_halt` zeroes gas, refills state gas, sets
  `frame_status := Exceptional k`, and the operands are still on the host stack.
- **Trigger**: any ALU opcode with insufficient gas or insufficient stack.
- **Expected EVM behavior**: the Yellow Paper's exceptional halt discards the frame;
  intermediate stack contents of a halted frame are not observable. Both orders yield
  the same observable outcome (halt kind + all-gas-consumed).
- **Fork**: all. **Reachability**: trivially reachable. **Severity**: none expected.
- **Likely cause**: intentional — evm-sail hoists the YP exceptional-halt predicate;
  execution-specs (and SpecRef) inline it per operation.
- **Disposition**: *intentional abstraction* — **proven** equivalent at the halt
  observation boundary for every landed family (binop/unop/ternop shape theorems,
  `exp_step_equiv`, `pop_step_equiv`: the underflow and OOG cases pair SpecRef throws
  with `Evm` `Exceptional` statuses; both sides check stack shape before gas, so the
  kinds align case by case). EXP is the one opcode where the orders *coincide*: the
  extraction also pops before charging there, because `exp_gas` needs the exponent
  (Execute.lean:283); the halted post-cursor differs from the other shapes
  (`top - 2`, not `top`) and is equally unobservable. The copy family
  (CALLDATACOPY/CODECOPY/RETURNDATACOPY) is pop-first with a **three-stage** extraction charge
  (base / per-word / expansion) against SpecRef's single charge; the OOG states
  still pair kind-for-kind (`calldatacopy_step_equiv`, `codecopy_step_equiv`,
  `returndatacopy_step_equiv`). EXTCODECOPY is also pop-first and splits
  SpecRef's single charge into access/read, copy, and expansion stages; its
  staged failures are paired by `extcodecopy_step_equiv`. Re-establish per class
  as new families land.

## MM-5: Halt-kind divergence for charge-first handlers on double-fault states

- **Area**: opcodes whose SpecRef handler charges gas **before** validating
  the stack shape: `iPushN`, `iDupN`, `iSwapN` (InstructionsCore.lean:346–372)
  and the charge-first env pushers (`iAddress`, `iOrigin`, `iCaller`, …,
  InstructionsEnv.lean). Contrast the ALU family, which pops first — MM-1's
  kind-alignment argument covers only pop-first handlers.
- **SpecRef**: `charge_gas` runs first; a state that is simultaneously out of
  gas **and** stack-invalid throws `.outOfGas` before the depth/overflow check
  is reached.
- **`Evm`**: `validate_stack` runs before every handler; the same state halts
  `StackUnderflow` / `StackOverflow` and the charge is never attempted.
- **Trigger**: e.g. `DUP1` on an empty stack with `gasLeft < 3`; `PUSH1` with a
  1024-deep stack and `gasLeft < 3`.
- **Expected EVM behavior**: the Yellow Paper's exceptional halts are uniform —
  consume all gas, discard the frame. The halt *kind* is diagnostic only, not
  chain-observable.
- **Fork**: all. **Reachability**: trivially reachable. **Severity**: none at
  the chain observation boundary; visible only to our (stronger) kind-matching
  relation.
- **Likely cause**: intentional — the same YP-predicate hoisting as MM-1;
  execution-specs (and SpecRef) inline the charge per the Python statement
  order, which for PUSH/DUP/SWAP precedes the stack access.
- **Disposition**: *intentional abstraction* — encoded as an explicit, documented
  `StepResultRel.haltedChargeFirst` constructor (Relations/Outcome.lean) pairing
  SpecRef `.outOfGas` with the extraction's stack-fault kind on exactly these
  double-fault states. Single-fault states still align kind-for-kind.
  Discharging artifacts: `push_step_equiv`, `dup_step_equiv`,
  `swap_step_equiv` (underflow only — SWAP cannot overflow), the
  `envPush_step_equiv` family, and the live-state pushers
  `pc_step_equiv` / `gas_step_equiv` / `msize_step_equiv` (overflow only —
  0-in cannot underflow).

## MM-6: u32 memory space — `memory_access` fatal-errors where SpecRef extends

- **Area**: memory-family opcodes (MLOAD/MSTORE/MSTORE8/RETURN/REVERT/copies).
- **SpecRef**: memory is an unbounded `Bytes`; any offset is reachable if the
  quadratic expansion charge is affordable.
- **`Evm`**: memory offsets/lengths live in a u32 space; after the expansion
  charge succeeds, `memory_access` (Gas.lean:684) **fatal-errors**
  (`ExecutionInvalid`, a spec abort — not an EVM halt) when
  `start + size > 2^32 - 1`.
- **Trigger**: a frame whose live gas can afford `mem_cost (2^27)` words
  (≈ `3.5 × 10^13` gas) reaching for the last u32 page. The boundary cases
  cost identical gas (`required = 2^32 - 31` vs `2^32`), so no charge-side
  reasoning separates them — only a gas *budget* does.
- **Expected EVM behavior**: real block gas limits (~3.6 × 10^7) sit about
  eight orders of magnitude below the bound, so the fatal path is
  unreachable in any valid chain execution.
- **Fork**: all. **Reachability**: only with unbounded gas (our `g : Nat` is
  unbounded). **Severity**: none under real budgets; a genuine model-boundary
  divergence at unbounded gas.
- **Disposition**: *intentional abstraction* (zkVM guest memory bound) —
  threaded as the `MemGasSafe` hypothesis (Relations/Memory.lean): the frame's
  gas cannot pay for word count `2^27`. Ledgered in `Assumptions.lean`;
  `safe_required_bound` discharges the range check from it.

## MM-7: RETURNDATACOPY out-of-bounds diagnostic kind

- **Area**: RETURNDATACOPY source-range validation.
- **SpecRef**: after charging gas, throws `.outOfBoundsRead` when
  `source + size > returnData.length`.
- **`Evm`**: after the same charges and memory expansion,
  `validated_returndata_copy` calls `exc_halt ... InvalidOpcode` for either
  failed bounds check.
- **Trigger**: any sufficiently funded RETURNDATACOPY whose source range is
  outside the previous call's returndata, including `size = 0` with
  `source > returnData.length`.
- **Expected EVM behavior**: exceptional halt consuming the frame's remaining
  gas. The internal diagnostic label is not chain-observable.
- **Fork**: all. **Reachability**: trivially reachable. **Severity**: none at
  the chain observation boundary; visible to diagnostic-kind comparison.
- **Likely cause**: the Sail model uses its existing `ExceptionKind` vocabulary
  for the exceptional halt and has no dedicated returndata-bounds kind.
- **Disposition**: *intentional abstraction* — represented explicitly by
  `ErrorRel.outOfBoundsRead`; `returndatacopy_step_equiv` proves the complete
  in-bounds and out-of-bounds paths without weakening `StepResultRel`.

## MM-8: `push_gas` reduces modulo `2^256` where SpecRef pushes a raw `Nat`

- **Area**: GAS (and any future site that pushes a gas quantity as a word).
- **SpecRef**: `iGas` pushes `evm.gasLeft` — an unbounded `Nat` — directly
  (InstructionsCore.lean:278).
- **`Evm`**: `push_gas` (Machine.lean:196) pushes
  `u256 (value mod 2^256)`; `u256` is the identity, so the modulus is the
  whole content. Its own doc comment says transaction validation
  establishes the bound and the reduction "retains modular behavior outside
  that invariant".
- **Trigger**: a frame carrying more than `2^256 - 1` live gas. The two
  sides then push **different words** — and, unlike MM-6, the extraction
  does not abort, it silently wraps.
- **Expected EVM behavior**: `GAS` pushes the remaining gas as a 256-bit
  word; gas is `u64`-bounded in every real transaction (block gas limits
  are ~`3.6 × 10^7`), so the values coincide.
- **Fork**: all. **Reachability**: only with unbounded gas (our `g : Nat`
  is unbounded, as in MM-6). **Severity**: none under real budgets.
- **Likely cause**: intentional — the extraction keeps total functions by
  reducing instead of asserting.
- **Disposition**: *intentional abstraction* — threaded as
  `hwfg : WordWf sRef.evm.gasLeft` on `gas_step_equiv` (Opcodes/Gas.lean)
  and ledgered in `Assumptions.lean`; `runS_push_gas` is where the
  reduction is discharged. Eliminable by bounding frame gas globally, the
  same frame-entry invariant MM-6's `MemGasSafe` wants.

## MM-4: Step-boundary pc convention

- **Area**: program-counter advancement.
- **SpecRef**: handlers advance `pc` themselves (`pcAdd 1` inside `binOp`).
- **`Evm`**: `fetch` advances `pc` past the opcode *before* `execute`; ALU handlers
  return `pc_in` unchanged.
- **Impact**: at handler entry the pcs differ by one; they re-align at step boundaries.
  Encoded in the theorems as `pc_in = sRef.evm.pc + 1` (hypothesis) and
  `returned pc = post.evm.pc` (conclusion, inside `BasePost`).
- **Disposition**: *intentional abstraction* (decode/fetch layering difference),
  handled by the statement shape; will need care at JUMP/JUMPI and PUSH.

## MM-2: Gas constant vocabularies and the storage-access schedule

- **Area**: gas schedule constants.
- **SpecRef**: per-opcode `GasCosts.OPCODE_*` (InstructionsCore.lean:41,
  InstructionsEnv.lean:30) plus a `StateGasCosts` dimension; storage/account constants
  are post-reprice values (e.g. `COLD_STORAGE_ACCESS = 3000`, `STORAGE_WRITE = 10000`,
  `TX_BASE = 12000` — Gas.lean).
- **`Evm`**: classic tier constants `G_*` (Gas.lean:425–509: `G_verylow = 3`,
  `G_cold_sload = 2100`, `G_sset = 20000`, …) plus Amsterdam state-gas constants
  `G_amsterdam_*` (Gas.lean:487–507).
- **Verified so far (2026-08-12)**: the ALU-family execution-gas constants agree —
  SpecRef `OPCODE_ADD/SUB/AND/… = 3` = `G_verylow`, `OPCODE_MUL/DIV/MOD/… = 5` = `G_low`,
  `OPCODE_ADDMOD/MULMOD = 8` = `G_mid`, `OPCODE_EXP_BASE = 10`/`PER_BYTE = 50` =
  `G_exp`/`G_expbyte`, `OPCODE_POP/PC/MSIZE/GAS = 2` = `G_base`,
  `OPCODE_JUMPDEST = 1` = `G_jumpdest`. **No mismatch in this tranche's scope.**
- **Open**: whether SpecRef's repriced storage/account constants equal the `Evm` side's
  `G_cold_sload`-classic + `G_amsterdam_*` state-gas split once both dimensions are
  summed per operation. To be resolved when the storage tranche starts.
- **Verified 2026-08-17 (SLOAD)**: the SLOAD access constants agree at Amsterdam —
  `sload_cost` returns `G_warm_access = 100 = WARM_ACCESS` (warm) and, on the
  `fork ≥ Amsterdam` path, `G_amsterdam_cold_storage_access = 3000 =
  COLD_STORAGE_ACCESS` (cold); the classic `G_cold_sload = 2100` is dead at this fork.
  Machine-checked by `runS_sload_cost` + `sload_step_equiv` (Opcodes/Sload.lean).
- **Verified 2026-08-17 (BALANCE + env pushers)**: the account-access constants agree at
  Amsterdam — warm `100` (`WARM_ACCESS` = `G_warm_access`), cold account `3000`
  (`COLD_ACCOUNT_ACCESS` = `G_amsterdam_cold_account_access`, the `fork ≥ Amsterdam`
  path of `account_cost`); and `OPCODE_ADDRESS`/`OPCODE_ORIGIN` `= 2 = G_base`.
  Machine-checked by `runS_account_cost` + `balance_step_equiv` and the
  ADDRESS/ORIGIN step theorems. Remaining open subset: SSTORE and the
  CALL/CREATE-family account writes.
- **Verified 2026-08-19 (copy family + size pushers)**: `OPCODE_CALLDATASIZE` /
  `OPCODE_CODESIZE` `= 2 = G_base`; `OPCODE_CALLDATACOPY_BASE` /
  `OPCODE_CODECOPY_BASE` `= 3 = G_verylow` and
  `OPCODE_COPY_PER_WORD = 3 = G_copy_word` with the same per-word count
  (`ceil32 size / 32` = `memory_word_count size`, incl. the extraction's
  257-bit-avoiding `memory_word_count_word`). Machine-checked by
  `calldatasize_step_equiv` / `codesize_step_equiv` / `calldatacopy_step_equiv` /
  `codecopy_step_equiv` (+ `runS_charge_copy_ok`/`_oog`,
  `memory_word_count_word_eq`). Also `OPCODE_MSTORE8_BASE = 3 = G_verylow`
  (`mstore8_step_equiv`) and `OPCODE_GASPRICE = 2 = G_base`
  (`gasprice_step_equiv`).
- **Verified 2026-08-19 (BLOCKHASH)**: `OPCODE_BLOCKHASH = 20` on both sides
  (SpecRef constant, extraction literal), machine-checked by
  `blockhash_step_equiv`.
- **Verified 2026-08-19 (block-env pushers)**: `OPCODE_COINBASE` /
  `OPCODE_TIMESTAMP` / `OPCODE_NUMBER` / `OPCODE_PREVRANDAO` /
  `OPCODE_GASLIMIT` / `OPCODE_CHAINID` / `OPCODE_BASEFEE` /
  `OPCODE_SLOTNUM` `= 2 = G_base`, machine-checked by the
  `envPush_step_equiv` family (Opcodes/BlockEnv.lean).
- **Verified 2026-08-24 (EXTCODESIZE)**: at Amsterdam, SpecRef's account
  access plus EIP-8038 `WARM_ACCESS` code-read surcharge agrees with the
  extraction's `account_cost + external_code_read_cost`: warm `200`, cold
  `3100`, machine-checked by `runS_account_cost`,
  `runS_external_code_read_cost`, and `extcodesize_step_equiv`.
- **Verified 2026-08-24 (EXTCODECOPY)**: the same Amsterdam account + code-read
  charge is followed by `3 * memory_word_count size` and the identical memory
  expansion cost. `extcodecopy_step_equiv` proves the three-stage extraction
  charge equivalent to SpecRef's single total charge for warm and cold targets.
- **Verified 2026-09-02 (control family)**: `OPCODE_JUMPDEST = 1 = G_jumpdest`
  and `OPCODE_JUMP = 8 = G_mid` (`OPCODE_JUMPI = 10 = G_high` was already
  covered by `jumpi_step_equiv`), `OPCODE_PC = 2 = G_base` and
  `OPCODE_GAS = 2 = G_base` and `OPCODE_MSIZE = 2 = G_base`.
  Machine-checked by `jumpdest_step_equiv`, `jump_step_equiv`,
  `pc_step_equiv`, `gas_step_equiv` and `msize_step_equiv`; and
  `OPCODE_SWAP = 3 = G_verylow` by `swap_step_equiv`.
- **Fork**: Amsterdam. **Severity**: potentially high if real (conformance-level).
- **Disposition**: *needs investigation* (SSTORE/account subset only).

## MM-3: SpecRef dispatch is `partial` — no proof surface

- **Area**: opcode dispatch (`opImplementation`, `executeLoop`, CALL/CREATE family;
  Interpreter.lean:314 `mutual partial` block).
- **SpecRef**: `partial def` — no equation lemmas, no induction principle; nothing
  about dispatch or the step loop is provable, including `opImplementation … 0x01 = iAdd`.
- **`Evm`**: fully total (`whileFuelM` with computed fuel; zero `partial def`).
- **Impact**: theorems must target SpecRef handler `def`s directly; dispatch-level and
  loop-level equivalence are blocked on the SpecRef side.
- **Disposition**: *deliberate scope restriction* here + candidate upstream request to
  evm-asm (the fuel is already threaded; de-partialing looks mechanical). Recorded in
  `EvmSpecsVerify/Assumptions.lean`.
