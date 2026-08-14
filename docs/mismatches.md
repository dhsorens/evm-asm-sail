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
  (`top - 2`, not `top`) and is equally unobservable. Re-establish per class as new
  families land.

## MM-4: Step-boundary pc convention

- **Area**: program-counter advancement.
- **SpecRef**: handlers advance `pc` themselves (`pcAdd 1` inside `binOp`).
- **`Evm`**: `fetch` advances `pc` past the opcode *before* `execute`; ALU handlers
  return `pc_in` unchanged.
- **Impact**: at handler entry the pcs differ by one; they re-align at step boundaries.
  Encoded in the theorems as `pc_in = sRef.evm.pc + 1` (hypothesis) and
  `returned pc = post.evm.pc` (conclusion, inside `AluPost`).
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
- **Fork**: Amsterdam. **Severity**: potentially high if real (conformance-level).
- **Disposition**: *needs investigation* (storage/account subset only).

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
