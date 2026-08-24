import EvmSpecsVerify.Relations.State

/-!
# Assumptions ledger

Every assumption class used by the equivalence theorems, per the comparison
methodology. For each: why required, who guarantees it, whether a reachable
EVM state can violate it, and whether it is eliminable by proving.

## Fork / configuration

* `AmsterdamProfile` (Relations/State.lean) — the comparison is pinned to
  the Amsterdam configuration; SpecRef is structurally Amsterdam, the
  extraction is fork-parameterized via the `k_execution_profile` register.
  Threaded hypothesis, part of the intended statement; not eliminable.

## Representation invariants

* `StackRel.wf` — every stack entry `< 2^256`. An EVM invariant: SpecRef
  re-establishes it in each handler by wrapping (never states it); the
  extraction maintains it by `u256` reduction. Violations are unreachable
  from valid initial states; eliminable in principle by proving it
  invariant under all handlers (future work, tracked by the registry).
* `StackRel.frame`/`height` — the cursor reads as the height and the
  active frame's cursor-prefix represents the stack. Guaranteed by the
  host contract's reference reading (HostAxioms.lean:1845); established
  at frame entry (`stack_reset`) and preserved by the step lemmas.
* `StepRel` register hypotheses (`profile`, `message`, gas registers) —
  registers present in the register file. Guaranteed by `sail_model_init`
  + the interpreter's write discipline.
* `ReturnDataRel` (Relations/ReturnData.lean) — SpecRef's inline returndata
  equals the extraction's `returndata` output-slice window. Established when
  CALL-family frames return and consumed by RETURNDATASIZE/RETURNDATACOPY;
  violations are representation-invalid rather than reachable EVM states.
  Eliminable from individual opcode statements once a frame-transition
  simulation carries the relation globally.

## Gas budget (memory family)

* `MemGasSafe` (Relations/Memory.lean) — the frame's live gas plus the cost
  already sunk into memory stays below `mem_cost (2^27)` ≈ `3.5 × 10^13`,
  the point where the extraction's u32 memory space could be exhausted
  (mismatch ledger MM-6: `memory_access` spec-aborts there, SpecRef extends).
  Real block gas limits are ~8 orders of magnitude smaller, so every real
  execution satisfies it. Threaded hypothesis on the memory-family step
  theorems; eliminable only by bounding `g` globally (frame-entry invariant),
  future work.

## Storage read agreement (SLOAD)

* `SloadAgree` (Opcodes/Sload.lean) — the two sides' storage reads return
  the same word for the owning account and popped slot: SpecRef's
  `getStorage` walks the journalled tracker, the extraction's `k_sload`
  misses through its tx/block caches into a keccak-hashed witness-trie
  walk. Threaded hypothesis on `sload_step_equiv` only for the *value*;
  warm/cold accounting and gas are proven outright (`WarmRel`,
  Relations/Warm.lean). Quantified over the ambient warm stamps because
  the extraction marks warm before reading. Violations would be a real
  divergence between the state-tracker and the witness backend — none
  known; eliminable by the world-state tranche's `StorageRel` (the
  comparison-matrix "persistent storage" row).

## Account/code read agreement + address warmth (BALANCE / EXTCODESIZE)

* `BalanceAgree` (Opcodes/Balance.lean) — the `SloadAgree` sibling for
  account reads: SpecRef's journalled `getAccount` and the kernel's
  `k_get_balance` return the same balance, quantified over the ambient
  address stamps. Eliminable by the world tranche's account relation.
* `ExtcodesizeAgree` (Opcodes/Extcodesize.lean) — the external-code sibling:
  SpecRef's `getAccount` + `getCode` and the extraction's
  `k_get_code_size` return the same code length, quantified over ambient
  address stamps. The hypothesis also carries the code-length word bound.
  Eliminable by the world tranche's account/code-store relation.
* `WarmAddrRel` (Relations/WarmAddr.lean) — SpecRef's `accessedAddresses`
  vs the extraction's epoch stamps, **modulo precompiles**: the extraction
  short-circuits active precompiles as always warm, SpecRef prewarms them
  into the set at transaction start. The relation is the step-level form
  of that prewarm invariant; discharged at tx level (M3).
* `hpid` (classifier run shape, `balance_step_equiv` /
  `extcodesize_step_equiv`) — the precompile
  classifier `precompile_id_for_address` returns a fixed value per address
  and leaves state untouched. It reads only the profile register, so this
  is mechanically provable (a ~17-way address case split); kept as a
  hypothesis to keep the BALANCE slice bounded, dischargeable any time.

## Message-field ties and invariants (env family)

* Register-field ties (`haddr`, `hcaller`, `hvalue`, `htx`/`horigin`/`hgp`,
  `hcdreg`/`hcdrel`, and the block-env family `hhdr`/`hcid` + per-field
  ties in Opcodes/BlockEnv.lean — fragments of the future `BlockEnvRel`) — the extraction's `message`/`k_tx`/`calldata`
  registers carry the same frame data as SpecRef's `Message`. These are
  fragments of the future `MessageRel`/`TxEnvRel`, threaded per opcode
  until the CALL family relates whole frames; established at frame entry.
* `hwfv` (`callvalue_step_equiv`) — `message.value < 2^256`. A message
  invariant neither side states locally; maintained by both constructions,
  discharged at frame entry (M3).
* `CalldataRel` (Relations/Calldata.lean) covers both calldata windows
  (top-frame `InputCalldata` and nested-frame `MemoryCalldata`) — the read
  and copy paths are fully proven; what remains for the CALL family is
  establishing the nested window at frame entry (CALL sets up a
  parent-memory window that reads back the child's `message.data`).
* `CalldataBelow` (Relations/Calldata.lean, `calldatacopy_step_equiv`) —
  a nested frame's parent-memory calldata window lies entirely below the
  current frame's base, so the current frame's memory writes (expansion
  zero-fill, copy splice) cannot touch it. Trivially true for the
  top-frame input-arena window. A frame-allocation invariant (child
  frames are established above their parents); to be established at
  frame entry with the rest of `CalldataRel` (M3).
* `CodeRel` (Relations/Code.lean, `codesize_step_equiv` /
  `codecopy_step_equiv`) — the `frame_code` register holds a slice whose
  window reads back SpecRef's `evm.code` byte-for-byte (the same register
  `JumpdestRel` reads for JUMPI). Established at frame entry (M3);
  threaded per opcode meanwhile. Slice-length wf (`< 2^256`, also for
  `message.data.length` in `calldatasize_step_equiv`) is the extraction's
  `≤ 2^32 - 1` slice-type invariant, hypothesized like `hwfv`;
  `word_of_source_byte_count`'s assert is unreachable under it.

## Witness sufficiency (BLOCKHASH)

* `AncestorRel` (Opcodes/Blockhash.lean) — the extraction's parent-first
  `ancestorHashes` store + `k_n_headers` count represent SpecRef's
  oldest-first `blockEnv.blockHashes` with reversed indexing. A
  `BlockEnvRel` fragment, established at frame entry (M3).
* `hwit : BlockhashReady sRef` (`blockhash_step_equiv`) — a
  **lookup-specific domain restriction**: when this invocation has an
  operand, enough gas, and an in-window depth, that one depth must be present
  in the witness. Underflow, OOG, out-of-window queries, and short but
  sufficient witnesses remain in scope. A missing in-window depth makes both
  sides abort at the spec level — SpecRef `executionRejected`, the extraction
  `fatal_error WitnessDeficient` — but those aligned outer errors are outside
  the `StepResultRel` observation boundary. Eliminable only by widening the
  outcome relation to pair spec aborts.

## Deliberate scope restrictions (this tranche)

* SpecRef dispatch (`opImplementation`) is `partial` — theorems target the
  handler `def`s directly (mismatch ledger MM-3). Lifts if upstream
  de-partials the interpreter block.
* The `mem` slice is a pass-through for the ALU family; memory content is
  not yet related (matrix row: unrelated).
* Precompiles, hashing, world state: out of scope; `n/a` rows in the
  coverage matrix.

## External trust

* Extraction fidelity: the committed `Evm` package is generated by the
  custom Sail compiler from the Sail model and validated byte-exact against
  EELS over the tests-zkevm v0.6.2 corpus (upstream CI). We verify against
  the generated Lean, not the Sail source.
* Crypto: `nativeAccelerateBytes` is `opaque` — unused by this tranche.
-/

namespace EvmSpecsVerify

/-- The fork constant the comparison is pinned to (`Evm` side numbering:
Amsterdam = 16, Primitives/Fork.lean). -/
abbrev pinnedFork : Nat := Evm.Functions.Amsterdam

end EvmSpecsVerify
