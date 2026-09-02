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

* ~~`TloadAgree`~~ (Opcodes/Tload.lean) — **discharged**. It was the
  transient sibling of `SloadAgree`: SpecRef's `getTransientStorage` on
  the executing account and the extraction's `k_tload (self_addr ())`
  return the same word, and the read leaves the operand stack alone.
  `TransientRel` (Relations/Transient.lean, landed with TSTORE) relates
  the two transient maps pointwise, and
  `tloadAgree_of_transientRel` proves the hypothesis from it — so this
  row is now a theorem, not an assumption. `tload_step_equiv` keeps the
  `TloadAgree` interface; what changed is that a caller can supply it by
  proof. `SloadAgree` above is the remaining member of this class, and
  it needs the persistent-storage relation rather than the transient
  one.

* `TransientRel` (Relations/Transient.lean) — a *relation*, threaded on
  `tstore_step_equiv` the way `LogRel` is on the LOG family, not an
  agreement assumption: the step theorem both consumes and re-establishes
  it. Its `wf` field (every stored value is a well-formed word) is the
  transient analogue of `StackRel.wf`, established at frame entry and
  preserved by every write, since both sides only ever store operands.

## Account/code read agreement + address warmth

* `BalanceAgree` (Opcodes/Balance.lean) — the `SloadAgree` sibling for
  account reads: SpecRef's journalled `getAccount` and the kernel's
  `k_get_balance` return the same balance, quantified over the ambient
  address stamps. Eliminable by the world tranche's account relation.
* `SelfBalanceAgree` (Opcodes/Selfbalance.lean) — the own-account form of
  `BalanceAgree`: SpecRef's journalled `getAccount message.currentTarget`
  and the extraction's `k_get_balance (self_addr ())` return the same
  balance, and the extraction's read leaves the operand stack alone.
  Strictly weaker than `BalanceAgree` — SELFBALANCE consults no access set,
  so nothing is quantified over ambient warm stamps. Eliminable by the
  world tranche's account relation.
* `ExtcodesizeAgree` (Opcodes/Extcodesize.lean) — the external-code sibling:
  SpecRef's `getAccount` + `getCode` and the extraction's
  `k_get_code_size` return the same code length, quantified over ambient
  address stamps. The hypothesis also carries the code-length word bound.
  Eliminable by the world tranche's account/code-store relation.
* `ExtcodehashAgree` (Opcodes/Extcodehash.lean) — relates SpecRef's
  missing-account-zero / account-code-hash result to the extraction's
  `k_get_codehash` plus `hash_to_word`, quantified over ambient address
  stamps. Eliminable by the world tranche's account/code-store relation.
* `ExternalCodeRel` (Relations/ExternalCode.lean) — the byte-level external
  code sibling used by `extcodecopy_step_equiv`: SpecRef's journalled
  `getAccount`/`getCode` result is the exact zero-padded byte source written by
  the extraction's `k_code_copy`. It quantifies over the warm-stamp and memory
  variants established before lookup and explicitly preserves stack frames,
  memory frames, warmth, and epoch while allowing lookup-cache updates.
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

* `hwfg` (`gas_step_equiv`) — the frame's live gas is a well-formed word
  (`gasLeft < 2^256`). Mismatch ledger MM-8: the extraction's `push_gas`
  reduces modulo `2^256` while SpecRef pushes the raw `Nat`, so above the
  modulus the two push different words — silently, without an abort. Real
  gas is `u64`-bounded, so the restriction excludes no reachable state.
  Eliminable by the same global gas bound `MemGasSafe` wants.
* `hwfpc` (`pc_step_equiv`) — the advanced program counter is a
  well-formed word (`pc_in < 2^256`). SpecRef's `Machine.pc` is an
  unbounded `Nat`; the extraction embeds it with
  `word_of_source_byte_count`, whose assert spec-aborts above `2^256`.
  The extraction's code slices live in a u32 space (and EIP-170 caps
  deployed code at 24576 bytes), so every reachable pc is ~70 orders of
  magnitude below the bound — the same class as the `CodeRel` slice-length
  wf above, and unreachable rather than merely unproven. Discharged at
  frame entry with the code relation (M3).

* `BlobHashAgree` (Opcodes/Blobhash.lean) — SpecRef's
  `message.txEnv.blobVersionedHashes` indexed with a 32-zero-byte default
  and the extraction's `k_blobhash` (index vs `k_tx`'s `blob_hashes.count`,
  then a 32-byte stateless-input-slice load, `ZERO_WORD` past the end)
  agree at **every** index — both zero-pad rather than fault, so no range
  restriction enters. Its `wf` clause is the envelope invariant that each
  versioned hash is 32 bytes (the `hwfv` analogue). A `TxEnvRel` fragment,
  established at frame entry (M3).

## Immediate decode fidelity (PUSH / DUPN family)

* `himm` (`dupn_step_equiv` / `swapn_step_equiv` / `exchange_step_equiv`)
  — the byte SpecRef reads out of its own code
  buffer at `pc + 1` is the byte the extraction's `.DUPN` constructor
  carries. The two sides split the decoder differently: SpecRef fetches the
  immediate *inside* the handler, the extraction decodes it upstream of
  `execute` and passes it as a constructor argument, so no single `def`
  contains both reads and nothing local can relate them. The same shape as
  PUSH's `hv`; it is an artifact of the MM-3 dispatch boundary, not a
  restriction on reachable states, and is discharged once a decode-layer
  simulation exists (`CodeRel` already ties the underlying code bytes).

## Log store correspondence (LOG family)

* `LogRel` (Relations/Log.lean) — SpecRef's frame-local `Evm.logs` vs the
  extraction's block-lifetime `HostState.logs` rows from a frame `base`,
  with the payload read out of the shared `logBytes` arena. The `base`
  offset is intrinsic, not a weakening: SpecRef resets `logs` per frame and
  merges into the parent on success, while the host array only grows within
  a transaction, so no frame-local statement can pin `logs.size` to the list
  length alone. Its `bounded` field (each related row's span already lies
  inside the arena) is a store invariant the host maintains by construction
  — every emission appends its payload before recording the span — and is
  what makes the relation stable under further emission (`logRel_append`).
  Established at frame entry with the rest of the frame relations (M3).

* `hstatic` (`log0_step_equiv`) — the `message` register's `is_static`
  flag equals SpecRef's `message.isStatic`. Another `MessageRel` fragment,
  the same class as `haddr`/`hcaller`/`hvalue`; established at frame entry
  (M3). It is load-bearing in both directions here, because the two sides
  check it at different points (mismatch ledger MM-11).

## Blob-fee regime and profile parameters (BLOBBASEFEE)

* `hword` (`blobbasefee_step_equiv`) — the blob base fee fits a word.
  **Not a convenience**: mismatch ledger MM-15 shows the two sides
  genuinely disagree above it, inside the range the extraction's own
  profile admits, so this hypothesis *is* the agreement regime. It is
  also all the proof needs: inside it the running sum bounds the
  accumulator, the iteration count and the term index, so neither
  extraction overflow guard can fire and no exponential estimate is
  required. Not eliminable — the divergence above it is real.
* `hprice` (`blobbasefee_step_equiv`) — SpecRef's `taylor_exponential`
  terminates within its fuel. Its other outcome is a `SpecError`, an
  outer abort outside the step-result boundary (the same treatment MM-6's
  spec aborts get). Eliminable by proving the fuel bound sufficient — a
  numeric side-quest, not a modelling gap.
* `hden` (`blobbasefee_step_equiv`) — the profile's blob-schedule
  denominator index is `BLOB_BASE_FEE_UPDATE_FRACTION`. The Sail type
  system fixes this per fork (`protocol_profile_parameters` correlates
  fork and schedule), but the Lean extraction erases type quantifiers, so
  it must be re-supplied. Discharged at tx level (M3) with the rest of
  the profile.
* `hcfg` (`BlobConfigOk`, `blobbasefee_step_equiv`) — the extraction's own
  precondition on `blob_base_fee`: the fork has blobs and the header's
  excess is within the profile ceiling. Outside it the extraction
  `fatal_error`s, which is an outer abort.
* `hexcess` (`blobbasefee_step_equiv`) — the header register's
  `excess_blob_gas` equals SpecRef's `blockEnv.excessBlobGas`: another
  `BlockEnvRel` fragment, like the ties in Opcodes/BlockEnv.lean.

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
