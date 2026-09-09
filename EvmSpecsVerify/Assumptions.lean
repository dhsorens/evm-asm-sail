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
* `StateRel`'s register fields (`profile`, `message`, and `gas`'s
  reservoir/spill reads) — the registers a step reads are present in the
  register file. `SeqState` is `PreSail.SequentialState`, whose `regs` is a
  plain `Std.ExtDHashMap Register RegisterType` with **no totality
  invariant**, so a missing register is expressible; that is what makes
  this an assumption rather than a triviality.

  Presence *is* established somewhere, but every writer sits above the
  step boundary: `sail_model_init` (Evm.lean:68) writes
  `k_execution_profile` (:73) and `k_header` (:74) and is composed into
  the binary's entry point as `sail_model_init >=> sail_main` (:116);
  `decode_stateless_input` rewrites the profile from the decoded input
  (Lib/Ssz/StatelessInput.lean:1462); `enter_transaction_frame` writes
  `message` (Evm/Transaction.lean:1167); `restore_frame` restores it on
  frame return (Evm/Machine.lean:501). Nothing in this tranche connects a
  step's `SeqState` to any of them — three layers of context away — which
  is what keeps presence an assumption here and a theorem at M3. Every
  step theorem takes it as an explicit hypothesis (`hprof`/`hmsg`/`hsp`)
  or through `StateRel`.

  (An earlier revision named a `StepRel` structure, which does not
  exist — the register hypotheses live on `StateRel`, whose fields are
  literally `profile`/`message`/`gas`. The same revision then claimed the
  EVM extraction had no model-init entry point at all, having found
  `sail_model_init` only under `EvmAsm/Rv64/SailEquiv/` — a genuinely
  different Sail model. That negative was false, and false for an
  instructive reason: the search was rooted at the *directory*
  `extractions/lean/src/Evm`, which excludes the package's top-level
  module, the sibling file `src/Evm.lean` — exactly where
  `sail_model_init` lives. `check_assumptions` then confirmed the false
  negative, because `LEAN_ROOTS` had the same root. Both are fixed. The
  lesson is narrower than "beware the wrong model": **a negative claim
  needs a search whose root can contain the answer**, and a guard sharing
  that search is not independent evidence.)
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

## Gas budget and refund range (SSTORE)

* `hroom` / `hhead` on `sstore_step_equiv` (Opcodes/Sstore.lean) — the
  two extraction-only hard aborts of the Amsterdam state-gas path
  (mismatch ledger MM-17), the state-gas analogues of `MemGasSafe`:
  `state_gas_spill_add` spec-aborts once the recorded spill passes `2^24`
  (EIP-7825's transaction gas limit, the same constant on both sides) and
  `validated_refund_add` spec-aborts outside `±gas_refund_bound`, while
  SpecRef tracks both quantities as unbounded `Nat`/`Int`. Both
  hypotheses are stated on the pre-state — the spill plus one
  `STORAGE_SET`, the counter plus one step's worst-case refund movement —
  so a caller establishes them from the frame it already has. Unreachable
  for a well-formed transaction, but the argument is transaction-level
  (`SstoreRefundHeadroom` records the arithmetic); eliminable only by a
  frame-entry gas/refund invariant, as for `MemGasSafe`.

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

  **Reduced** (with `StorageRel`, Relations/Storage.lean):
  `sloadAgree_of_storageRel` proves the hypothesis for any slot the
  transaction has already written — that is a `storage_tx_get` hit, where
  `k_sload` returns the stored row without touching state and SpecRef's
  `getStorage` finds the same value in its first probe. What is left
  assumed is the two miss regimes: the extraction's block overlay (which
  doubles as its witness read-through cache) and the authenticated trie
  walk below it, plus the `storageCleared` branch. So the row stays, but
  it is now an assumption about the *base* storage layers rather than
  about storage reads in general.

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

* `StorageRel` (Relations/Storage.lean) — a *relation*, not an agreement
  assumption: every row the extraction's `storageTx` overlay holds,
  SpecRef's transaction-layer `storageWrites` holds with the same live
  value, and the extraction's stored `orig` is the value SpecRef
  recomputes with `getStorageOriginal`. **One-directional by design**
  (mismatch ledger MM-16): an `SSTORE` that writes the value already
  there records a row on SpecRef's side and none on the extraction's, so
  the converse inclusion is false on a reachable state.
  `storageRel_write` preserves it across a changing write,
  `storageRel_write_noop` across that no-op, `storageRel_frame` across
  the read bookkeeping every SpecRef probe performs, and
  `storageRel_hostFrame` across host steps that leave the overlay alone.
  Its `wf` field plays the role `TransientRel.wf` does. Consumed by
  `sloadAgree_of_storageRel` above and by `sstore_step_equiv`.

## Storage write agreement (SSTORE)

* `SstoreAgree` (Opcodes/Sstore.lean) — the writer's sibling of
  `SloadAgree`: SpecRef's `getStorageOriginal`/`getStorage` return the
  `orig`/`curr` pair of the row the extraction's `k_sload` returns, and
  SpecRef's `setStorage` succeeds. It also records `k_sload`'s framing —
  it leaves the operand stack, the warm stamps and the `storageTx`
  overlay alone (its caching is one layer down, in `storageBlock`), and
  when the overlay already holds a row for the slot, that row is the one
  it returns. Threaded on `sstore_step_equiv` only for the *values*: the
  Amsterdam schedule (`sstoreCst_eq`), the warm/cold accounting
  (`WarmRel`), the two-dimensional gas and the refund are proven
  outright. `sstoreAgree_of_storageRel` reduces it, exactly as for
  `SloadAgree`, to the transaction-overlay regime plus SpecRef's
  account-existence check — that check has no counterpart in `k_sstore`
  (SpecRef rejects a store to a non-existent account, the extraction
  writes the row), so it stays a hypothesis rather than being derived.

* `TransientRel` (Relations/Transient.lean) — a *relation*, threaded on
  `tstore_step_equiv` the way `LogRel` is on the LOG family, not an
  agreement assumption: the step theorem both consumes and re-establishes
  it. Its `wf` field (every stored value is a well-formed word) is the
  transient analogue of `StackRel.wf`, established at frame entry and
  preserved by every write, since both sides only ever store operands.

## Account/code read agreement + address warmth

* `AccountRel` (Relations/Account.lean) — a *relation*, not an agreement
  assumption, and the account sibling of `StorageRel`: every row the
  extraction's `accountTx` overlay holds, SpecRef's `accountWrites` holds
  as the row's **EIP-161 view** (`hostAcctView`: the three trie fields, or
  `none` when the row is not `present`). Two of its four fields are the
  host's EIP-161 discipline and are load-bearing, not cosmetic — an absent
  row carries the empty tuple (`absentEmpty`) and a present row does not
  (`presentNonEmpty`) — because the extraction's readers return `info`
  fields straight out of the row where SpecRef substitutes `EMPTY_ACCOUNT`
  for a deleted entry. They are also *preserved*, not merely assumed:
  `specAcctEmpty_eq` proves SpecRef's `accountExistsAndIsEmpty` test —
  which `modifyState` runs after every account write — and the
  extraction's inline `account_info_empty` are the same function of the
  tuple, and `accountRel_write` carries the relation across one
  **non-collapsing** write (SpecRef's `modifyState` against the
  extraction's `store_account_info`, whole-row install and scalar fast
  paths alike). The collapsing write is **now also proven** for the
  account overlay (`accountRel_write_collapse` against
  `runS_store_account_info_clear`): both sides land "no account" at the
  address, so no `hval` is needed — an absent row's EIP-161 view is
  `none` unconditionally. Its fast-path branch is discharged by
  `absentEmpty` itself: an absent row already carries the empty tuple, so
  all three scalar tests fail and the write is a complete no-op.
  What stays open is the *storage* half, now ledgered as **MM-21**: the
  extraction's `storage_tx_clear` records a clear generation that makes
  later uncached slots read zero, where SpecRef's `destroyStorage` is the
  identity and has no such notion. Unreachable — an account holding
  storage is never EIP-161-empty — and the clearing lemma's frame clause
  is stated against `hostStorageClear` so a caller cannot cross it with a
  `StorageRel` by accident. `accountRel_frame`/`accountRel_hostFrame` carry
  the relation across the read bookkeeping on either side. It **reduces the three
  account-read hypotheses below** on the transaction-overlay regime, and
  was the account-side prerequisite SELFDESTRUCT needed — since landed
  (`selfdestruct_step_equiv`).

## The value transfer

* `hsum` (`transfer_equiv`, Relations/Transfer.lean) — the destination's
  post-transfer balance fits a word. Mismatch ledger MM-19: the
  extraction credits with `alu_add` (`(l + r) % 2^256`), SpecRef with
  unbounded `Nat` addition, so above the modulus they store different
  balances — and SpecRef's is not a word, breaking `AccountRel.wf`. The
  same class as `hwfg` (MM-8) and `hword` (MM-15): a modelling gap in
  SpecRef's `U256 := Nat` alias rather than a coding slip. Unreachable in
  a well-formed chain (the total ether supply is far below `2^256` and a
  transfer is balance-preserving), but the witness is caller-supplied, so
  nothing local rules the pre-state out. Eliminable only by a supply
  invariant on the witness.
* ~~`hne` / `hv`~~ (`transfer_equiv`) — **discharged.** These excluded
  `k_transfer`'s two early-return branches (mismatch ledger MM-18), both
  reachable through `SELFDESTRUCT`. `transfer_equiv_self`,
  `transfer_equiv_zero` and `transfer_equiv_zero_collapse` now prove them
  instead, through `accountRel_rowsFrame`: SpecRef writes where the
  extraction does not, and every row it writes holds the value that was
  already there — including the collapsing branch, where a dead
  beneficiary is written empty and deleted again, landing back on the
  `some none` entry the relation had. `transfer_equiv` keeps the
  hypotheses; what changed is that a caller can now supply either case by
  proof.
* `hsne` / `hdne` (`transfer_equiv`) — neither write collapses. Not an
  invariant: it is the `accountRel_write` scope restriction, stated on
  the extraction's `account_info_empty` and transported to SpecRef's test
  by `specAcctEmpty_eq`, so one hypothesis serves both sides. Both of
  SELFDESTRUCT's writes and a value-carrying CALL's satisfy it, and
  `hdne` is *automatic* for a nonzero transfer (the credited balance
  cannot be zero). `hsne` survives in the degenerate theorems too, where
  it says the source is not EIP-161-empty after the debit — true for any
  account executing code.
* `hstore` (`runTx_modifyState_collapse`, and through it
  `transfer_equiv_zero_collapse`) — a collapsing account has no pending
  storage writes, which is what confines `destroyStorage` to its identity
  branch. Every reachable collapse satisfies it: `iSstore` writes storage
  only to `message.currentTarget`, which is executing code, and an
  account with code is never EIP-161-empty — so a collapsing account
  never has a `storageWrites` entry. Without it SpecRef would move those
  slots into `storageReads` (block-access-list observable) and delete
  them, breaking `StorageRel` in the one direction that matters. The
  argument is transaction-level, so it stays a hypothesis; eliminable by
  a tx-level invariant tying `storageWrites` keys to code-bearing
  accounts.
* The EIP-7708 constants are **not** assumptions: `transferLogAddress_eq`
  and `transferTopic_eq` are kernel computations, the second going
  through `byteArray_toList` because `String.toUTF8.toList` is
  well-founded and so opaque to `decide`.

## The `SELFDESTRUCT` lifecycle

* `LifecycleRel` (Relations/Selfdestruct.lean) — a *relation*: SpecRef's
  `txState.createdAccounts` and `evm.accountsToDelete` against the
  extraction's per-row `created`/`selfdestructed` flags. Its `outer`
  parameter is the same device as [`LogRel`](Relations/Log.lean)'s
  `base` and for the same reason: `accountsToDelete` is frame-local and
  merged upward by `incorporate_child_on_success`, while the row flag is
  global within the transaction, so no frame-local statement can pin one
  to the other. `lifecycleRel_mark` preserves it across the opcode's
  mark, and `accountRel_flagWrite` shows a lifecycle-flag write cannot
  disturb `AccountRel` (which reads only `info` and `present`).
  The `deleted` component is an equality — SpecRef discards a failed
  child's whole `evm` and the extraction's journal restores the flag, so
  both roll back together. The `created` component is
  **one-directional**, and that is mismatch ledger MM-20.
* `CreatedAgree` (Relations/Selfdestruct.lean) — the converse of
  `LifecycleRel.created` at **one** address, needed because
  `SELFDESTRUCT` *branches* on the EIP-6780 same-transaction test and a
  branch needs both directions. What makes it an assumption rather than a
  theorem is MM-20: `restoreTxState` keeps `createdAccounts` across a
  revert (its own docstring says so) where the extraction's
  `state_journal_revert` restores the whole row. The divergent state is
  **unreachable** — the originator must be executing code when
  `SELFDESTRUCT` runs, and the only creation of that address in this
  transaction reverted, which rolled its code back too — but the argument
  is transaction-level, so it cannot be discharged inside one step.
  Eliminable by the CREATE family (M3), where reverted frames become
  expressible. MM-20 also records the neighbouring worry that is *not*
  real: `generic_create` runs its collision test before
  `markAccountCreated`, so SpecRef never marks a pre-existing contract as
  created this transaction.

* `BalanceAgree` (Opcodes/Balance.lean) — the `SloadAgree` sibling for
  account reads: SpecRef's journalled `getAccount` and the kernel's
  `k_get_balance` return the same balance, quantified over the ambient
  address stamps. Eliminable by the world tranche's account relation.

  **Reduced** (with `AccountRel`): `balanceAgree_of_accountRel` proves it
  for any account the transaction has already written — an `acct_tx_get`
  hit, where `k_aload` returns the stored row without touching state. What
  stays assumed is the two miss regimes: the block overlay (which doubles
  as the extraction's witness read-through cache) and the authenticated
  trie walk below it.
* `SelfdestructAgree` (Opcodes/Selfdestruct.lean) — the widest of the
  read-agreement bundles, because `SELFDESTRUCT` reads two rows and then
  *writes* through them. It carries: the originator's and beneficiary's
  rows in the transaction overlay (the `BalanceAgree` domain restriction),
  `CreatedAgree` at the originator (MM-20's converse), the transfer in
  whichever of its four shapes applies, and the EIP-7825 spill cap — an
  extraction-only hard abort with no SpecRef counterpart, threaded exactly
  as `sstore_step_equiv` threads its own `hroom`.

  **Reduced** (with `AccountRel` + `LogRel`): the transfer clause is
  discharged in *all four* shapes —
  `selfdestructTransfer_nondegenerate`, `selfdestructTransfer_self`,
  `selfdestructTransfer_zero` and `selfdestructTransfer_zero_collapse`. So what stays assumed there is only which shape a
  given state is in, plus those pairings' own ledger conditions: MM-19's
  non-wrap bound on the beneficiary's balance, and MM-18's collapse tests.
  Two of `transfer_equiv`'s side conditions are *automatic* for
  `SELFDESTRUCT` and are noted rather than assumed: the originator cannot
  EIP-161-collapse, because it is executing code, and a nonzero-value
  beneficiary cannot either, because the credit leaves it a nonzero
  balance.
* `SelfBalanceAgree` (Opcodes/Selfbalance.lean) — the own-account form of
  `BalanceAgree`: SpecRef's journalled `getAccount message.currentTarget`
  and the extraction's `k_get_balance (self_addr ())` return the same
  balance, and the extraction's read leaves the operand stack alone.
  Strictly weaker than `BalanceAgree` — SELFBALANCE consults no access set,
  so nothing is quantified over ambient warm stamps. Eliminable by the
  world tranche's account relation.

  **Reduced** (with `AccountRel`): `selfBalanceAgree_of_accountRel`, the
  own-account form of the above.
* `ExtcodesizeAgree` (Opcodes/Extcodesize.lean) — the external-code sibling:
  SpecRef's `getAccount` + `getCode` and the extraction's
  `k_get_code_size` return the same code length, quantified over ambient
  address stamps. The hypothesis also carries the code-length word bound.
  Eliminable by the world tranche's account/code-store relation.
* `ExtcodehashAgree` (Opcodes/Extcodehash.lean) — relates SpecRef's
  missing-account-zero / account-code-hash result to the extraction's
  `k_get_codehash` plus `hash_to_word`, quantified over ambient address
  stamps. Eliminable by the world tranche's account/code-store relation.

  **Reduced** (with `AccountRel`): `extcodehashAgree_of_accountRel`, via
  `accountRel_codehash`. This one needs a constant identity beyond the
  relation — SpecRef *computes* `keccak256 []` while the extraction
  carries the digest as a literal — and that identity is a **theorem**
  (`empty_code_hash_eq`, `decide`-checked by the kernel), not a trust
  assumption: the `nativeAccelerateBytes` opacity below covers keccak on
  general input, but the empty digest is evaluated. Without it the two
  sides' notion of "codeless account" would not be comparable at all.
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
* The `mem` slice is a pass-through for the **ALU** family — that family's
  theorems relate no memory content. Memory itself is related and
  preserved: `MemoryRel` with `mload_step_equiv`/`mstore_step_equiv`/
  `return_step_equiv`, matrix rows `memory (bytes)` and `memory size` both
  `proven-memory-ops`. (Earlier revisions of this bullet said memory was
  "not yet related (matrix row: unrelated)", which the matrix had already
  contradicted.)
* Hashing is out of scope: `KECCAK256` is the **single** `n/a` row in the
  coverage table, behind the opaque-hash axiom both sides share.
  Precompiles have no row at all — they are not `Evm.Defs.ast`
  constructors.
* World state is **not** out of scope, though this section used to say so.
  Five relations have landed — `AccountRel`, `StorageRel`, `TransientRel`,
  `WarmAddrRel`, `LifecycleRel` — and the opcodes that read and write it
  (SLOAD, SSTORE, TLOAD, TSTORE, BALANCE, SELFBALANCE, EXTCODE*,
  SELFDESTRUCT) are all `full`. What remains scoped out is the
  **transaction-level** tower: the CREATE/CALL frames (MM-3), the journal
  and revert discipline, and the base storage layers behind the
  transaction overlay (MM-16's miss regimes).

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
