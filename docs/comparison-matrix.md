# Comparison matrix: SpecRef ↔ `Evm`

The master coverage document for the SpecRef ↔ `Evm` (evm-sail extraction) comparison:
one row per **observable state component**. Every semantically relevant field or behavior
gets both-side representations, a relation, invariants, proof coverage, and a status —
rows are added rather than hiding concepts in prose.

Sources: `SpecRef` = `.lake/packages/EvmAsm/EvmAsm/Stateless/SpecRef/` @ evm-asm `6a43f7d`;
`Evm` = `extraction/evm-sail/extractions/lean/src/Evm/` @ evm-sail `d0e4aab`.

Statuses: `unrelated` (no relation defined yet) · `related` (relation defined) ·
`proven-<scope>` (relation preserved by the named proof scope) · `n/a` (+ reason).

## Machine-frame components

| component | SpecRef repr | `Evm` repr | relation | invariants | status |
|---|---|---|---|---|---|
| word | `U256 := Nat` (Types.lean:26) | `word := Nat` (Defs.lean:51) | `WordRel` (eq) | `< 2^256` (wf, both) | proven-alu-ops (all 26 ALU binop/unop/ternop/EXP step theorems + POP/PUSH/DUP/JUMPI) |
| pc | `Evm.pc : Uint` (Vm.lean:188) | `pc` register (`code_pointer := Nat`) + live `pc_in`/return arg of `execute` | `PcRel` | register authoritative at frame boundary; live value threaded (state-passing convention) | proven-step-boundary (every landed step theorem ties the returned pc to SpecRef's post-pc via `BasePost`, incl. PUSH immediates (`pc+1+n`) and taken jumps (`jumpi_step_equiv`); MM-4) |
| operand stack | `Evm.stack : List U256`, head = top (Vm.lean:189) | `HostState.stackFrames` head: bottom-indexed `List word` + `stack_top` register / live `top : StackTop := BitVec 64` cursor (HostAxioms.lean:1846) | `StackRel` (prefix-up-to-cursor refinement) | height = `top.toNat` ≤ 1024; SpecRef entries `< 2^256` | proven-alu-ops (preserved by the binop/unop/ternop shape theorems and `exp_step_equiv` / `pop_step_equiv` / `push_step_equiv` / `dup_step_equiv` / `jumpi_step_equiv`) |
| regular gas | `Evm.gasLeft : Uint` (Vm.lean:192) | `gas_remaining` register (`gas := Nat`) / live `g : Nat` argument | `GasRel` | live value threaded during step | proven-alu-ops (charge/OOG both sides, constant costs via the shape theorems; exponent-dependent EIP-160 cost via `exp_gas_eq` in `exp_step_equiv`) |
| state gas reservoir | `Evm.stateGasLeft : Uint` (Vm.lean:193) | `state_gas_remaining` register | `GasRel.reservoir` | — | proven-alu-ops (success path; failure paths relate halt kind only — the extraction refills at `exc_halt`) |
| state gas spilled | `Evm.stateGasSpilled : Uint` (Vm.lean:207) | `state_gas_spilled` register | `GasRel.spilled` | — | proven-alu-ops (success path; see reservoir row) |
| regular gas used | `Evm.regularGasUsed : Uint` (Vm.lean:206) | (derived: initial − remaining) | tbd | check: is this observable or bookkeeping? | unrelated |
| halt / error status | `Evm.running : Bool` + `Evm.error : Option EvmError` (Vm.lean:198,202) + `EvmM` `throw` | `frame_status` register: `Running/Halted HaltKind/Exceptional ExceptionKind` | `StatusRel` / `ErrorRel` | SpecRef throws where `Evm` sets `Exceptional` + zeroes gas (`exc_halt`, Machine.lean:152) | proven-alu-ops (underflow/OOG kinds, `StepResultRel.halted`); normal halt proven for RETURN (`Halted (HaltReturn …)` via `ReturnPost`) and STOP (`Halted (HaltStop ())` via `StopPost`) |
| memory (bytes) | `Evm.memory : Bytes` (Vm.lean:190) | `HostState.memoryBytes : Array byte` + `evm_memory` register (`EvmMemorySlice`, Sigma-packed) / live `mem` argument | `MemoryRel` (Relations/Memory.lean: established-prefix correspondence + ceil32 alignment tail) | frame-scoped via `memoryFrames`; MM-6 `MemGasSafe` budget | proven-memory-ops (`mload_step_equiv` / `mstore_step_equiv` / `return_step_equiv`, `MemPost`) |
| memory size | `memory.length` (implicit, always ceil32-aligned) | `EvmMemorySlice` len index = exact established byte | `MemoryRel.aligned` | expansion gas agrees via `extend_cost_eq` | proven-memory-ops |
| code | `Evm.code : Bytes` (Vm.lean:191) | `frame_code` register (`Code`) + `HostState.codeBytes`/`codeDb` | `CodeRel` (Relations/Code.lean: register read + the slice window reads back `evm.code` byte-for-byte; both sides zero-pad copies past the end) | established at frame entry (M3), threaded as a step-level hypothesis meanwhile | proven-code-readers (`codesize_step_equiv` / `codecopy_step_equiv`) |
| valid jumpdests | `Evm.validJumpDestinations : List Uint` (Vm.lean:194) | `HostState.jumpdestTables : List (jump_table_index × List code_pointer)` + `frame_code` register's `jumpdests` index | `JumpdestRel` (Relations/Jumpdest.lean: set-membership ↔ range-guarded table lookup) | — | proven-jumpi (hypothesis + preserved in `JumpiPost`, `jumpi_step_equiv`) |
| return data | `Evm.returnData : Bytes` (Vm.lean:201) | `returndata` register (`OutputSlice`) + `HostState.outputBytes` | [`ReturnDataRel`](../EvmSpecsVerify/Relations/ReturnData.lean#L22) | frame-return invariant; MM-7 diagnostic-kind abstraction on OOB reads | proven-return-data (`returndatasize_step_equiv`, `returndatacopy_step_equiv`) |
| output | `Evm.output : Bytes` (Vm.lean:199) | host output buffer (`outputBytes`) + `HaltReturn` `OutputSlice` | `ReturnPost` output clause (byte-for-byte) | — | proven-return (`return_step_equiv`) |
| logs | `Evm.logs : List Log` (Vm.lean:195) | `HostState.logs : Array LogRecordRow` + `logBytes` arena | `LogsRel` | — | unrelated |
| refund counter | `Evm.refundCounter : Int` (Vm.lean:196) | `frame_refund` register (`gas_refund := Int`) | `RefundRel` | — | unrelated |
| message / call frame | `Evm.message : Message` (Vm.lean:197) | `message` register (`Message`) | `MessageRel` | field ties threaded per opcode meanwhile: `haddr` (SLOAD/ADDRESS), `hcaller`/`hvalue` (CALLER/CALLVALUE); full relation lands with the CALL family | unrelated |
| calldata | `message.data : Bytes` (SpecRef Message) | `calldata` register (`CalldataSlice`) + `HostState.inputBytes` arena (top frame) or parent memory (nested) | `CalldataRel` (Relations/Calldata.lean: the register's window — top-frame input arena or nested-frame parent memory — reads back the data byte-for-byte; both sides zero-pad reads) | establishing the nested window at frame entry is CALL-family scope (incl. `CalldataBelow`, the nested window's separation from the current frame); the read and copy paths cover both windows | proven-calldata-readers (`calldataload_step_equiv` / `calldatasize_step_equiv` / `calldatacopy_step_equiv`) |
| call depth | `message.depth` (SpecRef Message) | `call_depth` register (`frame_depth := Nat`) | `DepthRel` | ≤ 1024 | unrelated |
| suspended frames | (Python-style recursion in `process_message`, fuelled) | `HostState.continuationFrames : List FrameContinuation` + `stackFrames`/`memoryFrames` tails | `FramesRel` | tranche ≥ 3 | unrelated |
| accounts to delete | `Evm.accountsToDelete : List Address` (Vm.lean:200) | journal/host equivalent (tbd) | tbd | — | unrelated |
| accessed addresses (warm) | `Evm.accessedAddresses : List Address` (Vm.lean:203) | `HostState.warmAddresses : List (address × block_access_index)` (epoch-stamped) | `WarmAddrRel` (Relations/WarmAddr.lean: set membership ↔ precompile-or-current-stamp; the extraction short-circuits active precompiles, SpecRef prewarms them at tx start) | prewarm invariant + classifier run shape are step-level hypotheses | proven-account-readers (`balance_step_equiv`, `extcodesize_step_equiv`, `extcodehash_step_equiv`) |
| accessed storage keys | `Evm.accessedStorageKeys : List (Address × Bytes32)` (Vm.lean:204) | `HostState.warmSlots : List (StorageKey × block_access_index)` | `WarmRel` (Relations/Warm.lean: set membership ↔ epoch-current stamp, via the `toBeBytes32` decode roundtrip) | epoch vs set semantics; SpecRef keys are 32-byte BE encodings | proven-sload (hypothesis + preserved by `sload_step_equiv` on every path that marks) |

## World / transaction components (tranche ≥ 3)

| component | SpecRef repr | `Evm` repr | relation | invariants | status |
|---|---|---|---|---|---|
| accounts | `BlockState`/`TransactionState` journals (StateTracker.lean:87,107) | `HostState.accountTx/accountBlock : List (address × AcctValue)` (+ `Evm.Contracts.ReferenceWorldState` spec layer, unconnected) | `WorldRel` | HostState↔Contracts connective tissue does not exist yet; BALANCE/EXTCODESIZE/EXTCODEHASH reads are bridged meanwhile by ledgered agree hypotheses | unrelated |
| persistent storage | `TransactionState` journals | `HostState.storageTx/storageBlock : List (StorageKey × StorageValue)` | `StorageRel` | SLOAD reads bridged meanwhile by the ledgered `SloadAgree` hypothesis (Opcodes/Sload.lean, Assumptions.lean) — discharged when this row is proven | unrelated |
| transient storage | (in `TransactionState`) | `HostState.transient : List (StorageKey × word)` | `TransientRel` | — | unrelated |
| journal / revert | journaled tracker (StateTracker.lean) | `HostState.journal : List JournalFrame` (HostAxioms.lean:1092) | `JournalRel` | snapshot vs replay semantics | unrelated |
| tx env | `TransactionEnvironment` (Vm.lean:146) | `k_tx` register (`TxEnv`) | `TxEnvRel` | ORIGIN reads bridged meanwhile by the `htx`/`horigin` register-tie hypotheses (`origin_step_equiv`) | unrelated |
| block env | `BlockEnvironment` (Vm.lean:107) | `k_header` register (`BlockHeader`) + `k_n_headers`, `ancestorHashes` | `BlockEnvRel` | field ties threaded per opcode meanwhile (coinbase/time/number/prevRandao/gasLimit/chainId/baseFee/slotNumber, the `envPush_step_equiv` family); block hashes via `AncestorRel` (reversed-index witness window + `k_n_headers` count, `blockhash_step_equiv`) | proven-blockenv-pushers + proven-blockhash (Opcodes/BlockEnv.lean, Opcodes/Blockhash.lean) |
| chain id | in `BlockEnvironment` | `k_chain_id` register | `BlockEnvRel` | — | unrelated |
| fork / profile | structurally Amsterdam (whole port) | `k_execution_profile` register (13-index Sigma `ExecutionProfile`); gates like `fork ≥b Amsterdam` | `AmsterdamProfile` hypothesis | fixed-fork comparison; hypothesis threaded, not eliminated | unrelated |

## Monads and outcomes

| aspect | SpecRef | `Evm` | relation |
|---|---|---|---|
| monad | `EvmM = ExceptT EvmError (StateT Machine (Except SpecError))` (Vm.lean:223) | `SailM = StateT HostState (EStateM (Error Unit) (SequentialState RegisterType …))` (HostAxioms.lean:1181) | run-shape lemmas in `Representation/` |
| step convention | handler mutates `Machine` (`iAdd : EvmM Unit`) | state-passing: `execute op pc top mem g : SailM (pc' × top' × mem' × g')` (Execute.lean:3809); registers authoritative at frame boundaries | `StateRel` binds live args to registers |
| exceptional halt | `throw : EvmError` (state kept, caught at frame boundary) | `exc_halt`: zero gas + `frame_status := Exceptional k` + state-gas refill (Machine.lean:152) | `StepResultRel` / `ErrorRel` |
| spec abort | `SpecError` (aborts everything) | `Error Unit` (EStateM error) / `fatal_error` | out of scope this tranche; both are "not an EVM outcome" |
| crypto | concrete keccak/sha256 (Crypto.lean:103) | `opaque nativeAccelerateBytes` (HostAxioms.lean:1242) | out of scope this tranche; later: parameterized `PureKeccak` + bridging hypothesis |

## Error kind mapping (ErrorRel)

| SpecRef `EvmError` (Vm.lean:60) | `Evm` `ExceptionKind` | notes |
|---|---|---|
| `.stackUnderflow` | `StackUnderflow` | Evm checks in `validate_stack` *before* handler; SpecRef throws mid-handler at `stackPop`. Charge-first handlers (PUSH/DUP/SWAP) diverge on double-fault states — MM-5, `StepResultRel.haltedChargeFirst` |
| `.stackOverflow` | `StackOverflow` | Evm pre-validates height−inputs+outputs > 1024; SpecRef throws at `stackPush`. MM-5 applies to charge-first handlers |
| `.outOfGas` | `OutOfGas` | SpecRef pops before charging; Evm charges before popping (see mismatches.md #2) |
| `.invalidJumpDest` | `InvalidJump` | mapped by `jumpi_step_equiv` (`do_jump` range + table check vs `validJumpDestinations`) |
| (others: revert, invalid opcode, write protection, …) | (`InvalidOpcode`, `StaticViolation`, …) | mapped as their opcodes enter scope |
