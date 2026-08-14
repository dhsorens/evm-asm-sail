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
| word | `U256 := Nat` (Types.lean:26) | `word := Nat` (Defs.lean:51) | `WordRel` (eq) | `< 2^256` (wf, both) | proven-alu-ops (all 26 ALU binop/unop/ternop/EXP step theorems + POP) |
| pc | `Evm.pc : Uint` (Vm.lean:188) | `pc` register (`code_pointer := Nat`) + live `pc_in`/return arg of `execute` | `PcRel` | register authoritative at frame boundary; live value threaded (state-passing convention) | unrelated |
| operand stack | `Evm.stack : List U256`, head = top (Vm.lean:189) | `HostState.stackFrames` head: bottom-indexed `List word` + `stack_top` register / live `top : StackTop := BitVec 64` cursor (HostAxioms.lean:1846) | `StackRel` (prefix-up-to-cursor refinement) | height = `top.toNat` ≤ 1024; SpecRef entries `< 2^256` | proven-alu-ops (preserved by `binop_step_equiv` / `unop_step_equiv` / `ternop_step_equiv` / `exp_step_equiv` / `pop_step_equiv`) |
| regular gas | `Evm.gasLeft : Uint` (Vm.lean:192) | `gas_remaining` register (`gas := Nat`) / live `g : Nat` argument | `GasRel` | live value threaded during step | proven-alu-ops (charge/OOG both sides, constant costs via the shape theorems; exponent-dependent EIP-160 cost via `exp_gas_eq` in `exp_step_equiv`) |
| state gas reservoir | `Evm.stateGasLeft : Uint` (Vm.lean:193) | `state_gas_remaining` register | `GasRel.reservoir` | — | proven-alu-ops (success path; failure paths relate halt kind only — the extraction refills at `exc_halt`) |
| state gas spilled | `Evm.stateGasSpilled : Uint` (Vm.lean:207) | `state_gas_spilled` register | `GasRel.spilled` | — | proven-alu-ops (success path; see reservoir row) |
| regular gas used | `Evm.regularGasUsed : Uint` (Vm.lean:206) | (derived: initial − remaining) | tbd | check: is this observable or bookkeeping? | unrelated |
| halt / error status | `Evm.running : Bool` + `Evm.error : Option EvmError` (Vm.lean:198,202) + `EvmM` `throw` | `frame_status` register: `Running/Halted HaltKind/Exceptional ExceptionKind` | `StatusRel` / `ErrorRel` | SpecRef throws where `Evm` sets `Exceptional` + zeroes gas (`exc_halt`, Machine.lean:152) | proven-alu-ops (underflow/OOG kinds, `StepResultRel.halted`) |
| memory (bytes) | `Evm.memory : Bytes` (Vm.lean:190) | `HostState.memoryBytes : Array byte` + `evm_memory` register (`EvmMemorySlice`, Sigma-packed) / live `mem` argument | `MemoryRel` | frame-scoped via `memoryFrames` | unrelated |
| memory size | `memory.length` (implicit) | `EvmMemorySlice` len index | `MemoryRel` | expansion in words | unrelated |
| code | `Evm.code : Bytes` (Vm.lean:191) | `frame_code` register (`Code`) + `HostState.codeBytes`/`codeDb` | `CodeRel` | — | unrelated |
| valid jumpdests | `Evm.validJumpDestinations : List Uint` (Vm.lean:194) | `HostState.jumpdestTables : List (jump_table_index × List code_pointer)` | `JumpdestRel` | — | unrelated |
| return data | `Evm.returnData : Bytes` (Vm.lean:201) | `returndata` register (`OutputSlice`) + `HostState.outputBytes` | `ReturnDataRel` | — | unrelated |
| output | `Evm.output : Bytes` (Vm.lean:199) | frame output via `frame_output` / `OutputSlice` | `OutputRel` | — | unrelated |
| logs | `Evm.logs : List Log` (Vm.lean:195) | `HostState.logs : Array LogRecordRow` + `logBytes` arena | `LogsRel` | — | unrelated |
| refund counter | `Evm.refundCounter : Int` (Vm.lean:196) | `frame_refund` register (`gas_refund := Int`) | `RefundRel` | — | unrelated |
| message / call frame | `Evm.message : Message` (Vm.lean:197) | `message` register (`Message`) | `MessageRel` | — | unrelated |
| call depth | `message.depth` (SpecRef Message) | `call_depth` register (`frame_depth := Nat`) | `DepthRel` | ≤ 1024 | unrelated |
| suspended frames | (Python-style recursion in `process_message`, fuelled) | `HostState.continuationFrames : List FrameContinuation` + `stackFrames`/`memoryFrames` tails | `FramesRel` | tranche ≥ 3 | unrelated |
| accounts to delete | `Evm.accountsToDelete : List Address` (Vm.lean:200) | journal/host equivalent (tbd) | tbd | — | unrelated |
| accessed addresses (warm) | `Evm.accessedAddresses : List Address` (Vm.lean:203) | `HostState.warmAddresses : List (address × block_access_index)` (epoch-stamped) | `WarmRel` | epoch vs set semantics | unrelated |
| accessed storage keys | `Evm.accessedStorageKeys : List (Address × Bytes32)` (Vm.lean:204) | `HostState.warmSlots : List (StorageKey × block_access_index)` | `WarmRel` | — | unrelated |

## World / transaction components (tranche ≥ 3)

| component | SpecRef repr | `Evm` repr | relation | invariants | status |
|---|---|---|---|---|---|
| accounts | `BlockState`/`TransactionState` journals (StateTracker.lean:87,107) | `HostState.accountTx/accountBlock : List (address × AcctValue)` (+ `Evm.Contracts.ReferenceWorldState` spec layer, unconnected) | `WorldRel` | HostState↔Contracts connective tissue does not exist yet | unrelated |
| persistent storage | `TransactionState` journals | `HostState.storageTx/storageBlock : List (StorageKey × StorageValue)` | `StorageRel` | — | unrelated |
| transient storage | (in `TransactionState`) | `HostState.transient : List (StorageKey × word)` | `TransientRel` | — | unrelated |
| journal / revert | journaled tracker (StateTracker.lean) | `HostState.journal : List JournalFrame` (HostAxioms.lean:1092) | `JournalRel` | snapshot vs replay semantics | unrelated |
| tx env | `TransactionEnvironment` (Vm.lean:146) | `k_tx` register (`TxEnv`) | `TxEnvRel` | — | unrelated |
| block env | `BlockEnvironment` (Vm.lean:107) | `k_header` register (`BlockHeader`) + `k_n_headers`, `ancestorHashes` | `BlockEnvRel` | — | unrelated |
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
| `.stackUnderflow` | `StackUnderflow` | Evm checks in `validate_stack` *before* handler; SpecRef throws mid-handler at `stackPop` |
| `.stackOverflow` | `StackOverflow` | Evm pre-validates height−inputs+outputs > 1024; SpecRef throws at `stackPush` |
| `.outOfGas` | `OutOfGas` | SpecRef pops before charging; Evm charges before popping (see mismatches.md #2) |
| (others: revert, invalid jump/opcode, write protection, …) | (`InvalidJump`, `InvalidOpcode`, `StaticViolation`, …) | mapped as their opcodes enter scope |
