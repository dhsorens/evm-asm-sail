# Opcode coverage matrix

One row per constructor of the `Evm` extraction's instruction AST
(`Evm.Defs.ast`, Defs.lean:2672 — 88 constructors), cross-referenced with SpecRef's
handlers. The Counts section below is checked against these rows by
`scripts/refresh-proof-coverage-canvas.py`, which refuses to regenerate the site if
they disagree; the planned `EvmSpecsVerify/Coverage/Registry.lean` will make the
same counts machine-checked against the AST itself.

Statuses: `unstated` · `stated` (theorem exists, may cite pending lemmas) ·
`success-proven` (success path only — not acceptable as final) ·
`full` (full `StepResultRel`: success + every reachable failure — or, for
revert-capable handlers, full `RevertResultRel`) · `n/a` (+ reason).
Named theorems in the status column are markdown links to the `theorem` line.

SpecRef handlers marked *(partial)* live in the `partial def mutual` block
(Interpreter.lean:314) and are dispatch-inaccessible to proofs until upstream
de-partials; their rows can only be `stated` against the handler bodies once those
are total.

## Shape classes

ALU step skeletons live in [`EvmSpecsVerify/Opcodes/Shapes/`](../EvmSpecsVerify/Opcodes/Shapes/README.md).

- **binop**: `charge → pop ×2 → alu → push` on both sides (SpecRef `binOp`, Evm `execute_<op>`) — [`Shapes/Binop.lean`](../EvmSpecsVerify/Opcodes/Shapes/Binop.lean)
- **unop**: 1-in/1-out analogue — [`Shapes/Unop.lean`](../EvmSpecsVerify/Opcodes/Shapes/Unop.lean)
- **ternop**: 3-in/1-out (ADDMOD, MULMOD) — [`Shapes/Ternop.lean`](../EvmSpecsVerify/Opcodes/Shapes/Ternop.lean)
- **stack**: pure stack manipulation (POP/PUSH/DUP/SWAP/…)
- **env pusher**: base-cost `k_env` block-environment pushers (SpecRef `pushConstOf`, Evm `envPushShape`) — [`Shapes/EnvPusher.lean`](../EvmSpecsVerify/Opcodes/Shapes/EnvPusher.lean)
- **live-state pusher**: base-cost 0-in/1-out pushers whose word comes from the live step state, read *after* the charge (SpecRef `livePushOf`) — [`Shapes/LivePusher.lean`](../EvmSpecsVerify/Opcodes/Shapes/LivePusher.lean)
- **memory / control / env / storage / system**: as named

## ALU family

| opcode | byte | SpecRef | `Evm` | shape | status |
|---|---|---|---|---|---|
| STOP | 0x00 | `iStop` | `execute_stop` | system | **full** ([`stop_step_equiv`](../EvmSpecsVerify/Opcodes/Stop.lean#L94) — the free normal halt is the only reachable outcome: 0-in/0-out excludes stack faults, no gas charge; `StopPost` = `ReturnPost` minus output) |
| ADD | 0x01 | `iAdd` | `execute_add` | binop | **full** ([`add_step_equiv`](../EvmSpecsVerify/Opcodes/Add.lean#L30) — success/underflow/OOG; overflow unreachable for 2-in/1-out) |
| MUL | 0x02 | `iMul` | `execute_mul` | binop | **full** ([`mul_step_equiv`](../EvmSpecsVerify/Opcodes/Mul.lean#L26) — success/underflow/OOG; overflow unreachable) |
| SUB | 0x03 | `iSub` | `execute_sub` | binop | **full** ([`sub_step_equiv`](../EvmSpecsVerify/Opcodes/Sub.lean#L30) — success/underflow/OOG; overflow unreachable) |
| DIV | 0x04 | `iDiv` | `execute_div` | binop | **full** ([`div_step_equiv`](../EvmSpecsVerify/Opcodes/Div.lean#L33) — success/underflow/OOG; overflow unreachable) |
| SDIV | 0x05 | `iSdiv` | `execute_sdiv` | binop | **full** ([`sdiv_step_equiv`](../EvmSpecsVerify/Opcodes/Sdiv.lean#L185) — success/underflow/OOG; overflow unreachable) |
| MOD | 0x06 | `iMod` | `execute_mod` | binop | **full** ([`mod_step_equiv`](../EvmSpecsVerify/Opcodes/Mod.lean#L33) — success/underflow/OOG; overflow unreachable) |
| SMOD | 0x07 | `iSmod` | `execute_smod` | binop | **full** ([`smod_step_equiv`](../EvmSpecsVerify/Opcodes/Smod.lean#L95) — success/underflow/OOG; overflow unreachable) |
| ADDMOD | 0x08 | `iAddmod` | `execute_addmod` | ternop | **full** ([`addmod_step_equiv`](../EvmSpecsVerify/Opcodes/Addmod.lean#L36) — success/underflow/OOG; overflow unreachable for 3-in/1-out) |
| MULMOD | 0x09 | `iMulmod` | `execute_mulmod` | ternop | **full** ([`mulmod_step_equiv`](../EvmSpecsVerify/Opcodes/Mulmod.lean#L38) — success/underflow/OOG; overflow unreachable for 3-in/1-out) |
| EXP | 0x0a | `iExp` | `execute_exp` | binop (dyn gas, fuelled pow) | **full** ([`exp_step_equiv`](../EvmSpecsVerify/Opcodes/Exp.lean#L527) — success/underflow/OOG; overflow unreachable; EIP-160 gas via `exp_gas_eq`, fuelled `alu_exp` ↔ `powMod` via `runS_alu_exp`) |
| SIGNEXTEND | 0x0b | `iSignextend` | `execute_signextend` | binop | **full** ([`signextend_step_equiv`](../EvmSpecsVerify/Opcodes/Signextend.lean#L134) — success/underflow/OOG; overflow unreachable) |
| LT | 0x10 | `iLt` | `execute_lt` | binop | **full** ([`lt_step_equiv`](../EvmSpecsVerify/Opcodes/Lt.lean#L28) — success/underflow/OOG; overflow unreachable) |
| GT | 0x11 | `iGt` | `execute_gt` | binop | **full** ([`gt_step_equiv`](../EvmSpecsVerify/Opcodes/Gt.lean#L28) — success/underflow/OOG; overflow unreachable) |
| SLT | 0x12 | `iSlt` | `execute_slt` | binop | **full** ([`slt_step_equiv`](../EvmSpecsVerify/Opcodes/Slt.lean#L100) — success/underflow/OOG; overflow unreachable) |
| SGT | 0x13 | `iSgt` | `execute_sgt` | binop | **full** ([`sgt_step_equiv`](../EvmSpecsVerify/Opcodes/Sgt.lean#L33) — success/underflow/OOG; overflow unreachable) |
| EQ | 0x14 | `iEq` | `execute_eq` | binop | **full** ([`eq_step_equiv`](../EvmSpecsVerify/Opcodes/Eq.lean#L28) — success/underflow/OOG; overflow unreachable) |
| ISZERO | 0x15 | `iIszero` | `execute_iszero` | unop | **full** ([`iszero_step_equiv`](../EvmSpecsVerify/Opcodes/Iszero.lean#L28) — success/underflow/OOG; overflow unreachable for 1-in/1-out) |
| AND | 0x16 | `iAnd` | `execute_and` | binop | **full** ([`and_step_equiv`](../EvmSpecsVerify/Opcodes/And.lean#L28) — success/underflow/OOG; overflow unreachable) |
| OR | 0x17 | `iOr` | `execute_or` | binop | **full** ([`or_step_equiv`](../EvmSpecsVerify/Opcodes/Or.lean#L28) — success/underflow/OOG; overflow unreachable) |
| XOR | 0x18 | `iXor` | `execute_xor` | binop | **full** ([`xor_step_equiv`](../EvmSpecsVerify/Opcodes/Xor.lean#L28) — success/underflow/OOG; overflow unreachable) |
| NOT | 0x19 | `iNot` | `execute_not` | unop | **full** ([`not_step_equiv`](../EvmSpecsVerify/Opcodes/Not.lean#L33) — success/underflow/OOG; overflow unreachable for 1-in/1-out) |
| BYTE | 0x1a | `iByte` | `execute_byte` | binop | **full** ([`byte_step_equiv`](../EvmSpecsVerify/Opcodes/Byte.lean#L45) — success/underflow/OOG; overflow unreachable) |
| SHL | 0x1b | `iShl` | `execute_shl` | binop | **full** ([`shl_step_equiv`](../EvmSpecsVerify/Opcodes/Shl.lean#L36) — success/underflow/OOG; overflow unreachable) |
| SHR | 0x1c | `iShr` | `execute_shr` | binop | **full** ([`shr_step_equiv`](../EvmSpecsVerify/Opcodes/Shr.lean#L37) — success/underflow/OOG; overflow unreachable) |
| SAR | 0x1d | `iSar` | `execute_sar` | binop | **full** ([`sar_step_equiv`](../EvmSpecsVerify/Opcodes/Sar.lean#L160) — success/underflow/OOG; overflow unreachable) |
| CLZ | 0x1e | `iClz` | `execute_clz` | unop (fork-gated ≥ Osaka; gate lives in decode, upstream of `execute`) | **full** ([`clz_step_equiv`](../EvmSpecsVerify/Opcodes/Clz.lean#L40) — success/underflow/OOG; overflow unreachable for 1-in/1-out) |

## Hashing

| opcode | byte | SpecRef | `Evm` | shape | status |
|---|---|---|---|---|---|
| KECCAK256 | 0x20 | `iKeccak` | `execute_keccak256` | memory+crypto | n/a this tranche (opaque keccak) |

## Environment / block

| opcode | byte | SpecRef | `Evm` | shape | status |
|---|---|---|---|---|---|
| ADDRESS | 0x30 | `iAddress` | `execute_address` | env | **full** ([`address_step_equiv`](../EvmSpecsVerify/Opcodes/Address.lean#L212) — success/overflow/OOG/MM-5 double fault; codec bridge `address_to_word_eq`) |
| BALANCE | 0x31 | `iBalance` | `execute_balance` | env+world | **full** ([`balance_step_equiv`](../EvmSpecsVerify/Opcodes/Balance.lean#L472) — success (warm/cold)/underflow/OOG ×2; `WarmAddrRel` (prewarm invariant + classifier shape hypotheses), value behind ledgered `BalanceAgree` — see `Assumptions.lean`) |
| ORIGIN | 0x32 | `iOrigin` | `execute_origin` | env | **full** ([`origin_step_equiv`](../EvmSpecsVerify/Opcodes/Origin.lean#L216) — success/overflow/OOG/MM-5 double fault; `k_tx` register tie hypothesis) |
| CALLER | 0x33 | `iCaller` | `execute_caller` | env | **full** ([`caller_step_equiv`](../EvmSpecsVerify/Opcodes/Caller.lean#L205) — success/overflow/OOG/MM-5 double fault; codec bridge `address_to_word_eq`) |
| CALLVALUE | 0x34 | `iCallvalue` | `execute_callvalue` | env | **full** ([`callvalue_step_equiv`](../EvmSpecsVerify/Opcodes/Callvalue.lean#L206) — success/overflow/OOG/MM-5 double fault; codec-free, message-value wf hypothesized) |
| CALLDATALOAD | 0x35 | `iCalldataload` | `execute_calldataload` | env+memory | **full** ([`calldataload_step_equiv`](../EvmSpecsVerify/Opcodes/Calldataload.lean#L222) — success/underflow/OOG; `CalldataRel` covers both calldata windows (input arena / parent memory), both sides zero-pad so no range hypothesis) |
| CALLDATASIZE | 0x36 | `iCalldatasize` | `execute_calldatasize` | env | **full** ([`calldatasize_step_equiv`](../EvmSpecsVerify/Opcodes/Calldatasize.lean#L216) — success/overflow/OOG/MM-5 double fault; `CalldataRel` supplies the length tie, slice-length wf hypothesized like CALLVALUE's `hwfv`) |
| CALLDATACOPY | 0x37 | `iCalldatacopy` | `execute_calldatacopy` | memory | **full** ([`calldatacopy_step_equiv`](../EvmSpecsVerify/Opcodes/Calldatacopy.lean#L653) — success ×3 (zero size/grow/in-window)/underflow ×3/OOG ×3 (base/per-word/expansion, three-way charge split vs SpecRef's single charge); `MemoryRel` + MM-6 `MemGasSafe` + `CalldataRel` + `CalldataBelow` nested-window separation hypotheses) |
| CODESIZE | 0x38 | `iCodesize` | `execute_codesize` | env | **full** ([`codesize_step_equiv`](../EvmSpecsVerify/Opcodes/Codesize.lean#L217) — success/overflow/OOG/MM-5 double fault; `CodeRel` supplies the `frame_code` register read + length tie (shared with CODECOPY), code-length wf hypothesized) |
| CODECOPY | 0x39 | `iCodecopy` | `execute_codecopy` | memory | **full** ([`codecopy_step_equiv`](../EvmSpecsVerify/Opcodes/Codecopy.lean#L642) — success ×3 (zero size/grow/in-window)/underflow ×3/OOG ×3, the CALLDATACOPY harvest through SpecRef's shared `copyFromBuffer`; `MemoryRel` + MM-6 `MemGasSafe` + `CodeRel` hypotheses — code regions are immutable, so no `CalldataBelow` analogue) |
| GASPRICE | 0x3a | `iGasprice` | `execute_gasprice` | env | **full** ([`gasprice_step_equiv`](../EvmSpecsVerify/Opcodes/Gasprice.lean#L216) — success/overflow/OOG/MM-5 double fault; `k_tx` register tie `hgp` (codec-free), envelope wf hypothesized) |
| EXTCODESIZE | 0x3b | `iExtcodesize` | `execute_extcodesize` | env+world | **full** ([`extcodesize_step_equiv`](../EvmSpecsVerify/Opcodes/Extcodesize.lean#L416) — success warm/cold, underflow, OOG warm/cold; `WarmAddrRel` preserves address warmth, Amsterdam account/code-read gas is proven `200`/`3100`, and the ledgered `ExtcodesizeAgree` ties the account/code-store lookup and length) |
| EXTCODECOPY | 0x3c | `iExtcodecopy` | `execute_extcodecopy` | memory+world | **full** ([`extcodecopy_step_equiv`](../EvmSpecsVerify/Opcodes/Extcodecopy.lean#L935) — underflow ×4, warm/cold access OOG, copy OOG, expansion OOG, and zero/grow/in-window success; `ExternalCodeRel` fixes the exact arbitrary-account bytes and lookup preservation, with `MemoryRel` + MM-6 `MemGasSafe` + `WarmAddrRel`) |
| RETURNDATASIZE | 0x3d | `iReturndatasize` | `execute_returndatasize` | env | **full** ([`returndatasize_step_equiv`](../EvmSpecsVerify/Opcodes/Returndatasize.lean#L210) — success/overflow/OOG/MM-5 double fault; `ReturnDataRel` ties the output-slice length to SpecRef's inline returndata) |
| RETURNDATACOPY | 0x3e | `iReturndatacopy` | `execute_returndatacopy` | memory | **full** ([`returndatacopy_step_equiv`](../EvmSpecsVerify/Opcodes/Returndatacopy.lean#L847) — success ×3/underflow ×3/OOG ×3/out-of-bounds after charging and expansion, including zero-size OOB; `MemoryRel` + MM-6 `MemGasSafe` + `ReturnDataRel`; MM-7 maps SpecRef `outOfBoundsRead` to Sail `InvalidOpcode`) |
| EXTCODEHASH | 0x3f | `iExtcodehash` | `execute_extcodehash` | env+world+crypto | **full** ([`extcodehash_step_equiv`](../EvmSpecsVerify/Opcodes/Extcodehash.lean#L481) — warm/cold success and OOG plus underflow; `WarmAddrRel` proves account-access classification/gas, while ledgered `ExtcodehashAgree` ties missing-account zero and the 32-byte code-hash codec) |
| BLOCKHASH | 0x40 | `iBlockhash` | `execute_blockhash` | env | **full** ([`blockhash_step_equiv`](../EvmSpecsVerify/Opcodes/Blockhash.lean#L363) — success ×2 (in-window hash/out-of-window zero)/underflow/OOG; `AncestorRel` ties the reversed-index witness windows, codec `hash_to_word_eq`; `BlockhashReady` excludes only a reached missing-depth outer abort, while admitting short but sufficient witnesses; see `Assumptions.lean`) |
| COINBASE | 0x41 | `iCoinbase` | `execute_coinbase` | env | **full** ([`coinbase_step_equiv`](../EvmSpecsVerify/Opcodes/BlockEnv.lean#L127) — success/overflow/OOG/MM-5 double fault via `envPush_step_equiv`; header fee-recipient tie, wf via `address_to_word`) |
| TIMESTAMP | 0x42 | `iTimestamp` | `execute_timestamp` | env | **full** ([`timestamp_step_equiv`](../EvmSpecsVerify/Opcodes/BlockEnv.lean#L152) — success/overflow/OOG/MM-5 double fault via `envPush_step_equiv`; header timestamp tie, u64 wf hypothesized) |
| NUMBER | 0x43 | `iNumber` | `execute_number` | env | **full** ([`number_step_equiv`](../EvmSpecsVerify/Opcodes/BlockEnv.lean#L173) — success/overflow/OOG/MM-5 double fault via `envPush_step_equiv`; header number tie, u64 wf hypothesized) |
| PREVRANDAO | 0x44 | `iPrevrandao` | `execute_prevrandao` | env | **full** ([`prevrandao_step_equiv`](../EvmSpecsVerify/Opcodes/BlockEnv.lean#L194) — success/overflow/OOG/MM-5 double fault via `envPush_step_equiv`; randao word ↔ 32-byte decode tie, wf hypothesized) |
| GASLIMIT | 0x45 | `iGaslimit` | `execute_gaslimit` | env | **full** ([`gaslimit_step_equiv`](../EvmSpecsVerify/Opcodes/BlockEnv.lean#L217) — success/overflow/OOG/MM-5 double fault via `envPush_step_equiv`; header gas-limit tie, wf hypothesized) |
| CHAINID | 0x46 | `iChainid` | `execute_chainid` | env | **full** ([`chainid_step_equiv`](../EvmSpecsVerify/Opcodes/BlockEnv.lean#L238) — success/overflow/OOG/MM-5 double fault via `envPush_step_equiv`; `k_chain_id` register tie, u64 wf hypothesized) |
| SELFBALANCE | 0x47 | `iSelfbalance` | `execute_selfbalance` | env+world | **full** ([`selfbalance_step_equiv`](../EvmSpecsVerify/Opcodes/Selfbalance.lean#L248) — success/overflow/OOG/MM-5 double fault; underflow unreachable for 0-in. No warm/cold split: the own account is a flat `5` on both sides, so `SelfBalanceAgree` needs no warm-stamp quantification unlike `BalanceAgree` — see `Assumptions.lean`) |
| BASEFEE | 0x48 | `iBasefee` | `execute_basefee` | env (fork-gated) | **full** ([`basefee_step_equiv`](../EvmSpecsVerify/Opcodes/BlockEnv.lean#L258) — success/overflow/OOG/MM-5 double fault via `envPush_step_equiv`; header base-fee tie, wf hypothesized) |
| BLOBHASH | 0x49 | `iBlobhash` | `execute_blobhash` | env (fork-gated) | **full** ([`blobhash_step_equiv`](../EvmSpecsVerify/Opcodes/Blobhash.lean#L240) — success/underflow/OOG; overflow unreachable for 1-in/1-out. Both sides zero-pad past the end of the versioned-hash list, so one success case covers in- and out-of-range indices with no range hypothesis; `BlobHashAgree` ties SpecRef's `txEnv.blobVersionedHashes` to the extraction's `k_tx` input-slice load) |
| BLOBBASEFEE | 0x4a | `iBlobbasefee` | `execute_blobbasefee` | env (fork-gated) | unstated (needs a fake-exponential bridge: SpecRef's fuelled `taylorAux` vs the extraction's `whileFuelM` `fake_exponential_word` — same recurrence, different fuel and overflow guards; an EXP-sized slice of its own — see `PROGRESS.md`) |
| SLOTNUM | 0x4b | `iSlotnum` | `execute_slotnum` | env (fork-gated) | **full** ([`slotnum_step_equiv`](../EvmSpecsVerify/Opcodes/BlockEnv.lean#L278) — success/overflow/OOG/MM-5 double fault via `envPush_step_equiv`; header slot-number tie, u64 wf hypothesized) |

## Stack / memory / storage / control

| opcode | byte | SpecRef | `Evm` | shape | status |
|---|---|---|---|---|---|
| POP | 0x50 | `iPop` | `execute_pop` | stack | **full** ([`pop_step_equiv`](../EvmSpecsVerify/Opcodes/Pop.lean#L176) — success/underflow/OOG; overflow unreachable: height decreases) |
| MLOAD | 0x51 | `iMload` | `execute_mload` | memory | **full** ([`mload_step_equiv`](../EvmSpecsVerify/Opcodes/Mload.lean#L400) — success (grow/in-window)/underflow/OOG ×2; `MemoryRel` + MM-6 `MemGasSafe` hypotheses) |
| MSTORE | 0x52 | `iMstore` | `execute_mstore` | memory | **full** ([`mstore_step_equiv`](../EvmSpecsVerify/Opcodes/Mstore.lean#L388) — success (grow/in-window)/underflow ×2/OOG ×2; `MemoryRel` + MM-6 `MemGasSafe` hypotheses) |
| MSTORE8 | 0x53 | `iMstore8` | `execute_mstore8` | memory | **full** ([`mstore8_step_equiv`](../EvmSpecsVerify/Opcodes/Mstore8.lean#L396) — success (grow/in-window)/underflow ×2/OOG ×2; `MemoryRel` + MM-6 `MemGasSafe` hypotheses, byte codec `word_low_byte_masked`) |
| SLOAD | 0x54 | `iSload` | `execute_sload` | storage | **full** ([`sload_step_equiv`](../EvmSpecsVerify/Opcodes/Sload.lean#L503) — success (warm/cold)/underflow/OOG ×2; warm-cold accounting and gas proven outright via `WarmRel`, the value read behind the ledgered `SloadAgree` hypothesis — see `Assumptions.lean`) |
| SSTORE | 0x55 | `iSstore` | `execute_sstore` | storage | unstated |
| JUMP | 0x56 | `iJump` | `execute_jump` | control | **full** ([`jump_step_equiv`](../EvmSpecsVerify/Opcodes/Jump.lean#L285) — taken jump/underflow/OOG/invalid destination; the JUMPI harvest through `do_jump` and `JumpdestRel`, sharing `ControlPost`; no fall-through branch, overflow unreachable for 1-in/0-out) |
| JUMPI | 0x57 | `iJumpi` | `execute_jumpi` | control | **full** ([`jumpi_step_equiv`](../EvmSpecsVerify/Opcodes/Jumpi.lean#L501) — fall/jump/underflow/OOG/invalid jump; `JumpdestRel` ties the valid-destination set to the frame jump table) |
| PC | 0x58 | `iPc` | `execute_pc` | env (live-state pusher) | **full** ([`pc_step_equiv`](../EvmSpecsVerify/Opcodes/Pc.lean#L98) — success/overflow/OOG/MM-5 double fault; underflow unreachable for 0-in. The extraction recovers the opcode position as `pc_in - 1` (`alu_sub_one`, no wrap since `pc_in ≥ 1`); domain restricted by `hwfpc : pc_in < 2^256` — see `Assumptions.lean`) |
| MSIZE | 0x59 | `iMsize` | `execute_msize` | env (live-state pusher) + memory | **full** ([`msize_step_equiv`](../EvmSpecsVerify/Opcodes/Msize.lean#L247) — success/overflow/OOG/MM-5 double fault; underflow unreachable for 0-in. SpecRef's raw `memory.length` and the extraction's `32 * memory_word_count (memory_high_water mem)` agree *exactly by* `MemoryRel.aligned` — this is where SpecRef's 32-alignment invariant earns its keep; `MemPost` + MM-6 `MemGasSafe`) |
| GAS | 0x5a | `iGas` | `execute_gas` | env (live-state pusher) | **full** ([`gas_step_equiv`](../EvmSpecsVerify/Opcodes/Gas.lean#L114) — success/overflow/OOG/MM-5 double fault; underflow unreachable for 0-in. Both sides push the *post-charge* gas (`gasLeft - 2`); domain restricted by `hwfg` for the new MM-8 `push_gas` modular reduction — see `Assumptions.lean`) |
| JUMPDEST | 0x5b | `iJumpdest` | `execute_jumpdest` | control | **full** ([`jumpdest_step_equiv`](../EvmSpecsVerify/Opcodes/Jumpdest.lean#L127) — success/OOG; stack faults unreachable for 0-in/0-out) |
| TLOAD | 0x5c | `iTload` | `execute_tload` | storage (transient) | **full** ([`tload_step_equiv`](../EvmSpecsVerify/Opcodes/Tload.lean#L246) — success/underflow/OOG; overflow unreachable for 1-in/1-out. EIP-1153 prices transient access flat on both sides, so `TloadAgree` needs no warm-stamp quantification unlike `SloadAgree`; the read value is behind that ledgered hypothesis — see `Assumptions.lean`) |
| TSTORE | 0x5d | `iTstore` | `execute_tstore` | storage (transient) | unstated (needs a transient-store relation in the post: `BasePost` observes only stack/gas/pc, so a `StepResultRel BasePost` theorem would say nothing about the write — the same prerequisite SSTORE has. Its `writeInStaticContext` ↔ `WriteProtection` path also needs a new `ErrorRel` constructor) |
| MCOPY | 0x5e | `iMcopy` | `execute_mcopy` | memory | **full** ([`mcopy_step_equiv`](../EvmSpecsVerify/Opcodes/Mcopy.lean#L711) — success ×3 (zero length/grow/in-window), underflow ×3, OOG at each of the extraction's three charges; overflow unreachable. Two new pieces: `calc_extend_pair_eq_single` proves SpecRef's two-range extension fold telescopes to the single range at `max destination source`, and `memoryRel_mcopy` (via the new `memoryRel_read`) proves the overlapping-safe copy agrees — both sides snapshot the source before writing, so no disjointness hypothesis is needed. `MemoryRel` + MM-6 `MemGasSafe`) |
| PUSH (n, w) | 0x5f–0x7f | `iPushN` | `execute_push` | stack (immediate via fetch) | **full** ([`push_step_equiv`](../EvmSpecsVerify/Opcodes/Push.lean#L253) — success/overflow/OOG, underflow unreachable; decode-fidelity hypothesis for the fetched immediate (MM-3 scope); MM-5 on double faults) |
| DUP n | 0x80–0x8f | `iDupN` | `execute_dup` | stack | **full** ([`dup_step_equiv`](../EvmSpecsVerify/Opcodes/Dup.lean#L240) — success/underflow/overflow/OOG; MM-5 on double faults) |
| SWAP n | 0x90–0x9f | `iSwapN` | `execute_swap` | stack | **full** ([`swap_step_equiv`](../EvmSpecsVerify/Opcodes/Swap.lean#L338) — success/underflow/OOG/MM-5 double fault; overflow unreachable since the height is unchanged. `take_swap_writes` bridges SpecRef's head-indexed `listSwap S 0 n` to the extraction's two `stack_set` writes at cursor slots 0 and n; index conventions already agree (`iSwapN (op - 0x8F)`)) |
| LOG n | 0xa0–0xa4 | `iLogN` | `execute_log` | memory+logs | **stated** (LOG0 is `full`: [`log0_step_equiv`](../EvmSpecsVerify/Opcodes/Log.lean#L701) — success ×3 (zero size/grow/in-window), underflow ×2, the static halt, OOG at each of the three live charge stages, plus the MM-11 double fault. Targets the new [`LogPost`](../EvmSpecsVerify/Relations/Log.lean) = `MemPost` ∧ `LogRel`. LOG1–LOG4 pending: `pop_log_topics` matches on `n` and SpecRef's `mapM` unrolls per `n`, so each arity carries its own outcome set — a `Shapes/Log.lean` harvest, see `PROGRESS.md`) |
| DUPN | 0xe6 | `iDupn` | `execute_dupn` | stack (fork-gated, immediate) | **full** ([`dupn_step_equiv`](../EvmSpecsVerify/Opcodes/Dupn.lean#L487) — success, invalid immediate, underflow, overflow, OOG, plus the MM-5 and MM-10 double faults. First opcode with an immediate-validity outcome: `decode_single_agree` proves SpecRef's `(x + 145) % 256` and the extraction's two-branch `x + 145` / `x - 111` are the same decoder, MM-10 records the `.invalidParameter`/`InvalidOpcode` kind split and the decode/charge order, and the ledgered `himm` ties the immediate byte across the MM-3 dispatch boundary) |
| SWAPN | 0xe7 | `iSwapn` | `execute_swapn` | stack (fork-gated, immediate) | **full** ([`swapn_step_equiv`](../EvmSpecsVerify/Opcodes/Swapn.lean#L343) — success, invalid immediate, underflow, OOG, plus the MM-5 and MM-10 double faults; overflow unreachable (height-preserving, `opcode_stack_effect = (n+1, n+1)`). A harvest in both directions: the decoder from DUPN (`decode_single` is shared), the permutation from SWAP (`take_swap_writes`, `listSwap_mem`, `swapHost`) — `execute_swapn`'s tail is `execute_swap`'s) |
| EXCHANGE | 0xe8 | `iExchange` | `execute_exchange` | stack (fork-gated, immediate) | **full** ([`exchange_step_equiv`](../EvmSpecsVerify/Opcodes/Exchange.lean#L463) — success, invalid immediate, underflow, OOG, plus the MM-5 and MM-10 double faults; overflow unreachable. The `decode_pair` bridge is two byte-exhaustive `decide`s over the nibble split (SpecRef divides/mods by 16, the extraction slices bits `[7:4]`/`[3:0]`), plus `exchangePair_lt` proving the decoder's second component is the larger — which is what makes SpecRef's `max n m` guard and the extraction's `higher` guard agree. Motivated generalizing `take_swap_writes` / `listSwap_getElem?` / `listSwap_mem` from `(0, n)` to arbitrary `(i, j)`) |

## System

| opcode | byte | SpecRef | `Evm` | shape | status |
|---|---|---|---|---|---|
| CREATE | 0xf0 | `iCreate` *(partial)* | `execute_create` | system | unstated |
| CALL | 0xf1 | `iCall` *(partial)* | `execute_call` | system | unstated |
| CALLCODE | 0xf2 | `iCallcode` *(partial)* | `execute_callcode` | system | unstated |
| RETURN | 0xf3 | `iReturn` | `execute_return` | system | **full** ([`return_step_equiv`](../EvmSpecsVerify/Opcodes/Return.lean#L565) — normal halt with output correspondence (`ReturnPost`), zero/grow/in-window reads, underflow ×2, expansion OOG) |
| DELEGATECALL | 0xf4 | `iDelegatecall` *(partial)* | `execute_delegatecall` | system | unstated |
| CREATE2 | 0xf5 | `iCreate2` *(partial)* | `execute_create2` | system | unstated |
| STATICCALL | 0xfa | `iStaticcall` *(partial)* | `execute_staticcall` | system | unstated |
| REVERT | 0xfd | `iRevert` | `execute_revert` | system | **full** ([`revert_step_equiv`](../EvmSpecsVerify/Opcodes/Revert.lean#L521) — revert with output correspondence (`RevertPost`), zero/grow/in-window reads, underflow ×2, expansion OOG. Targets [`RevertResultRel`](../EvmSpecsVerify/Relations/Outcome.lean#L110), not `StepResultRel`: `.revert` is not an exceptional halt, so the gas survives. New MM-9 records the state-gas refill's layer, proven equal to SpecRef's own `refill_frame_state_gas` via `runR_refill`) |
| INVALID | 0xfe | (dispatch throws `.invalidOpcode`) | `execute_invalid` | system | unstated |
| SELFDESTRUCT | 0xff | `iSelfdestruct` | `execute_selfdestruct` | system+world | unstated |

## Counts (checked against the rows above by the refresh script)

| status | count |
|---|---|
| full | 75 |
| stated | 1 |
| unstated | 11 |
| n/a (opaque keccak) | 1 |
| **total ast constructors** | **88** |
