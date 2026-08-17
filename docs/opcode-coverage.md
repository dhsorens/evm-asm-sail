# Opcode coverage matrix

One row per constructor of the `Evm` extraction's instruction AST
(`Evm.Defs.ast`, Defs.lean:2672 — 90 constructors), cross-referenced with SpecRef's
handlers. Machine-checked counts live in `EvmSpecsVerify/Coverage/Registry.lean` and must
match this table.

Statuses: `unstated` · `stated` (theorem exists, may cite pending lemmas) ·
`success-proven` (success path only — not acceptable as final) ·
`full` (full `StepResultRel`: success + every reachable failure) · `n/a` (+ reason).
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
| CALLER | 0x33 | `iCaller` | `execute_caller` | env | unstated |
| CALLVALUE | 0x34 | `iCallvalue` | `execute_callvalue` | env | unstated |
| CALLDATALOAD | 0x35 | `iCalldataload` | `execute_calldataload` | env+memory | unstated |
| CALLDATASIZE | 0x36 | `iCalldatasize` | `execute_calldatasize` | env | unstated |
| CALLDATACOPY | 0x37 | `iCalldatacopy` | `execute_calldatacopy` | memory | unstated |
| CODESIZE | 0x38 | `iCodesize` | `execute_codesize` | env | unstated |
| CODECOPY | 0x39 | `iCodecopy` | `execute_codecopy` | memory | unstated |
| GASPRICE | 0x3a | `iGasprice` | `execute_gasprice` | env | unstated |
| EXTCODESIZE | 0x3b | `iExtcodesize` | `execute_extcodesize` | env+world | unstated |
| EXTCODECOPY | 0x3c | `iExtcodecopy` | `execute_extcodecopy` | memory+world | unstated |
| RETURNDATASIZE | 0x3d | `iReturndatasize` | `execute_returndatasize` | env | unstated |
| RETURNDATACOPY | 0x3e | `iReturndatacopy` | `execute_returndatacopy` | memory | unstated |
| EXTCODEHASH | 0x3f | `iExtcodehash` | `execute_extcodehash` | env+world+crypto | unstated |
| BLOCKHASH | 0x40 | `iBlockhash` | `execute_blockhash` | env | unstated |
| COINBASE | 0x41 | `iCoinbase` | `execute_coinbase` | env | unstated |
| TIMESTAMP | 0x42 | `iTimestamp` | `execute_timestamp` | env | unstated |
| NUMBER | 0x43 | `iNumber` | `execute_number` | env | unstated |
| PREVRANDAO | 0x44 | `iPrevrandao` | `execute_prevrandao` | env | unstated |
| GASLIMIT | 0x45 | `iGaslimit` | `execute_gaslimit` | env | unstated |
| CHAINID | 0x46 | `iChainid` | `execute_chainid` | env | unstated |
| SELFBALANCE | 0x47 | `iSelfbalance` | `execute_selfbalance` | env+world | unstated |
| BASEFEE | 0x48 | `iBasefee` | `execute_basefee` | env (fork-gated) | unstated |
| BLOBHASH | 0x49 | `iBlobhash` | `execute_blobhash` | env (fork-gated) | unstated |
| BLOBBASEFEE | 0x4a | `iBlobbasefee` | `execute_blobbasefee` | env (fork-gated) | unstated |
| SLOTNUM | 0x4b | `iSlotnum` | `execute_slotnum` | env (fork-gated) | unstated |

## Stack / memory / storage / control

| opcode | byte | SpecRef | `Evm` | shape | status |
|---|---|---|---|---|---|
| POP | 0x50 | `iPop` | `execute_pop` | stack | **full** ([`pop_step_equiv`](../EvmSpecsVerify/Opcodes/Pop.lean#L176) — success/underflow/OOG; overflow unreachable: height decreases) |
| MLOAD | 0x51 | `iMload` | `execute_mload` | memory | **full** ([`mload_step_equiv`](../EvmSpecsVerify/Opcodes/Mload.lean#L400) — success (grow/in-window)/underflow/OOG ×2; `MemoryRel` + MM-6 `MemGasSafe` hypotheses) |
| MSTORE | 0x52 | `iMstore` | `execute_mstore` | memory | **full** ([`mstore_step_equiv`](../EvmSpecsVerify/Opcodes/Mstore.lean#L388) — success (grow/in-window)/underflow ×2/OOG ×2; `MemoryRel` + MM-6 `MemGasSafe` hypotheses) |
| MSTORE8 | 0x53 | `iMstore8` | `execute_mstore8` | memory | unstated |
| SLOAD | 0x54 | `iSload` | `execute_sload` | storage | **full** ([`sload_step_equiv`](../EvmSpecsVerify/Opcodes/Sload.lean#L503) — success (warm/cold)/underflow/OOG ×2; warm-cold accounting and gas proven outright via `WarmRel`, the value read behind the ledgered `SloadAgree` hypothesis — see `Assumptions.lean`) |
| SSTORE | 0x55 | `iSstore` | `execute_sstore` | storage | unstated |
| JUMP | 0x56 | `iJump` | `execute_jump` | control | unstated |
| JUMPI | 0x57 | `iJumpi` | `execute_jumpi` | control | **full** ([`jumpi_step_equiv`](../EvmSpecsVerify/Opcodes/Jumpi.lean#L499) — fall/jump/underflow/OOG/invalid jump; `JumpdestRel` ties the valid-destination set to the frame jump table) |
| PC | 0x58 | `iPc` | `execute_pc` | env | unstated |
| MSIZE | 0x59 | `iMsize` | `execute_msize` | env | unstated |
| GAS | 0x5a | `iGas` | `execute_gas` | env | unstated |
| JUMPDEST | 0x5b | `iJumpdest` | `execute_jumpdest` | control | unstated |
| TLOAD | 0x5c | `iTload` | `execute_tload` | storage (transient) | unstated |
| TSTORE | 0x5d | `iTstore` | `execute_tstore` | storage (transient) | unstated |
| MCOPY | 0x5e | `iMcopy` | `execute_mcopy` | memory | unstated |
| PUSH (n, w) | 0x5f–0x7f | `iPushN` | `execute_push` | stack (immediate via fetch) | **full** ([`push_step_equiv`](../EvmSpecsVerify/Opcodes/Push.lean#L253) — success/overflow/OOG, underflow unreachable; decode-fidelity hypothesis for the fetched immediate (MM-3 scope); MM-5 on double faults) |
| DUP n | 0x80–0x8f | `iDupN` | `execute_dup` | stack | **full** ([`dup_step_equiv`](../EvmSpecsVerify/Opcodes/Dup.lean#L240) — success/underflow/overflow/OOG; MM-5 on double faults) |
| SWAP n | 0x90–0x9f | `iSwapN` | `execute_swap` | stack | unstated |
| LOG n | 0xa0–0xa4 | `iLogN` | `execute_log` | memory+logs | unstated |
| DUPN | 0xe6 | `iDupn` | `execute_dupn` | stack (fork-gated, immediate) | unstated |
| SWAPN | 0xe7 | `iSwapn` | `execute_swapn` | stack (fork-gated, immediate) | unstated |
| EXCHANGE | 0xe8 | `iExchange` | `execute_exchange` | stack (fork-gated, immediate) | unstated |

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
| REVERT | 0xfd | `iRevert` | `execute_revert` | system | unstated |
| INVALID | 0xfe | (dispatch throws `.invalidOpcode`) | `execute_invalid` | system | unstated |
| SELFDESTRUCT | 0xff | `iSelfdestruct` | `execute_selfdestruct` | system+world | unstated |

## Counts (must match `EvmSpecsVerify/Coverage/Registry.lean`)

| status | count |
|---|---|
| full | 38 |
| unstated | 51 |
| n/a (opaque keccak) | 1 |
| **total ast constructors** | **90** |
