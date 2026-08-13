# Opcode coverage matrix

One row per constructor of the `Evm` extraction's instruction AST
(`Evm.Defs.ast`, Defs.lean:2672 — 90 constructors), cross-referenced with SpecRef's
handlers. Machine-checked counts live in `EvmAsmSail/Coverage/Registry.lean` and must
match this table.

Statuses: `unstated` · `stated` (theorem exists, may cite pending lemmas) ·
`success-proven` (success path only — not acceptable as final) ·
`full` (full `StepResultRel`: success + every reachable failure) · `n/a` (+ reason).

SpecRef handlers marked *(partial)* live in the `partial def mutual` block
(Interpreter.lean:314) and are dispatch-inaccessible to proofs until upstream
de-partials; their rows can only be `stated` against the handler bodies once those
are total.

## Shape classes

- **binop**: `charge → pop ×2 → alu → push` on both sides (SpecRef `binOp`, Evm `execute_<op>`)
- **unop**: 1-in/1-out analogue
- **ternop**: 3-in/1-out (ADDMOD, MULMOD)
- **stack**: pure stack manipulation (POP/PUSH/DUP/SWAP/…)
- **memory / control / env / storage / system**: as named

## ALU family

| opcode | byte | SpecRef | `Evm` | shape | status |
|---|---|---|---|---|---|
| STOP | 0x00 | `iStop` | `execute_stop` | system | unstated |
| ADD | 0x01 | `iAdd` | `execute_add` | binop | **full** (`add_step_equiv`, EvmAsmSail/Opcodes/Add.lean — success/underflow/OOG; overflow unreachable for 2-in/1-out) |
| MUL | 0x02 | `iMul` | `execute_mul` | binop | **full** (`mul_step_equiv`, EvmAsmSail/Opcodes/Mul.lean — success/underflow/OOG; overflow unreachable) |
| SUB | 0x03 | `iSub` | `execute_sub` | binop | **full** (`sub_step_equiv`, EvmAsmSail/Opcodes/Sub.lean — success/underflow/OOG; overflow unreachable) |
| DIV | 0x04 | `iDiv` | `execute_div` | binop | **full** (`div_step_equiv`, EvmAsmSail/Opcodes/Div.lean — success/underflow/OOG; overflow unreachable) |
| SDIV | 0x05 | `iSdiv` | `execute_sdiv` | binop | **full** (`sdiv_step_equiv`, EvmAsmSail/Opcodes/Sdiv.lean — success/underflow/OOG; overflow unreachable) |
| MOD | 0x06 | `iMod` | `execute_mod` | binop | **full** (`mod_step_equiv`, EvmAsmSail/Opcodes/Mod.lean — success/underflow/OOG; overflow unreachable) |
| SMOD | 0x07 | `iSmod` | `execute_smod` | binop | **full** (`smod_step_equiv`, EvmAsmSail/Opcodes/Smod.lean — success/underflow/OOG; overflow unreachable) |
| ADDMOD | 0x08 | `iAddmod` | `execute_addmod` | ternop | unstated |
| MULMOD | 0x09 | `iMulmod` | `execute_mulmod` | ternop | unstated |
| EXP | 0x0a | `iExp` | `execute_exp` | binop (dyn gas, fuelled pow) | unstated |
| SIGNEXTEND | 0x0b | `iSignextend` | `execute_signextend` | binop | **full** (`signextend_step_equiv`, EvmAsmSail/Opcodes/Signextend.lean — success/underflow/OOG; overflow unreachable) |
| LT | 0x10 | `iLt` | `execute_lt` | binop | **full** (`lt_step_equiv`, EvmAsmSail/Opcodes/Lt.lean — success/underflow/OOG; overflow unreachable) |
| GT | 0x11 | `iGt` | `execute_gt` | binop | **full** (`gt_step_equiv`, EvmAsmSail/Opcodes/Gt.lean — success/underflow/OOG; overflow unreachable) |
| SLT | 0x12 | `iSlt` | `execute_slt` | binop | **full** (`slt_step_equiv`, EvmAsmSail/Opcodes/Slt.lean — success/underflow/OOG; overflow unreachable) |
| SGT | 0x13 | `iSgt` | `execute_sgt` | binop | **full** (`sgt_step_equiv`, EvmAsmSail/Opcodes/Sgt.lean — success/underflow/OOG; overflow unreachable) |
| EQ | 0x14 | `iEq` | `execute_eq` | binop | **full** (`eq_step_equiv`, EvmAsmSail/Opcodes/Eq.lean — success/underflow/OOG; overflow unreachable) |
| ISZERO | 0x15 | `iIszero` | `execute_iszero` | unop | **full** (`iszero_step_equiv`, EvmAsmSail/Opcodes/Iszero.lean — success/underflow/OOG; overflow unreachable for 1-in/1-out) |
| AND | 0x16 | `iAnd` | `execute_and` | binop | **full** (`and_step_equiv`, EvmAsmSail/Opcodes/And.lean — success/underflow/OOG; overflow unreachable) |
| OR | 0x17 | `iOr` | `execute_or` | binop | **full** (`or_step_equiv`, EvmAsmSail/Opcodes/Or.lean — success/underflow/OOG; overflow unreachable) |
| XOR | 0x18 | `iXor` | `execute_xor` | binop | **full** (`xor_step_equiv`, EvmAsmSail/Opcodes/Xor.lean — success/underflow/OOG; overflow unreachable) |
| NOT | 0x19 | `iNot` | `execute_not` | unop | unstated |
| BYTE | 0x1a | `iByte` | `execute_byte` | binop | **full** (`byte_step_equiv`, EvmAsmSail/Opcodes/Byte.lean — success/underflow/OOG; overflow unreachable) |
| SHL | 0x1b | `iShl` | `execute_shl` | binop | **full** (`shl_step_equiv`, EvmAsmSail/Opcodes/Shl.lean — success/underflow/OOG; overflow unreachable) |
| SHR | 0x1c | `iShr` | `execute_shr` | binop | **full** (`shr_step_equiv`, EvmAsmSail/Opcodes/Shr.lean — success/underflow/OOG; overflow unreachable) |
| SAR | 0x1d | `iSar` | `execute_sar` | binop | **full** (`sar_step_equiv`, EvmAsmSail/Opcodes/Sar.lean — success/underflow/OOG; overflow unreachable) |
| CLZ | 0x1e | `iClz` | `execute_clz` | unop (fork-gated ≥ Osaka) | unstated |

## Hashing

| opcode | byte | SpecRef | `Evm` | shape | status |
|---|---|---|---|---|---|
| KECCAK256 | 0x20 | `iKeccak` | `execute_keccak256` | memory+crypto | n/a this tranche (opaque keccak) |

## Environment / block

| opcode | byte | SpecRef | `Evm` | shape | status |
|---|---|---|---|---|---|
| ADDRESS | 0x30 | `iAddress` | `execute_address` | env | unstated |
| BALANCE | 0x31 | `iBalance` | `execute_balance` | env+world | unstated |
| ORIGIN | 0x32 | `iOrigin` | `execute_origin` | env | unstated |
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
| POP | 0x50 | `iPop` | `execute_pop` | stack | unstated |
| MLOAD | 0x51 | `iMload` | `execute_mload` | memory | unstated |
| MSTORE | 0x52 | `iMstore` | `execute_mstore` | memory | unstated |
| MSTORE8 | 0x53 | `iMstore8` | `execute_mstore8` | memory | unstated |
| SLOAD | 0x54 | `iSload` | `execute_sload` | storage | unstated |
| SSTORE | 0x55 | `iSstore` | `execute_sstore` | storage | unstated |
| JUMP | 0x56 | `iJump` | `execute_jump` | control | unstated |
| JUMPI | 0x57 | `iJumpi` | `execute_jumpi` | control | unstated |
| PC | 0x58 | `iPc` | `execute_pc` | env | unstated |
| MSIZE | 0x59 | `iMsize` | `execute_msize` | env | unstated |
| GAS | 0x5a | `iGas` | `execute_gas` | env | unstated |
| JUMPDEST | 0x5b | `iJumpdest` | `execute_jumpdest` | control | unstated |
| TLOAD | 0x5c | `iTload` | `execute_tload` | storage (transient) | unstated |
| TSTORE | 0x5d | `iTstore` | `execute_tstore` | storage (transient) | unstated |
| MCOPY | 0x5e | `iMcopy` | `execute_mcopy` | memory | unstated |
| PUSH (n, w) | 0x5f–0x7f | `iPushN` | `execute_push` | stack (immediate via fetch) | unstated |
| DUP n | 0x80–0x8f | `iDupN` | `execute_dup` | stack | unstated |
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
| RETURN | 0xf3 | `iReturn` | `execute_return` | system | unstated |
| DELEGATECALL | 0xf4 | `iDelegatecall` *(partial)* | `execute_delegatecall` | system | unstated |
| CREATE2 | 0xf5 | `iCreate2` *(partial)* | `execute_create2` | system | unstated |
| STATICCALL | 0xfa | `iStaticcall` *(partial)* | `execute_staticcall` | system | unstated |
| REVERT | 0xfd | `iRevert` | `execute_revert` | system | unstated |
| INVALID | 0xfe | (dispatch throws `.invalidOpcode`) | `execute_invalid` | system | unstated |
| SELFDESTRUCT | 0xff | `iSelfdestruct` | `execute_selfdestruct` | system+world | unstated |

## Counts (must match `EvmAsmSail/Coverage/Registry.lean`)

| status | count |
|---|---|
| full | 21 |
| unstated | 68 |
| n/a (opaque keccak) | 1 |
| **total ast constructors** | **90** |
