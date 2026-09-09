import Evm

/-!
# The coverage registry

`docs/opcode-coverage.md` is the source of truth for what the comparison
proves, and `scripts/refresh-proof-coverage-canvas.py` already checks its
Counts table against its own rows. Neither can say anything about the
thing being counted: markdown cannot notice a constructor of
`Evm.Defs.ast` that has no row at all, and a re-extraction that adds or
renames one would leave both the table and the row list quietly
incomplete.

This file states the classification in Lean instead, where the totality
checker enforces what the table cannot:

* `astStatus` is a **total** function on `Evm.Defs.ast`. Every
  constructor is classified or the file does not compile. A constructor
  added upstream breaks the build here rather than going unnoticed.
* `astCtors` lists one representative per constructor, and
  `astCtors_map_idx` / `astCtors_getElem_idx` prove it is exactly that —
  see their docstrings for why the pair is airtight.
* The counts are **computed** from that list (`astStatusCount`), so the
  numbers in the docs table are checked against a definition rather than
  against a second transcription of themselves.

What this does **not** claim. A `full` entry records the row's status, not
its proof: the artifact discharging each row is the theorem linked from
the status column, and `check_anchors` in the refresh script is what keeps
those links pointing at real declarations. Seeding the entries from the
doc rows makes the initial agreement tautological; the value is that the
two artifacts cannot drift afterwards, which is the same bargain
`check_counts` already makes inside the markdown.

The row order was checked against `Defs.lean`'s constructor order when
this file was written: the 88 rows are in 1:1 constructor order, the only
spelling difference being the row `CREATE` for the constructor
`opcode_CREATE`.
-/

namespace EvmSpecsVerify.Coverage

open Evm.Defs (ast)

/-- The status kinds `docs/opcode-coverage.md` defines. All five are here,
including the two with no rows today: `astStatusCount .successProven = 0`
is the machine-checked form of that document's rule that a success-only
row "is not acceptable as final". -/
inductive Status where
  /-- Full `StepResultRel` — success and every reachable failure — or
  `RevertResultRel` for a revert-capable handler. -/
  | full
  /-- A theorem exists but cites pending lemmas. -/
  | stated
  /-- Success path only. Never a final status. -/
  | successProven
  /-- No theorem yet. -/
  | unstated
  /-- `KECCAK256`, behind the opaque-hash axiom shared by both sides. -/
  | naOpaqueHash
  deriving DecidableEq, Repr

/-- The constructor's position in `Evm.Defs.ast`. A total match, so every
constructor gets an index, and the 88 right-hand sides are literals — that
the assignment is injective is visible here and *proven* by
`astCtors_map_idx`. -/
def astCtorIdx : ast → Nat
  | .STOP _ => 0
  | .ADD _ => 1
  | .MUL _ => 2
  | .SUB _ => 3
  | .DIV _ => 4
  | .SDIV _ => 5
  | .MOD _ => 6
  | .SMOD _ => 7
  | .ADDMOD _ => 8
  | .MULMOD _ => 9
  | .EXP _ => 10
  | .SIGNEXTEND _ => 11
  | .LT _ => 12
  | .GT _ => 13
  | .SLT _ => 14
  | .SGT _ => 15
  | .EQ _ => 16
  | .ISZERO _ => 17
  | .AND _ => 18
  | .OR _ => 19
  | .XOR _ => 20
  | .NOT _ => 21
  | .BYTE _ => 22
  | .SHL _ => 23
  | .SHR _ => 24
  | .SAR _ => 25
  | .CLZ _ => 26
  | .KECCAK256 _ => 27
  | .ADDRESS _ => 28
  | .BALANCE _ => 29
  | .ORIGIN _ => 30
  | .CALLER _ => 31
  | .CALLVALUE _ => 32
  | .CALLDATALOAD _ => 33
  | .CALLDATASIZE _ => 34
  | .CALLDATACOPY _ => 35
  | .CODESIZE _ => 36
  | .CODECOPY _ => 37
  | .GASPRICE _ => 38
  | .EXTCODESIZE _ => 39
  | .EXTCODECOPY _ => 40
  | .RETURNDATASIZE _ => 41
  | .RETURNDATACOPY _ => 42
  | .EXTCODEHASH _ => 43
  | .BLOCKHASH _ => 44
  | .COINBASE _ => 45
  | .TIMESTAMP _ => 46
  | .NUMBER _ => 47
  | .PREVRANDAO _ => 48
  | .GASLIMIT _ => 49
  | .CHAINID _ => 50
  | .SELFBALANCE _ => 51
  | .BASEFEE _ => 52
  | .BLOBHASH _ => 53
  | .BLOBBASEFEE _ => 54
  | .SLOTNUM _ => 55
  | .POP _ => 56
  | .MLOAD _ => 57
  | .MSTORE _ => 58
  | .MSTORE8 _ => 59
  | .SLOAD _ => 60
  | .SSTORE _ => 61
  | .JUMP _ => 62
  | .JUMPI _ => 63
  | .PC _ => 64
  | .MSIZE _ => 65
  | .GAS _ => 66
  | .JUMPDEST _ => 67
  | .TLOAD _ => 68
  | .TSTORE _ => 69
  | .MCOPY _ => 70
  | .PUSH _ => 71
  | .DUP _ => 72
  | .SWAP _ => 73
  | .LOG _ => 74
  | .DUPN _ => 75
  | .SWAPN _ => 76
  | .EXCHANGE _ => 77
  | .opcode_CREATE _ => 78
  | .CALL _ => 79
  | .CALLCODE _ => 80
  | .RETURN _ => 81
  | .DELEGATECALL _ => 82
  | .CREATE2 _ => 83
  | .STATICCALL _ => 84
  | .REVERT _ => 85
  | .INVALID _ => 86
  | .SELFDESTRUCT _ => 87

/-- What the comparison proves about each constructor, mirroring the row
statuses in `docs/opcode-coverage.md`. Total by construction: a
constructor added upstream fails to compile here. -/
def astStatus : ast → Status
  | .STOP _ => .full
  | .ADD _ => .full
  | .MUL _ => .full
  | .SUB _ => .full
  | .DIV _ => .full
  | .SDIV _ => .full
  | .MOD _ => .full
  | .SMOD _ => .full
  | .ADDMOD _ => .full
  | .MULMOD _ => .full
  | .EXP _ => .full
  | .SIGNEXTEND _ => .full
  | .LT _ => .full
  | .GT _ => .full
  | .SLT _ => .full
  | .SGT _ => .full
  | .EQ _ => .full
  | .ISZERO _ => .full
  | .AND _ => .full
  | .OR _ => .full
  | .XOR _ => .full
  | .NOT _ => .full
  | .BYTE _ => .full
  | .SHL _ => .full
  | .SHR _ => .full
  | .SAR _ => .full
  | .CLZ _ => .full
  | .KECCAK256 _ => .naOpaqueHash
  | .ADDRESS _ => .full
  | .BALANCE _ => .full
  | .ORIGIN _ => .full
  | .CALLER _ => .full
  | .CALLVALUE _ => .full
  | .CALLDATALOAD _ => .full
  | .CALLDATASIZE _ => .full
  | .CALLDATACOPY _ => .full
  | .CODESIZE _ => .full
  | .CODECOPY _ => .full
  | .GASPRICE _ => .full
  | .EXTCODESIZE _ => .full
  | .EXTCODECOPY _ => .full
  | .RETURNDATASIZE _ => .full
  | .RETURNDATACOPY _ => .full
  | .EXTCODEHASH _ => .full
  | .BLOCKHASH _ => .full
  | .COINBASE _ => .full
  | .TIMESTAMP _ => .full
  | .NUMBER _ => .full
  | .PREVRANDAO _ => .full
  | .GASLIMIT _ => .full
  | .CHAINID _ => .full
  | .SELFBALANCE _ => .full
  | .BASEFEE _ => .full
  | .BLOBHASH _ => .full
  | .BLOBBASEFEE _ => .full
  | .SLOTNUM _ => .full
  | .POP _ => .full
  | .MLOAD _ => .full
  | .MSTORE _ => .full
  | .MSTORE8 _ => .full
  | .SLOAD _ => .full
  | .SSTORE _ => .full
  | .JUMP _ => .full
  | .JUMPI _ => .full
  | .PC _ => .full
  | .MSIZE _ => .full
  | .GAS _ => .full
  | .JUMPDEST _ => .full
  | .TLOAD _ => .full
  | .TSTORE _ => .full
  | .MCOPY _ => .full
  | .PUSH _ => .full
  | .DUP _ => .full
  | .SWAP _ => .full
  | .LOG _ => .full
  | .DUPN _ => .full
  | .SWAPN _ => .full
  | .EXCHANGE _ => .full
  | .opcode_CREATE _ => .unstated
  | .CALL _ => .unstated
  | .CALLCODE _ => .unstated
  | .RETURN _ => .full
  | .DELEGATECALL _ => .unstated
  | .CREATE2 _ => .unstated
  | .STATICCALL _ => .unstated
  | .REVERT _ => .full
  | .INVALID _ => .full
  | .SELFDESTRUCT _ => .full

/-- One value per `ast` constructor, in declaration order. Payloads are
irrelevant to the status (`PUSH n` is `full` for every width), so each
entry carries a placeholder; `astStatus` matches the payload with `_` to
make that independence syntactic rather than a claim. -/
def astCtors : List ast :=
  [ .STOP (),
   .ADD (),
   .MUL (),
   .SUB (),
   .DIV (),
   .SDIV (),
   .MOD (),
   .SMOD (),
   .ADDMOD (),
   .MULMOD (),
   .EXP (),
   .SIGNEXTEND (),
   .LT (),
   .GT (),
   .SLT (),
   .SGT (),
   .EQ (),
   .ISZERO (),
   .AND (),
   .OR (),
   .XOR (),
   .NOT (),
   .BYTE (),
   .SHL (),
   .SHR (),
   .SAR (),
   .CLZ (),
   .KECCAK256 (),
   .ADDRESS (),
   .BALANCE (),
   .ORIGIN (),
   .CALLER (),
   .CALLVALUE (),
   .CALLDATALOAD (),
   .CALLDATASIZE (),
   .CALLDATACOPY (),
   .CODESIZE (),
   .CODECOPY (),
   .GASPRICE (),
   .EXTCODESIZE (),
   .EXTCODECOPY (),
   .RETURNDATASIZE (),
   .RETURNDATACOPY (),
   .EXTCODEHASH (),
   .BLOCKHASH (),
   .COINBASE (),
   .TIMESTAMP (),
   .NUMBER (),
   .PREVRANDAO (),
   .GASLIMIT (),
   .CHAINID (),
   .SELFBALANCE (),
   .BASEFEE (),
   .BLOBHASH (),
   .BLOBBASEFEE (),
   .SLOTNUM (),
   .POP (),
   .MLOAD (),
   .MSTORE (),
   .MSTORE8 (),
   .SLOAD (),
   .SSTORE (),
   .JUMP (),
   .JUMPI (),
   .PC (),
   .MSIZE (),
   .GAS (),
   .JUMPDEST (),
   .TLOAD (),
   .TSTORE (),
   .MCOPY (),
   .PUSH (0, 0),
   .DUP 0,
   .SWAP 0,
   .LOG 0,
   .DUPN (0 : Evm.Defs.byte),
   .SWAPN (0 : Evm.Defs.byte),
   .EXCHANGE (0 : Evm.Defs.byte),
   .opcode_CREATE (),
   .CALL (),
   .CALLCODE (),
   .RETURN (),
   .DELEGATECALL (),
   .CREATE2 (),
   .STATICCALL (),
   .REVERT (),
   .INVALID (),
   .SELFDESTRUCT ()]

/-- **`astCtors` hits each constructor exactly once, and misses none.**
The entry at position `i` has index `i`, for `i` running over `0 .. 87`:
88 entries carrying 88 distinct indices. With `astCtors_getElem_idx` —
every `ast` value's own index selects an entry of its own status — this
pins the list down as a complete, duplicate-free set of representatives,
which is what makes the counts below counts over *constructors*. -/
theorem astCtors_map_idx : astCtors.map astCtorIdx = List.range 88 := by
  rfl

/-- **Every value is represented at its own index.** Together with
`astCtors_map_idx`: no constructor is absent from the list, and none is
listed twice. -/
theorem astCtors_getElem_idx (a : ast) :
    (astCtors[astCtorIdx a]?).map astStatus = some (astStatus a) := by
  cases a <;> rfl

/-- 88 entries, matching `Defs.lean`'s constructor count. -/
theorem astCtors_length : astCtors.length = 88 := by rfl

/-! ## The counts

`decide`-free: every statement below is a closed computation, so `rfl`
evaluates it. -/

/-- How many constructors carry a given status. -/
def astStatusCount (s : Status) : Nat :=
  astCtors.countP (fun a => astStatus a = s)

/-- 81 of the 88 constructors have a full-outcome step theorem. -/
theorem astStatusCount_full : astStatusCount .full = 81 := by rfl

/-- The six `unstated` constructors are the CREATE/CALL family, whose
SpecRef handlers are `partial def` (MM-3). -/
theorem astStatusCount_unstated : astStatusCount .unstated = 6 := by rfl

/-- `KECCAK256` alone. -/
theorem astStatusCount_naOpaqueHash : astStatusCount .naOpaqueHash = 1 := by
  rfl

/-- No row cites pending lemmas. -/
theorem astStatusCount_stated : astStatusCount .stated = 0 := by rfl

/-- **No row is success-only.** `docs/opcode-coverage.md` calls that status
"not acceptable as final"; this is the checked form of the rule. -/
theorem astStatusCount_successProven : astStatusCount .successProven = 0 := by
  rfl

/-- The five kinds exhaust the AST: the counts sum to every constructor,
so nothing is classified twice and nothing is left over. -/
theorem astStatusCount_sum :
    astStatusCount .full + astStatusCount .stated
        + astStatusCount .successProven + astStatusCount .unstated
        + astStatusCount .naOpaqueHash
      = astCtors.length := by
  rfl

end EvmSpecsVerify.Coverage
