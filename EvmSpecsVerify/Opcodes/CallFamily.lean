import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# The CALL/CREATE family — the extraction's half

The six frame-entering opcodes are the only rows left `unstated`, and
they are blocked on **SpecRef's** side: `iCreate` (:612), `iCreate2`
(:628), `iCall` (:703), `iCallcode` (:764), `iDelegatecall` (:817) and
`iStaticcall` (:859) are all `partial def`, so there is no equation to
run and nothing to state a `StepResultRel` against. That is MM-3, and it
is the *handlers* being partial rather than the dispatch match — the
distinction INVALID separated.

The extraction's half is not blocked: `run_call`, `run_create` and the
six `execute_*` wrappers are total. This file lands the layer above them,
which is what the eventual pairing will sit on and what makes the
blocker per-opcode rather than a class-wide hand-wave:

* the six wrappers reduce to **two** runners plus a kind tag;
* the kind tag's meaning is a five-field record (`call_semantics`), and
  the flags are given here as equations over *all* kinds rather than four
  restatements;
* the stack effects, which are all each of the six needs to have its
  underflow outcome in one application of `runS_execute_underflow` —
  that lemma is generic in the opcode because `execute`'s failure path
  is, so no per-opcode restatement is added here.

What is **not** claimed: nothing here pairs anything with SpecRef, and
the coverage rows stay `unstated`. Two cross-checks against SpecRef were
made by reading, and they are recorded rather than proven because a
`partial def` cannot be run:

1. **The pop counts agree, one for one.** `opcode_stack_effect` gives
   `(3,1)` `(4,1)` `(7,1)` `(7,1)` `(6,1)` `(6,1)` for
   CREATE/CREATE2/CALL/CALLCODE/DELEGATECALL/STATICCALL, and the SpecRef
   handlers contain exactly 3/4/7/7/6/6 `stackPop`s. Each pushes exactly
   one word, though on SpecRef's side the push lives in the shared
   `generic_create`/`generic_call` (once per outcome branch) rather than
   in the handler.
2. **`takes_value` matches where SpecRef puts its balance check.**
   `call_semantics` sets `takes_value` for `Call` and `CallCode` only,
   and those are exactly the two handlers carrying an
   insufficient-balance early exit that pushes `0` without entering a
   frame (Interpreter.lean:747 and :803). `DelegateCall` inherits the
   caller's value and `StaticCall` has none, so neither can fail that
   way — and neither has the branch.
-/

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## Six wrappers, two runners

Each `execute_*` unpacks the memory sigma and applies its runner to a
kind tag. Nothing else. -/

open Evm.Functions in
theorem execute_create_eq (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_create pc_in top mem g
      = Evm.Functions.run_create .CreateByNonce pc_in top mem g := rfl

open Evm.Functions in
theorem execute_create2_eq (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_create2 pc_in top mem g
      = Evm.Functions.run_create .CreateBySalt pc_in top mem g := rfl

open Evm.Functions in
theorem execute_call_eq (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_call pc_in top mem g
      = Evm.Functions.run_call .Call pc_in top mem g := rfl

open Evm.Functions in
theorem execute_callcode_eq (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_callcode pc_in top mem g
      = Evm.Functions.run_call .CallCode pc_in top mem g := rfl

open Evm.Functions in
theorem execute_delegatecall_eq (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_delegatecall pc_in top mem g
      = Evm.Functions.run_call .DelegateCall pc_in top mem g := rfl

open Evm.Functions in
theorem execute_staticcall_eq (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_staticcall pc_in top mem g
      = Evm.Functions.run_call .StaticCall pc_in top mem g := rfl

/-! ## What the kind tag means

Stated as equations over *all* kinds, so a later proof can case on a flag
without re-deriving the table, and so a new `CallKind` would have to be
accounted for here. -/

/-- Only `CALL` and `CALLCODE` take a `value` operand — the two whose
SpecRef handlers carry an insufficient-balance early exit. -/
theorem call_takes_value (k : CallKind) :
    (Evm.Functions.call_semantics k).takes_value
      = (k == .Call || k == .CallCode) := by
  cases k <;> rfl

/-- Only `CALL` moves ether. `CALLCODE` takes a value operand and uses it
for the child's `callvalue` without transferring it. -/
theorem call_transfers_value (k : CallKind) :
    (Evm.Functions.call_semantics k).transfers_value = (k == .Call) := by
  cases k <;> rfl

/-- `CALL` and `STATICCALL` run the target's code as the target;
`CALLCODE` and `DELEGATECALL` run it as the caller. -/
theorem call_uses_target_address (k : CallKind) :
    (Evm.Functions.call_semantics k).uses_target_address
      = (k == .Call || k == .StaticCall) := by
  cases k <;> rfl

/-- Only `DELEGATECALL` inherits the parent's caller and value. -/
theorem call_inherits_caller_and_value (k : CallKind) :
    (Evm.Functions.call_semantics k).inherits_caller_and_value
      = (k == .DelegateCall) := by
  cases k <;> rfl

/-- Only `STATICCALL` forces a static child frame. A `CALL` from an
already-static frame is static by inheritance, not by this flag. -/
theorem call_enters_static_context (k : CallKind) :
    (Evm.Functions.call_semantics k).enters_static_context
      = (k == .StaticCall) := by
  cases k <;> rfl

/-- `CREATE2` is `CREATE` plus the salt. The whole difference. -/
theorem create_uses_salt (k : CreateKind) :
    (Evm.Functions.create_semantics k).uses_salt = (k == .CreateBySalt) := by
  cases k <;> rfl

/-! ## Stack effects, and the underflow outcome

Each equation is `rfl`; each underflow shape follows from
`runS_execute_underflow`, which is generic in the opcode because
`execute`'s failure path is. -/

theorem create_stack_effect :
    Evm.Functions.opcode_stack_effect (.opcode_CREATE ()) = pure (3, 1) := rfl

theorem create2_stack_effect :
    Evm.Functions.opcode_stack_effect (.CREATE2 ()) = pure (4, 1) := rfl

theorem call_stack_effect :
    Evm.Functions.opcode_stack_effect (.CALL ()) = pure (7, 1) := rfl

theorem callcode_stack_effect :
    Evm.Functions.opcode_stack_effect (.CALLCODE ()) = pure (7, 1) := rfl

theorem delegatecall_stack_effect :
    Evm.Functions.opcode_stack_effect (.DELEGATECALL ()) = pure (6, 1) := rfl

theorem staticcall_stack_effect :
    Evm.Functions.opcode_stack_effect (.STATICCALL ()) = pure (6, 1) := rfl

/-- The family's stack effects, as one table over the six constructors.
Stated together because the interesting fact is the *pattern* — each
takes its operands and leaves one result word — and because a change to
any single effect should fail here rather than in one opcode's proof. -/
theorem callFamily_stack_effects :
    Evm.Functions.opcode_stack_effect (.opcode_CREATE ()) = pure (3, 1)
      ∧ Evm.Functions.opcode_stack_effect (.CREATE2 ()) = pure (4, 1)
      ∧ Evm.Functions.opcode_stack_effect (.CALL ()) = pure (7, 1)
      ∧ Evm.Functions.opcode_stack_effect (.CALLCODE ()) = pure (7, 1)
      ∧ Evm.Functions.opcode_stack_effect (.DELEGATECALL ()) = pure (6, 1)
      ∧ Evm.Functions.opcode_stack_effect (.STATICCALL ()) = pure (6, 1) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end EvmSpecsVerify
