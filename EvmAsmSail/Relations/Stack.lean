import EvmAsmSail.Representation.EvmStack
import EvmAsmSail.Relations.Word
import EvmAsm.Stateless.SpecRef

/-!
# Stack relation

SpecRef's operand stack is `Evm.stack : List U256` with the **head as top**
(Vm.lean:189). The extraction's is the active frame of
`HostState.stackFrames` — a **bottom-indexed** `List word` — addressed
through the `StackTop` cursor, where popped entries linger above the cursor
as inaccessible scratch (see `Representation/EvmStack.lean`). The faithful
relation is therefore prefix-up-to-cursor against the reversed SpecRef
stack, plus the cursor/height agreement and the EVM validity bounds.
-/

namespace EvmAsmSail

open Evm (HostState)
open Evm.Defs (StackTop word)

/-- The host stack (active frame of `hs` + cursor `top`) represents the
SpecRef stack `S` (head = top). -/
structure StackRel (S : List Nat) (hs : HostState) (top : StackTop) : Prop where
  /-- The active frame exists and its cursor-prefix is the reversed stack. -/
  frame : ∃ l rest, hs.stackFrames = l :: rest ∧
    l.take top.toNat = S.reverse ∧ top.toNat ≤ l.length
  /-- The cursor is the stack height. -/
  height : top.toNat = S.length
  /-- The 1024-element operand-stack limit (EVM validity; both sides
  enforce it dynamically). -/
  limit : S.length ≤ 1024
  /-- Every entry is a well-formed word (SpecRef invariant, re-established
  by each handler; the `Evm` side maintains it by `u256` reduction). -/
  wf : ∀ x ∈ S, WordWf x

namespace StackRel

theorem cursor_headroom {S : List Nat} {hs : HostState} {top : StackTop}
    (h : StackRel S hs top) (hlt : S.length < 1024) :
    top.toNat + 1 < 2 ^ 64 := by
  have hh := h.height
  have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  omega

end StackRel

end EvmAsmSail
