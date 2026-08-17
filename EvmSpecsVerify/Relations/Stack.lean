import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Relations.Word
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

namespace EvmSpecsVerify

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

open private writeListAt from Evm.HostAxioms

/-- The post-state stack relation shared by 1-in/1-out readers (SLOAD,
BALANCE, CALLDATALOAD): one pop, one push, net cursor unchanged, value
written at `top.toNat - 1`. -/
theorem pop_push_post_stack (top : StackTop) (hs' : Evm.HostState)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (v : word)
    (hframe' : hs'.stackFrames = writeListAt l (top.toNat - 1) v :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hlim : (x :: rest).length ≤ 1024)
    (hlen : top.toNat ≤ l.length)
    (hwfS : ∀ y ∈ x :: rest, WordWf y)
    (hv : WordWf v) :
    StackRel (v :: rest) hs' top := by
  have hn : top.toNat = rest.length + 1 := by simpa using htop
  refine ⟨⟨writeListAt l (top.toNat - 1) v, frest, hframe', ?_, ?_⟩, ?_, ?_, ?_⟩
  · have hpfx' : l.take ((top.toNat - 1) + 1) = (x :: rest).reverse := by
      rw [show top.toNat - 1 + 1 = top.toNat from by omega]
      exact hpfx
    have hpfx1 : l.take (top.toNat - 1) = rest.reverse :=
      take_shrink l rest x (top.toNat - 1) hpfx' (by omega)
    calc (writeListAt l (top.toNat - 1) v).take top.toNat
        = (writeListAt l (top.toNat - 1) v).take ((top.toNat - 1) + 1) := by
          rw [show (top.toNat - 1) + 1 = top.toNat from by omega]
      _ = l.take (top.toNat - 1) ++ [v] :=
          take_writeListAt l (top.toNat - 1) v (by omega)
      _ = rest.reverse ++ [v] := by rw [hpfx1]
      _ = (v :: rest).reverse := by simp
  · rw [length_writeListAt]
    omega
  · simpa using htop
  · simpa using hlim
  · intro w hw
    rcases List.mem_cons.mp hw with hw | hw
    · subst hw
      exact hv
    · exact hwfS w (by simp [hw])

namespace StackRel

theorem cursor_headroom {S : List Nat} {hs : HostState} {top : StackTop}
    (h : StackRel S hs top) (hlt : S.length < 1024) :
    top.toNat + 1 < 2 ^ 64 := by
  have hh := h.height
  have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  omega

end StackRel

end EvmSpecsVerify
