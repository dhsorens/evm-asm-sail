import EvmSpecsVerify.Representation.EvmMonad

/-!
# Run-shape algebra for the extraction's early-return monad

Some generated handlers are written with an early return:
`SailME.run do … SailME.throw v …`, where
`Evm.SailME α β = ExceptT (Sail.Error exception ⊕ α) Evm.SailM β`
(Specialization.lean:193). `SailME.run` reads the `ExceptT` result and
turns a `Sum.inr` — a *deliberate* early return — back into an ordinary
value, while a `Sum.inl` stays a real `SailM` error.

`k_sload` (Kernel/Storage.lean:827) is the first such handler in scope and
`execute_sstore` is the second, so this layer is shared rather than
inlined per opcode. It mirrors `EvmMonad.lean`'s convention: one fused
lemma per shape, hypotheses in `runS … = .ok …` form, no simp-normal-form
games — the `ExceptT`/`liftM` unfolding loops if handed to `simp`.
-/

namespace EvmSpecsVerify

open Evm (HostState)

/-- The `ExceptT` payload of a `SailME` computation, run. -/
abbrev runE (m : Evm.SailME α β) (hs : HostState) (ss : SeqState) :
    EStateM.Result SailError SeqState (Except (SailError ⊕ α) β × HostState) :=
  runS (ExceptT.run m) hs ss

/-! ## `SailME.run`: turning an early return back into a value -/

/-- The computation finished normally. -/
theorem runS_sailME_ok {m : Evm.SailME α α} {a : α}
    {hs hs' : HostState} {ss ss' : SeqState}
    (h : runE m hs ss = .ok (.ok a, hs') ss') :
    runS (Evm.SailME.run m) hs ss = .ok (a, hs') ss' := by
  show runS (ExceptT.run m >>= _) hs ss = _
  refine runS_bind_ok h ?_
  exact runS_pure _ _ _

/-- The computation took its early return. -/
theorem runS_sailME_throw {m : Evm.SailME α α} {a : α}
    {hs hs' : HostState} {ss ss' : SeqState}
    (h : runE m hs ss = .ok (.error (.inr a), hs') ss') :
    runS (Evm.SailME.run m) hs ss = .ok (a, hs') ss' := by
  show runS (ExceptT.run m >>= _) hs ss = _
  refine runS_bind_ok h ?_
  exact runS_pure _ _ _

/-! ## The `ExceptT` layer -/

/-- A lifted `SailM` action succeeds into the `.ok` branch. -/
theorem runE_lift {m : Evm.SailM α} {a : α}
    {hs hs' : HostState} {ss ss' : SeqState}
    (h : runS m hs ss = .ok (a, hs') ss') :
    runE (liftM m : Evm.SailME β α) hs ss = .ok (.ok a, hs') ss' :=
  runS_map Except.ok m a h

theorem runE_pure (a : β) (hs : HostState) (ss : SeqState) :
    runE (pure a : Evm.SailME α β) hs ss = .ok (.ok a, hs) ss :=
  runS_pure _ _ _

/-- The early return itself. -/
theorem runE_throw (a : α) (hs : HostState) (ss : SeqState) :
    runE (Evm.SailME.throw a : Evm.SailME α β) hs ss
      = .ok (.error (.inr a), hs) ss :=
  runS_pure _ _ _

/-- Bind, continuing normally. -/
theorem runE_bind_ok {m : Evm.SailME α β} {k : β → Evm.SailME α γ} {b : β}
    {hs hs' : HostState} {ss ss' : SeqState}
    {r : EStateM.Result SailError SeqState
      (Except (SailError ⊕ α) γ × HostState)}
    (h1 : runE m hs ss = .ok (.ok b, hs') ss')
    (h2 : runE (k b) hs' ss' = r) :
    runE (m >>= k) hs ss = r :=
  runS_bind_ok h1 h2

/-- Bind after an early return: the continuation is skipped and the
return value propagates. -/
theorem runE_bind_throw {m : Evm.SailME α β} {k : β → Evm.SailME α γ} {a : α}
    {hs hs' : HostState} {ss ss' : SeqState}
    (h1 : runE m hs ss = .ok (.error (.inr a), hs') ss') :
    runE (m >>= k) hs ss = .ok (.error (.inr a), hs') ss' :=
  runS_bind_ok h1 (runS_pure _ _ _)

/-! ## Guarded statements

The do-elaborator turns `if c then act` inside a `SailME` block into
`if c then (liftM act >>= k) else (pure b >>= k)`, with the continuation
pushed into both branches. This lemma steps over one such guard without
splitting the proof: the post-state is an `if`, which the caller's own
`if`-shaped definitions match. -/

/-- The same guard in *value* position (`let x ← if c then … else …`),
where the do-elaborator leaves the continuation outside. -/
theorem runE_bind_cond {α β γ : Type} (cond : Bool) (m : Evm.SailM γ)
    (a b : γ) (k : γ → Evm.SailME α β) {hs hs' : HostState}
    {ss ss' : SeqState}
    {r : EStateM.Result SailError SeqState
      (Except (SailError ⊕ α) β × HostState)}
    (hm : runS m hs ss = .ok (a, hs') ss')
    (h : runE (k (if cond = true then a else b))
        (if cond = true then hs' else hs)
        (if cond = true then ss' else ss) = r) :
    runE ((if cond = true then liftM m else pure b) >>= k) hs ss = r := by
  cases cond
  · rw [if_neg (by simp)] at h ⊢
    exact runE_bind_ok (runE_pure _ _ _) h
  · rw [if_pos rfl] at h ⊢
    exact runE_bind_ok (runE_lift hm) h

theorem runE_cond_val {α β γ : Type} (cond : Bool) (m : Evm.SailM γ) (a b : γ)
    (k : γ → Evm.SailME α β) {hs hs' : HostState} {ss ss' : SeqState}
    {r : EStateM.Result SailError SeqState
      (Except (SailError ⊕ α) β × HostState)}
    (hm : runS m hs ss = .ok (a, hs') ss')
    (h : runE (k (if cond = true then a else b))
        (if cond = true then hs' else hs)
        (if cond = true then ss' else ss) = r) :
    runE (if cond = true then liftM m >>= k else pure b >>= k) hs ss = r := by
  cases cond
  · rw [if_neg (by simp)] at h ⊢
    exact runE_bind_ok (runE_pure _ _ _) h
  · rw [if_pos rfl] at h ⊢
    exact runE_bind_ok (runE_lift hm) h

end EvmSpecsVerify
