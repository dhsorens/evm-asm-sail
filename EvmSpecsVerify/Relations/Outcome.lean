import EvmSpecsVerify.Representation.EvmMonad
import EvmAsm.Stateless.SpecRef

/-!
# Outcomes: error mapping and the step-result relation

The observation boundary for one opcode step:

* **SpecRef** (`runR`): `Except SpecError (Except EvmError Unit × Machine)` —
  the inner `.error e` is an exceptional halt *carrying the mutated machine*
  (unobservable past the frame boundary); the outer `.error` is a spec abort
  (not an EVM outcome — excluded by hypothesis).
* **`Evm`** (`runS` of `execute`): `.ok ((pc', top', mem', g'), hs') ss'` —
  failure is *encoded in the state*: `exc_halt` zeroes the returned gas and
  sets the `frame_status` register to `Exceptional k`.

`StepResultRel` relates the two: success on both sides with related
post-states, or an exceptional halt on both sides with corresponding kinds.
Per the comparison methodology this is an inductive covering **all**
outcomes — success-only theorems are not acceptable.

On failure, no post-state relation is required beyond the halt kind and the
zeroed gas: a halted frame's stack/pc/memory are not observable (the two
sides genuinely differ there — mismatch ledger MM-1 — and the frame
teardown discards them).
-/

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef (EvmError SpecError Machine)
open Evm.Defs (ExceptionKind FrameStatus StackTop EvmMemorySlice)

/-- Correspondence of exceptional-halt kinds (extended as opcode families
enter scope). -/
inductive ErrorRel : EvmError → ExceptionKind → Prop
  | stackUnderflow : ErrorRel .stackUnderflow .StackUnderflow
  | stackOverflow : ErrorRel .stackOverflow .StackOverflow
  | outOfGas : ErrorRel .outOfGas .OutOfGas
  | invalidJumpDest : ErrorRel .invalidJumpDest .InvalidJump
  | outOfBoundsRead : ErrorRel .outOfBoundsRead .InvalidOpcode

/-- The value returned by the extraction's `execute`: the state-passing
tuple (next pc, stack cursor, memory slice, remaining gas). -/
abbrev EvmStep := Nat × StackTop × EvmMemorySlice × Nat

/-- The result of running one `Evm` step. -/
abbrev EvmStepResult :=
  EStateM.Result SailError SeqState (EvmStep × Evm.HostState)

/-- The result of running one SpecRef handler. -/
abbrev SpecStepResult := Except SpecError (Except EvmError Unit × Machine)

/-- One-step outcome correspondence, parameterized by the post-state
relation `Post` applied on the success path. -/
inductive StepResultRel
    (Post : Machine → EvmStep → Evm.HostState → SeqState → Prop) :
    SpecStepResult → EvmStepResult → Prop
  | success {sR' : Machine} {step : EvmStep} {hs' : Evm.HostState}
      {ss' : SeqState}
      (hpost : Post sR' step hs' ss') :
      StepResultRel Post (.ok (.ok (), sR')) (.ok (step, hs') ss')
  | halted {e : EvmError} {k : ExceptionKind} {sR' : Machine}
      {pc' : Nat} {top' : StackTop} {mem' : EvmMemorySlice}
      {hs' : Evm.HostState} {ss' : SeqState}
      (herr : ErrorRel e k)
      (hstatus : ss'.regs.get? Evm.Defs.Register.frame_status =
        some (FrameStatus.Exceptional k)) :
      StepResultRel Post (.ok (.error e, sR'))
        (.ok ((pc', top', mem', 0), hs') ss')
  /-- Mismatch ledger MM-5: charge-first SpecRef handlers (PUSH/DUP/SWAP)
  report `outOfGas` on states that are simultaneously out of gas and
  stack-invalid, where the extraction's hoisted `validate_stack` reports the
  stack fault. Both are exceptional halts with all gas consumed; the kind is
  not observable past the frame boundary, so the divergence is documented
  here rather than hidden behind a hypothesis. Only the double-fault states
  of charge-first handlers may use this constructor. -/
  | haltedChargeFirst {k : ExceptionKind} {sR' : Machine}
      {pc' : Nat} {top' : StackTop} {mem' : EvmMemorySlice}
      {hs' : Evm.HostState} {ss' : SeqState}
      (hk : k = ExceptionKind.StackUnderflow ∨ k = ExceptionKind.StackOverflow)
      (hstatus : ss'.regs.get? Evm.Defs.Register.frame_status =
        some (FrameStatus.Exceptional k)) :
      StepResultRel Post (.ok (.error .outOfGas, sR'))
        (.ok ((pc', top', mem', 0), hs') ss')

/-! ## Reverts

A revert is neither of `StepResultRel`'s outcomes. SpecRef throws
`.revert`, whose `EvmError.isHalt` is **false**: the frame teardown keeps
the remaining gas and the `output` bytes instead of discarding them, so
the `halted` constructor's "all gas consumed" clause is simply wrong for
it. The extraction likewise writes `Halted (HaltRevert …)` — a *normal*
halt kind carrying an output slice — rather than `Exceptional …`.

`RevertResultRel` is therefore an additive wrapper rather than a new
constructor on `StepResultRel`, which would have re-typed every existing
step theorem. Its `exceptional` case reuses `StepResultRel` at
[`NoSuccess`](#NoSuccess), which additionally records that the ordinary
success branch is unreachable for a revert-only handler.
-/

/-- The `Post` of a handler with no ordinary success outcome: REVERT's
only non-failure result is the revert itself, so instantiating
`StepResultRel` here makes the `success` constructor uninhabited. -/
def NoSuccess : Machine → EvmStep → Evm.HostState → SeqState → Prop :=
  fun _ _ _ _ => False

/-- One-step outcome correspondence for handlers that can revert
(REVERT now; the CALL family's propagated reverts later). -/
inductive RevertResultRel
    (Post : Machine → EvmStep → Evm.HostState → SeqState → Prop) :
    SpecStepResult → EvmStepResult → Prop
  /-- Exceptional halts and (vacuously) ordinary success, via
  `StepResultRel`. -/
  | exceptional {r : SpecStepResult} {s : EvmStepResult}
      (h : StepResultRel NoSuccess r s) : RevertResultRel Post r s
  /-- The revert itself: gas and output survive on both sides. -/
  | reverted {sR' : Machine} {step : EvmStep} {hs' : Evm.HostState}
      {ss' : SeqState} (hpost : Post sR' step hs' ss') :
      RevertResultRel Post (.ok (.error .revert, sR')) (.ok (step, hs') ss')

end EvmSpecsVerify
