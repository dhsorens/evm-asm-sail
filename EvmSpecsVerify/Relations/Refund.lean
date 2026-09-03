import EvmSpecsVerify.Representation.EvmMonad
import EvmAsm.Stateless.SpecRef

/-!
# Refund relation (EIP-2200 / EIP-3529)

SpecRef accumulates the signed gas refund in the frame
(`Evm.refundCounter : Int`, Vm.lean:196); the extraction keeps it in the
`frame_refund` register (`gas_refund := Int`). Both are settled — and
capped against the transaction's gas — at transaction end, not per step,
so the step-level relation is plain equality.

The one extra component is `room`. The extraction's `record_refund`
validates the running sum against `±gas_refund_bound`
(`199 · (2^64 − 1)`, Defs.lean:724) and hard-aborts outside it, where
SpecRef's `Int` counter has no bound. That guard is unreachable for a
real transaction — under the EIP-7825 cap a transaction has at most
`2^24 / G_sstore_sentry` ≈ 7291 SSTOREs, each moving the counter by at
most `R_amsterdam_storage_clear` — but nothing at step level says so, so
the relation carries the invariant: the counter stays one SSTORE delta
away from the bound. It is the refund analogue of `MemGasSafe`.
-/

namespace EvmSpecsVerify

open Evm (HostState)

/-- The largest magnitude one `SSTORE` can move the counter by. Its two
components cannot both fire: `clear_delta ≠ 0` needs `new = 0` or
`current = 0`, and `restore_delta ≠ 0` needs `original = new`, which
together force `original = 0` — excluded by `clear_delta`'s own
`original ≠ 0`. -/
def refundStep : Int := 12480

/-- SpecRef's refund counter vs the extraction's `frame_refund`. -/
structure RefundRel (evmRef : EvmAsm.Stateless.SpecRef.Evm) (ss : SeqState) :
    Prop where
  rel : ss.regs.get? Evm.Defs.Register.frame_refund =
    some evmRef.refundCounter
  /-- One step of headroom on both sides of the extraction's validated
  range (see the module docstring). -/
  room : -(Evm.Defs.gas_refund_bound - refundStep) ≤ evmRef.refundCounter
    ∧ evmRef.refundCounter ≤ Evm.Defs.gas_refund_bound - refundStep

end EvmSpecsVerify
