import EvmSpecsVerify.Representation.EvmMonad
import EvmAsm.Stateless.SpecRef

/-!
# Refund relation (EIP-2200 / EIP-3529)

SpecRef accumulates the signed gas refund in the frame
(`Evm.refundCounter : Int`, Vm.lean:196); the extraction keeps it in the
`frame_refund` register (`gas_refund := Int`). Both are settled — and
capped against the transaction's gas — at transaction end, not per step,
so the step-level relation is plain equality.

The extraction's `record_refund` additionally validates the running sum
against `±gas_refund_bound` (`199 · (2^64 − 1)`, Defs.lean:724) and
hard-aborts outside it, where SpecRef's `Int` counter has no bound. That
guard is unreachable for a real transaction — under the EIP-7825 cap a
transaction has at most `2^24 / G_sstore_sentry` ≈ 7291 `SSTORE`s, each
moving the counter by at most `R_amsterdam_storage_clear` = 12480 — but
nothing at *step* level says so. It is therefore a threaded step
hypothesis on the opcode theorems that record refunds (the refund
analogue of `MemGasSafe`), not a field of this relation: an invariant
that the step both consumes and re-establishes would have to shrink the
range by one step's delta each time.
-/

namespace EvmSpecsVerify

open Evm (HostState)

/-- SpecRef's refund counter vs the extraction's `frame_refund`. -/
structure RefundRel (evmRef : EvmAsm.Stateless.SpecRef.Evm) (ss : SeqState) :
    Prop where
  rel : ss.regs.get? Evm.Defs.Register.frame_refund =
    some evmRef.refundCounter

/-- The extraction's validated refund range, as the step hypothesis it
is (see the module docstring). -/
def RefundInRange (r : Int) : Prop :=
  -(Evm.Defs.gas_refund_bound : Int) ≤ r
    ∧ r ≤ (Evm.Defs.gas_refund_bound : Int)

end EvmSpecsVerify
