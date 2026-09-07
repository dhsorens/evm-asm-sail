import EvmSpecsVerify.Relations.Selfdestruct
import EvmSpecsVerify.Relations.WarmAddr
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.EvmSailME

/-!
# SELFDESTRUCT

The last opcode outside the MM-3-blocked CALL/CREATE family, and the one
that touches the most state: the operand stack, the address access set,
both gas dimensions, the account overlay, the log store, and the EIP-6780
lifecycle flags.

Everything below the step theorem landed in earlier slices —
[`AccountRel`](../Relations/Account.lean) for the overlay,
[`transfer_equiv`](../Relations/Transfer.lean) and its three degenerate
siblings for the value transfer and the EIP-7708 log,
[`Relations/Selfdestruct.lean`](../Relations/Selfdestruct.lean) for the
Amsterdam schedule, the `creates_account` predicate and
[`LifecycleRel`](../Relations/Selfdestruct.lean). This file assembles them.

## Shape

Both sides test the static flag **before** popping (SpecRef's
`if isStatic then throw` precedes `stackPop`; the extraction's
`guard_static` precedes `pop`), so MM-14's mirror-image does *not* apply
here even though MM-14's Area lists `iSelfdestruct`: the two agree, and
the `halted` constructor suffices for the static outcome.

The gas comes in two stages on both sides, for the same reason: the
account-write surcharge depends on the beneficiary, which must not be
read before the frame can afford the access. SpecRef checks
`check_gas gas_cost` (a sentry that spends nothing), then reads, then
charges `gas_cost + account_write_gas`; the extraction checks
`check_execution_gas g0 access_cost`, then reads, then charges
`execution_cost` — both from the *pre-sentry* gas, so neither
double-charges. `selfdestructCost` is the shared closed form.

SpecRef does **not** advance the pc here, where `iStop` does; the frame
is halted either way and a halted frame's pc is not observable past the
frame boundary, so `SelfdestructPost` mirrors `StopPost` and mentions
neither pc nor stack.
-/

open private pcAdd from EvmAsm.Stateless.SpecRef.InstructionsCore
open private assocGet assocPut from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## SpecRef's frame effects, as a composition -/

/-- The frame after the pop. -/
def sdPoppedEvm (e : Evm) (rest : List U256) : Evm := { e with stack := rest }

/-- The conditional cold-address marking. -/
def sdWarmEvm (e : Evm) (cold : Bool) (b : Address) : Evm :=
  if cold then { e with accessedAddresses := setAdd e.accessedAddresses b }
  else e

/-- The frame after the pop and the marking — where both reads happen. -/
def sdWarmedEvm (e : Evm) (rest : List U256) (cold : Bool) (b : Address) :
    Evm :=
  sdWarmEvm (sdPoppedEvm e rest) cold b

/-- The frame after both charges. -/
def sdChargedEvm (e : Evm) (rest : List U256) (cold creates : Bool)
    (b : Address) : Evm :=
  chargeStateEvm
    (chargeEvm (sdWarmedEvm e rest cold b) (selfdestructCost cold creates))
    (if creates then StateGasCosts.NEW_ACCOUNT else 0)

/-- The conditional lifecycle mark, and the halt. -/
def sdMarkEvm (e : Evm) (mark : Bool) (a : Address) : Evm :=
  if mark then specMarkDeleted e a else e

def sdHaltEvm (e : Evm) : Evm := { e with running := false }

/-! ### Projections

The affordability tests are stated on the pre-charge frame, so each
converts to a closed form without case analysis. -/

@[simp] theorem sdWarmedEvm_gasLeft (e : Evm) (rest : List U256)
    (cold : Bool) (b : Address) :
    (sdWarmedEvm e rest cold b).gasLeft = e.gasLeft := by
  unfold sdWarmedEvm sdWarmEvm sdPoppedEvm
  cases cold <;> rfl

@[simp] theorem sdWarmedEvm_stateGasLeft (e : Evm) (rest : List U256)
    (cold : Bool) (b : Address) :
    (sdWarmedEvm e rest cold b).stateGasLeft = e.stateGasLeft := by
  unfold sdWarmedEvm sdWarmEvm sdPoppedEvm
  cases cold <;> rfl

@[simp] theorem sdWarmedEvm_message (e : Evm) (rest : List U256)
    (cold : Bool) (b : Address) :
    (sdWarmedEvm e rest cold b).message = e.message := by
  unfold sdWarmedEvm sdWarmEvm sdPoppedEvm
  cases cold <;> rfl

@[simp] theorem sdWarmedEvm_logs (e : Evm) (rest : List U256)
    (cold : Bool) (b : Address) :
    (sdWarmedEvm e rest cold b).logs = e.logs := by
  unfold sdWarmedEvm sdWarmEvm sdPoppedEvm
  cases cold <;> rfl

@[simp] theorem chargeEvm_gasLeft (e : Evm) (amount : Uint) :
    (chargeEvm e amount).gasLeft = e.gasLeft - amount := rfl

@[simp] theorem chargeEvm_stateGasLeft (e : Evm) (amount : Uint) :
    (chargeEvm e amount).stateGasLeft = e.stateGasLeft := rfl

/-! ## SpecRef run shapes -/

theorem runR_iSelfdestruct_static (s : Machine)
    (hstatic : s.evm.message.isStatic = true) :
    runR iSelfdestruct s = .ok (.error .writeInStaticContext, s) := by
  simp only [iSelfdestruct]
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_pos (by simpa using hstatic)]
  exact runR_bind_err (runR_throw _ _)

theorem runR_iSelfdestruct_underflow (s : Machine)
    (hstatic : s.evm.message.isStatic = false)
    (hstack : s.evm.stack = []) :
    runR iSelfdestruct s = .ok (.error .stackUnderflow, s) := by
  simp only [iSelfdestruct]
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_neg (by simpa using hstatic)]
  refine runR_bind_ok (runR_pure _ _) ?_
  exact runR_bind_err (runR_stackPop_nil s hstack)

/-- The sentry: the frame must afford the access cost before the
beneficiary is read. -/
theorem runR_iSelfdestruct_sentry_oog (s : Machine) (x : U256)
    (rest : List U256) (cold : Bool)
    (hstack : s.evm.stack = x :: rest)
    (hstatic : s.evm.message.isStatic = false)
    (hcold : cold = !s.evm.accessedAddresses.contains (to_address_masked x))
    (hsentry : s.evm.gasLeft < selfdestructAccessCost cold) :
    runR iSelfdestruct s
      = .ok (.error .outOfGas,
          { s with evm := sdPoppedEvm s.evm rest }) := by
  simp only [iSelfdestruct]
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_neg (by simpa using hstatic)]
  refine runR_bind_ok (runR_pure _ _) ?_
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [← hcold]
  exact runR_bind_err (runR_check_gas_oog _ _ (by
    unfold selfdestructAccessCost at hsentry
    exact hsentry))

/-- The `creates_account` flag as SpecRef's handler spells it: a dead
beneficiary and a nonzero originator balance. The `decide` is the
`Prop → Bool` coercion `&&` forces on `originator_has_balance`. -/
def sdCreates (alive : Bool) (bal : U256) : Bool :=
  !alive && decide (bal ≠ 0)

/-- The account-write surcharge and the state charge come out of one
conditional pair in the handler; these are its two projections. -/
theorem sdCreates_writeGas (alive : Bool) (bal : U256) :
    (if sdCreates alive bal = true then
        (StateGasCosts.NEW_ACCOUNT, GasCosts.ACCOUNT_WRITE)
      else ((0 : Uint), (0 : Uint))).2
      = (if sdCreates alive bal then GasCosts.ACCOUNT_WRITE else 0) := by
  cases sdCreates alive bal <;> rfl

theorem sdCreates_stateGas (alive : Bool) (bal : U256) :
    (if sdCreates alive bal = true then
        (StateGasCosts.NEW_ACCOUNT, GasCosts.ACCOUNT_WRITE)
      else ((0 : Uint), (0 : Uint))).1
      = (if sdCreates alive bal then StateGasCosts.NEW_ACCOUNT else 0) := by
  cases sdCreates alive bal <;> rfl

/-- The handler's total regular charge is `selfdestructCost`. -/
theorem sdChargeAmount_eq (cold alive : Bool) (bal : U256) :
    (GasCosts.OPCODE_SELFDESTRUCT_BASE
        + (if cold = true then GasCosts.COLD_ACCOUNT_ACCESS else 0))
      + (if sdCreates alive bal then GasCosts.ACCOUNT_WRITE else 0)
      = selfdestructCost cold (sdCreates alive bal) := rfl

end EvmSpecsVerify
