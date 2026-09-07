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

## The reads, audited against `execute_selfdestruct`

The two sides read the same three facts but not in the same order, and
not the same number of times. The Amsterdam branch of
`execute_selfdestruct` (`Evm/Evm/Execute.lean:1843`) reads

1. `k_account_is_warm beneficiary` — *before* the sentry, since the
   access cost depends on it,
2. `k_get_balance address` (the originator), then
3. `k_account_is_empty beneficiary`,

while `iSelfdestruct` tests `accessedAddresses.contains` (a frame field,
no tracker read at all), then reads `isAccountAlive beneficiary`, then
`getAccount originator` — **twice**, once to price the surcharge
(Interpreter.lean:290) and once to move the balance (:296).

None of the three differences is observable, but each costs the
composition a specific fact, and they are worth naming before the
extraction side lands:

- the warmth test is state-preserving on both sides
  ([`runS_k_account_is_warm`](../Relations/WarmAddr.lean) returns `hs`
  unchanged, and SpecRef's is a pure field read), so the sentry-OOG
  outcome leaves no read behind on either side. The extraction's
  unconditional `k_account_mark_warm` against SpecRef's `if is_cold`
  agrees because `setAdd`/`assocPut` are idempotent
  ([`warmaddr_after_mark`](../Relations/WarmAddr.lean));
- the two tracker reads commute, because each records into a read set;
- SpecRef's second `getAccount originator` must return the first read's
  account. `runR_iSelfdestruct_success` therefore takes it as a separate
  parameter (`acct₂`, at `ts₂`) rather than assuming it: the surcharge is
  priced off `acct` and the transfer moves `acct₂.balance`, and the step
  theorem supplies the equality instead of the run shape hiding it.

Nothing else in that branch has no SpecRef counterpart: the Amsterdam
path does not call `k_zero_balance` (deletion is deferred to transaction
end on both sides, EIP-8246) and it charges no state gas unless
`creates_account` — where SpecRef's `charge_state_gas 0` is the identity,
so the unconditional statement matches the extraction's guarded one.
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

/-- Stated so `simp only [← sdCreates_def]` can fold the handler's raw
conjunction back into the named flag. -/
theorem sdCreates_def (alive : Bool) (bal : U256) :
    sdCreates alive bal = (!alive && decide (bal ≠ 0)) := rfl

/-- The two amounts the handler charges, **exactly as it spells them**:
one conditional pair, projected twice. Named because the projections do
not survive a `rw` against the elaborated chain — `exact` reaches them by
delta instead. `sdChargeRaw_eq`/`sdStateRaw_eq` put them in closed form
for the arithmetic. -/
def sdChargeRaw (cold alive : Bool) (bal : U256) : Uint :=
  (GasCosts.OPCODE_SELFDESTRUCT_BASE
      + (if cold = true then GasCosts.COLD_ACCOUNT_ACCESS else 0))
    + (if (!alive && decide (bal ≠ 0)) = true then
        (StateGasCosts.NEW_ACCOUNT, GasCosts.ACCOUNT_WRITE)
      else ((0 : Uint), (0 : Uint))).2

def sdStateRaw (alive : Bool) (bal : U256) : Uint :=
  (if (!alive && decide (bal ≠ 0)) = true then
      (StateGasCosts.NEW_ACCOUNT, GasCosts.ACCOUNT_WRITE)
    else ((0 : Uint), (0 : Uint))).1

/-- The handler's regular charge is `selfdestructCost` (MM-2's
account-write subset, now assembled). -/
theorem sdChargeRaw_eq (cold alive : Bool) (bal : U256) :
    sdChargeRaw cold alive bal
      = selfdestructCost cold (sdCreates alive bal) := by
  unfold sdChargeRaw selfdestructCost sdCreates
  cases alive <;> by_cases hb : bal = 0 <;> simp [hb]

theorem sdStateRaw_eq (alive : Bool) (bal : U256) :
    sdStateRaw alive bal
      = (if sdCreates alive bal then StateGasCosts.NEW_ACCOUNT else 0) := by
  unfold sdStateRaw sdCreates
  cases alive <;> by_cases hb : bal = 0 <;> simp [hb]

/-- The cold-address marking, stepped over. -/
theorem runR_sdWarm_guard {α : Type} (s : Machine) (rest : List U256)
    (cold : Bool) (b : Address) (k : PUnit → EvmM α)
    {r : Except SpecError (Except EvmError α × Machine)}
    (hk : runR (k PUnit.unit)
      { s with evm := sdWarmedEvm s.evm rest cold b } = r) :
    runR (if cold = true then
          EvmM.modifyEvm
              (fun e => { e with accessedAddresses := setAdd e.accessedAddresses b })
            >>= k
        else (pure PUnit.unit : EvmM PUnit) >>= k)
        { s with evm := sdPoppedEvm s.evm rest } = r := by
  refine runR_guard_step cold _ k _
    { s with evm := sdWarmedEvm s.evm rest cold b } ?_ hk
  cases cold
  · rw [if_neg (by simp)]
    rfl
  · rw [if_pos rfl]
    exact runR_modifyEvm _ _

/-! ### The tail

`iSelfdestruct` from the first charge onward, as a standalone action. The
handler's statements from `charge_gas` to the halt elaborate to exactly
this chain, so the prefix lemma can hand it over with `exact` — the two
guards keep their continuation-duplicating shape on both sides. -/

def sdChargeTail (chargeAmt stateAmt : Uint) (o b : Address) : EvmM Unit := do
  charge_gas chargeAmt
  charge_state_gas stateAmt
  let bal := (← EvmM.liftTx (getAccount o)).balance
  EvmM.liftTx (moveEther o b bal)
  if b != o then emit_transfer_log o b bal
  if (← get).txState.createdAccounts.contains o then
    EvmM.modifyEvm (fun e =>
      { e with accountsToDelete := setAdd e.accountsToDelete o })
  EvmM.modifyEvm (fun e => { e with running := false })

/-- **The shared prefix.** From `iSelfdestruct` to the first charge: the
static test, the pop, the warm test, the sentry, the cold marking, and
the liveness and balance reads that decide the account-write surcharge.
Every non-static, non-underflowing, sentry-affordable outcome goes
through it, so the outcomes differ only in how `sdChargeTail` ends. -/
theorem runR_iSelfdestruct_prefix (s : Machine) (x : U256) (rest : List U256)
    (cold alive : Bool) (acct : EvmAsm.Stateless.SpecRef.Account)
    (ts₁ ts₂ : TransactionState)
    {r : Except SpecError (Except EvmError Unit × Machine)}
    (hstack : s.evm.stack = x :: rest)
    (hstatic : s.evm.message.isStatic = false)
    (hcold : cold = !s.evm.accessedAddresses.contains (to_address_masked x))
    (hsentry : selfdestructAccessCost cold ≤ s.evm.gasLeft)
    (halive : (isAccountAlive (to_address_masked x)).run s.txState
      = .ok (alive, ts₁))
    (hacct : (getAccount s.evm.message.currentTarget).run ts₁ = .ok (acct, ts₂))
    (h : runR
        (sdChargeTail (sdChargeRaw cold alive acct.balance)
          (sdStateRaw alive acct.balance)
          s.evm.message.currentTarget (to_address_masked x))
        { s with
            txState := ts₂
            evm := sdWarmedEvm s.evm rest cold (to_address_masked x) }
      = r) :
    runR iSelfdestruct s = r := by
  simp only [iSelfdestruct]
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_neg (by simpa using hstatic)]
  refine runR_bind_ok (runR_pure _ _) ?_
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [← hcold]
  refine runR_bind_ok (runR_check_gas _ _ (by
    unfold selfdestructAccessCost at hsentry
    exact hsentry)) ?_
  refine runR_sdWarm_guard s rest cold (to_address_masked x) _ ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  simp only [sdWarmedEvm_message]
  refine runR_bind_ok (runR_liftTx_ok _ _ alive ts₁ halive) ?_
  refine runR_bind_ok (runR_liftTx_ok _ _ acct ts₂ hacct) ?_
  exact h

/-! ### Both charges, in closed form

`charge_gas`/`charge_state_gas` each split on affordability in
`Representation/SpecRefLemmas.lean`; `chargeEvm`/`chargeStateEvm` are the
closed forms that already carry the split, so the successful legs
compose without case analysis at the call site. -/

theorem runR_charge_gas_ok (s : Machine) (amount : Uint)
    (h : amount ≤ s.evm.gasLeft) :
    runR (charge_gas amount) s
      = .ok (.ok (), { s with evm := chargeEvm s.evm amount }) :=
  runR_charge_gas s amount h

theorem runR_charge_state_gas_ok (s : Machine) (amount : Uint)
    (h : amount ≤ s.evm.stateGasLeft + s.evm.gasLeft) :
    runR (charge_state_gas amount) s
      = .ok (.ok (), { s with evm := chargeStateEvm s.evm amount }) := by
  unfold chargeStateEvm
  by_cases hr : amount ≤ s.evm.stateGasLeft
  · rw [if_pos hr]
    exact runR_charge_state_gas_reservoir _ _ hr
  · rw [if_neg hr]
    exact runR_charge_state_gas_spill _ _ (Nat.lt_of_not_le hr) h

/-! ### The transfer's log, and the lifecycle mark

Both are `if c then act` with no `else`, which the do-elaborator
compiles by duplicating the rest of the block into each branch — so each
is stepped with `runR_guard_step`, not a plain bind. The log's condition
is split across two levels: the caller tests `b != o`, and
`emit_transfer_log` tests `v == 0` itself. -/

/-- `emit_transfer_log`'s own zero guard. -/
def sdLoggedInner (s : Machine) (o b : Address) (v : U256) : Machine :=
  if v != 0 then { s with evm := specLogAppend s (specTransferLog o b v) }
  else s

/-- Unconditional, unlike [`runR_emit_transfer_log`](../Relations/Transfer.lean):
the zero case is reachable here, since an originator with no balance still
selfdestructs. -/
theorem runR_emit_transfer_log_any (o b : Address) (v : U256) (s : Machine) :
    runR (emit_transfer_log o b v) s = .ok (.ok (), sdLoggedInner s o b v) := by
  unfold emit_transfer_log sdLoggedInner
  by_cases hv : v = 0
  · rw [if_pos (by simp [hv]), if_neg (by simp [hv])]
    rfl
  · rw [if_neg (by simp [hv]), if_pos (by simp [hv])]
    rfl

/-- The machine after the guarded log. -/
def sdLogged (s : Machine) (o b : Address) (v : U256) : Machine :=
  if b != o then sdLoggedInner s o b v else s

theorem runR_sd_log_guard {α : Type} (s : Machine) (o b : Address) (v : U256)
    (k : PUnit → EvmM α)
    {r : Except SpecError (Except EvmError α × Machine)}
    (hk : runR (k PUnit.unit) (sdLogged s o b v) = r) :
    runR (if (b != o) = true then emit_transfer_log o b v >>= k
        else (pure PUnit.unit : EvmM PUnit) >>= k) s = r := by
  refine runR_guard_step _ _ k s (sdLogged s o b v) ?_ hk
  unfold sdLogged
  cases b != o
  · rfl
  · exact runR_emit_transfer_log_any _ _ _ _

/-- The machine after the EIP-6780 mark. The condition is read from the
*live* tracker state, after the transfer. -/
def sdMarked (s : Machine) (o : Address) : Machine :=
  { s with evm := sdMarkEvm s.evm (s.txState.createdAccounts.contains o) o }

theorem runR_sd_mark_guard {α : Type} (s : Machine) (o : Address)
    (k : PUnit → EvmM α)
    {r : Except SpecError (Except EvmError α × Machine)}
    (hk : runR (k PUnit.unit) (sdMarked s o) = r) :
    runR (if s.txState.createdAccounts.contains o = true then
          EvmM.modifyEvm
              (fun e => { e with accountsToDelete := setAdd e.accountsToDelete o })
            >>= k
        else (pure PUnit.unit : EvmM PUnit) >>= k) s = r := by
  refine runR_guard_step _ _ k s (sdMarked s o) ?_ hk
  unfold sdMarked sdMarkEvm specMarkDeleted
  cases s.txState.createdAccounts.contains o
  · rfl
  · exact runR_modifyEvm
      (fun e => { e with accountsToDelete := setAdd e.accountsToDelete o }) s

/-! ## SpecRef's three remaining outcomes -/

/-- **The regular charge runs out.** The frame afforded the access cost
at the sentry but not the account-write surcharge on top of it, so the
only outcome the mark is that the pop and the cold marking already
happened — SpecRef leaves the failed charge's frame untouched. -/
theorem runR_iSelfdestruct_charge_oog (s : Machine) (x : U256)
    (rest : List U256) (cold alive : Bool)
    (acct : EvmAsm.Stateless.SpecRef.Account) (ts₁ ts₂ : TransactionState)
    (hstack : s.evm.stack = x :: rest)
    (hstatic : s.evm.message.isStatic = false)
    (hcold : cold = !s.evm.accessedAddresses.contains (to_address_masked x))
    (hsentry : selfdestructAccessCost cold ≤ s.evm.gasLeft)
    (halive : (isAccountAlive (to_address_masked x)).run s.txState
      = .ok (alive, ts₁))
    (hacct : (getAccount s.evm.message.currentTarget).run ts₁ = .ok (acct, ts₂))
    (hoog : s.evm.gasLeft
      < selfdestructCost cold (sdCreates alive acct.balance)) :
    runR iSelfdestruct s
      = .ok (.error .outOfGas,
          { s with
              txState := ts₂
              evm := sdWarmedEvm s.evm rest cold (to_address_masked x) }) := by
  refine runR_iSelfdestruct_prefix s x rest cold alive acct ts₁ ts₂
    hstack hstatic hcold hsentry halive hacct ?_
  simp only [sdChargeTail]
  refine runR_bind_err (runR_charge_gas_oog _ _ ?_)
  rw [sdChargeRaw_eq]
  simpa using hoog

/-- **The state charge runs out.** Both dimensions are exhausted: the
reservoir plus what execution gas the regular charge left over does not
cover `NEW_ACCOUNT`. The regular charge stands — `charge_state_gas`
throws without spending — so the frame keeps it. -/
theorem runR_iSelfdestruct_state_oog (s : Machine) (x : U256)
    (rest : List U256) (cold alive : Bool)
    (acct : EvmAsm.Stateless.SpecRef.Account) (ts₁ ts₂ : TransactionState)
    (hstack : s.evm.stack = x :: rest)
    (hstatic : s.evm.message.isStatic = false)
    (hcold : cold = !s.evm.accessedAddresses.contains (to_address_masked x))
    (hsentry : selfdestructAccessCost cold ≤ s.evm.gasLeft)
    (halive : (isAccountAlive (to_address_masked x)).run s.txState
      = .ok (alive, ts₁))
    (hacct : (getAccount s.evm.message.currentTarget).run ts₁ = .ok (acct, ts₂))
    (hcharge : selfdestructCost cold (sdCreates alive acct.balance)
      ≤ s.evm.gasLeft)
    (hoog : s.evm.stateGasLeft
        + (s.evm.gasLeft - selfdestructCost cold (sdCreates alive acct.balance))
      < (if sdCreates alive acct.balance then StateGasCosts.NEW_ACCOUNT
          else 0)) :
    runR iSelfdestruct s
      = .ok (.error .outOfGas,
          { s with
              txState := ts₂
              evm := chargeEvm
                (sdWarmedEvm s.evm rest cold (to_address_masked x))
                (selfdestructCost cold (sdCreates alive acct.balance)) }) := by
  refine runR_iSelfdestruct_prefix s x rest cold alive acct ts₁ ts₂
    hstack hstatic hcold hsentry halive hacct ?_
  simp only [sdChargeTail]
  rw [sdChargeRaw_eq, sdStateRaw_eq]
  refine runR_bind_ok (runR_charge_gas_ok _ _ (by simpa using hcharge)) ?_
  exact runR_bind_err (runR_charge_state_gas_oog _ _ (by simpa using hoog))

/-- SpecRef's frame after a successful `SELFDESTRUCT`: both charges, the
guarded log, the guarded EIP-6780 mark, and the halt. `ts'` is the
tracker state the transfer leaves. -/
def sdSuccessOut (s : Machine) (rest : List U256) (cold creates : Bool)
    (b : Address) (v : U256) (ts' : TransactionState) : Machine :=
  let m := sdMarked
    (sdLogged
      { s with
          txState := ts'
          evm := sdChargedEvm s.evm rest cold creates b }
      s.evm.message.currentTarget b v)
    s.evm.message.currentTarget
  { m with evm := sdHaltEvm m.evm }

/-- **Success.** Both charges are afforded; the frame halts.

Note the *two* `getAccount originator` reads: the handler reads the
balance once to decide the account-write surcharge and again to move it
(`Interpreter.lean:290,296`). They are separate reads, so the two
accounts are separate parameters here — the transfer moves `acct₂`'s
balance while the surcharge was priced off `acct`'s. -/
theorem runR_iSelfdestruct_success (s : Machine) (x : U256)
    (rest : List U256) (cold alive : Bool)
    (acct acct₂ : EvmAsm.Stateless.SpecRef.Account)
    (ts₁ ts₂ ts₃ ts₄ : TransactionState)
    (hstack : s.evm.stack = x :: rest)
    (hstatic : s.evm.message.isStatic = false)
    (hcold : cold = !s.evm.accessedAddresses.contains (to_address_masked x))
    (hsentry : selfdestructAccessCost cold ≤ s.evm.gasLeft)
    (halive : (isAccountAlive (to_address_masked x)).run s.txState
      = .ok (alive, ts₁))
    (hacct : (getAccount s.evm.message.currentTarget).run ts₁ = .ok (acct, ts₂))
    (hcharge : selfdestructCost cold (sdCreates alive acct.balance)
      ≤ s.evm.gasLeft)
    (hstate : (if sdCreates alive acct.balance then StateGasCosts.NEW_ACCOUNT
          else 0)
      ≤ s.evm.stateGasLeft
        + (s.evm.gasLeft
            - selfdestructCost cold (sdCreates alive acct.balance)))
    (hacct₂ : (getAccount s.evm.message.currentTarget).run ts₂
      = .ok (acct₂, ts₃))
    (hmove : (moveEther s.evm.message.currentTarget (to_address_masked x)
          acct₂.balance).run ts₃ = .ok ((), ts₄)) :
    runR iSelfdestruct s
      = .ok (.ok (),
          sdSuccessOut s rest cold (sdCreates alive acct.balance)
            (to_address_masked x) acct₂.balance ts₄) := by
  refine runR_iSelfdestruct_prefix s x rest cold alive acct ts₁ ts₂
    hstack hstatic hcold hsentry halive hacct ?_
  simp only [sdChargeTail]
  rw [sdChargeRaw_eq, sdStateRaw_eq]
  refine runR_bind_ok (runR_charge_gas_ok _ _ (by simpa using hcharge)) ?_
  refine runR_bind_ok (runR_charge_state_gas_ok _ _ (by simpa using hstate)) ?_
  refine runR_bind_ok (runR_liftTx_ok _ _ acct₂ ts₃ (by simpa using hacct₂)) ?_
  refine runR_bind_ok
    (runR_liftTx_ok _ _ () ts₄ (by simpa using hmove)) ?_
  refine runR_sd_log_guard _ _ _ acct₂.balance _ ?_
  refine runR_sd_mark_guard _ _ _ ?_
  simp only [sdSuccessOut, sdHaltEvm]
  exact runR_modifyEvm _ _

end EvmSpecsVerify
