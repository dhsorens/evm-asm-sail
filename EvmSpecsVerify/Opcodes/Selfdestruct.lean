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

**MM-14 does apply here** — an earlier draft of this docstring said it
did not, on the grounds that both handlers test the static flag before
their own pop (SpecRef's `if isStatic then throw` precedes `stackPop`;
`execute_selfdestruct`'s `guard_static` precedes `pop`). That misses
where the extraction's stack check actually sits: `execute` hoists
`validate_stack` *outside* `execute_opcode`, so it runs before
`execute_selfdestruct` is even entered. An empty stack in a static frame
therefore halts as `.writeInStaticContext` on SpecRef and as
`StackUnderflow` on the extraction, exactly as MM-14's Area line says.
Both are exceptional halts consuming the frame's gas, so the `halted`
constructor still pairs them; `runS_execute_selfdestruct_underflow` and
`runR_iSelfdestruct_static` are the two shapes involved.

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

/-- `sdChargeTail`'s two transfer statements **are** `specTransfer`, with
the handler's remaining statements duplicated into the log guard's
branches. Re-associating lets `transfer_equiv*`'s bundled conclusion be
consumed as a unit, instead of splitting it into a tracker run and a log
effect. -/
theorem runR_sd_transfer_step {α : Type} (s s' : Machine) (o b : Address)
    (v : U256) (k : PUnit → EvmM α)
    {r : Except SpecError (Except EvmError α × Machine)}
    (htr : runR (specTransfer o b v) s = .ok (.ok PUnit.unit, s'))
    (hk : runR (k PUnit.unit) s' = r) :
    runR (EvmM.liftTx (moveEther o b v) >>= fun _ =>
        if (b != o) = true then emit_transfer_log o b v >>= k
        else (pure PUnit.unit : EvmM PUnit) >>= k) s = r := by
  have hact : (EvmM.liftTx (moveEther o b v) >>= fun _ =>
        if (b != o) = true then emit_transfer_log o b v >>= k
        else (pure PUnit.unit : EvmM PUnit) >>= k)
      = specTransfer o b v >>= k := by
    unfold specTransfer
    rw [bind_assoc]
    congr 1
    funext _
    cases b != o
    · rw [if_neg (by simp), if_neg (by simp)]
    · rw [if_pos rfl, if_pos rfl]
  rw [hact]
  exact runR_bind_ok htr hk

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

/-- **Success, with the transfer stepped as a unit.** The form the step
theorem consumes: `transfer_equiv*` hands over the composite
`specTransfer` run, so this takes that rather than the tracker run and
the log effect separately (`runR_iSelfdestruct_success` is the other
factoring, useful when the transfer's two halves are known). -/
theorem runR_iSelfdestruct_success_xfer (s : Machine) (x : U256)
    (rest : List U256) (cold alive : Bool)
    (acct acct₂ : EvmAsm.Stateless.SpecRef.Account)
    (ts₁ ts₂ ts₃ : TransactionState) (sR' : Machine)
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
    (hxfer : runR (specTransfer s.evm.message.currentTarget
          (to_address_masked x) acct₂.balance)
        { s with
            txState := ts₃
            evm := sdChargedEvm s.evm rest cold
              (sdCreates alive acct.balance) (to_address_masked x) }
      = .ok (.ok (), sR')) :
    runR iSelfdestruct s
      = .ok (.ok (),
          { sR' with evm := sdHaltEvm (sdMarkEvm sR'.evm
              (sR'.txState.createdAccounts.contains
                s.evm.message.currentTarget)
              s.evm.message.currentTarget) }) := by
  refine runR_iSelfdestruct_prefix s x rest cold alive acct ts₁ ts₂
    hstack hstatic hcold hsentry halive hacct ?_
  simp only [sdChargeTail]
  rw [sdChargeRaw_eq, sdStateRaw_eq]
  refine runR_bind_ok (runR_charge_gas_ok _ _ (by simpa using hcharge)) ?_
  refine runR_bind_ok (runR_charge_state_gas_ok _ _ (by simpa using hstate)) ?_
  refine runR_bind_ok (runR_liftTx_ok _ _ acct₂ ts₃ (by simpa using hacct₂)) ?_
  refine runR_sd_transfer_step _ sR' _ _ _ _ hxfer ?_
  refine runR_sd_mark_guard _ _ _ ?_
  simp only [sdMarked, sdHaltEvm]
  exact runR_modifyEvm _ _

/-! ## The extraction's side

`execute_selfdestruct` is a `SailME` chain: the outcomes before the state
charge fall out of the surrounding `if`s, and only the state-gas failure
takes the early return (`SailME.throw`). The Amsterdam branch is the one
in scope; the legacy branch below it is a different schedule and out of
scope for a fixed-fork comparison, exactly as with SSTORE. -/

open Evm.Functions in
/-- The dispatch equation for SELFDESTRUCT. -/
theorem selfdestruct_dispatch (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_opcode (.SELFDESTRUCT ()) pc_in top mem g =
      Evm.Functions.execute_selfdestruct top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
/-- `SELFDESTRUCT` takes one operand and returns none. -/
theorem selfdestruct_stack_effect :
    Evm.Functions.opcode_stack_effect (.SELFDESTRUCT ())
      = (pure (1, 0) : Evm.SailM (Nat × Nat)) := rfl

open Evm.Functions in
/-- **The static outcome.** `guard_static` halts before the pop, so the
cursor is unmoved — the mirror image of `runR_iSelfdestruct_static`, and
the reason MM-14's guard-ordering note does not bite here. -/
theorem runS_selfdestruct_body_static (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hstatic : msg.is_static = true) :
    runS (Evm.Functions.execute_selfdestruct top g) hs ss
      = .ok ((top, GAS_ZERO), hs)
          { ss with regs := haltRegs ss msg .WriteProtection } := by
  obtain ⟨fork, t, mx, dn, cl, il, ptl, prl, tbl, rd, bl, ttl, trl, epf⟩ := prof
  simp only at hfork
  simp only [Evm.Functions.execute_selfdestruct]
  refine runS_sailME_ok ?_
  refine runE_bind_ok (runE_lift (runS_readReg _ _ _ _ hprof)) ?_
  refine runE_bind_ok
    (runE_lift (runS_guard_static_halt g hs ss _ sp msg hprof hsp hmsg
      hfork hstatic)) ?_
  rw [if_pos rfl]
  exact runE_pure _ _ _

open Evm.Functions in
/-- **The sentry outcome.** The access cost is unaffordable: the pop
stands, the beneficiary is *not* marked warm, and no account row is read
— matching `runR_iSelfdestruct_sentry_oog`. -/
theorem runS_selfdestruct_body_sentry_oog (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (pid : Evm.Defs.address → PrecompileId) (warm : Bool)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hstatic : msg.is_static = false)
    (hpid : runS (Evm.Functions.precompile_id_for_address
        (Evm.Functions.word_to_address x)) hs ss
      = .ok (pid (Evm.Functions.word_to_address x), hs) ss)
    (hwarm : warm = (if (pid (Evm.Functions.word_to_address x)
          != PrecompileId.NotPrecompile) then true
        else decide (hs.warmEpoch
          ≤ (assocGet hs.warmAddresses
              (Evm.Functions.word_to_address x)).getD 0)))
    (hoog : g < selfdestructAccessCost (!warm)) :
    runS (Evm.Functions.execute_selfdestruct top g) hs ss
      = .ok ((cursorDrop top 1, GAS_ZERO), hs)
          { ss with regs := haltRegs ss msg .OutOfGas } := by
  have hwarmrun : runS (Evm.Functions.k_account_is_warm
      (Evm.Functions.word_to_address x)) hs ss = .ok (warm, hs) ss := by
    rw [hwarm]
    exact runS_k_account_is_warm pid _ hs ss hpid
  obtain ⟨fork, t, mx, dn, cl, il, ptl, prl, tbl, rd, bl, ttl, trl, epf⟩ := prof
  simp only at hfork
  simp only [Evm.Functions.execute_selfdestruct]
  refine runS_sailME_ok ?_
  refine runE_bind_ok (runE_lift (runS_readReg _ _ _ _ hprof)) ?_
  refine runE_bind_ok
    (runE_lift (runS_guard_static_ok g hs ss msg hmsg hstatic)) ?_
  rw [if_neg (by simp)]
  refine runE_bind_ok
    (runE_lift (runS_pop top hs ss l frest x rest hframe hpfx htop)) ?_
  refine runE_bind_ok (runE_lift (runS_self_addr msg hs ss hmsg)) ?_
  simp only [ProtocolProfileFields.fork, decide_eq_true_eq]
  rw [if_pos (by simpa using hfork)]
  refine runE_bind_ok (runE_lift hwarmrun) ?_
  refine runE_bind_ok
    (runE_lift (runS_check_execution_gas_oog g
      ((0 + G_selfdestruct)
        + (if warm then G_zero else G_amsterdam_cold_account_access))
      hs ss _ sp msg hprof hsp hmsg hfork (by
        rw [extractionAccessCost_eq warm]
        exact hoog))) ?_
  rw [if_pos (by simp)]
  exact runE_pure _ _ _

/-! ### The extraction's amounts and its post-sentry host state -/

open Evm.Functions in
/-- `access_cost`, as `execute_selfdestruct` spells it. -/
def sdAccessRaw (warm : Bool) : Nat :=
  (0 + G_selfdestruct)
    + (if warm then G_zero else G_amsterdam_cold_account_access)

open Evm.Functions in
/-- `execution_cost`, as `execute_selfdestruct` spells it. -/
def sdExecRaw (warm creates : Bool) : Nat :=
  if creates then sdAccessRaw warm + G_amsterdam_account_write
  else sdAccessRaw warm

theorem sdAccessRaw_eq (warm : Bool) :
    sdAccessRaw warm = selfdestructAccessCost (!warm) :=
  extractionAccessCost_eq warm

theorem sdExecRaw_eq (warm creates : Bool) :
    sdExecRaw warm creates = selfdestructCost (!warm) creates := by
  unfold sdExecRaw
  rw [sdAccessRaw_eq]
  exact extractionExecutionCost_eq warm creates

open Evm.Functions in
/-- `creates_account`, as `execute_selfdestruct` spells it: the
originator's balance is nonzero and the beneficiary is EIP-161 empty.
[`originatorHasBalance_eq`](../Relations/Selfdestruct.lean) and
[`beneficiaryDead_eq`](../Relations/Selfdestruct.lean) identify the two
operands with SpecRef's, in the opposite order. -/
def sdCreatesS (ov bv : Evm.Defs.AcctValue) : Bool :=
  word_nonzero ov.curr.info.balance && account_info_empty bv.curr.info

/-- The host state after the beneficiary is marked warm — where both
account rows are read. -/
def sdHostWarm (pid : Evm.Defs.address → PrecompileId)
    (bV : Evm.Defs.address) (hs : Evm.HostState) : Evm.HostState :=
  { hs with warmAddresses := wsAfterMark pid bV hs }

open Evm.Functions in
/-- **The regular charge runs out.** The pop and the warm mark stand; no
row is written. -/
theorem runS_selfdestruct_body_charge_oog (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (pid : Evm.Defs.address → PrecompileId) (warm : Bool)
    (ov bv : Evm.Defs.AcctValue)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hstatic : msg.is_static = false)
    (hpid : runS (precompile_id_for_address (word_to_address x)) hs ss
      = .ok (pid (word_to_address x), hs) ss)
    (hwarm : warm = (if (pid (word_to_address x)
          != PrecompileId.NotPrecompile) then true
        else decide (hs.warmEpoch
          ≤ (assocGet hs.warmAddresses (word_to_address x)).getD 0)))
    (hsentry : selfdestructAccessCost (!warm) ≤ g)
    (horow : hostAcctRow (sdHostWarm pid (word_to_address x) hs) msg.address
      = some ov)
    (hbrow : hostAcctRow (sdHostWarm pid (word_to_address x) hs)
        (word_to_address x) = some bv)
    (hoog : g < selfdestructCost (!warm) (sdCreatesS ov bv)) :
    runS (Evm.Functions.execute_selfdestruct top g) hs ss
      = .ok ((cursorDrop top 1, GAS_ZERO),
          sdHostWarm pid (word_to_address x) hs)
          { ss with regs := haltRegs ss msg .OutOfGas } := by
  have hwarmrun : runS (k_account_is_warm (word_to_address x)) hs ss
      = .ok (warm, hs) ss := by
    rw [hwarm]
    exact runS_k_account_is_warm pid _ hs ss hpid
  obtain ⟨fork, t, mx, dn, cl, il, ptl, prl, tbl, rd, bl, ttl, trl, epf⟩ := prof
  simp only at hfork
  simp only [Evm.Functions.execute_selfdestruct]
  refine runS_sailME_ok ?_
  refine runE_bind_ok (runE_lift (runS_readReg _ _ _ _ hprof)) ?_
  refine runE_bind_ok
    (runE_lift (runS_guard_static_ok g hs ss msg hmsg hstatic)) ?_
  rw [if_neg (by simp)]
  refine runE_bind_ok
    (runE_lift (runS_pop top hs ss l frest x rest hframe hpfx htop)) ?_
  refine runE_bind_ok (runE_lift (runS_self_addr msg hs ss hmsg)) ?_
  simp only [ProtocolProfileFields.fork, decide_eq_true_eq]
  rw [if_pos (by simpa using hfork)]
  refine runE_bind_ok (runE_lift hwarmrun) ?_
  refine runE_bind_ok
    (runE_lift (runS_check_execution_gas_ok g (sdAccessRaw warm) hs ss
      (by rw [sdAccessRaw_eq]; exact hsentry))) ?_
  rw [if_neg (by simp)]
  refine runE_bind_ok
    (runE_lift (runS_k_account_mark_warm pid _ hs ss hpid)) ?_
  refine runE_bind_ok
    (runE_lift (runS_k_get_balance_hit _ ov _ ss horow)) ?_
  refine runE_bind_ok
    (runE_lift (runS_k_account_is_empty_hit _ bv _ ss hbrow)) ?_
  refine runE_bind_ok
    (runE_lift (runS_charge_oog g (sdExecRaw warm (sdCreatesS ov bv)) _ ss
      _ sp msg hprof hsp hmsg hfork
      (by rw [sdExecRaw_eq]; exact hoog))) ?_
  rw [if_pos (by simp)]
  exact runE_pure _ _ _

open Evm.Functions in
/-- **The state charge runs out.** Only reachable when
`creates_account` — the state charge is guarded by it — so the regular
charge has already gone through and the reservoir plus what it left of
the execution gas still does not cover `NEW_ACCOUNT`. Nothing is
written; the pop and the warm mark stand. -/
theorem runS_selfdestruct_body_state_oog (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (res sp : Nat) (msg : Evm.Defs.Message)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (pid : Evm.Defs.address → PrecompileId) (warm : Bool)
    (ov bv : Evm.Defs.AcctValue)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hres : ss.regs.get? Register.state_gas_remaining = some res)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hstatic : msg.is_static = false)
    (hpid : runS (precompile_id_for_address (word_to_address x)) hs ss
      = .ok (pid (word_to_address x), hs) ss)
    (hwarm : warm = (if (pid (word_to_address x)
          != PrecompileId.NotPrecompile) then true
        else decide (hs.warmEpoch
          ≤ (assocGet hs.warmAddresses (word_to_address x)).getD 0)))
    (hsentry : selfdestructAccessCost (!warm) ≤ g)
    (horow : hostAcctRow (sdHostWarm pid (word_to_address x) hs) msg.address
      = some ov)
    (hbrow : hostAcctRow (sdHostWarm pid (word_to_address x) hs)
        (word_to_address x) = some bv)
    (hcreates : sdCreatesS ov bv = true)
    (hcharge : selfdestructCost (!warm) true ≤ g)
    (hshort : res < StateGasCosts.NEW_ACCOUNT)
    (hoog : g - selfdestructCost (!warm) true
      < StateGasCosts.NEW_ACCOUNT - res) :
    runS (Evm.Functions.execute_selfdestruct top g) hs ss
      = .ok ((cursorDrop top 1, GAS_ZERO),
          sdHostWarm pid (word_to_address x) hs)
          { ss with regs := haltRegs ss msg .OutOfGas } := by
  have hwarmrun : runS (k_account_is_warm (word_to_address x)) hs ss
      = .ok (warm, hs) ss := by
    rw [hwarm]
    exact runS_k_account_is_warm pid _ hs ss hpid
  have hc' : (word_nonzero ov.curr.info.balance
      && account_info_empty bv.curr.info) = true := hcreates
  obtain ⟨fork, t, mx, dn, cl, il, ptl, prl, tbl, rd, bl, ttl, trl, epf⟩ := prof
  simp only at hfork
  simp only [Evm.Functions.execute_selfdestruct]
  refine runS_sailME_throw ?_
  refine runE_bind_ok (runE_lift (runS_readReg _ _ _ _ hprof)) ?_
  refine runE_bind_ok
    (runE_lift (runS_guard_static_ok g hs ss msg hmsg hstatic)) ?_
  rw [if_neg (by simp)]
  refine runE_bind_ok
    (runE_lift (runS_pop top hs ss l frest x rest hframe hpfx htop)) ?_
  refine runE_bind_ok (runE_lift (runS_self_addr msg hs ss hmsg)) ?_
  simp only [ProtocolProfileFields.fork, decide_eq_true_eq]
  rw [if_pos (by simpa using hfork)]
  refine runE_bind_ok (runE_lift hwarmrun) ?_
  refine runE_bind_ok
    (runE_lift (runS_check_execution_gas_ok g (sdAccessRaw warm) hs ss
      (by rw [sdAccessRaw_eq]; exact hsentry))) ?_
  rw [if_neg (by simp)]
  refine runE_bind_ok
    (runE_lift (runS_k_account_mark_warm pid _ hs ss hpid)) ?_
  refine runE_bind_ok
    (runE_lift (runS_k_get_balance_hit _ ov _ ss horow)) ?_
  refine runE_bind_ok
    (runE_lift (runS_k_account_is_empty_hit _ bv _ ss hbrow)) ?_
  refine runE_bind_ok
    (runE_lift (runS_charge_ok g (sdExecRaw warm (sdCreatesS ov bv)) _ ss
      (by rw [sdExecRaw_eq, hcreates]; exact hcharge))) ?_
  rw [if_neg (by simp)]
  refine runE_bind_throw ?_
  rw [if_pos hc']
  refine runE_bind_ok
    (runE_lift (runS_charge_state_gas_oog _ G_amsterdam_state_new_account
      _ ss res _ sp msg hprof hsp hmsg hres hfork (by decide)
      (by rw [newAccount_eq]; exact hshort)
      (by rw [newAccount_eq, sdExecRaw_eq, hcreates]; exact hoog))) ?_
  rw [if_pos (by simp)]
  exact runE_bind_throw (runE_throw _ _ _)

/-! ### The success path

The state charge is guarded by `creates_account`, so it is stepped over
by `runE_sd_state_charge` and its three closed forms rather than split at
the call site; the lifecycle mark is a lifted guard, which
`runE_cond_val` steps. -/

/-- The live execution gas after the (guarded) state charge. -/
def sdGasOut (g1 res : Nat) (creates : Bool) : Nat :=
  if creates then
    g1 - (StateGasCosts.NEW_ACCOUNT - min StateGasCosts.NEW_ACCOUNT res)
  else g1

/-- The state-gas reservoir after it. -/
def sdResOut (res : Nat) (creates : Bool) : Nat :=
  if creates then res - min StateGasCosts.NEW_ACCOUNT res else res

/-- The recorded spill after it. -/
def sdSpillOut (res sp : Nat) (creates : Bool) : Nat :=
  if creates then
    sp + (StateGasCosts.NEW_ACCOUNT - min StateGasCosts.NEW_ACCOUNT res)
  else sp

open Evm.Functions in
/-- **The guarded state charge, stepped over.** Both legs leave
`sdGasOut`, and the register file is `sdResOut`/`sdSpillOut` with
everything else untouched — so the continuation gets the frame condition
it needs to carry `hprof`/`hmsg` across the charge. This is the
affordable leg only; the other one is
`runS_selfdestruct_body_state_oog`, which is why `hafford`/`hroom` are
conditional on `creates`: an unaffordable state charge that never runs
must not narrow the theorem's domain.

The register file is handed back through an existential rather than a
continuation so that a caller whose own conclusion is `∃ ss'` can name
its witness before stepping into the chain. -/
theorem runE_sd_state_charge (creates : Bool) (g1 : Nat)
    (hs : Evm.HostState) (ss : SeqState) (res sp : Nat) (top1 : StackTop)
    (hres : ss.regs.get? Register.state_gas_remaining = some res)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hafford : creates = true →
      StateGasCosts.NEW_ACCOUNT - min StateGasCosts.NEW_ACCOUNT res ≤ g1)
    (hroom : creates = true →
      sp + (StateGasCosts.NEW_ACCOUNT
        - min StateGasCosts.NEW_ACCOUNT res) ≤ 2 ^ 24) :
    ∃ ssC : SeqState,
      (∀ (k : Nat → Evm.SailME (StackTop × Nat) (StackTop × Nat))
          (r : EStateM.Result SailError SeqState
            (Except (SailError ⊕ (StackTop × Nat)) (StackTop × Nat)
              × Evm.HostState)),
        runE (k (sdGasOut g1 res creates)) hs ssC = r →
        runE ((if creates = true then do
            let y ← liftM (charge_state_gas g1 G_amsterdam_state_new_account)
            if (!y.1) = true then do
                Evm.SailME.throw ((top1, y.2) : StackTop × Nat)
                pure y.2
              else do
                pure ()
                pure y.2
          else pure g1) >>= k) hs ss = r)
      ∧ ssC.regs.get? Register.state_gas_remaining
          = some (sdResOut res creates)
      ∧ ssC.regs.get? Register.state_gas_spilled
          = some (sdSpillOut res sp creates)
      ∧ (∀ rg : Register, rg ≠ Register.state_gas_remaining →
          rg ≠ Register.state_gas_spilled →
          ssC.regs.get? rg = ss.regs.get? rg) := by
  cases creates
  · refine ⟨ss, fun k r hk => ?_, hres, hsp, fun _ _ _ => rfl⟩
    rw [if_neg (by simp)]
    exact runE_bind_ok (runE_pure _ _ _) hk
  · obtain ⟨ssC, hC, hCres, hCsp, hCframe⟩ :=
      runS_charge_state_closed g1 G_amsterdam_state_new_account hs ss res sp
        hres hsp (by rw [newAccount_eq]; exact hafford rfl)
        (by rw [newAccount_eq]; exact hroom rfl)
    refine ⟨ssC, fun k r hk => ?_, hCres, hCsp, hCframe⟩
    rw [if_pos rfl]
    refine runE_bind_ok
      (b := g1 - (G_amsterdam_state_new_account
        - min G_amsterdam_state_new_account res))
      (hs' := hs) (ss' := ssC) ?_ hk
    refine runE_bind_ok (runE_lift hC) ?_
    rw [if_neg (by simp)]
    exact runE_bind_ok (runE_pure _ _ _) (runE_pure _ _ _)

/-- The row install `k_selfdestruct` performs, when
`k_was_created` says so — and otherwise nothing. -/
def SdMarkWritten (created : Bool) (hs hs' : Evm.HostState)
    (aV : Evm.Defs.address) (v : Evm.Defs.AcctValue) : Prop :=
  if created then
    HostAcctWritten hs hs' aV { v with curr := acctRowDeleted v.curr }
  else hs' = hs

open Evm.Functions in
/-- **Success.** Both charges are afforded, the balance moves, the
EIP-6780 mark fires if the originator was created this transaction, and
the frame halts with `HaltSelfDestruct`.

The transfer is a hypothesis rather than a run shape: it is the piece
[`transfer_equiv`](../Relations/Transfer.lean) and its three degenerate
siblings settle, and it is reached at the register file the state charge
left, so the hypothesis is quantified over that. -/
theorem runS_selfdestruct_body_ok (top : StackTop) (g : Nat)
    (hs hsT : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (res sp : Nat) (msg : Evm.Defs.Message)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (pid : Evm.Defs.address → PrecompileId) (warm : Bool)
    (ov bv ovT : Evm.Defs.AcctValue)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hres : ss.regs.get? Register.state_gas_remaining = some res)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hstatic : msg.is_static = false)
    (hpid : runS (precompile_id_for_address (word_to_address x)) hs ss
      = .ok (pid (word_to_address x), hs) ss)
    (hwarm : warm = (if (pid (word_to_address x)
          != PrecompileId.NotPrecompile) then true
        else decide (hs.warmEpoch
          ≤ (assocGet hs.warmAddresses (word_to_address x)).getD 0)))
    (hsentry : selfdestructAccessCost (!warm) ≤ g)
    (horow : hostAcctRow (sdHostWarm pid (word_to_address x) hs) msg.address
      = some ov)
    (hbrow : hostAcctRow (sdHostWarm pid (word_to_address x) hs)
        (word_to_address x) = some bv)
    (hcharge : selfdestructCost (!warm) (sdCreatesS ov bv) ≤ g)
    (hafford : sdCreatesS ov bv = true →
      StateGasCosts.NEW_ACCOUNT - min StateGasCosts.NEW_ACCOUNT res
        ≤ g - selfdestructCost (!warm) (sdCreatesS ov bv))
    (hroom : sdCreatesS ov bv = true →
      sp + (StateGasCosts.NEW_ACCOUNT
        - min StateGasCosts.NEW_ACCOUNT res) ≤ 2 ^ 24)
    (htrans : ∀ ss₀ : SeqState,
      ss₀.regs.get? Register.k_execution_profile = some prof →
      runS (k_transfer msg.address (word_to_address x) ov.curr.info.balance)
          (sdHostWarm pid (word_to_address x) hs) ss₀ = .ok ((), hsT) ss₀)
    (hoT : hostAcctRow hsT msg.address = some ovT) :
    ∃ (hsOut : Evm.HostState) (ss' : SeqState),
      runS (Evm.Functions.execute_selfdestruct top g) hs ss
          = .ok ((cursorDrop top 1,
              sdGasOut (g - selfdestructCost (!warm) (sdCreatesS ov bv)) res
                (sdCreatesS ov bv)), hsOut) ss'
      ∧ SdMarkWritten ovT.curr.created hsT hsOut msg.address ovT
      ∧ ss'.regs.get? Register.state_gas_remaining
          = some (sdResOut res (sdCreatesS ov bv))
      ∧ ss'.regs.get? Register.state_gas_spilled
          = some (sdSpillOut res sp (sdCreatesS ov bv))
      ∧ ss'.regs.get? Register.frame_status
          = some (FrameStatus.Halted (HaltKind.HaltSelfDestruct ()))
      ∧ ss'.regs.get? Register.k_execution_profile = some prof
      ∧ ss'.regs.get? Register.message = some msg := by
  have hwarmrun : runS (k_account_is_warm (word_to_address x)) hs ss
      = .ok (warm, hs) ss := by
    rw [hwarm]
    exact runS_k_account_is_warm pid _ hs ss hpid
  obtain ⟨hsD, hmark, hwritten⟩ :=
    runS_k_selfdestruct_hit msg.address ovT hsT hoT
  obtain ⟨ssC, hstep, hCres, hCsp, hCframe⟩ :=
    runE_sd_state_charge (sdCreatesS ov bv)
      (g - selfdestructCost (!warm) (sdCreatesS ov bv))
      (sdHostWarm pid (word_to_address x) hs) ss res sp
      (cursorDrop top 1) hres hsp hafford hroom
  refine ⟨if ovT.curr.created then hsD else hsT,
    { ssC with
        regs := ssC.regs.insert Register.frame_status
          (FrameStatus.Halted (HaltKind.HaltSelfDestruct ())) },
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨fork, t, mx, dn, cl, il, ptl, prl, tbl, rd, bl, ttl, trl, epf⟩ :=
      prof
    simp only at hfork
    simp only [Evm.Functions.execute_selfdestruct]
    refine runS_sailME_ok ?_
    refine runE_bind_ok (runE_lift (runS_readReg _ _ _ _ hprof)) ?_
    refine runE_bind_ok
      (runE_lift (runS_guard_static_ok g hs ss msg hmsg hstatic)) ?_
    rw [if_neg (by simp)]
    refine runE_bind_ok
      (runE_lift (runS_pop top hs ss l frest x rest hframe hpfx htop)) ?_
    refine runE_bind_ok (runE_lift (runS_self_addr msg hs ss hmsg)) ?_
    simp only [ProtocolProfileFields.fork, decide_eq_true_eq]
    rw [if_pos (by simpa using hfork)]
    refine runE_bind_ok (runE_lift hwarmrun) ?_
    refine runE_bind_ok
      (runE_lift (runS_check_execution_gas_ok g (sdAccessRaw warm) hs ss
        (by rw [sdAccessRaw_eq]; exact hsentry))) ?_
    rw [if_neg (by simp)]
    refine runE_bind_ok
      (runE_lift (runS_k_account_mark_warm pid _ hs ss hpid)) ?_
    refine runE_bind_ok
      (runE_lift (runS_k_get_balance_hit _ ov _ ss horow)) ?_
    refine runE_bind_ok
      (runE_lift (runS_k_account_is_empty_hit _ bv _ ss hbrow)) ?_
    refine runE_bind_ok
      (runE_lift (runS_charge_ok g (sdExecRaw warm (sdCreatesS ov bv)) _ ss
        (by rw [sdExecRaw_eq]; exact hcharge))) ?_
    rw [if_neg (by simp), sdExecRaw_eq]
    refine hstep _ _ ?_
    refine runE_bind_ok
      (runE_lift (htrans ssC ((hCframe _ (by decide) (by decide)).trans
        (by simpa using hprof)))) ?_
    refine runE_bind_ok
      (runE_lift (runS_k_was_created_hit msg.address ovT hsT ssC hoT)) ?_
    refine runE_cond_val ovT.curr.created _ () () _ (hmark ssC) ?_
    rw [ite_self]
    refine runE_bind_ok (runE_lift (runS_writeReg _ _ _ _)) ?_
    exact runE_pure _ _ _
  · unfold SdMarkWritten
    cases ovT.curr.created
    · rfl
    · exact hwritten
  · rw [regs_get?_insert_ne _ _ (by decide)]
    exact hCres
  · rw [regs_get?_insert_ne _ _ (by decide)]
    exact hCsp
  · simp only [Std.ExtDHashMap.get?_insert]
    simp
  · rw [regs_get?_insert_ne _ _ (by decide)]
    exact (hCframe _ (by decide) (by decide)).trans hprof
  · rw [regs_get?_insert_ne _ _ (by decide)]
    exact (hCframe _ (by decide) (by decide)).trans hmsg

/-! ### The `execute` wrappers

`execute` runs the Yellow Paper stack-validity predicate before any gas
or side effect, then dispatches. `SELFDESTRUCT` takes one operand and
returns none, so the only new outcome at this level is the underflow —
every other one just carries a body shape through the dispatch. -/

open Evm.Functions in
/-- **Underflow.** `validate_stack` fails before `execute_selfdestruct`
is entered, so this shape holds whatever `msg.is_static` is — which is
MM-14 (see the module docstring): in a static frame with an empty stack
SpecRef reports `.writeInStaticContext` where this reports
`StackUnderflow`. Both consume the frame's gas, so the pairing is settled
by the `halted` constructor at `StepResultRel`. -/
theorem runS_execute_selfdestruct_underflow (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 1) :
    runS (Evm.Functions.execute (.SELFDESTRUCT ()) pc_in top mem g) hs ss
      = .ok ((pc_in, top, mem, GAS_ZERO), hs)
          { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute, selfdestruct_stack_effect]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 1 0 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
/-- The stack-validity predicate passes, so `execute` is the body plus
the pass-through of `pc_in` and the memory. Stated once, over an
arbitrary body outcome, so each of the five outcomes below is one line. -/
theorem runS_execute_selfdestruct_of_body (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs hs' : Evm.HostState)
    (ss ss' : SeqState) (top' : StackTop) (g' : Nat)
    (hin : 1 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (hbody : runS (Evm.Functions.execute_selfdestruct top g) hs ss
      = .ok ((top', g'), hs') ss') :
    runS (Evm.Functions.execute (.SELFDESTRUCT ()) pc_in top mem g) hs ss
      = .ok ((pc_in, top', mem, g'), hs') ss' := by
  simp only [Evm.Functions.execute, selfdestruct_stack_effect]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 0 hs ss hin
      (by have h : top.toNat - 1 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, selfdestruct_dispatch]
  exact runS_bind_ok hbody (runS_pure _ _ _)

/-! ## The step equivalence

### The rows, and what the step needs about them

`sdHostWarm` touches only `warmAddresses`, so every account row survives
it — which is what lets the agreement bundle below be stated on the
*pre*-state rows. -/

@[simp] theorem hostAcctRow_sdHostWarm (pid : Evm.Defs.address → PrecompileId)
    (bV : Evm.Defs.address) (hs : Evm.HostState) (aV : Evm.Defs.address) :
    hostAcctRow (sdHostWarm pid bV hs) aV = hostAcctRow hs aV := rfl

/-- **The transfer agrees**, in whichever of its four shapes applies.
This is `transfer_equiv`'s conclusion minus the log clause (which
`TransferPost` already carries), quantified over the machine the handler
actually reaches the transfer at — the charges and the reads have already
moved `sRef`'s gas and read marks by then, and `moveEther` reads the live
tracker, so a statement at `sRef` would not transport. The three frame
conditions on `M` are exactly what a caller needs to re-derive
`AccountRel`/`LogRel` there. Each of
[`transfer_equiv`](../Relations/Transfer.lean),
`transfer_equiv_self`, `transfer_equiv_zero` and
`transfer_equiv_zero_collapse` produces it.

It is a hypothesis rather than something the step theorem derives because
choosing among the four needs facts `AccountRel` does not supply: the
non-wrap bound on the beneficiary's balance (MM-19), and — for the zero
case — whether the beneficiary collapses and whether it has pending
storage writes (MM-18). Two of `transfer_equiv`'s side conditions *are*
automatic here and are noted rather than assumed: the originator cannot
collapse, because it is executing code and so is not EIP-161-empty, and a
nonzero-value beneficiary cannot collapse, because the credit leaves it
with a nonzero balance. -/
def SelfdestructTransfer (sRef : Machine) (hs : Evm.HostState) (base : Nat)
    (prof : ExecutionProfile) (oV bV : Evm.Defs.address) (v : U256) : Prop :=
  ∀ M : Machine,
    M.txState.accountWrites = sRef.txState.accountWrites →
    M.txState.createdAccounts = sRef.txState.createdAccounts →
    M.evm.logs = sRef.evm.logs →
    ∃ (sR' : Machine) (hs' : Evm.HostState),
      runR (specTransfer oV.toList bV.toList v) M = .ok (.ok (), sR')
      ∧ (∀ ss : SeqState,
          ss.regs.get? Register.k_execution_profile = some prof →
          runS (Evm.Functions.k_transfer oV bV v) hs ss = .ok ((), hs') ss)
      ∧ TransferPost base sR' hs'
      ∧ TransferFrame M sR'
      ∧ TransferHostFrame hs hs'
      ∧ TransferFlagFrame hs hs'

/-- Success post-relation for SELFDESTRUCT. The gas clauses mirror
[`StopPost`](Stop.lean) — a halted frame's pc, stack and memory are not
observable past the frame boundary — and the four world clauses are the
step's footprint: the account overlay, the log store, the access list and
the EIP-6780 lifecycle flags. -/
def SelfdestructPost (pid : Evm.Defs.address → PrecompileId) (base : Nat)
    (outer : List Address) (sR' : Machine) (step : EvmStep)
    (hs' : Evm.HostState) (ss' : SeqState) : Prop :=
  sR'.evm.running = false
  ∧ step.2.2.2 = sR'.evm.gasLeft
  ∧ ss'.regs.get? Register.state_gas_remaining = some sR'.evm.stateGasLeft
  ∧ ss'.regs.get? Register.state_gas_spilled = some sR'.evm.stateGasSpilled
  ∧ ss'.regs.get? Register.frame_status
      = some (FrameStatus.Halted (HaltKind.HaltSelfDestruct ()))
  ∧ AccountRel sR'.txState hs'
  ∧ LogRel sR'.evm.logs hs' base
  ∧ WarmAddrRel pid sR' hs'
  ∧ LifecycleRel sR' hs' outer

/-! ### The frame's other fields, across the whole step

Everything the post-relation reads that is *not* gas: the access set
(`WarmAddrRel`), the log store (`LogRel`), the deletion list
(`LifecycleRel`) and `running`. Each is a projection of the composition,
so each is one `rfl`-or-`cases` lemma rather than a record unfolding at
the use site. -/

@[simp] theorem sdWarmedEvm_accessedAddresses (e : Evm) (rest : List U256)
    (cold : Bool) (b : Address) :
    (sdWarmedEvm e rest cold b).accessedAddresses
      = if cold then setAdd e.accessedAddresses b else e.accessedAddresses := by
  unfold sdWarmedEvm sdWarmEvm sdPoppedEvm
  cases cold <;> rfl

@[simp] theorem sdWarmedEvm_accountsToDelete (e : Evm) (rest : List U256)
    (cold : Bool) (b : Address) :
    (sdWarmedEvm e rest cold b).accountsToDelete = e.accountsToDelete := by
  unfold sdWarmedEvm sdWarmEvm sdPoppedEvm
  cases cold <;> rfl

@[simp] theorem chargeEvm_accessedAddresses (e : Evm) (amount : Uint) :
    (chargeEvm e amount).accessedAddresses = e.accessedAddresses := rfl

@[simp] theorem chargeEvm_accountsToDelete (e : Evm) (amount : Uint) :
    (chargeEvm e amount).accountsToDelete = e.accountsToDelete := rfl

@[simp] theorem chargeEvm_logs (e : Evm) (amount : Uint) :
    (chargeEvm e amount).logs = e.logs := rfl

@[simp] theorem chargeStateEvm_accessedAddresses (e : Evm) (amount : Uint) :
    (chargeStateEvm e amount).accessedAddresses = e.accessedAddresses := by
  unfold chargeStateEvm
  split <;> rfl

@[simp] theorem chargeStateEvm_accountsToDelete (e : Evm) (amount : Uint) :
    (chargeStateEvm e amount).accountsToDelete = e.accountsToDelete := by
  unfold chargeStateEvm
  split <;> rfl

@[simp] theorem chargeStateEvm_logs (e : Evm) (amount : Uint) :
    (chargeStateEvm e amount).logs = e.logs := by
  unfold chargeStateEvm
  split <;> rfl

@[simp] theorem sdHaltEvm_running (e : Evm) : (sdHaltEvm e).running = false := rfl

@[simp] theorem sdHaltEvm_gasLeft (e : Evm) :
    (sdHaltEvm e).gasLeft = e.gasLeft := rfl

@[simp] theorem sdHaltEvm_stateGasLeft (e : Evm) :
    (sdHaltEvm e).stateGasLeft = e.stateGasLeft := rfl

@[simp] theorem sdHaltEvm_stateGasSpilled (e : Evm) :
    (sdHaltEvm e).stateGasSpilled = e.stateGasSpilled := rfl

@[simp] theorem sdHaltEvm_logs (e : Evm) : (sdHaltEvm e).logs = e.logs := rfl

@[simp] theorem sdHaltEvm_accessedAddresses (e : Evm) :
    (sdHaltEvm e).accessedAddresses = e.accessedAddresses := rfl

@[simp] theorem sdHaltEvm_accountsToDelete (e : Evm) :
    (sdHaltEvm e).accountsToDelete = e.accountsToDelete := rfl

@[simp] theorem sdMarkEvm_gasLeft (e : Evm) (mark : Bool) (a : Address) :
    (sdMarkEvm e mark a).gasLeft = e.gasLeft := by
  unfold sdMarkEvm specMarkDeleted
  cases mark <;> rfl

@[simp] theorem sdMarkEvm_stateGasLeft (e : Evm) (mark : Bool) (a : Address) :
    (sdMarkEvm e mark a).stateGasLeft = e.stateGasLeft := by
  unfold sdMarkEvm specMarkDeleted
  cases mark <;> rfl

@[simp] theorem sdMarkEvm_stateGasSpilled (e : Evm) (mark : Bool)
    (a : Address) :
    (sdMarkEvm e mark a).stateGasSpilled = e.stateGasSpilled := by
  unfold sdMarkEvm specMarkDeleted
  cases mark <;> rfl

@[simp] theorem sdMarkEvm_logs (e : Evm) (mark : Bool) (a : Address) :
    (sdMarkEvm e mark a).logs = e.logs := by
  unfold sdMarkEvm specMarkDeleted
  cases mark <;> rfl

@[simp] theorem sdMarkEvm_accessedAddresses (e : Evm) (mark : Bool)
    (a : Address) :
    (sdMarkEvm e mark a).accessedAddresses = e.accessedAddresses := by
  unfold sdMarkEvm specMarkDeleted
  cases mark <;> rfl

@[simp] theorem sdMarkEvm_accountsToDelete (e : Evm) (mark : Bool)
    (a : Address) :
    (sdMarkEvm e mark a).accountsToDelete
      = if mark then setAdd e.accountsToDelete a else e.accountsToDelete := by
  unfold sdMarkEvm specMarkDeleted
  cases mark <;> rfl

/-! ### The two gas dimensions, matched

Both sides split on whether the reservoir covers `NEW_ACCOUNT`;
`chargeStateEvm` and `sdGasOut`/`sdResOut`/`sdSpillOut` each already
carry the split, so this is one lemma rather than a case analysis at
every use. No affordability hypothesis: `chargeStateEvm` is total, and
for `creates = false` the amount is zero and both sides are identities. -/

@[simp] theorem sdWarmedEvm_stateGasSpilled (e : Evm) (rest : List U256)
    (cold : Bool) (b : Address) :
    (sdWarmedEvm e rest cold b).stateGasSpilled = e.stateGasSpilled := by
  unfold sdWarmedEvm sdWarmEvm sdPoppedEvm
  cases cold <;> rfl

@[simp] theorem chargeEvm_stateGasSpilled (e : Evm) (amount : Uint) :
    (chargeEvm e amount).stateGasSpilled = e.stateGasSpilled := rfl

/-- **The two gas dimensions agree after both charges.** SpecRef's
`chargeEvm` then `chargeStateEvm` against the extraction's
`sdGasOut`/`sdResOut`/`sdSpillOut`. Both sides split on whether the
reservoir covers `NEW_ACCOUNT` and both closed forms already carry the
split, so no affordability hypothesis is needed: `chargeStateEvm` is
total, and for `creates = false` the amount is zero and every leg is an
identity. -/
theorem sdChargedEvm_gas (e : Evm) (rest : List U256) (cold creates : Bool)
    (b : Address) :
    (sdChargedEvm e rest cold creates b).gasLeft
        = sdGasOut (e.gasLeft - selfdestructCost cold creates) e.stateGasLeft
            creates
      ∧ (sdChargedEvm e rest cold creates b).stateGasLeft
        = sdResOut e.stateGasLeft creates
      ∧ (sdChargedEvm e rest cold creates b).stateGasSpilled
        = sdSpillOut e.stateGasLeft e.stateGasSpilled creates := by
  obtain ⟨⟨hg, hr⟩, hsp⟩ := chargeStateEvm_proj
    (chargeEvm (sdWarmedEvm e rest cold b) (selfdestructCost cold creates))
    (if creates then StateGasCosts.NEW_ACCOUNT else 0)
  unfold sdChargedEvm sdGasOut sdResOut sdSpillOut
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]
    simp only [chargeEvm_gasLeft, chargeEvm_stateGasLeft,
      sdWarmedEvm_gasLeft, sdWarmedEvm_stateGasLeft]
    cases creates <;> simp
  · rw [hr]
    simp only [chargeEvm_stateGasLeft, sdWarmedEvm_stateGasLeft]
    cases creates <;> simp
  · rw [hsp]
    simp only [chargeEvm_stateGasLeft, chargeEvm_stateGasSpilled,
      sdWarmedEvm_stateGasLeft, sdWarmedEvm_stateGasSpilled]
    cases creates <;> simp

/-! ### `SelfdestructTransfer` is reducible, in all four shapes

The hypothesis is not an article of faith: each of the four transfer
pairings discharges it, so what actually stays assumed is only *which*
shape a given state is in, plus the side conditions those pairings
already ledger (MM-19's non-wrap bound, MM-18's collapse tests). The
frame conditions on `M` are exactly what re-derives `AccountRel` and
`LogRel` at the machine the handler reaches the transfer at. -/

theorem selfdestructTransfer_nondegenerate (sRef : Machine)
    (hs : Evm.HostState) (base : Nat) (prof : ExecutionProfile)
    (oV bV : Evm.Defs.address) (v : U256) (sv dv : Evm.Defs.AcctValue)
    (hfork : AmsterdamProfile prof)
    (harel : AccountRel sRef.txState hs)
    (hlrel : LogRel sRef.evm.logs hs base)
    (hsrc : hostAcctRow hs oV = some sv)
    (hdst : hostAcctRow hs bV = some dv)
    (hne : bV ≠ oV) (hv : v ≠ 0)
    (hbal : v ≤ sv.curr.info.balance)
    (hsum : dv.curr.info.balance + v < 2 ^ 256)
    (hsne : Evm.Functions.account_info_empty (transferSrcInfo sv.curr.info v)
      = false)
    (hdne : Evm.Functions.account_info_empty (transferDstInfo dv.curr.info v)
      = false) :
    SelfdestructTransfer sRef hs base prof oV bV v := by
  intro M hfa _ hfl
  obtain ⟨sR', hs', hspec, hrunS, hpost, -, hfr, hhf, hflag⟩ :=
    transfer_equiv oV bV v M hs base sv dv prof hfork
      (accountRel_frame hfa harel) (by rw [hfl]; exact hlrel)
      hsrc hdst hne hv hbal hsum hsne hdne
  exact ⟨sR', hs', hspec, hrunS, hpost, hfr, hhf, hflag⟩

theorem selfdestructTransfer_self (sRef : Machine) (hs : Evm.HostState)
    (base : Nat) (prof : ExecutionProfile) (aV : Evm.Defs.address) (v : U256)
    (av : Evm.Defs.AcctValue)
    (harel : AccountRel sRef.txState hs)
    (hlrel : LogRel sRef.evm.logs hs base)
    (hrow : hostAcctRow hs aV = some av)
    (hv : v ≠ 0) (hbal : v ≤ av.curr.info.balance)
    (hsne : Evm.Functions.account_info_empty (transferSrcInfo av.curr.info v)
      = false) :
    SelfdestructTransfer sRef hs base prof aV aV v := by
  intro M hfa _ hfl
  obtain ⟨sR', hspec, hrunS, hpost, -, hfr, hhf, hflag⟩ :=
    transfer_equiv_self aV v M hs base av
      (accountRel_frame hfa harel) (by rw [hfl]; exact hlrel)
      hrow hv hbal hsne
  exact ⟨sR', hs, hspec, fun _ _ => hrunS _, hpost, hfr, hhf, hflag⟩

theorem selfdestructTransfer_zero (sRef : Machine) (hs : Evm.HostState)
    (base : Nat) (prof : ExecutionProfile) (oV bV : Evm.Defs.address)
    (sv dv : Evm.Defs.AcctValue)
    (harel : AccountRel sRef.txState hs)
    (hlrel : LogRel sRef.evm.logs hs base)
    (hsrc : hostAcctRow hs oV = some sv)
    (hdst : hostAcctRow hs bV = some dv)
    (hne : bV ≠ oV)
    (hsne : Evm.Functions.account_info_empty sv.curr.info = false)
    (hdne : Evm.Functions.account_info_empty dv.curr.info = false) :
    SelfdestructTransfer sRef hs base prof oV bV 0 := by
  intro M hfa _ hfl
  obtain ⟨sR', hspec, hrunS, hpost, -, hfr, hhf, hflag⟩ :=
    transfer_equiv_zero oV bV M hs base sv dv
      (accountRel_frame hfa harel) (by rw [hfl]; exact hlrel)
      hsrc hdst hne hsne hdne
  exact ⟨sR', hs, hspec, fun _ _ => hrunS _, hpost, hfr, hhf, hflag⟩

theorem selfdestructTransfer_zero_collapse (sRef : Machine)
    (hs : Evm.HostState) (base : Nat) (prof : ExecutionProfile)
    (oV bV : Evm.Defs.address) (sv dv : Evm.Defs.AcctValue)
    (harel : AccountRel sRef.txState hs)
    (hlrel : LogRel sRef.evm.logs hs base)
    (hsrc : hostAcctRow hs oV = some sv)
    (hdst : hostAcctRow hs bV = some dv)
    (hne : bV ≠ oV)
    (hsne : Evm.Functions.account_info_empty sv.curr.info = false)
    (hdemp : Evm.Functions.account_info_empty dv.curr.info = true)
    (hstore : ∀ M : Machine,
      M.txState.accountWrites = sRef.txState.accountWrites →
      dictGet? M.txState.storageWrites bV.toList = none) :
    SelfdestructTransfer sRef hs base prof oV bV 0 := by
  intro M hfa _ hfl
  obtain ⟨sR', hspec, hrunS, hpost, -, hfr, hhf, hflag⟩ :=
    transfer_equiv_zero_collapse oV bV M hs base sv dv
      (accountRel_frame hfa harel) (by rw [hfl]; exact hlrel)
      hsrc hdst hne hsne hdemp (hstore M hfa)
  exact ⟨sR', hs, hspec, fun _ _ => hrunS _, hpost, hfr, hhf, hflag⟩

/-! ### The outcomes, paired

One lemma per outcome, each concluding `StepResultRel` on its own state
class. The dispatcher that case-splits over them is the last piece. -/

open Evm.Functions in
/-- **Underflow, and MM-14's double fault.** The extraction's hoisted
`validate_stack` fires whatever the static flag is, so this single shape
covers both SpecRef outcomes: `.stackUnderflow` in a non-static frame and
`.writeInStaticContext` in a static one (the latter through
`haltedStaticFirst`). It needs no static hypothesis for that reason. -/
theorem selfdestruct_equiv_underflow (sRef : Machine) (top : StackTop)
    (g : Nat) (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat) (pid : Evm.Defs.address → PrecompileId) (base : Nat)
    (outer : List Address)
    (hrel : StateRel sRef top g hs ss)
    (hunder : sRef.evm.stack = []) :
    StepResultRel (SelfdestructPost pid base outer) (runR iSelfdestruct sRef)
      (runS (Evm.Functions.execute (.SELFDESTRUCT ()) pc_in top mem g) hs ss)
      := by
  obtain ⟨hstackR, hgasR, -, -, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨-, htop, -, -⟩ := hstackR
  rw [runS_execute_selfdestruct_underflow pc_in top g mem hs ss prof
      sRef.evm.stateGasSpilled msg hprof hgasR.spilled hmsg hfork
      (by rw [htop, hunder]; simp)]
  by_cases hstat : sRef.evm.message.isStatic = true
  · rw [runR_iSelfdestruct_static sRef hstat]
    exact StepResultRel.haltedStaticFirst
      (haltRegs_frame_status ss msg .StackUnderflow)
  · rw [runR_iSelfdestruct_underflow sRef (by simpa using hstat) hunder]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)

open Evm.Functions in
/-- **The static halt**, with an operand present so the stack check
passes and both sides reach their own `isStatic` test. -/
theorem selfdestruct_equiv_static (sRef : Machine) (top : StackTop)
    (g : Nat) (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat) (pid : Evm.Defs.address → PrecompileId) (base : Nat)
    (outer : List Address)
    (hrel : StateRel sRef top g hs ss)
    (hstatic : ∀ m : Evm.Defs.Message,
      ss.regs.get? Register.message = some m →
      m.is_static = sRef.evm.message.isStatic)
    (hstat : sRef.evm.message.isStatic = true)
    (hne : 1 ≤ sRef.evm.stack.length) :
    StepResultRel (SelfdestructPost pid base outer) (runR iSelfdestruct sRef)
      (runS (Evm.Functions.execute (.SELFDESTRUCT ()) pc_in top mem g) hs ss)
      := by
  obtain ⟨hstackR, hgasR, -, -, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨-, htop, hlim, -⟩ := hstackR
  rw [runR_iSelfdestruct_static sRef hstat,
    runS_execute_selfdestruct_of_body pc_in top g mem hs _ ss _ _ _
      (by rw [htop]; exact hne) (by rw [htop]; exact hlim)
      (runS_selfdestruct_body_static top g hs ss prof
        sRef.evm.stateGasSpilled msg hprof hgasR.spilled hmsg hfork
        (by rw [hstatic msg hmsg]; exact hstat))]
  exact StepResultRel.halted ErrorRel.writeInStaticContext
    (haltRegs_frame_status ss msg .WriteProtection)

/-- **The two `creates_account` flags agree.** SpecRef's
`beneficiary_dead && originator_has_balance` against the extraction's
`nonzero_balance && beneficiary_empty`: the same conjunction with its
operands the other way round, over operands
[`beneficiaryDead_eq`](../Relations/Selfdestruct.lean) and
`originatorHasBalance_eq` identify. -/
theorem sdCreates_eq {sRef : Machine} {hs : Evm.HostState}
    (harel : AccountRel sRef.txState hs)
    (oV bV : Evm.Defs.address) (ov bv : Evm.Defs.AcctValue)
    (horow : hostAcctRow hs oV = some ov)
    (hbrow : hostAcctRow hs bV = some bv) :
    sdCreates ((hostAcctView bv.curr).getD EMPTY_ACCOUNT != EMPTY_ACCOUNT)
        ((hostAcctView ov.curr).getD EMPTY_ACCOUNT).balance
      = sdCreatesS ov bv := by
  unfold sdCreates sdCreatesS
  rw [beneficiaryDead_eq harel bV bv hbrow,
    show decide (((hostAcctView ov.curr).getD EMPTY_ACCOUNT).balance ≠ 0)
        = (((hostAcctView ov.curr).getD EMPTY_ACCOUNT).balance != 0)
      from by
        by_cases hb : ((hostAcctView ov.curr).getD EMPTY_ACCOUNT).balance = 0
          <;> simp [hb],
    originatorHasBalance_eq harel oV ov horow, Bool.and_comm]

open Evm.Functions in
/-- **The sentry halt.** Neither side has read a row or marked the
beneficiary warm, so the halt is the pop alone. -/
theorem selfdestruct_equiv_sentry_oog (sRef : Machine) (top : StackTop)
    (g : Nat) (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat) (pid : Evm.Defs.address → PrecompileId) (base : Nat)
    (outer : List Address) (x : U256) (rest : List U256)
    (hrel : StateRel sRef top g hs ss)
    (hwrel : WarmAddrRel pid sRef hs)
    (hpid : ∀ aV, runS (precompile_id_for_address aV) hs ss
      = .ok (pid aV, hs) ss)
    (hstatic : ∀ m : Evm.Defs.Message,
      ss.regs.get? Register.message = some m →
      m.is_static = sRef.evm.message.isStatic)
    (hstat : sRef.evm.message.isStatic = false)
    (hstack : sRef.evm.stack = x :: rest)
    (hoog : sRef.evm.gasLeft < selfdestructAccessCost
      (!sRef.evm.accessedAddresses.contains (to_address_masked x))) :
    StepResultRel (SelfdestructPost pid base outer) (runR iSelfdestruct sRef)
      (runS (Evm.Functions.execute (.SELFDESTRUCT ()) pc_in top mem g) hs ss)
      := by
  obtain ⟨hstackR, hgasR, -, -, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, -⟩ := hstackR
  rw [hstack] at hpfx htop hlim
  have hwb := warm_of_warmAddrRel pid hwrel (word_to_address x)
  rw [word_to_address_toList] at hwb
  rw [runR_iSelfdestruct_sentry_oog sRef x rest _ hstack hstat rfl hoog,
    runS_execute_selfdestruct_of_body pc_in top g mem hs _ ss _ _ _
      (by rw [htop]; simp) (by simp at htop hlim; omega)
      (runS_selfdestruct_body_sentry_oog top g hs ss prof
        sRef.evm.stateGasSpilled msg l frest x rest pid _
        hprof hgasR.spilled hmsg hfork hframe hpfx htop
        (by rw [hstatic msg hmsg]; exact hstat) (hpid _) hwb.symm
        (by rw [hgasR.live]; exact hoog))]
  exact StepResultRel.halted ErrorRel.outOfGas
    (haltRegs_frame_status ss msg .OutOfGas)

/-- A read mark leaves the write map alone, so a row read back at the
state after one read is the row before it. -/
theorem specAcctRow_specAccountReadOf (ts : TransactionState) (a b : Address) :
    specAcctRow (specAccountReadOf ts b) a = specAcctRow ts a := rfl

open Evm.Functions in
/-- **The regular-charge halt.** Both sides have popped, marked the
beneficiary warm and read both rows; neither has written one. -/
theorem selfdestruct_equiv_charge_oog (sRef : Machine) (top : StackTop)
    (g : Nat) (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat) (pid : Evm.Defs.address → PrecompileId) (base : Nat)
    (outer : List Address) (x : U256) (rest : List U256)
    (ov bv : Evm.Defs.AcctValue)
    (hrel : StateRel sRef top g hs ss)
    (hwrel : WarmAddrRel pid sRef hs)
    (harel : AccountRel sRef.txState hs)
    (hpid : ∀ aV, runS (precompile_id_for_address aV) hs ss
      = .ok (pid aV, hs) ss)
    (haddr : ∀ m : Evm.Defs.Message,
      ss.regs.get? Register.message = some m →
      m.address.toList = sRef.evm.message.currentTarget)
    (hstatic : ∀ m : Evm.Defs.Message,
      ss.regs.get? Register.message = some m →
      m.is_static = sRef.evm.message.isStatic)
    (hrows : ∀ m : Evm.Defs.Message,
      ss.regs.get? Register.message = some m →
      hostAcctRow hs m.address = some ov)
    (hbrow : hostAcctRow hs (word_to_address x) = some bv)
    (hstat : sRef.evm.message.isStatic = false)
    (hstack : sRef.evm.stack = x :: rest)
    (hsentry : selfdestructAccessCost
      (!sRef.evm.accessedAddresses.contains (to_address_masked x))
      ≤ sRef.evm.gasLeft)
    (hoog : sRef.evm.gasLeft
      < selfdestructCost
          (!sRef.evm.accessedAddresses.contains (to_address_masked x))
          (sdCreatesS ov bv)) :
    StepResultRel (SelfdestructPost pid base outer) (runR iSelfdestruct sRef)
      (runS (Evm.Functions.execute (.SELFDESTRUCT ()) pc_in top mem g) hs ss)
      := by
  obtain ⟨hstackR, hgasR, -, -, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, -⟩ := hstackR
  rw [hstack] at hpfx htop hlim
  have horow := hrows msg hmsg
  have hax := haddr msg hmsg
  have hwb := warm_of_warmAddrRel pid hwrel (word_to_address x)
  rw [word_to_address_toList] at hwb
  -- SpecRef's two reads, from the extraction's rows
  have hbrowR : specAcctRow sRef.txState (to_address_masked x)
      = some (hostAcctView bv.curr) := by
    have h := harel.curr (word_to_address x) bv hbrow
    rwa [word_to_address_toList] at h
  have halive := runTx_isAccountAlive_hit sRef.txState (to_address_masked x)
    _ hbrowR
  have horowR : specAcctRow
      (specAccountReadOf sRef.txState (to_address_masked x))
      sRef.evm.message.currentTarget = some (hostAcctView ov.curr) := by
    rw [specAcctRow_specAccountReadOf, ← hax]
    exact harel.curr msg.address ov horow
  have hacct := runTx_getAccount_hit _ sRef.evm.message.currentTarget _ horowR
  have hcr := sdCreates_eq harel msg.address (word_to_address x) ov bv horow hbrow
  rw [runR_iSelfdestruct_charge_oog sRef x rest _ _ _ _ _
      hstack hstat rfl hsentry halive hacct (by rw [hcr]; exact hoog),
    runS_execute_selfdestruct_of_body pc_in top g mem hs _ ss _ _ _
      (by rw [htop]; simp) (by simp at htop hlim; omega)
      (runS_selfdestruct_body_charge_oog top g hs ss prof
        sRef.evm.stateGasSpilled msg l frest x rest pid _ ov bv
        hprof hgasR.spilled hmsg hfork hframe hpfx htop
        (by rw [hstatic msg hmsg]; exact hstat) (hpid _) hwb.symm
        (by rw [hgasR.live]; exact hsentry) horow hbrow
        (by rw [hgasR.live]; exact hoog))]
  exact StepResultRel.halted ErrorRel.outOfGas
    (haltRegs_frame_status ss msg .OutOfGas)

open Evm.Functions in
/-- **The state-charge halt.** Only reachable when `creates_account`, so
the regular charge has already gone through on both sides and what fails
is the `NEW_ACCOUNT` charge against the reservoir plus the execution gas
the regular charge left. The one hypothesis is SpecRef's form of that;
the extraction's two-part form (`hshort` and its own `hoog`) follows by
arithmetic, which is the whole content of the two dimensions agreeing
here. -/
theorem selfdestruct_equiv_state_oog (sRef : Machine) (top : StackTop)
    (g : Nat) (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat) (pid : Evm.Defs.address → PrecompileId) (base : Nat)
    (outer : List Address) (x : U256) (rest : List U256)
    (ov bv : Evm.Defs.AcctValue)
    (hrel : StateRel sRef top g hs ss)
    (hwrel : WarmAddrRel pid sRef hs)
    (harel : AccountRel sRef.txState hs)
    (hpid : ∀ aV, runS (precompile_id_for_address aV) hs ss
      = .ok (pid aV, hs) ss)
    (haddr : ∀ m : Evm.Defs.Message,
      ss.regs.get? Register.message = some m →
      m.address.toList = sRef.evm.message.currentTarget)
    (hstatic : ∀ m : Evm.Defs.Message,
      ss.regs.get? Register.message = some m →
      m.is_static = sRef.evm.message.isStatic)
    (hrows : ∀ m : Evm.Defs.Message,
      ss.regs.get? Register.message = some m →
      hostAcctRow hs m.address = some ov)
    (hbrow : hostAcctRow hs (word_to_address x) = some bv)
    (hstat : sRef.evm.message.isStatic = false)
    (hstack : sRef.evm.stack = x :: rest)
    (hsentry : selfdestructAccessCost
      (!sRef.evm.accessedAddresses.contains (to_address_masked x))
      ≤ sRef.evm.gasLeft)
    (hcreates : sdCreatesS ov bv = true)
    (hcharge : selfdestructCost
        (!sRef.evm.accessedAddresses.contains (to_address_masked x)) true
      ≤ sRef.evm.gasLeft)
    (hoog : sRef.evm.stateGasLeft
        + (sRef.evm.gasLeft - selfdestructCost
            (!sRef.evm.accessedAddresses.contains (to_address_masked x)) true)
      < StateGasCosts.NEW_ACCOUNT) :
    StepResultRel (SelfdestructPost pid base outer) (runR iSelfdestruct sRef)
      (runS (Evm.Functions.execute (.SELFDESTRUCT ()) pc_in top mem g) hs ss)
      := by
  obtain ⟨hstackR, hgasR, -, -, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, -⟩ := hstackR
  rw [hstack] at hpfx htop hlim
  have hlive := hgasR.live
  have horow := hrows msg hmsg
  have hax := haddr msg hmsg
  have hwb := warm_of_warmAddrRel pid hwrel (word_to_address x)
  rw [word_to_address_toList] at hwb
  have hbrowR : specAcctRow sRef.txState (to_address_masked x)
      = some (hostAcctView bv.curr) := by
    have h := harel.curr (word_to_address x) bv hbrow
    rwa [word_to_address_toList] at h
  have halive := runTx_isAccountAlive_hit sRef.txState (to_address_masked x)
    _ hbrowR
  have horowR : specAcctRow
      (specAccountReadOf sRef.txState (to_address_masked x))
      sRef.evm.message.currentTarget = some (hostAcctView ov.curr) := by
    rw [specAcctRow_specAccountReadOf, ← hax]
    exact harel.curr msg.address ov horow
  have hacct := runTx_getAccount_hit _ sRef.evm.message.currentTarget _ horowR
  have hcr := sdCreates_eq harel msg.address (word_to_address x) ov bv horow hbrow
  rw [hcreates] at hcr
  -- The extraction's two-part state-gas failure from SpecRef's one-part
  -- form. Stated abstractly first: `omega` silently drops hypotheses
  -- once the goal carries enough opaque atoms and `Nat` subtractions,
  -- and this context has both.
  have key : ∀ a b n : Nat, a + b < n → a < n ∧ b < n - a :=
    fun _ _ _ h => ⟨by omega, by omega⟩
  obtain ⟨hshort, hoogR⟩ := key sRef.evm.stateGasLeft
    (sRef.evm.gasLeft - selfdestructCost
      (!sRef.evm.accessedAddresses.contains (to_address_masked x)) true)
    StateGasCosts.NEW_ACCOUNT hoog
  have hoog' : g - selfdestructCost
        (!sRef.evm.accessedAddresses.contains (to_address_masked x)) true
      < StateGasCosts.NEW_ACCOUNT - sRef.evm.stateGasLeft := by
    rw [hlive]; exact hoogR
  rw [runR_iSelfdestruct_state_oog sRef x rest _ _ _ _ _
      hstack hstat rfl hsentry halive hacct
      (by rw [hcr]; exact hcharge)
      (by rw [hcr, if_pos rfl]; exact hoog),
    runS_execute_selfdestruct_of_body pc_in top g mem hs _ ss _ _ _
      (by rw [htop]; simp) (by simp at htop hlim; omega)
      (runS_selfdestruct_body_state_oog top g hs ss prof
        sRef.evm.stateGasLeft sRef.evm.stateGasSpilled msg l frest x rest
        pid _ ov bv
        hprof hgasR.reservoir hgasR.spilled hmsg hfork hframe hpfx htop
        (by rw [hstatic msg hmsg]; exact hstat) (hpid _) hwb.symm
        (by rw [hgasR.live]; exact hsentry) horow hbrow hcreates
        (by rw [hgasR.live]; exact hcharge) hshort hoog')]
  exact StepResultRel.halted ErrorRel.outOfGas
    (haltRegs_frame_status ss msg .OutOfGas)

open Evm.Functions in
/-- **Success.** Both charges are afforded, the balance moves, the
EIP-6780 mark fires exactly when the originator was created this
transaction, and the frame halts with `HaltSelfDestruct`.

`hroom` is the EIP-7825 cap on the recorded spill, an extraction-only
hard abort with no SpecRef counterpart — threaded rather than
eliminated, exactly as `sstore_step_equiv` threads its own. `hxfer` is
the transfer, in whichever of its four shapes applies; see
`SelfdestructTransfer`. -/
theorem selfdestruct_equiv_ok (sRef : Machine) (top : StackTop)
    (g : Nat) (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat) (pid : Evm.Defs.address → PrecompileId) (base : Nat)
    (outer : List Address) (x : U256) (rest : List U256)
    (ov bv : Evm.Defs.AcctValue)
    (hrel : StateRel sRef top g hs ss)
    (hwrel : WarmAddrRel pid sRef hs)
    (harel : AccountRel sRef.txState hs)
    (hlfrel : LifecycleRel sRef hs outer)
    (hpid : ∀ aV, runS (precompile_id_for_address aV) hs ss
      = .ok (pid aV, hs) ss)
    (haddr : ∀ m : Evm.Defs.Message,
      ss.regs.get? Register.message = some m →
      m.address.toList = sRef.evm.message.currentTarget)
    (hstatic : ∀ m : Evm.Defs.Message,
      ss.regs.get? Register.message = some m →
      m.is_static = sRef.evm.message.isStatic)
    (hrows : ∀ m : Evm.Defs.Message,
      ss.regs.get? Register.message = some m →
      hostAcctRow hs m.address = some ov)
    (hbrow : hostAcctRow hs (word_to_address x) = some bv)
    (hcreated : ∀ m : Evm.Defs.Message,
      ss.regs.get? Register.message = some m → CreatedAgree sRef hs m.address)
    (hxfer : ∀ (m : Evm.Defs.Message) (prof : ExecutionProfile),
      ss.regs.get? Register.message = some m →
      ss.regs.get? Register.k_execution_profile = some prof →
      SelfdestructTransfer sRef (sdHostWarm pid (word_to_address x) hs) base
        prof m.address (word_to_address x)
        ((hostAcctView ov.curr).getD EMPTY_ACCOUNT).balance)
    (hstat : sRef.evm.message.isStatic = false)
    (hstack : sRef.evm.stack = x :: rest)
    (hsentry : selfdestructAccessCost
      (!sRef.evm.accessedAddresses.contains (to_address_masked x))
      ≤ sRef.evm.gasLeft)
    (hcharge : selfdestructCost
        (!sRef.evm.accessedAddresses.contains (to_address_masked x))
        (sdCreatesS ov bv) ≤ sRef.evm.gasLeft)
    (hstate : (if sdCreatesS ov bv then StateGasCosts.NEW_ACCOUNT else 0)
      ≤ sRef.evm.stateGasLeft
        + (sRef.evm.gasLeft - selfdestructCost
            (!sRef.evm.accessedAddresses.contains (to_address_masked x))
            (sdCreatesS ov bv)))
    (hroom : sdCreatesS ov bv = true →
      sRef.evm.stateGasSpilled + (StateGasCosts.NEW_ACCOUNT
        - min StateGasCosts.NEW_ACCOUNT sRef.evm.stateGasLeft) ≤ 2 ^ 24) :
    StepResultRel (SelfdestructPost pid base outer) (runR iSelfdestruct sRef)
      (runS (Evm.Functions.execute (.SELFDESTRUCT ()) pc_in top mem g) hs ss)
      := by
  obtain ⟨hstackR, hgasR, -, -, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, -⟩ := hstackR
  rw [hstack] at hpfx htop hlim
  have hlive := hgasR.live
  have horow := hrows msg hmsg
  have hax := haddr msg hmsg
  have hwb := warm_of_warmAddrRel pid hwrel (word_to_address x)
  rw [word_to_address_toList] at hwb
  -- SpecRef's three reads, from the extraction's rows
  have hbrowR : specAcctRow sRef.txState (to_address_masked x)
      = some (hostAcctView bv.curr) := by
    have h := harel.curr (word_to_address x) bv hbrow
    rwa [word_to_address_toList] at h
  have halive := runTx_isAccountAlive_hit sRef.txState (to_address_masked x)
    _ hbrowR
  have horowR : specAcctRow
      (specAccountReadOf sRef.txState (to_address_masked x))
      sRef.evm.message.currentTarget = some (hostAcctView ov.curr) := by
    rw [specAcctRow_specAccountReadOf, ← hax]
    exact harel.curr msg.address ov horow
  have hacct := runTx_getAccount_hit _ sRef.evm.message.currentTarget _ horowR
  have horowR2 : specAcctRow (specAccountReadOf
      (specAccountReadOf sRef.txState (to_address_masked x))
      sRef.evm.message.currentTarget) sRef.evm.message.currentTarget
      = some (hostAcctView ov.curr) := by
    rw [specAcctRow_specAccountReadOf]
    exact horowR
  have hacct₂ := runTx_getAccount_hit _ sRef.evm.message.currentTarget _
    horowR2
  have hcr := sdCreates_eq harel msg.address (word_to_address x) ov bv horow
    hbrow
  -- the transfer, at the machine the handler reaches it
  obtain ⟨sR', hs', hspec, hrunS, ⟨hpa, hpl⟩, ⟨hfr, hfrc⟩, hhf, hflag⟩ :=
    hxfer msg prof hmsg hprof
      { sRef with
          txState := specAccountReadOf (specAccountReadOf
            (specAccountReadOf sRef.txState (to_address_masked x))
            sRef.evm.message.currentTarget) sRef.evm.message.currentTarget
          evm := sdChargedEvm sRef.evm rest
            (!sRef.evm.accessedAddresses.contains (to_address_masked x))
            (sdCreatesS ov bv) (to_address_masked x) }
      rfl rfl (by simp only [sdChargedEvm, chargeStateEvm_logs, chargeEvm_logs,
        sdWarmedEvm_logs])
  -- the originator's row survives the transfer
  obtain ⟨ovT, hoT⟩ : ∃ ovT, hostAcctRow hs' msg.address = some ovT := by
    have h := hflag msg.address
    rw [show hostAcctRow (sdHostWarm pid (word_to_address x) hs) msg.address
      = some ov from horow] at h
    match hv : hostAcctRow hs' msg.address with
    | none => rw [hv] at h; exact absurd h (by simp)
    | some w => exact ⟨w, rfl⟩
  -- and its `created` flag with it, so the two mark tests agree
  have hcrT : ovT.curr.created
      = sR'.txState.createdAccounts.contains msg.address.toList :=
    createdAgree_transferFrame hflag (by rw [hfrc]; rfl) (hcreated msg hmsg)
      ovT hoT
  -- the extraction's affordability form, from SpecRef's
  have key : ∀ n r q : Nat, n ≤ r + q → n - min n r ≤ q :=
    fun _ _ _ h => by omega
  have hafford : sdCreatesS ov bv = true →
      StateGasCosts.NEW_ACCOUNT
          - min StateGasCosts.NEW_ACCOUNT sRef.evm.stateGasLeft
        ≤ g - selfdestructCost
            (!sRef.evm.accessedAddresses.contains (to_address_masked x))
            (sdCreatesS ov bv) := by
    intro hc
    rw [hlive, hc]
    rw [hc, if_pos rfl] at hstate
    exact key _ _ _ hstate
  have hbal := accountRel_balance harel msg.address ov horow
  rw [hax, word_to_address_toList, ← hcr] at hspec
  obtain ⟨hsOut, ss', hrunE, hmarkW, hOres, hOsp, hOstatus, hOprof, hOmsg⟩ :=
    runS_selfdestruct_body_ok top g hs hs' ss prof sRef.evm.stateGasLeft
      sRef.evm.stateGasSpilled msg l frest x rest pid _ ov bv ovT
      hprof hgasR.reservoir hgasR.spilled hmsg hfork hframe hpfx htop
      (by rw [hstatic msg hmsg]; exact hstat) (hpid _) hwb.symm
      (by rw [hlive]; exact hsentry) horow hbrow
      (by rw [hlive]; exact hcharge) hafford (by rw [hlive] at *; exact hroom)
      (by rw [← hbal]; exact hrunS) hoT
  rw [runR_iSelfdestruct_success_xfer sRef x rest _ _ _ _ _ _ _ sR'
      hstack hstat rfl hsentry halive hacct
      (by rw [hcr]; exact hcharge) (by rw [hcr]; exact hstate) hacct₂ hspec,
    runS_execute_selfdestruct_of_body pc_in top g mem hs _ ss _ _ _
      (by rw [htop]; simp) (by simp at htop hlim; omega) hrunE]
  -- `sR'` differs from the charged machine only in `txState` and `logs`
  have hE : sR'.evm = { sdChargedEvm sRef.evm rest
        (!sRef.evm.accessedAddresses.contains (to_address_masked x))
        (sdCreatesS ov bv) (to_address_masked x) with
      logs := sR'.evm.logs } := congrArg Machine.evm hfr
  obtain ⟨hGgas, hGres, hGsp⟩ := sdChargedEvm_gas sRef.evm rest
    (!sRef.evm.accessedAddresses.contains (to_address_masked x))
    (sdCreatesS ov bv) (to_address_masked x)
  have hPgas : sR'.evm.gasLeft = sdGasOut
      (sRef.evm.gasLeft - selfdestructCost
        (!sRef.evm.accessedAddresses.contains (to_address_masked x))
        (sdCreatesS ov bv)) sRef.evm.stateGasLeft (sdCreatesS ov bv) := by
    rw [show sR'.evm.gasLeft = _ from congrArg Evm.gasLeft hE]
    exact hGgas
  have hPres : sR'.evm.stateGasLeft
      = sdResOut sRef.evm.stateGasLeft (sdCreatesS ov bv) := by
    rw [show sR'.evm.stateGasLeft = _ from congrArg Evm.stateGasLeft hE]
    exact hGres
  have hPsp : sR'.evm.stateGasSpilled
      = sdSpillOut sRef.evm.stateGasLeft sRef.evm.stateGasSpilled
          (sdCreatesS ov bv) := by
    rw [show sR'.evm.stateGasSpilled = _ from congrArg Evm.stateGasSpilled hE]
    exact hGsp
  have hPaa : sR'.evm.accessedAddresses
      = setAdd sRef.evm.accessedAddresses (to_address_masked x) := by
    rw [show sR'.evm.accessedAddresses = _
      from congrArg Evm.accessedAddresses hE]
    simp only [sdChargedEvm, chargeStateEvm_accessedAddresses,
      chargeEvm_accessedAddresses, sdWarmedEvm_accessedAddresses]
    cases hc : sRef.evm.accessedAddresses.contains (to_address_masked x)
    · rw [if_pos (by simp)]
    · rw [if_neg (by simp), setAdd_eq_of_contains _ _ hc]
  have hPad : sR'.evm.accountsToDelete = sRef.evm.accountsToDelete := by
    rw [show sR'.evm.accountsToDelete = _
      from congrArg Evm.accountsToDelete hE]
    simp only [sdChargedEvm, chargeStateEvm_accountsToDelete,
      chargeEvm_accountsToDelete, sdWarmedEvm_accountsToDelete]
  have hPcre : sR'.txState.createdAccounts = sRef.txState.createdAccounts := by
    rw [hfrc]; rfl
  -- `LifecycleRel` at the post-transfer state, before the mark
  have hlfW : LifecycleRel sRef (sdHostWarm pid (word_to_address x) hs) outer :=
    by refine lifecycleRel_transferFrame ?_ ?_ ?_ hlfrel
       · exact fun _ => rfl
       · rfl
       · rfl
  have hlfT : LifecycleRel sR' hs' outer :=
    lifecycleRel_transferFrame hflag hPad hPcre hlfW
  rw [hax] at hcrT
  refine StepResultRel.success ⟨rfl, ?_, ?_, ?_, hOstatus, ?_, ?_, ?_, ?_⟩
  · -- the live execution gas
    simp only [sdHaltEvm_gasLeft, sdMarkEvm_gasLeft, hPgas, hlive]
  · -- the state-gas reservoir
    rw [hOres]
    simp only [sdHaltEvm_stateGasLeft, sdMarkEvm_stateGasLeft, hPres]
  · -- the recorded spill
    rw [hOsp]
    simp only [sdHaltEvm_stateGasSpilled, sdMarkEvm_stateGasSpilled, hPsp]
  · -- the account overlay, across the EIP-6780 row write
    show AccountRel sR'.txState hsOut
    unfold SdMarkWritten at hmarkW
    cases hc : ovT.curr.created
    · rw [hc, if_neg (by simp)] at hmarkW
      rw [hmarkW]
      exact hpa
    · rw [hc, if_pos rfl] at hmarkW
      exact accountRel_flagWrite hpa msg.address ovT hmarkW hoT
  · -- the log store, across the same write
    simp only [sdHaltEvm_logs, sdMarkEvm_logs]
    unfold SdMarkWritten at hmarkW
    cases hc : ovT.curr.created
    · rw [hc, if_neg (by simp)] at hmarkW
      rw [hmarkW]
      exact hpl
    · rw [hc, if_pos rfl] at hmarkW
      obtain ⟨-, -, -, -, hlogs, hbytes, -⟩ := hostAcctWritten_frame hmarkW
      exact logRel_frame _ base hlogs hbytes hpl
  · -- the access list
    intro aV
    have hOaa : hsOut.warmAddresses = wsAfterMark pid (word_to_address x) hs := by
      unfold SdMarkWritten at hmarkW
      cases hc : ovT.curr.created
      · rw [hc, if_neg (by simp)] at hmarkW
        rw [hmarkW, hhf.1]
        rfl
      · rw [hc, if_pos rfl] at hmarkW
        rw [(hostAcctWritten_frame hmarkW).2.1, hhf.1]
        rfl
    have hOep : hsOut.warmEpoch = hs.warmEpoch := by
      unfold SdMarkWritten at hmarkW
      cases hc : ovT.curr.created
      · rw [hc, if_neg (by simp)] at hmarkW
        rw [hmarkW, hhf.2.1]
        rfl
      · rw [hc, if_pos rfl] at hmarkW
        rw [(hostAcctWritten_frame hmarkW).2.2.1, hhf.2.1]
        rfl
    simp only [sdHaltEvm_accessedAddresses, sdMarkEvm_accessedAddresses, hPaa,
      hOaa, hOep]
    by_cases hp : (pid (word_to_address x) != PrecompileId.NotPrecompile) = true
    · rw [show wsAfterMark pid (word_to_address x) hs = hs.warmAddresses
        from by unfold wsAfterMark; rw [if_pos hp]]
      rw [show setAdd sRef.evm.accessedAddresses (to_address_masked x)
          = sRef.evm.accessedAddresses from by
        refine setAdd_eq_of_contains _ _ ?_
        rw [← word_to_address_toList]
        exact (hwrel (word_to_address x)).mpr (Or.inl (by simpa using hp))]
      exact hwrel aV
    · rw [show wsAfterMark pid (word_to_address x) hs
          = assocPut hs.warmAddresses (word_to_address x) hs.warmEpoch
        from by unfold wsAfterMark; rw [if_neg hp]]
      have hmark := warmaddr_after_mark pid sRef.evm.accessedAddresses
        hs.warmAddresses hs.warmEpoch (word_to_address x) hwrel aV
      rw [word_to_address_toList] at hmark
      exact hmark
  · -- the EIP-6780 lifecycle flags
    unfold SdMarkWritten at hmarkW
    cases hc : ovT.curr.created
    · rw [hc, if_neg (by simp)] at hmarkW
      rw [hmarkW]
      have hdel : (sdHaltEvm (sdMarkEvm sR'.evm
            (sR'.txState.createdAccounts.contains
              sRef.evm.message.currentTarget)
            sRef.evm.message.currentTarget)).accountsToDelete
          = sR'.evm.accountsToDelete := by
        simp only [sdHaltEvm_accountsToDelete, sdMarkEvm_accountsToDelete]
        rw [if_neg (by rw [← hcrT, hc]; simp)]
      refine lifecycleRel_transferFrame ?_ hdel ?_ hlfT
      · exact fun _ => rfl
      · rfl
    · rw [hc, if_pos rfl] at hmarkW
      have hmk := lifecycleRel_mark hlfT msg.address ovT hoT hmarkW
      rw [hax] at hmk
      have hdel : (sdHaltEvm (sdMarkEvm sR'.evm
            (sR'.txState.createdAccounts.contains
              sRef.evm.message.currentTarget)
            sRef.evm.message.currentTarget)).accountsToDelete
          = (specMarkDeleted sR'.evm
              sRef.evm.message.currentTarget).accountsToDelete := by
        simp only [sdHaltEvm_accountsToDelete, sdMarkEvm_accountsToDelete]
        rw [if_pos (by rw [← hcrT, hc])]
        rfl
      refine lifecycleRel_transferFrame ?_ hdel ?_ hmk
      · exact fun _ => rfl
      · rfl

/-! ### The step theorem -/

/-- Everything the step theorem needs at the popped beneficiary beyond
the relations: the two account rows in the transaction-overlay regime,
the EIP-6780 converse the relation cannot supply (MM-20), the transfer in
whichever of its four shapes applies, and the EIP-7825 spill cap — an
extraction-only hard abort with no SpecRef counterpart. -/
def SelfdestructAgree (pid : Evm.Defs.address → PrecompileId) (base : Nat)
    (sRef : Machine) (hs : Evm.HostState) (ss : SeqState) : Prop :=
  ∀ (m : Evm.Defs.Message) (prof : ExecutionProfile) (x : U256)
    (rest : List U256),
    ss.regs.get? Register.message = some m →
    ss.regs.get? Register.k_execution_profile = some prof →
    sRef.evm.stack = x :: rest →
    ∃ ov bv : Evm.Defs.AcctValue,
      hostAcctRow hs m.address = some ov
      ∧ hostAcctRow hs (Evm.Functions.word_to_address x) = some bv
      ∧ CreatedAgree sRef hs m.address
      ∧ SelfdestructTransfer sRef
          (sdHostWarm pid (Evm.Functions.word_to_address x) hs) base prof
          m.address (Evm.Functions.word_to_address x)
          ((hostAcctView ov.curr).getD EMPTY_ACCOUNT).balance
      ∧ (sdCreatesS ov bv = true →
          sRef.evm.stateGasSpilled + (StateGasCosts.NEW_ACCOUNT
            - min StateGasCosts.NEW_ACCOUNT sRef.evm.stateGasLeft) ≤ 2 ^ 24)

open Evm.Functions in
/-- **`SELFDESTRUCT`, all reachable outcomes.** The Amsterdam schedule is
proven outright (`selfdestructCost`, `sdChargedEvm_gas`), the warm/cold
accounting against `WarmAddrRel` (`warm_of_warmAddrRel`), the
`creates_account` predicate against `AccountRel` (`sdCreates_eq`), the
value transfer and its EIP-7708 log by `transfer_equiv` and its three
degenerate siblings, and the EIP-6780 mark by `LifecycleRel`. The reads
and the transfer's case are behind the ledgered `SelfdestructAgree`
hypothesis.

MM-14 is discharged by the underflow outcome, which pairs SpecRef's
`.writeInStaticContext` with the extraction's `StackUnderflow` through
`haltedStaticFirst` — `execute` hoists `validate_stack` above
`guard_static`, so an empty stack in a static frame reaches different
diagnostics on the two sides. MM-1's halt-kind discipline covers the
other four halts. -/
theorem selfdestruct_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (pid : Evm.Defs.address → PrecompileId) (base : Nat)
    (outer : List Address)
    (hrel : StateRel sRef top g hs ss)
    (hwrel : WarmAddrRel pid sRef hs)
    (harel : AccountRel sRef.txState hs)
    (hlfrel : LifecycleRel sRef hs outer)
    (hpid : ∀ aV, runS (precompile_id_for_address aV) hs ss
      = .ok (pid aV, hs) ss)
    (haddr : ∀ m : Evm.Defs.Message,
      ss.regs.get? Register.message = some m →
      m.address.toList = sRef.evm.message.currentTarget)
    (hstatic : ∀ m : Evm.Defs.Message,
      ss.regs.get? Register.message = some m →
      m.is_static = sRef.evm.message.isStatic)
    (hagree : SelfdestructAgree pid base sRef hs ss) :
    StepResultRel (SelfdestructPost pid base outer) (runR iSelfdestruct sRef)
      (runS (Evm.Functions.execute (.SELFDESTRUCT ()) pc_in top mem g) hs ss)
      := by
  obtain ⟨prof, hprof, hfork⟩ := hrel.profile
  obtain ⟨msg, hmsg⟩ := hrel.message
  match hS : sRef.evm.stack with
  | [] =>
    exact selfdestruct_equiv_underflow sRef top g hs ss mem pc_in pid base
      outer hrel hS
  | x :: rest =>
    by_cases hstat : sRef.evm.message.isStatic = true
    · exact selfdestruct_equiv_static sRef top g hs ss mem pc_in pid base
        outer hrel hstatic hstat (by rw [hS]; simp)
    · have hstat0 : sRef.evm.message.isStatic = false := by simpa using hstat
      obtain ⟨ov, bv, horow, hbrow, hcre, hxf, hroom⟩ :=
        hagree msg prof x rest hmsg hprof hS
      -- the specific facts, in the ∀-over-`message` form the outcome
      -- lemmas take (the register read pins `m`)
      have hpin : ∀ m : Evm.Defs.Message,
          ss.regs.get? Register.message = some m → m = msg :=
        fun m hm => Option.some.inj (hm.symm.trans hmsg)
      have hrows : ∀ m : Evm.Defs.Message,
          ss.regs.get? Register.message = some m →
          hostAcctRow hs m.address = some ov := by
        intro m hm; rw [hpin m hm]; exact horow
      have hcreated : ∀ m : Evm.Defs.Message,
          ss.regs.get? Register.message = some m →
          CreatedAgree sRef hs m.address := by
        intro m hm; rw [hpin m hm]; exact hcre
      have hxfer : ∀ (m : Evm.Defs.Message) (p : ExecutionProfile),
          ss.regs.get? Register.message = some m →
          ss.regs.get? Register.k_execution_profile = some p →
          SelfdestructTransfer sRef (sdHostWarm pid (word_to_address x) hs)
            base p m.address (word_to_address x)
            ((hostAcctView ov.curr).getD EMPTY_ACCOUNT).balance := by
        intro m p hm hp
        rw [hpin m hm, Option.some.inj (hp.symm.trans hprof)]
        exact hxf
      by_cases hsen : sRef.evm.gasLeft < selfdestructAccessCost
          (!sRef.evm.accessedAddresses.contains (to_address_masked x))
      · exact selfdestruct_equiv_sentry_oog sRef top g hs ss mem pc_in pid
          base outer x rest hrel hwrel hpid hstatic hstat0 hS hsen
      · push Not at hsen
        by_cases hchg : sRef.evm.gasLeft < selfdestructCost
            (!sRef.evm.accessedAddresses.contains (to_address_masked x))
            (sdCreatesS ov bv)
        · exact selfdestruct_equiv_charge_oog sRef top g hs ss mem pc_in pid
            base outer x rest ov bv hrel hwrel harel hpid haddr hstatic hrows
            hbrow hstat0 hS hsen hchg
        · push Not at hchg
          by_cases hst : (if sdCreatesS ov bv then StateGasCosts.NEW_ACCOUNT
                else 0)
              ≤ sRef.evm.stateGasLeft
                + (sRef.evm.gasLeft - selfdestructCost
                    (!sRef.evm.accessedAddresses.contains
                      (to_address_masked x)) (sdCreatesS ov bv))
          · exact selfdestruct_equiv_ok sRef top g hs ss mem pc_in pid base
              outer x rest ov bv hrel hwrel harel hlfrel hpid haddr hstatic
              hrows hbrow hcreated hxfer hstat0 hS hsen hchg hst hroom
          · -- the state charge fails, which forces `creates_account`
            have hc : sdCreatesS ov bv = true := by
              cases hcv : sdCreatesS ov bv
              · rw [hcv, if_neg (by simp)] at hst
                exact absurd (Nat.zero_le _) hst
              · rfl
            rw [hc, if_pos rfl] at hst
            push Not at hst
            rw [hc] at hchg
            exact selfdestruct_equiv_state_oog sRef top g hs ss mem pc_in pid
              base outer x rest ov bv hrel hwrel harel hpid haddr hstatic
              hrows hbrow hstat0 hS hsen hc hchg hst

end EvmSpecsVerify
