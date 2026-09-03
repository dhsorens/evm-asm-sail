import EvmSpecsVerify.Relations.Refund
import EvmSpecsVerify.Relations.Storage
import EvmSpecsVerify.Relations.Warm
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# SSTORE

The persistent-storage writer, and the widest single step in the
comparison: EIP-2929 warm/cold accounting, the EIP-2200 three-way
(original / current / new) price, the EIP-3529 refund, Amsterdam's
two-dimensional state gas with a credit leg, and the write itself.

The file is in four layers. First the schedule: the extraction computes
all four prices in one `amsterdam_sstore_costs` record where SpecRef
inlines them, and `sstoreCst_eq` is that correspondence field by field.
Then SpecRef's side, written as a composition of seven single-purpose
stage functions with their guards *outside* the record updates, so the
composition is definitionally what the proof's `runR_bind_ok` chain
produces. Then the extraction's side, where `runS_credit_closed` /
`runS_charge_state_closed` collapse the credit and the state charge to
single `min`-shaped forms and the two `runE` guard lemmas step over the
trailing conditionals — without which the success path is a 36-way branch
product. Finally the step equivalence, whose gas triple is the closed
form `sstoreGasOut`, shared by both sides.

Reachable outcomes: success · the static halt · the EIP-2200 sentry ·
execution-gas OOG · state-gas OOG · stack underflow (MM-14: the
extraction's hoisted `validate_stack` reports the stack fault where
SpecRef's earlier static guard reports write protection).

Two divergences were found here and are ledgered: **MM-16**, the no-op
store's elided row (which is why [`StorageRel`](../Relations/Storage.lean)
is one-directional), and **MM-17**, the extraction's two hard aborts on
bounds SpecRef does not have — threaded as `hroom`/`hhead`.
-/

open private pcAdd isWarmStorageKey warmStorageKey from
  EvmAsm.Stateless.SpecRef.InstructionsCore
open private assocGet assocPut from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## The Amsterdam SSTORE schedule, on both sides (MM-2)

The extraction computes all four quantities in one record
(`amsterdam_sstore_costs`); SpecRef inlines them into `iSstore` as a cost
expression, three conditional refund updates, a state-gas amount and a
state-gas credit. These four lemmas are that correspondence, and they are
where the constants are checked. -/

/-- The extraction's zero word is the numeral (`u256` is the identity and
`word_from_bits` a `toNat`). -/
private theorem word_zero_eq : Evm.Functions.WORD_ZERO = 0 := rfl

/-- EIP-2929's access price, shared by SLOAD and SSTORE. -/
def sstoreAccessCost (cold : Bool) : Nat :=
  if cold then GasCosts.COLD_STORAGE_ACCESS else GasCosts.WARM_ACCESS

theorem amsterdam_access_cost_eq (cold : Bool) :
    Evm.Functions.amsterdam_storage_access_cost cold = sstoreAccessCost cold := by
  cases cold <;> rfl

/-- The sentry SpecRef writes as `max access_cost (CALL_STIPEND + 1)`:
`G_sstore_sentry = 2301 = CALL_STIPEND + 1`. -/
theorem sstore_sentry_cost_eq (cold : Bool) :
    Evm.Functions.sstore_sentry_cost cold =
      max (sstoreAccessCost cold) (GasCosts.CALL_STIPEND + 1) := by
  cases cold <;> rfl

/-- SpecRef's composed refund delta: the sum of its three conditional
`refundCounter` updates, which fire only when the slot's value changes. -/
def specRefundDelta (o c n : U256) : Int :=
  if c != n then
    (if o != 0 && c != 0 && n == 0 then (GasCosts.REFUND_STORAGE_CLEAR : Int)
      else 0)
    + (if o != 0 && c == 0 then -(GasCosts.REFUND_STORAGE_CLEAR : Int) else 0)
    + (if o == n then (GasCosts.STORAGE_WRITE : Int) else 0)
  else 0

theorem sstore_execution_eq (o c n : U256) (cold : Bool) :
    (Evm.Functions.amsterdam_sstore_costs o c n cold).execution =
      sstoreAccessCost cold
        + (if o == c && c != n then GasCosts.STORAGE_WRITE else 0) := by
  simp only [Evm.Functions.amsterdam_sstore_costs, amsterdam_access_cost_eq]
  by_cases h : (o == c) = true ∧ (c != n) = true
  · rw [if_pos (by simp [h.1, h.2]), if_pos (by simp [h.1, h.2])]
    rfl
  · rw [if_neg (by simp only [Bool.and_eq_true]; exact h),
      if_neg (by simp only [Bool.and_eq_true]; exact h)]
    simp

theorem sstore_refund_eq (o c n : U256) (cold : Bool) :
    (Evm.Functions.amsterdam_sstore_costs o c n cold).refund =
      specRefundDelta o c n := by
  have hclear : (Evm.Functions.R_amsterdam_storage_clear : Int)
      = (GasCosts.REFUND_STORAGE_CLEAR : Int) := by
    simp [Evm.Functions.R_amsterdam_storage_clear,
      GasCosts.REFUND_STORAGE_CLEAR, GasCosts.STORAGE_WRITE,
      GasCosts.COLD_STORAGE_ACCESS]
  have hwrite : (Evm.Functions.G_amsterdam_storage_write : Int)
      = (GasCosts.STORAGE_WRITE : Int) := by
    simp [Evm.Functions.G_amsterdam_storage_write, GasCosts.STORAGE_WRITE]
  simp only [Evm.Functions.amsterdam_sstore_costs, specRefundDelta,
    Evm.Functions.word_is_zero, word_zero_eq, hclear]
  by_cases hchg : c = n
  · subst hchg
    simp
  · by_cases ho : o = 0 <;> by_cases hc : c = 0 <;> by_cases hn : n = 0 <;>
      simp_all

theorem sstore_state_charge_eq (o c n : U256) (cold : Bool) :
    (Evm.Functions.amsterdam_sstore_costs o c n cold).state_charge =
      (if o == c && c != n && o == 0 then StateGasCosts.STORAGE_SET
        else 0) := by
  simp only [Evm.Functions.amsterdam_sstore_costs, Evm.Functions.word_is_zero,
    word_zero_eq]
  by_cases h : (o == c) = true ∧ (c != n) = true ∧ (o == 0) = true
  · rw [if_pos (by simp [h.1, h.2.1, h.2.2]), if_pos (by simp [h.1, h.2.1, h.2.2])]
    rfl
  · rw [if_neg (by simp only [Bool.and_eq_true]; tauto),
      if_neg (by simp only [Bool.and_eq_true]; tauto)]
    rfl

theorem sstore_state_credit_eq (o c n : U256) (cold : Bool) :
    (Evm.Functions.amsterdam_sstore_costs o c n cold).state_credit =
      (if c != n && o == n && o == 0 then StateGasCosts.STORAGE_SET
        else 0) := by
  simp only [Evm.Functions.amsterdam_sstore_costs, Evm.Functions.word_is_zero,
    word_zero_eq]
  by_cases h : (c != n) = true ∧ (o == n) = true ∧ (o == 0) = true
  · rw [if_pos (by simp [h.1, h.2.1, h.2.2]), if_pos (by simp [h.1, h.2.1, h.2.2])]
    rfl
  · rw [if_neg (by simp only [Bool.and_eq_true]; tauto),
      if_neg (by simp only [Bool.and_eq_true]; tauto)]

/-! ## The step's effect on SpecRef's frame, as a composition

`iSstore` mutates the frame in seven stages. Each stage is written here as
a function with its **guard on the outside** of the record update, so the
composition is definitionally what the proof's `runR_bind_ok` chain
produces — that is what keeps the success lemma free of case analysis. -/

/-- Whether this store is a state-gas *credit*: an unchanged-original
zero slot being restored to zero. -/
def sstoreCreditCond (o c n : U256) : Bool := c != n && o == n && o == 0

/-- Whether it draws state gas: a clean write into a zero slot. -/
def sstoreStateCharge (o c n : U256) : Nat :=
  if o == c && c != n && o == 0 then StateGasCosts.STORAGE_SET else 0

/-- The execution-gas price: access plus the clean-write surcharge. -/
def sstoreExecCost (o c n : U256) (cold : Bool) : Nat :=
  sstoreAccessCost cold + (if o == c && c != n then GasCosts.STORAGE_WRITE else 0)

/-- EIP-2929's cold-slot marking. -/
def sstoreWarmEvm (e : Evm) (cold : Bool) (key : Address × Bytes32) : Evm :=
  if cold then
    { e with accessedStorageKeys := setAdd e.accessedStorageKeys key }
  else e

/-- The refund updates themselves, under the `changed` guard. -/
def sstoreRefundBody (e : Evm) (o c n : U256) : Evm :=
  let e1 :=
    if (o != 0 && c != 0 && n == 0) = true then
      { e with refundCounter := e.refundCounter + GasCosts.REFUND_STORAGE_CLEAR }
    else e
  let e2 :=
    if (o != 0 && c == 0) = true then
      { e1 with
          refundCounter := e1.refundCounter - GasCosts.REFUND_STORAGE_CLEAR }
    else e1
  if (o == n) = true then
    { e2 with refundCounter := e2.refundCounter + GasCosts.STORAGE_WRITE }
  else e2


/-- The three conditional refund updates, in `iSstore`'s order. They fire
only when the slot's value actually changes. -/
def sstoreRefundEvm (e : Evm) (o c n : U256) : Evm :=
  if (c != n) = true then
    sstoreRefundBody e o c n
  else e

/-- The composed refund updates move the counter by `specRefundDelta` —
which is the extraction's `amsterdam_sstore_costs.refund`
(`sstore_refund_eq`). -/
theorem sstoreRefundEvm_refundCounter (e : Evm) (o c n : U256) :
    (sstoreRefundEvm e o c n).refundCounter
      = e.refundCounter + specRefundDelta o c n := by
  unfold sstoreRefundEvm sstoreRefundBody specRefundDelta
  by_cases hchg : c = n
  · subst hchg
    simp
  · by_cases ho : o = 0 <;> by_cases hc : c = 0 <;> by_cases hn : n = 0 <;>
      by_cases hon : o = n <;> simp_all <;> try omega

/-- `credit_state_gas_refund`, LIFO: execution gas up to the recorded
spill, then the reservoir. -/
def creditEvm (e : Evm) (cond : Bool) (amount : Uint) : Evm :=
  if cond then
    { e with
        gasLeft := e.gasLeft + min amount e.stateGasSpilled
        stateGasSpilled := e.stateGasSpilled - min amount e.stateGasSpilled
        stateGasLeft :=
          e.stateGasLeft + (amount - min amount e.stateGasSpilled) }
  else e

/-- `charge_gas`. -/
def chargeEvm (e : Evm) (amount : Uint) : Evm :=
  { e with
      gasLeft := e.gasLeft - amount
      regularGasUsed := e.regularGasUsed + amount }

/-- `charge_state_gas`: reservoir first, then spill out of execution gas. -/
def chargeStateEvm (e : Evm) (amount : Uint) : Evm :=
  if amount ≤ e.stateGasLeft then
    { e with stateGasLeft := e.stateGasLeft - amount }
  else
    { e with
        stateGasLeft := 0
        gasLeft := e.gasLeft - (amount - e.stateGasLeft)
        stateGasSpilled :=
          e.stateGasSpilled + (amount - e.stateGasLeft) }

/-- `pcAdd 1`. -/
def pcBump (e : Evm) : Evm := { e with pc := e.pc + 1 }

/-- The frame after both pops and the cold-slot marking. -/
def sstoreWarmedEvm (e : Evm) (rest : List U256) (key : Address × Bytes32)
    (cold : Bool) : Evm :=
  sstoreWarmEvm { e with stack := rest } cold key

/-- The frame just before the execution charge: both pops, the cold-slot
marking, the refund updates and the state-gas credit. -/
def sstorePreChargeEvm (e : Evm) (rest : List U256) (key : Address × Bytes32)
    (v o c : U256) (cold : Bool) : Evm :=
  creditEvm (sstoreRefundEvm (sstoreWarmedEvm e rest key cold) o c v)
    (sstoreCreditCond o c v) StateGasCosts.STORAGE_SET

/-- With the value changed, the refund block runs. -/
theorem sstorePreChargeEvm_changed (e : Evm) (rest : List U256)
    (key : Address × Bytes32) (v o c : U256) (cold : Bool)
    (h : (c != v) = true) :
    creditEvm (sstoreRefundBody (sstoreWarmedEvm e rest key cold) o c v)
        (sstoreCreditCond o c v) StateGasCosts.STORAGE_SET
      = sstorePreChargeEvm e rest key v o c cold := by
  rw [sstorePreChargeEvm, sstoreRefundEvm, if_pos h]

/-- With the value unchanged, it does not. -/
theorem sstorePreChargeEvm_unchanged (e : Evm) (rest : List U256)
    (key : Address × Bytes32) (v o c : U256) (cold : Bool)
    (h : ¬(c != v) = true) :
    creditEvm (sstoreWarmedEvm e rest key cold) (sstoreCreditCond o c v)
        StateGasCosts.STORAGE_SET
      = sstorePreChargeEvm e rest key v o c cold := by
  rw [sstorePreChargeEvm, sstoreRefundEvm, if_neg h]

/-- SpecRef's frame after a successful `SSTORE`. -/
def sstorePostEvm (e : Evm) (rest : List U256) (key : Address × Bytes32)
    (v o c : U256) (cold : Bool) : Evm :=
  pcBump
    (chargeStateEvm
      (chargeEvm (sstorePreChargeEvm e rest key v o c cold)
        (sstoreExecCost o c v cold))
      (sstoreStateCharge o c v))

/-- Execution gas after the credit leg. -/
def sstoreLiveCredited (e : Evm) (o c n : U256) : Nat :=
  e.gasLeft
    + (if sstoreCreditCond o c n then
        min StateGasCosts.STORAGE_SET e.stateGasSpilled else 0)

/-- The state-gas reservoir after the credit leg. -/
def sstoreResCredited (e : Evm) (o c n : U256) : Nat :=
  e.stateGasLeft
    + (if sstoreCreditCond o c n then
        StateGasCosts.STORAGE_SET
          - min StateGasCosts.STORAGE_SET e.stateGasSpilled
      else 0)

/-- The recorded spill after the credit leg. -/
def sstoreSpillCredited (e : Evm) (o c n : U256) : Nat :=
  e.stateGasSpilled
    - (if sstoreCreditCond o c n then
        min StateGasCosts.STORAGE_SET e.stateGasSpilled else 0)

/-! ### Projections of the composition

The refund and warm-mark stages leave gas alone and the credit leg leaves
everything but gas alone, so each quantity has a closed form. -/

private theorem warm_refund_gas (e : Evm) (rest : List U256)
    (key : Address × Bytes32) (v o c : U256) (cold : Bool) :
    ((sstoreRefundEvm (sstoreWarmedEvm e rest key cold) o c v).gasLeft
        = e.gasLeft
      ∧ (sstoreRefundEvm (sstoreWarmedEvm e rest key cold) o c v).stateGasLeft
        = e.stateGasLeft)
      ∧ (sstoreRefundEvm (sstoreWarmedEvm e rest key cold) o c v).stateGasSpilled
        = e.stateGasSpilled := by
  unfold sstoreRefundEvm sstoreRefundBody sstoreWarmedEvm sstoreWarmEvm
  repeat' split
  all_goals exact ⟨⟨rfl, rfl⟩, rfl⟩

theorem sstorePreChargeEvm_gasLeft (e : Evm) (rest : List U256)
    (key : Address × Bytes32) (v o c : U256) (cold : Bool) :
    (sstorePreChargeEvm e rest key v o c cold).gasLeft
      = sstoreLiveCredited e o c v := by
  obtain ⟨⟨hg, _⟩, hsp⟩ := warm_refund_gas e rest key v o c cold
  unfold sstorePreChargeEvm sstoreLiveCredited creditEvm
  by_cases hcond : sstoreCreditCond o c v = true
  · rw [if_pos hcond, if_pos hcond]
    simp only [hg, hsp]
  · rw [if_neg hcond, if_neg hcond]
    simp only [hg, Nat.add_zero]

theorem sstorePreChargeEvm_stateGasLeft (e : Evm) (rest : List U256)
    (key : Address × Bytes32) (v o c : U256) (cold : Bool) :
    (sstorePreChargeEvm e rest key v o c cold).stateGasLeft
      = sstoreResCredited e o c v := by
  obtain ⟨⟨_, hr⟩, hsp⟩ := warm_refund_gas e rest key v o c cold
  unfold sstorePreChargeEvm sstoreResCredited creditEvm
  by_cases hcond : sstoreCreditCond o c v = true
  · rw [if_pos hcond, if_pos hcond]
    simp only [hr, hsp]
  · rw [if_neg hcond, if_neg hcond]
    simp only [hr, Nat.add_zero]

theorem sstorePreChargeEvm_stateGasSpilled (e : Evm) (rest : List U256)
    (key : Address × Bytes32) (v o c : U256) (cold : Bool) :
    (sstorePreChargeEvm e rest key v o c cold).stateGasSpilled
      = sstoreSpillCredited e o c v := by
  obtain ⟨⟨_, _⟩, hsp⟩ := warm_refund_gas e rest key v o c cold
  unfold sstorePreChargeEvm sstoreSpillCredited creditEvm
  by_cases hcond : sstoreCreditCond o c v = true
  · rw [if_pos hcond, if_pos hcond]
    simp only [hsp]
  · rw [if_neg hcond, if_neg hcond]
    simp only [hsp, Nat.sub_zero]

/-! ## Conditional single-field updates

`iSstore`'s guarded statements all have the do-elaborator's
`if c then act >>= k else pure () >>= k` shape. These three lemmas step
over one such guard without splitting the proof. -/

theorem runR_cond_warm {α : Type} (cold : Bool) (key : Address × Bytes32)
    (k : PUnit → EvmM α) (s : Machine)
    {r : Except SpecError (Except EvmError α × Machine)}
    (h : runR (k PUnit.unit) { s with evm := sstoreWarmEvm s.evm cold key }
      = r) :
    runR
        (if cold = true then
          EvmM.modifyEvm
              (fun e =>
                { e with accessedStorageKeys := setAdd e.accessedStorageKeys key })
            >>= k
         else pure PUnit.unit >>= k) s = r := by
  cases cold
  · rw [if_neg (by simp)]
    exact runR_bind_ok (runR_pure _ _) h
  · rw [if_pos rfl]
    exact runR_bind_ok (runR_modifyEvm _ _) h

theorem runR_cond_refund {α : Type} (cond : Bool) (f : Int → Int)
    (k : PUnit → EvmM α) (s : Machine)
    {r : Except SpecError (Except EvmError α × Machine)}
    (h : runR (k PUnit.unit)
        { s with evm :=
            if cond = true then
              { s.evm with refundCounter := f s.evm.refundCounter }
            else s.evm } = r) :
    runR
        (if cond = true then
          EvmM.modifyEvm (fun e => { e with refundCounter := f e.refundCounter })
            >>= k
         else pure PUnit.unit >>= k) s = r := by
  cases cond
  · rw [if_neg (by simp)]
    exact runR_bind_ok (runR_pure _ _) (by simpa using h)
  · rw [if_pos rfl]
    exact runR_bind_ok (runR_modifyEvm _ _) (by simpa using h)

theorem runR_cond_credit {α : Type} (cond : Bool) (amount : Uint)
    (k : PUnit → EvmM α) (s : Machine)
    {r : Except SpecError (Except EvmError α × Machine)}
    (h : runR (k PUnit.unit)
        { s with evm := creditEvm s.evm cond amount } = r) :
    runR
        (if cond = true then credit_state_gas_refund amount >>= k
         else pure PUnit.unit >>= k) s = r := by
  cases cond
  · rw [if_neg (by simp)]
    exact runR_bind_ok (runR_pure _ _) (by simpa [creditEvm] using h)
  · rw [if_pos rfl]
    exact runR_bind_ok (runR_credit_state_gas_refund _ _)
      (by simpa [creditEvm] using h)

/-! ## SpecRef run shapes -/

/-- The tail of `iSstore` after the refund block: the two charges, the
write and the pc bump. Named because the success proof reaches it from
both refund branches. -/
def sstoreTail (target : Address) (key : Bytes32) (v : U256)
    (cost amount : Uint) : EvmM Unit := do
  charge_gas cost
  charge_state_gas amount
  EvmM.liftTx (setStorage target key v)
  pcAdd 1

/-- The state-gas credit guard together with that tail: everything
`iSstore` does after the refund block. -/
def sstoreCreditTail (target : Address) (key : Bytes32) (v o c : U256)
    (cost : Uint) : EvmM Unit :=
  if sstoreCreditCond o c v = true then
    credit_state_gas_refund StateGasCosts.STORAGE_SET
      >>= fun _ => sstoreTail target key v cost (sstoreStateCharge o c v)
  else
    pure PUnit.unit
      >>= fun _ => sstoreTail target key v cost (sstoreStateCharge o c v)

/-- The state-gas credit guard plus that tail: everything from the credit
to the pc bump, with no case analysis left for the caller. -/
theorem runR_sstore_tail (m : Machine) (target : Address) (key : Bytes32)
    (v o c : U256) (cost : Uint) (ts₄ : TransactionState)
    (hexec : cost ≤ (creditEvm m.evm (sstoreCreditCond o c v)
      StateGasCosts.STORAGE_SET).gasLeft)
    (hstate : sstoreStateCharge o c v
      ≤ (chargeEvm (creditEvm m.evm (sstoreCreditCond o c v)
            StateGasCosts.STORAGE_SET) cost).stateGasLeft
        + (chargeEvm (creditEvm m.evm (sstoreCreditCond o c v)
            StateGasCosts.STORAGE_SET) cost).gasLeft)
    (hset : (setStorage target key v).run m.txState = .ok ((), ts₄)) :
    runR (sstoreCreditTail target key v o c cost) m
      = .ok (.ok (),
          { m with
              txState := ts₄
              evm :=
                pcBump
                  (chargeStateEvm
                    (chargeEvm (creditEvm m.evm (sstoreCreditCond o c v)
                      StateGasCosts.STORAGE_SET) cost)
                    (sstoreStateCharge o c v)) }) := by
  rw [sstoreCreditTail]
  refine runR_cond_credit _ _ _ _ ?_
  simp only [sstoreTail, pcAdd, pcBump]
  refine runR_bind_ok (runR_charge_gas _ _ hexec) ?_
  unfold chargeStateEvm
  by_cases hres : sstoreStateCharge o c v
      ≤ (chargeEvm (creditEvm m.evm (sstoreCreditCond o c v)
          StateGasCosts.STORAGE_SET) cost).stateGasLeft
  · rw [if_pos hres]
    refine runR_bind_ok (runR_charge_state_gas_reservoir _ _ hres) ?_
    refine runR_bind_ok (runR_liftTx_ok _ _ () ts₄ hset) ?_
    exact runR_modifyEvm _ _
  · rw [if_neg hres]
    refine runR_bind_ok
      (runR_charge_state_gas_spill _ _ (Nat.lt_of_not_le hres) hstate) ?_
    refine runR_bind_ok (runR_liftTx_ok _ _ () ts₄ hset) ?_
    exact runR_modifyEvm _ _

/-- The execution charge fails. -/
theorem runR_sstore_tail_exec_oog (m : Machine) (target : Address)
    (key : Bytes32) (v o c : U256) (cost : Uint)
    (hexec : ¬cost ≤ (creditEvm m.evm (sstoreCreditCond o c v)
      StateGasCosts.STORAGE_SET).gasLeft) :
    ∃ m', runR (sstoreCreditTail target key v o c cost) m
      = .ok (.error .outOfGas, m') := by
  exact ⟨_, by
    rw [sstoreCreditTail]
    refine runR_cond_credit _ _ _ _ ?_
    simp only [sstoreTail]
    exact runR_bind_err (runR_charge_gas_oog _ _ (Nat.lt_of_not_le hexec))⟩

/-- The state-gas charge fails. -/
theorem runR_sstore_tail_state_oog (m : Machine) (target : Address)
    (key : Bytes32) (v o c : U256) (cost : Uint)
    (hexec : cost ≤ (creditEvm m.evm (sstoreCreditCond o c v)
      StateGasCosts.STORAGE_SET).gasLeft)
    (hstate : ¬sstoreStateCharge o c v
      ≤ (chargeEvm (creditEvm m.evm (sstoreCreditCond o c v)
            StateGasCosts.STORAGE_SET) cost).stateGasLeft
        + (chargeEvm (creditEvm m.evm (sstoreCreditCond o c v)
            StateGasCosts.STORAGE_SET) cost).gasLeft) :
    ∃ m', runR (sstoreCreditTail target key v o c cost) m
      = .ok (.error .outOfGas, m') := by
  exact ⟨_, by
    rw [sstoreCreditTail]
    refine runR_cond_credit _ _ _ _ ?_
    simp only [sstoreTail]
    refine runR_bind_ok (runR_charge_gas _ _ hexec) ?_
    exact runR_bind_err
      (runR_charge_state_gas_oog _ _ (Nat.lt_of_not_le hstate))⟩

/-! ### The failure outcomes -/

/-- MM-14: the static throw fires before either pop. -/
theorem runR_iSstore_static (s : Machine)
    (hstatic : s.evm.message.isStatic = true) :
    runR iSstore s = .ok (.error .writeInStaticContext, s) := by
  simp only [iSstore]
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_pos (by simpa using hstatic)]
  exact runR_bind_err (runR_throw _ _)

theorem runR_iSstore_underflow (s : Machine)
    (hstatic : s.evm.message.isStatic = false)
    (hlen : s.evm.stack.length < 2) :
    ∃ s', runR iSstore s = .ok (.error .stackUnderflow, s') := by
  simp only [iSstore]
  match hS : s.evm.stack with
  | [] =>
    refine ⟨s, ?_⟩
    refine runR_bind_ok (runR_getEvm _) ?_
    rw [if_neg (by simpa using hstatic)]
    refine runR_bind_ok (runR_pure _ _) ?_
    exact runR_bind_err (runR_stackPop_nil s hS)
  | [y] =>
    refine ⟨{ s with evm := { s.evm with stack := [] } }, ?_⟩
    refine runR_bind_ok (runR_getEvm _) ?_
    rw [if_neg (by simpa using hstatic)]
    refine runR_bind_ok (runR_pure _ _) ?_
    refine runR_bind_ok (runR_stackPop_cons s y [] hS) ?_
    exact runR_bind_err (runR_stackPop_nil _ rfl)
  | y :: z :: rest =>
    rw [hS] at hlen
    simp only [List.length_cons] at hlen
    omega

/-- The EIP-2200 sentry: the frame must be able to afford the greater of
the access cost and the call stipend before any state is read. -/
theorem runR_iSstore_sentry_oog (s : Machine) (x v : U256) (rest : List U256)
    (cold : Bool)
    (hstack : s.evm.stack = x :: v :: rest)
    (hstatic : s.evm.message.isStatic = false)
    (hcold : cold = !s.evm.accessedStorageKeys.contains
      (s.evm.message.currentTarget, toBeBytes32 x))
    (hsentry : s.evm.gasLeft
      < max (sstoreAccessCost cold) (GasCosts.CALL_STIPEND + 1)) :
    ∃ s', runR iSstore s = .ok (.error .outOfGas, s') := by
  refine ⟨{ s with evm := { s.evm with stack := rest } }, ?_⟩
  simp only [iSstore]
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_neg (by simpa using hstatic)]
  refine runR_bind_ok (runR_pure _ _) ?_
  refine runR_bind_ok (runR_stackPop_cons s x (v :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ v rest rfl) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_isWarmStorageKey _ _) ?_
  rw [← hcold]
  exact runR_bind_err (runR_check_gas_oog _ _ hsentry)

/-- **The shared prefix.** From `iSstore` to the credit guard: the static
test, both pops, the warm test, the EIP-2200 sentry, the cold-slot
marking, the two state-tracker reads and the refund block. Every
non-static, non-underflowing outcome goes through it, so it is proven
once and the outcomes differ only in how the tail ends. -/
theorem runR_iSstore_prefix (s : Machine) (x v o c : U256)
    (rest : List U256) (ts₂ ts₃ : TransactionState) (cold : Bool)
    {r : Except SpecError (Except EvmError Unit × Machine)}
    (hstack : s.evm.stack = x :: v :: rest)
    (hstatic : s.evm.message.isStatic = false)
    (hcold : cold = !s.evm.accessedStorageKeys.contains
      (s.evm.message.currentTarget, toBeBytes32 x))
    (hsentry : max (sstoreAccessCost cold) (GasCosts.CALL_STIPEND + 1)
      ≤ s.evm.gasLeft)
    (horig : (getStorageOriginal s.evm.message.currentTarget
      (toBeBytes32 x)).run s.txState = .ok (o, ts₂))
    (hcurr : (getStorage s.evm.message.currentTarget (toBeBytes32 x)).run ts₂
      = .ok (c, ts₃))
    (h : runR
        (sstoreCreditTail s.evm.message.currentTarget (toBeBytes32 x) v o c
          (sstoreExecCost o c v cold))
        { s with
            txState := ts₃
            evm := sstoreRefundEvm (sstoreWarmedEvm s.evm rest
              (s.evm.message.currentTarget, toBeBytes32 x) cold) o c v }
      = r) :
    runR iSstore s = r := by
  simp only [iSstore, pcAdd, warmStorageKey]
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_neg (by simpa using hstatic)]
  refine runR_bind_ok (runR_pure _ _) ?_
  refine runR_bind_ok (runR_stackPop_cons s x (v :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ v rest rfl) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_isWarmStorageKey _ _) ?_
  rw [← hcold]
  refine runR_bind_ok (runR_check_gas _ _ hsentry) ?_
  refine runR_cond_warm _ _ _ _ ?_
  refine runR_bind_ok (runR_liftTx_ok _ _ o ts₂ horig) ?_
  refine runR_bind_ok (runR_liftTx_ok _ _ c ts₃ hcurr) ?_
  by_cases hchg : (c != v) = true
  · rw [if_pos hchg]
    refine runR_cond_refund _
      (fun r => r + (GasCosts.REFUND_STORAGE_CLEAR : Int)) _ _ ?_
    refine runR_cond_refund _
      (fun r => r - (GasCosts.REFUND_STORAGE_CLEAR : Int)) _ _ ?_
    refine runR_cond_refund _
      (fun r => r + (GasCosts.STORAGE_WRITE : Int)) _ _ ?_
    rw [sstoreRefundEvm, if_pos hchg] at h
    exact h
  · rw [if_neg hchg]
    refine runR_bind_ok (runR_pure _ _) ?_
    rw [sstoreRefundEvm, if_neg hchg] at h
    exact h

/-! ### The outcomes

The prefix's machine is `sstorePreChargeEvm`'s argument, so each
affordability test converts to its closed form by
`sstorePreChargeEvm_gasLeft` / `_stateGasLeft` with no case analysis. -/

/-- **The success path.** The reads are supplied as run equations
(`horig`/`hcurr`/`hset`): SpecRef resolves them through the state
tracker, which is what the storage relation and the ledgered
`SstoreAgree` are about. -/
theorem runR_iSstore_success (s : Machine) (x v o c : U256)
    (rest : List U256) (ts₂ ts₃ ts₄ : TransactionState) (cold : Bool)
    (hstack : s.evm.stack = x :: v :: rest)
    (hstatic : s.evm.message.isStatic = false)
    (hcold : cold = !s.evm.accessedStorageKeys.contains
      (s.evm.message.currentTarget, toBeBytes32 x))
    (hsentry : max (sstoreAccessCost cold) (GasCosts.CALL_STIPEND + 1)
      ≤ s.evm.gasLeft)
    (horig : (getStorageOriginal s.evm.message.currentTarget
      (toBeBytes32 x)).run s.txState = .ok (o, ts₂))
    (hcurr : (getStorage s.evm.message.currentTarget (toBeBytes32 x)).run ts₂
      = .ok (c, ts₃))
    (hexec : sstoreExecCost o c v cold ≤ sstoreLiveCredited s.evm o c v)
    (hstate : sstoreStateCharge o c v
      ≤ sstoreResCredited s.evm o c v
        + (sstoreLiveCredited s.evm o c v - sstoreExecCost o c v cold))
    (hset : (setStorage s.evm.message.currentTarget (toBeBytes32 x) v).run ts₃
      = .ok ((), ts₄)) :
    runR iSstore s =
      .ok (.ok (),
        { s with
            txState := ts₄
            evm := sstorePostEvm s.evm rest
              (s.evm.message.currentTarget, toBeBytes32 x) v o c cold }) := by
  refine runR_iSstore_prefix s x v o c rest ts₂ ts₃ cold hstack hstatic hcold
    hsentry horig hcurr ?_
  rw [sstorePostEvm]
  refine runR_sstore_tail _ _ _ _ _ _ _ _ ?_ ?_ hset
  · rw [show creditEvm
        (sstoreRefundEvm (sstoreWarmedEvm s.evm rest
          (s.evm.message.currentTarget, toBeBytes32 x) cold) o c v)
        (sstoreCreditCond o c v) StateGasCosts.STORAGE_SET
      = sstorePreChargeEvm s.evm rest
        (s.evm.message.currentTarget, toBeBytes32 x) v o c cold from rfl,
      sstorePreChargeEvm_gasLeft]
    exact hexec
  · rw [show creditEvm
        (sstoreRefundEvm (sstoreWarmedEvm s.evm rest
          (s.evm.message.currentTarget, toBeBytes32 x) cold) o c v)
        (sstoreCreditCond o c v) StateGasCosts.STORAGE_SET
      = sstorePreChargeEvm s.evm rest
        (s.evm.message.currentTarget, toBeBytes32 x) v o c cold from rfl]
    show sstoreStateCharge o c v
      ≤ (sstorePreChargeEvm s.evm rest _ v o c cold).stateGasLeft
        + ((sstorePreChargeEvm s.evm rest _ v o c cold).gasLeft
          - sstoreExecCost o c v cold)
    rw [sstorePreChargeEvm_gasLeft, sstorePreChargeEvm_stateGasLeft]
    exact hstate

/-- The execution charge cannot be met. -/
theorem runR_iSstore_exec_oog (s : Machine) (x v o c : U256)
    (rest : List U256) (ts₂ ts₃ : TransactionState) (cold : Bool)
    (hstack : s.evm.stack = x :: v :: rest)
    (hstatic : s.evm.message.isStatic = false)
    (hcold : cold = !s.evm.accessedStorageKeys.contains
      (s.evm.message.currentTarget, toBeBytes32 x))
    (hsentry : max (sstoreAccessCost cold) (GasCosts.CALL_STIPEND + 1)
      ≤ s.evm.gasLeft)
    (horig : (getStorageOriginal s.evm.message.currentTarget
      (toBeBytes32 x)).run s.txState = .ok (o, ts₂))
    (hcurr : (getStorage s.evm.message.currentTarget (toBeBytes32 x)).run ts₂
      = .ok (c, ts₃))
    (hexec : ¬sstoreExecCost o c v cold ≤ sstoreLiveCredited s.evm o c v) :
    ∃ s', runR iSstore s = .ok (.error .outOfGas, s') := by
  obtain ⟨m', hm'⟩ := runR_sstore_tail_exec_oog
    { s with
        txState := ts₃
        evm := sstoreRefundEvm (sstoreWarmedEvm s.evm rest
          (s.evm.message.currentTarget, toBeBytes32 x) cold) o c v }
    s.evm.message.currentTarget (toBeBytes32 x) v o c
    (sstoreExecCost o c v cold)
    (by rw [show creditEvm
            (sstoreRefundEvm (sstoreWarmedEvm s.evm rest
              (s.evm.message.currentTarget, toBeBytes32 x) cold) o c v)
            (sstoreCreditCond o c v) StateGasCosts.STORAGE_SET
          = sstorePreChargeEvm s.evm rest
            (s.evm.message.currentTarget, toBeBytes32 x) v o c cold from rfl,
          sstorePreChargeEvm_gasLeft]
        exact hexec)
  exact ⟨m', runR_iSstore_prefix s x v o c rest ts₂ ts₃ cold hstack hstatic
    hcold hsentry horig hcurr hm'⟩

/-- The state-gas charge cannot be met, reservoir plus execution gas. -/
theorem runR_iSstore_state_oog (s : Machine) (x v o c : U256)
    (rest : List U256) (ts₂ ts₃ : TransactionState) (cold : Bool)
    (hstack : s.evm.stack = x :: v :: rest)
    (hstatic : s.evm.message.isStatic = false)
    (hcold : cold = !s.evm.accessedStorageKeys.contains
      (s.evm.message.currentTarget, toBeBytes32 x))
    (hsentry : max (sstoreAccessCost cold) (GasCosts.CALL_STIPEND + 1)
      ≤ s.evm.gasLeft)
    (horig : (getStorageOriginal s.evm.message.currentTarget
      (toBeBytes32 x)).run s.txState = .ok (o, ts₂))
    (hcurr : (getStorage s.evm.message.currentTarget (toBeBytes32 x)).run ts₂
      = .ok (c, ts₃))
    (hexec : sstoreExecCost o c v cold ≤ sstoreLiveCredited s.evm o c v)
    (hstate : ¬sstoreStateCharge o c v
      ≤ sstoreResCredited s.evm o c v
        + (sstoreLiveCredited s.evm o c v - sstoreExecCost o c v cold)) :
    ∃ s', runR iSstore s = .ok (.error .outOfGas, s') := by
  have hpre : creditEvm
      (sstoreRefundEvm (sstoreWarmedEvm s.evm rest
        (s.evm.message.currentTarget, toBeBytes32 x) cold) o c v)
      (sstoreCreditCond o c v) StateGasCosts.STORAGE_SET
    = sstorePreChargeEvm s.evm rest
      (s.evm.message.currentTarget, toBeBytes32 x) v o c cold := rfl
  obtain ⟨m', hm'⟩ := runR_sstore_tail_state_oog
    { s with
        txState := ts₃
        evm := sstoreRefundEvm (sstoreWarmedEvm s.evm rest
          (s.evm.message.currentTarget, toBeBytes32 x) cold) o c v }
    s.evm.message.currentTarget (toBeBytes32 x) v o c
    (sstoreExecCost o c v cold)
    (by rw [hpre, sstorePreChargeEvm_gasLeft]; exact hexec)
    (by
      rw [hpre]
      show ¬sstoreStateCharge o c v
        ≤ (sstorePreChargeEvm s.evm rest _ v o c cold).stateGasLeft
          + ((sstorePreChargeEvm s.evm rest _ v o c cold).gasLeft
            - sstoreExecCost o c v cold)
      rw [sstorePreChargeEvm_gasLeft, sstorePreChargeEvm_stateGasLeft]
      exact hstate)
  exact ⟨m', runR_iSstore_prefix s x v o c rest ts₂ ts₃ cold hstack hstatic
    hcold hsentry horig hcurr hm'⟩

/-- The extraction's cost record for this step. -/
def sstoreCst (entry : Evm.Defs.StorageValue) (v : Nat) (cold : Bool) :
    Evm.Defs.SstoreCosts :=
  Evm.Functions.amsterdam_sstore_costs entry.orig entry.curr v cold

/-- The frame's three gas quantities after the credit leg and the two
charges. -/
def sstoreGasOut (g res sp : Nat) (cst : Evm.Defs.SstoreCosts) :
    Nat × Nat × Nat :=
  let back := min cst.state_credit sp
  let res1 := res + (cst.state_credit - back)
  let g2 := g + back - cst.execution
  let draw := cst.state_charge - min cst.state_charge res1
  (g2 - draw, res1 - min cst.state_charge res1, sp - back + draw)

/-! ## The two sides' cost records meet

`sstoreCst_eq` is where the schedule lemmas above are cashed in: the
extraction's record equals the record of SpecRef's four inlined
quantities, field by field. Everything downstream can then be stated
once. -/

/-- SpecRef's four quantities, as the extraction's record. -/
def sstoreCstRef (o c v : U256) (cold : Bool) : Evm.Defs.SstoreCosts :=
  { execution := sstoreExecCost o c v cold
    refund := specRefundDelta o c v
    state_charge := sstoreStateCharge o c v
    state_credit :=
      if sstoreCreditCond o c v then StateGasCosts.STORAGE_SET else 0 }

theorem sstoreCst_eq (entry : Evm.Defs.StorageValue) (v : Nat) (cold : Bool) :
    sstoreCst entry v cold = sstoreCstRef entry.orig entry.curr v cold := by
  have h1 := sstore_execution_eq entry.orig entry.curr v cold
  have h2 := sstore_refund_eq entry.orig entry.curr v cold
  have h3 := sstore_state_charge_eq entry.orig entry.curr v cold
  have h4 := sstore_state_credit_eq entry.orig entry.curr v cold
  unfold sstoreCst sstoreCstRef
  cases hh : Evm.Functions.amsterdam_sstore_costs entry.orig entry.curr v cold
    with
  | mk ex rf sc scr =>
    rw [hh] at h1 h2 h3 h4
    simp only at h1 h2 h3 h4
    rw [h1, h2, h3, h4]
    rfl

/-! ### Projections of SpecRef's post-frame

Each stage of `sstorePostEvm` touches a known set of fields, so every
quantity the post-relations read has a closed form. The gas triple is
`sstoreGasOut`, shared with the extraction's side. -/

private theorem creditEvm_proj (e : Evm) (cond : Bool) (amount : Uint) :
    ((creditEvm e cond amount).gasLeft
        = e.gasLeft + (if cond then min amount e.stateGasSpilled else 0)
      ∧ (creditEvm e cond amount).stateGasLeft
        = e.stateGasLeft
          + (if cond then amount - min amount e.stateGasSpilled else 0))
      ∧ (creditEvm e cond amount).stateGasSpilled
        = e.stateGasSpilled
          - (if cond then min amount e.stateGasSpilled else 0) := by
  unfold creditEvm
  split
  · exact ⟨⟨rfl, rfl⟩, rfl⟩
  · exact ⟨⟨by simp, by simp⟩, by simp⟩

private theorem chargeStateEvm_proj (e : Evm) (amount : Uint) :
    ((chargeStateEvm e amount).gasLeft
        = e.gasLeft - (amount - min amount e.stateGasLeft)
      ∧ (chargeStateEvm e amount).stateGasLeft
        = e.stateGasLeft - min amount e.stateGasLeft)
      ∧ (chargeStateEvm e amount).stateGasSpilled
        = e.stateGasSpilled + (amount - min amount e.stateGasLeft) := by
  unfold chargeStateEvm
  split
  · rename_i h
    rw [Nat.min_eq_left h]
    exact ⟨⟨by simp, rfl⟩, by simp⟩
  · rename_i h
    rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le h))]
    exact ⟨⟨rfl, by simp⟩, rfl⟩

/-- The gas triple SpecRef's frame ends up with. -/
theorem sstorePostEvm_gas (e : Evm) (rest : List U256)
    (key : Address × Bytes32) (v o c : U256) (cold : Bool) :
    (((sstorePostEvm e rest key v o c cold).gasLeft
          = (sstoreGasOut e.gasLeft e.stateGasLeft e.stateGasSpilled
              (sstoreCstRef o c v cold)).1
        ∧ (sstorePostEvm e rest key v o c cold).stateGasLeft
          = (sstoreGasOut e.gasLeft e.stateGasLeft e.stateGasSpilled
              (sstoreCstRef o c v cold)).2.1)
      ∧ (sstorePostEvm e rest key v o c cold).stateGasSpilled
          = (sstoreGasOut e.gasLeft e.stateGasLeft e.stateGasSpilled
              (sstoreCstRef o c v cold)).2.2) := by
  have hpre := warm_refund_gas e rest key v o c cold
  obtain ⟨⟨hg, hr⟩, hsp⟩ := hpre
  obtain ⟨⟨hcg, hcr⟩, hcsp⟩ := creditEvm_proj
    (sstoreRefundEvm (sstoreWarmedEvm e rest key cold) o c v)
    (sstoreCreditCond o c v) StateGasCosts.STORAGE_SET
  obtain ⟨⟨hsg, hsr⟩, hssp⟩ := chargeStateEvm_proj
    (chargeEvm (sstorePreChargeEvm e rest key v o c cold)
      (sstoreExecCost o c v cold))
    (sstoreStateCharge o c v)
  have hcredit : min (if sstoreCreditCond o c v then
        StateGasCosts.STORAGE_SET else 0) e.stateGasSpilled
      = (if sstoreCreditCond o c v then
          min StateGasCosts.STORAGE_SET e.stateGasSpilled else 0) := by
    split <;> simp
  have hsub : (if sstoreCreditCond o c v then StateGasCosts.STORAGE_SET
        else 0)
      - (if sstoreCreditCond o c v then
          min StateGasCosts.STORAGE_SET e.stateGasSpilled else 0)
      = (if sstoreCreditCond o c v then
          StateGasCosts.STORAGE_SET
            - min StateGasCosts.STORAGE_SET e.stateGasSpilled
        else 0) := by
    split <;> simp
  unfold sstorePostEvm pcBump sstoreGasOut
  simp only [sstoreCstRef, hcredit, hsub]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show (chargeStateEvm _ _).gasLeft = _
    rw [hsg]
    show (chargeEvm (sstorePreChargeEvm e rest key v o c cold) _).gasLeft
        - (_ - min _ (chargeEvm (sstorePreChargeEvm e rest key v o c cold) _).stateGasLeft) = _
    show (sstorePreChargeEvm e rest key v o c cold).gasLeft
        - sstoreExecCost o c v cold
        - (_ - min _ (sstorePreChargeEvm e rest key v o c cold).stateGasLeft) = _
    rw [sstorePreChargeEvm_gasLeft, sstorePreChargeEvm_stateGasLeft,
      sstoreLiveCredited, sstoreResCredited]
  · show (chargeStateEvm _ _).stateGasLeft = _
    rw [hsr]
    show (sstorePreChargeEvm e rest key v o c cold).stateGasLeft
        - min _ (sstorePreChargeEvm e rest key v o c cold).stateGasLeft = _
    rw [sstorePreChargeEvm_stateGasLeft, sstoreResCredited]
  · show (chargeStateEvm _ _).stateGasSpilled = _
    rw [hssp]
    show (sstorePreChargeEvm e rest key v o c cold).stateGasSpilled
        + (_ - min _ (sstorePreChargeEvm e rest key v o c cold).stateGasLeft) = _
    rw [sstorePreChargeEvm_stateGasLeft, sstorePreChargeEvm_stateGasSpilled,
      sstoreResCredited, sstoreSpillCredited]

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for SSTORE. -/
theorem sstore_dispatch (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_opcode (.SSTORE ()) pc_in top mem g =
      Evm.Functions.execute_sstore top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
/-- Amsterdam selects `amsterdam_sstore_costs`; the legacy schedule is
out of scope (fixed-fork comparison). -/
theorem runS_sstore_costs (o c n : Nat) (cold : Bool) (hs : Evm.HostState)
    (ss : SeqState) (prof : ExecutionProfile)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hfork : Amsterdam ≤ prof.1) :
    runS (Evm.Functions.sstore_costs o c n cold) hs ss
      = .ok (Evm.Functions.amsterdam_sstore_costs o c n cold, hs) ss := by
  obtain ⟨fork, t, mx, dn, cl, il, ptl, prl, tbl, rd, bl, ttl, trl, epf⟩ := prof
  simp only at hfork
  simp only [Evm.Functions.sstore_costs, runS_bind,
    runS_readReg _ _ _ _ hprof]
  simp only [ProtocolProfileFields.fork, decide_eq_true_eq]
  rw [if_pos (by simpa using hfork)]
  exact runS_pure _ _ _

open Evm.Functions in
/-- MM-14: the hoisted stack validation runs before `guard_static`. -/
theorem runS_execute_sstore_underflow (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 2) :
    runS (Evm.Functions.execute (.SSTORE ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.SSTORE ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 2 0 hs ss prof sp msg hprof hsp
      hmsg hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_sstore_static (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hin : 2 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (hstatic : msg.is_static = true) :
    runS (Evm.Functions.execute (.SSTORE ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .WriteProtection } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.SSTORE ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss hin
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, sstore_dispatch]
  have hbody : runS (Evm.Functions.execute_sstore top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .WriteProtection } := by
    obtain ⟨fork, t, mx, dn, cl, il, ptl, prl, tbl, rd, bl, ttl, trl, epf⟩ :=
      prof
    simp only [Evm.Functions.execute_sstore]
    refine runS_sailME_ok ?_
    refine runE_bind_ok (runE_lift (runS_readReg _ _ _ _ hprof)) ?_
    refine runE_bind_ok
      (runE_lift (runS_guard_static_halt g hs ss _ sp msg hprof hsp hmsg
        hfork hstatic)) ?_
    rw [if_pos rfl]
    exact runE_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
/-- The EIP-2200 sentry, on the extraction side: an early return
(`SailME.throw`) rather than a fall-through, which is why this tranche
needed the `SailME` run-shape layer. -/
theorem runS_execute_sstore_sentry_oog (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (l : List word) (frest : List (List word)) (x v : Nat)
    (rest : List word) (cold : Bool)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: v :: rest).reverse)
    (htop : top.toNat = (x :: v :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hstatic : msg.is_static = false)
    (hcold : cold = !decide (hs.warmEpoch ≤ (assocGet hs.warmSlots
      ({ addr := msg.address, slot := x } : Evm.Defs.StorageKey)).getD 0))
    (hoog : g < Evm.Functions.sstore_sentry_cost cold) :
    runS (Evm.Functions.execute (.SSTORE ()) pc_in top mem g) hs ss =
      .ok ((pc_in, cursorDrop top 2, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  have hnn : top.toNat = rest.length + 2 := by simp at htop; omega
  obtain ⟨hp1, ht1⟩ := cursor_pop_step l top x (v :: rest) hpfx htop
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.SSTORE ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, sstore_dispatch]
  have hbody : runS (Evm.Functions.execute_sstore top g) hs ss =
      .ok ((cursorDrop top 2, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    obtain ⟨fork, t, mx, dn, cl, il, ptl, prl, tbl, rd, bl, ttl, trl, epf⟩ :=
      prof
    simp only at hfork
    simp only [Evm.Functions.execute_sstore]
    refine runS_sailME_throw ?_
    refine runE_bind_ok (runE_lift (runS_readReg _ _ _ _ hprof)) ?_
    refine runE_bind_ok
      (runE_lift (runS_guard_static_ok g hs ss msg hmsg hstatic)) ?_
    rw [if_neg (by simp)]
    simp only [ProtocolProfileFields.fork, decide_eq_true_eq]
    rw [if_neg (by simp; omega)]
    refine runE_bind_ok
      (runE_lift (runS_pop top hs ss l frest x (v :: rest) hframe hpfx htop))
      ?_
    refine runE_bind_ok
      (runE_lift (runS_pop _ hs ss l frest v rest hframe hp1 ht1)) ?_
    refine runE_bind_ok (runE_lift (runS_self_addr msg hs ss hmsg)) ?_
    refine runE_bind_ok
      (runE_lift
        (show runS (k_slot_is_warm msg.address x) hs ss
            = .ok (!cold, hs) ss from by
          rw [show Evm.Functions.k_slot_is_warm msg.address x
            = Evm.Functions.storage_is_warm msg.address x from rfl,
            runS_storage_is_warm, hcold]
          simp)) ?_
    rw [if_pos (by simpa using hfork)]
    refine runE_bind_throw ?_
    refine runE_bind_ok
      (runE_lift
        (runS_check_execution_gas_oog g _ hs ss _ sp msg hprof hsp hmsg
          hfork (by simpa [Bool.not_not] using hoog))) ?_
    rw [if_pos (by simp)]
    exact runE_throw _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

/-! ### The success path

The extraction's outputs in closed form. The credit and the state charge
each have three branches (`runS_credit_closed` /
`runS_charge_state_closed` collapse them), and the two trailing guards
are stepped over by `runE_cond_val`, so the chain below has no case
analysis in it. -/

/-- The warm stamps after the cold-slot marking. -/
def sstoreWarmSlots (hs : Evm.HostState) (aV : Evm.Defs.address) (x : Nat) :
    List (Evm.Defs.StorageKey × Nat) :=
  assocPut hs.warmSlots
    ({ addr := aV, slot := x } : Evm.Defs.StorageKey) hs.warmEpoch

/-- The host state after the (conditional) write. MM-16: the extraction
skips the write when the value is unchanged. -/
def sstoreHostOut (hs : Evm.HostState) (aV : Evm.Defs.address) (x v : Nat)
    (entry : Evm.Defs.StorageValue) : Evm.HostState :=
  if (entry.curr != v) = true then
    hostStorageWrite hs aV x { curr := v, orig := entry.orig }
  else hs

/-- The register file after the (conditional) refund record. -/
def sstoreRefundRegs (ss : SeqState) (ref : Int)
    (cst : Evm.Defs.SstoreCosts) : SeqState :=
  if (!cst.refund == Evm.Functions.GAS_REFUND_ZERO) = true then
    { ss with
        regs := ss.regs.insert Register.frame_refund (ref + cst.refund) }
  else ss

open Evm.Functions in
theorem runS_execute_sstore_ok (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (res sp : Nat) (ref : Int)
    (msg : Evm.Defs.Message)
    (l : List word) (frest : List (List word)) (x v : Nat)
    (rest : List word) (cold : Bool) (entry : Evm.Defs.StorageValue)
    (hostAfter : List (Evm.Defs.StorageKey × Nat) → Evm.HostState)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hres : ss.regs.get? Register.state_gas_remaining = some res)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (href : ss.regs.get? Register.frame_refund = some ref)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hstatus : ss.regs.get? Register.frame_status = some (FrameStatus.Running ()))
    (hfork : Amsterdam ≤ prof.1)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: v :: rest).reverse)
    (htop : top.toNat = (x :: v :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hstatic : msg.is_static = false)
    (hcold : cold = !decide (hs.warmEpoch ≤ (assocGet hs.warmSlots
      ({ addr := msg.address, slot := x } : Evm.Defs.StorageKey)).getD 0))
    (hsentry : Evm.Functions.sstore_sentry_cost cold ≤ g)
    (hrun : ∀ ws, runS (Evm.Functions.k_sload msg.address x)
      { hs with warmSlots := ws } ss = .ok (entry, hostAfter ws) ss)
    (hexec : (sstoreCst entry v cold).execution
      ≤ g + min (sstoreCst entry v cold).state_credit sp)
    (hcharge : (sstoreCst entry v cold).state_charge
        - min (sstoreCst entry v cold).state_charge
            (res + ((sstoreCst entry v cold).state_credit
              - min (sstoreCst entry v cold).state_credit sp))
      ≤ g + min (sstoreCst entry v cold).state_credit sp
        - (sstoreCst entry v cold).execution)
    (hroom : (sstoreGasOut g res sp (sstoreCst entry v cold)).2.2 ≤ 2 ^ 24)
    (hreflo : -(Evm.Defs.gas_refund_bound : Int)
      ≤ ref + (sstoreCst entry v cold).refund)
    (hrefhi : ref + (sstoreCst entry v cold).refund
      ≤ (Evm.Defs.gas_refund_bound : Int)) :
    ∃ ss', runS (Evm.Functions.execute (.SSTORE ()) pc_in top mem g) hs ss
        = .ok ((pc_in, cursorDrop top 2, mem,
            (sstoreGasOut g res sp (sstoreCst entry v cold)).1),
          sstoreHostOut (hostAfter (sstoreWarmSlots hs msg.address x))
            msg.address x v entry) ss'
      ∧ ss'.regs.get? Register.state_gas_remaining
          = some (sstoreGasOut g res sp (sstoreCst entry v cold)).2.1
      ∧ ss'.regs.get? Register.state_gas_spilled
          = some (sstoreGasOut g res sp (sstoreCst entry v cold)).2.2
      ∧ ss'.regs.get? Register.frame_refund
          = some (ref + (sstoreCst entry v cold).refund)
      ∧ ss'.regs.get? Register.frame_status
          = some (FrameStatus.Running ())
      ∧ ss'.regs.get? Register.k_execution_profile = some prof
      ∧ ss'.regs.get? Register.message = some msg := by
  have hnn : top.toNat = rest.length + 2 := by simp at htop; omega
  obtain ⟨hp1, ht1⟩ := cursor_pop_step l top x (v :: rest) hpfx htop
  -- the host state and the register file after the read
  have hmark := runS_storage_mark_warm msg.address x hs ss
  obtain ⟨ssC, hC, hCres, hCsp, hCframe⟩ := runS_credit_closed g
    (sstoreCst entry v cold).state_credit
    (hostAfter (sstoreWarmSlots hs msg.address x)) ss res sp hres hsp
  -- the register file after the credit leg, whichever branch it took
  obtain ⟨ssCr, hCr, hCrres, hCrsp, hCrframe⟩ :
      ∃ ssCr : SeqState,
        (if ((sstoreCst entry v cold).state_credit != 0) = true then ssC
          else ss) = ssCr
        ∧ ssCr.regs.get? Register.state_gas_remaining
            = some (res + ((sstoreCst entry v cold).state_credit
              - min (sstoreCst entry v cold).state_credit sp))
        ∧ ssCr.regs.get? Register.state_gas_spilled
            = some (sp - min (sstoreCst entry v cold).state_credit sp)
        ∧ ∀ (r : Register), r ≠ Register.state_gas_remaining →
            r ≠ Register.state_gas_spilled →
            ssCr.regs.get? r = ss.regs.get? r := by
    by_cases hc : ((sstoreCst entry v cold).state_credit != 0) = true
    · exact ⟨ssC, if_pos hc, hCres, hCsp, hCframe⟩
    · have h0 : (sstoreCst entry v cold).state_credit = 0 := by simpa using hc
      refine ⟨ss, if_neg hc, ?_, ?_, fun _ _ _ => rfl⟩
      · rw [h0]
        simpa using hres
      · rw [h0]
        simpa using hsp
  -- the credited execution gas, whichever branch it took
  have hcredval : (if ((sstoreCst entry v cold).state_credit != 0) = true then
        g + min (sstoreCst entry v cold).state_credit sp else g)
      = g + min (sstoreCst entry v cold).state_credit sp := by
    by_cases hc : ((sstoreCst entry v cold).state_credit != 0) = true
    · rw [if_pos hc]
    · rw [if_neg hc]
      have h0 : (sstoreCst entry v cold).state_credit = 0 := by simpa using hc
      rw [h0]
      simp
  obtain ⟨ssS, hS, hSres, hSsp, hSframe⟩ := runS_charge_state_closed
    (g + min (sstoreCst entry v cold).state_credit sp
      - (sstoreCst entry v cold).execution)
    (sstoreCst entry v cold).state_charge
    (hostAfter (sstoreWarmSlots hs msg.address x)) ssCr
    (res + ((sstoreCst entry v cold).state_credit
      - min (sstoreCst entry v cold).state_credit sp))
    (sp - min (sstoreCst entry v cold).state_credit sp)
    hCrres hCrsp hcharge hroom
  have hne1 : Register.frame_refund ≠ Register.state_gas_remaining := by decide
  have hne2 : Register.frame_refund ≠ Register.state_gas_spilled := by decide
  have hrefS : ssS.regs.get? Register.frame_refund = some ref := by
    rw [hSframe _ hne1 hne2, hCrframe _ hne1 hne2]
    exact href
  have hbody : True → runS (Evm.Functions.execute_sstore top g) hs ss
      = .ok ((cursorDrop top 2,
          (sstoreGasOut g res sp (sstoreCst entry v cold)).1),
        sstoreHostOut (hostAfter (sstoreWarmSlots hs msg.address x))
          msg.address x v entry)
        (sstoreRefundRegs ssS ref (sstoreCst entry v cold)) := by
    intro _
    obtain ⟨fork, t, mx, dn, cl, il, ptl, prl, tbl, rd, bl, ttl, trl, epf⟩ :=
      prof
    simp only at hfork
    simp only [Evm.Functions.execute_sstore]
    refine runS_sailME_ok ?_
    refine runE_bind_ok (runE_lift (runS_readReg _ _ _ _ hprof)) ?_
    refine runE_bind_ok
      (runE_lift (runS_guard_static_ok g hs ss msg hmsg hstatic)) ?_
    rw [if_neg (by simp)]
    simp only [ProtocolProfileFields.fork, decide_eq_true_eq]
    rw [if_neg (by simp; omega)]
    refine runE_bind_ok
      (runE_lift (runS_pop top hs ss l frest x (v :: rest) hframe hpfx htop))
      ?_
    refine runE_bind_ok
      (runE_lift (runS_pop _ hs ss l frest v rest hframe hp1 ht1)) ?_
    refine runE_bind_ok (runE_lift (runS_self_addr msg hs ss hmsg)) ?_
    refine runE_bind_ok
      (runE_lift
        (show runS (k_slot_is_warm msg.address x) hs ss
            = .ok (!cold, hs) ss from by
          rw [show Evm.Functions.k_slot_is_warm msg.address x
            = Evm.Functions.storage_is_warm msg.address x from rfl,
            runS_storage_is_warm, hcold]
          simp)) ?_
    simp only [Bool.not_not]
    rw [if_pos (by simpa using hfork)]
    refine runE_bind_ok (b := ()) (hs' := hs) (ss' := ss) ?_ ?_
    · refine runE_bind_ok
        (runE_lift
          (runS_check_execution_gas_ok g _ hs ss hsentry)) ?_
      rw [if_neg (by simp)]
      exact runE_pure _ _ _
    refine runE_bind_ok
      (runE_lift
        (show runS (k_slot_mark_warm msg.address x) hs ss
            = .ok ((), { hs with warmSlots := sstoreWarmSlots hs msg.address x })
              ss from hmark)) ?_
    refine runE_bind_ok (runE_lift (hrun _)) ?_
    refine runE_bind_ok
      (runE_lift (runS_sstore_costs entry.orig entry.curr v cold _ ss _ hprof
        hfork)) ?_
    rw [show Evm.Functions.amsterdam_sstore_costs entry.orig entry.curr v cold
      = sstoreCst entry v cold from rfl]
    refine runE_bind_cond _ _ _ g _ hC ?_
    rw [hcredval, hCr, ite_self]
    refine runE_bind_ok
      (runE_lift
        (runS_charge_ok (g + min (sstoreCst entry v cold).state_credit sp) _
          _ ssCr hexec)) ?_
    rw [if_neg (by simp)]
    refine runE_bind_ok (runE_lift hS) ?_
    rw [if_neg (by simp)]
    refine runE_cond_val _ _ () () _
      (runS_record_refund (sstoreCst entry v cold).refund
        (hostAfter (sstoreWarmSlots hs msg.address x)) ssS ref hrefS hreflo
        hrefhi) ?_
    rw [ite_self, ← sstoreRefundRegs]
    refine runE_cond_val _ _ () () _
      (runS_k_sstore msg.address x { curr := v, orig := entry.orig }
        (hostAfter (sstoreWarmSlots hs msg.address x))
        (sstoreRefundRegs ssS ref (sstoreCst entry v cold))) ?_
    rw [ite_self]
    exact runE_pure _ _ _
  -- the trailing refund record only touches `frame_refund`
  have hgas1 : ∀ (r : Register), r ≠ Register.frame_refund →
      (sstoreRefundRegs ssS ref (sstoreCst entry v cold)).regs.get? r
        = ssS.regs.get? r := by
    intro r h3
    unfold sstoreRefundRegs
    by_cases hc : (!(sstoreCst entry v cold).refund == GAS_REFUND_ZERO) = true
    · rw [if_pos hc]
      show (ssS.regs.insert Register.frame_refund _).get? r = _
      exact regs_get?_insert_ne _ _ h3
    · rw [if_neg hc]
  have hall : ∀ (r : Register), r ≠ Register.state_gas_remaining →
      r ≠ Register.state_gas_spilled → r ≠ Register.frame_refund →
      (sstoreRefundRegs ssS ref (sstoreCst entry v cold)).regs.get? r
        = ss.regs.get? r := by
    intro r h1 h2 h3
    rw [hgas1 _ h3, hSframe _ h1 h2, hCrframe _ h1 h2]
  refine ⟨sstoreRefundRegs ssS ref (sstoreCst entry v cold), ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
  · simp only [Evm.Functions.execute,
      show Evm.Functions.opcode_stack_effect (.SSTORE ()) = pure (2, 0)
        from rfl]
    refine runS_bind_ok (runS_pure _ _ _) ?_
    refine runS_bind_ok
      (runS_validate_stack_ok g top 2 0 hs ss (by omega)
        (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
            simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
    rw [dif_pos rfl, sstore_dispatch]
    exact runS_bind_ok (hbody trivial) (runS_pure _ _ _)
  · rw [hgas1 _ (by decide)]
    exact hSres
  · rw [hgas1 _ (by decide)]
    exact hSsp
  · unfold sstoreRefundRegs
    by_cases hc : (!(sstoreCst entry v cold).refund == GAS_REFUND_ZERO) = true
    · rw [if_pos hc]
      show (ssS.regs.insert Register.frame_refund _).get?
        Register.frame_refund = _
      simp only [Std.ExtDHashMap.get?_insert]
      simp
    · rw [if_neg hc]
      have h0 : (sstoreCst entry v cold).refund = 0 := by
        simpa [Evm.Functions.GAS_REFUND_ZERO] using hc
      rw [h0, Int.add_zero]
      exact hrefS
  · rw [hall _ (by decide) (by decide) (by decide)]
    exact hstatus
  · rw [hall _ (by decide) (by decide) (by decide)]
    exact hprof
  · rw [hall _ (by decide) (by decide) (by decide)]
    exact hmsg

open Evm.Functions in
/-- The execution charge fails, after the credit leg. -/
theorem runS_execute_sstore_exec_oog (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (res sp : Nat) (msg : Evm.Defs.Message)
    (l : List word) (frest : List (List word)) (x v : Nat)
    (rest : List word) (cold : Bool) (entry : Evm.Defs.StorageValue)
    (hostAfter : List (Evm.Defs.StorageKey × Nat) → Evm.HostState)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hres : ss.regs.get? Register.state_gas_remaining = some res)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: v :: rest).reverse)
    (htop : top.toNat = (x :: v :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hstatic : msg.is_static = false)
    (hcold : cold = !decide (hs.warmEpoch ≤ (assocGet hs.warmSlots
      ({ addr := msg.address, slot := x } : Evm.Defs.StorageKey)).getD 0))
    (hsentry : Evm.Functions.sstore_sentry_cost cold ≤ g)
    (hrun : ∀ ws, runS (Evm.Functions.k_sload msg.address x)
      { hs with warmSlots := ws } ss = .ok (entry, hostAfter ws) ss)
    (hexec : ¬(sstoreCst entry v cold).execution
      ≤ g + min (sstoreCst entry v cold).state_credit sp) :
    ∃ hs' ss', runS (Evm.Functions.execute (.SSTORE ()) pc_in top mem g) hs ss
        = .ok ((pc_in, cursorDrop top 2, mem, GAS_ZERO), hs') ss'
      ∧ ss'.regs.get? Register.frame_status
          = some (FrameStatus.Exceptional ExceptionKind.OutOfGas) := by
  have hnn : top.toNat = rest.length + 2 := by simp at htop; omega
  obtain ⟨hp1, ht1⟩ := cursor_pop_step l top x (v :: rest) hpfx htop
  have hmark := runS_storage_mark_warm msg.address x hs ss
  obtain ⟨ssC, hC, hCres, hCsp, hCframe⟩ := runS_credit_closed g
    (sstoreCst entry v cold).state_credit
    (hostAfter (sstoreWarmSlots hs msg.address x)) ss res sp hres hsp
  obtain ⟨ssCr, hCr, hCrres, hCrsp, hCrframe⟩ :
      ∃ ssCr : SeqState,
        (if ((sstoreCst entry v cold).state_credit != 0) = true then ssC
          else ss) = ssCr
        ∧ ssCr.regs.get? Register.state_gas_remaining
            = some (res + ((sstoreCst entry v cold).state_credit
              - min (sstoreCst entry v cold).state_credit sp))
        ∧ ssCr.regs.get? Register.state_gas_spilled
            = some (sp - min (sstoreCst entry v cold).state_credit sp)
        ∧ ∀ (r : Register), r ≠ Register.state_gas_remaining →
            r ≠ Register.state_gas_spilled →
            ssCr.regs.get? r = ss.regs.get? r := by
    by_cases hc : ((sstoreCst entry v cold).state_credit != 0) = true
    · exact ⟨ssC, if_pos hc, hCres, hCsp, hCframe⟩
    · have h0 : (sstoreCst entry v cold).state_credit = 0 := by simpa using hc
      refine ⟨ss, if_neg hc, ?_, ?_, fun _ _ _ => rfl⟩
      · rw [h0]
        simpa using hres
      · rw [h0]
        simpa using hsp
  have hcredval : (if ((sstoreCst entry v cold).state_credit != 0) = true then
        g + min (sstoreCst entry v cold).state_credit sp else g)
      = g + min (sstoreCst entry v cold).state_credit sp := by
    by_cases hc : ((sstoreCst entry v cold).state_credit != 0) = true
    · rw [if_pos hc]
    · rw [if_neg hc]
      have h0 : (sstoreCst entry v cold).state_credit = 0 := by simpa using hc
      rw [h0]
      simp
  have hprofCr : ssCr.regs.get? Register.k_execution_profile = some prof := by
    rw [hCrframe _ (by decide) (by decide)]
    exact hprof
  have hmsgCr : ssCr.regs.get? Register.message = some msg := by
    rw [hCrframe _ (by decide) (by decide)]
    exact hmsg
  have hbody : True → runS (Evm.Functions.execute_sstore top g) hs ss
      = .ok ((cursorDrop top 2, GAS_ZERO),
          hostAfter (sstoreWarmSlots hs msg.address x))
        { ssCr with regs := haltRegs ssCr msg .OutOfGas } := by
    intro _
    obtain ⟨fork, t, mx, dn, cl, il, ptl, prl, tbl, rd, bl, ttl, trl, epf⟩ :=
      prof
    simp only at hfork
    simp only [Evm.Functions.execute_sstore]
    refine runS_sailME_ok ?_
    refine runE_bind_ok (runE_lift (runS_readReg _ _ _ _ hprof)) ?_
    refine runE_bind_ok
      (runE_lift (runS_guard_static_ok g hs ss msg hmsg hstatic)) ?_
    rw [if_neg (by simp)]
    simp only [ProtocolProfileFields.fork, decide_eq_true_eq]
    rw [if_neg (by simp; omega)]
    refine runE_bind_ok
      (runE_lift (runS_pop top hs ss l frest x (v :: rest) hframe hpfx htop))
      ?_
    refine runE_bind_ok
      (runE_lift (runS_pop _ hs ss l frest v rest hframe hp1 ht1)) ?_
    refine runE_bind_ok (runE_lift (runS_self_addr msg hs ss hmsg)) ?_
    refine runE_bind_ok
      (runE_lift
        (show runS (k_slot_is_warm msg.address x) hs ss
            = .ok (!cold, hs) ss from by
          rw [show Evm.Functions.k_slot_is_warm msg.address x
            = Evm.Functions.storage_is_warm msg.address x from rfl,
            runS_storage_is_warm, hcold]
          simp)) ?_
    simp only [Bool.not_not]
    rw [if_pos (by simpa using hfork)]
    refine runE_bind_ok (b := ()) (hs' := hs) (ss' := ss) ?_ ?_
    · refine runE_bind_ok
        (runE_lift (runS_check_execution_gas_ok g _ hs ss hsentry)) ?_
      rw [if_neg (by simp)]
      exact runE_pure _ _ _
    refine runE_bind_ok
      (runE_lift
        (show runS (k_slot_mark_warm msg.address x) hs ss
            = .ok ((), { hs with warmSlots := sstoreWarmSlots hs msg.address x })
              ss from hmark)) ?_
    refine runE_bind_ok (runE_lift (hrun _)) ?_
    refine runE_bind_ok
      (runE_lift (runS_sstore_costs entry.orig entry.curr v cold _ ss _ hprof
        hfork)) ?_
    rw [show Evm.Functions.amsterdam_sstore_costs entry.orig entry.curr v cold
      = sstoreCst entry v cold from rfl]
    refine runE_bind_cond _ _ _ g _ hC ?_
    rw [hcredval, hCr, ite_self]
    refine runE_bind_ok
      (runE_lift
        (runS_charge_oog (g + min (sstoreCst entry v cold).state_credit sp) _
          _ ssCr _ _ msg hprofCr hCrsp hmsgCr hfork
          (Nat.lt_of_not_le hexec))) ?_
    rw [if_pos (by simp)]
    exact runE_pure _ _ _
  refine ⟨hostAfter (sstoreWarmSlots hs msg.address x),
    { ssCr with regs := haltRegs ssCr msg .OutOfGas }, ?_,
    haltRegs_frame_status ssCr msg .OutOfGas⟩
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.SSTORE ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, sstore_dispatch]
  exact runS_bind_ok (hbody trivial) (runS_pure _ _ _)

open Evm.Functions in
/-- The state-gas charge fails: neither the reservoir nor the remaining
execution gas can cover it. -/
theorem runS_execute_sstore_state_oog (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (res sp : Nat) (msg : Evm.Defs.Message)
    (l : List word) (frest : List (List word)) (x v : Nat)
    (rest : List word) (cold : Bool) (entry : Evm.Defs.StorageValue)
    (hostAfter : List (Evm.Defs.StorageKey × Nat) → Evm.HostState)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hres : ss.regs.get? Register.state_gas_remaining = some res)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: v :: rest).reverse)
    (htop : top.toNat = (x :: v :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hstatic : msg.is_static = false)
    (hcold : cold = !decide (hs.warmEpoch ≤ (assocGet hs.warmSlots
      ({ addr := msg.address, slot := x } : Evm.Defs.StorageKey)).getD 0))
    (hsentry : Evm.Functions.sstore_sentry_cost cold ≤ g)
    (hrun : ∀ ws, runS (Evm.Functions.k_sload msg.address x)
      { hs with warmSlots := ws } ss = .ok (entry, hostAfter ws) ss)
    (hexec : (sstoreCst entry v cold).execution
      ≤ g + min (sstoreCst entry v cold).state_credit sp)
    (hcharge : ¬(sstoreCst entry v cold).state_charge
        - min (sstoreCst entry v cold).state_charge
            (res + ((sstoreCst entry v cold).state_credit
              - min (sstoreCst entry v cold).state_credit sp))
      ≤ g + min (sstoreCst entry v cold).state_credit sp
        - (sstoreCst entry v cold).execution) :
    ∃ hs' ss', runS (Evm.Functions.execute (.SSTORE ()) pc_in top mem g) hs ss
        = .ok ((pc_in, cursorDrop top 2, mem, GAS_ZERO), hs') ss'
      ∧ ss'.regs.get? Register.frame_status
          = some (FrameStatus.Exceptional ExceptionKind.OutOfGas) := by
  have hnn : top.toNat = rest.length + 2 := by simp at htop; omega
  obtain ⟨hp1, ht1⟩ := cursor_pop_step l top x (v :: rest) hpfx htop
  have hmark := runS_storage_mark_warm msg.address x hs ss
  obtain ⟨ssC, hC, hCres, hCsp, hCframe⟩ := runS_credit_closed g
    (sstoreCst entry v cold).state_credit
    (hostAfter (sstoreWarmSlots hs msg.address x)) ss res sp hres hsp
  obtain ⟨ssCr, hCr, hCrres, hCrsp, hCrframe⟩ :
      ∃ ssCr : SeqState,
        (if ((sstoreCst entry v cold).state_credit != 0) = true then ssC
          else ss) = ssCr
        ∧ ssCr.regs.get? Register.state_gas_remaining
            = some (res + ((sstoreCst entry v cold).state_credit
              - min (sstoreCst entry v cold).state_credit sp))
        ∧ ssCr.regs.get? Register.state_gas_spilled
            = some (sp - min (sstoreCst entry v cold).state_credit sp)
        ∧ ∀ (r : Register), r ≠ Register.state_gas_remaining →
            r ≠ Register.state_gas_spilled →
            ssCr.regs.get? r = ss.regs.get? r := by
    by_cases hc : ((sstoreCst entry v cold).state_credit != 0) = true
    · exact ⟨ssC, if_pos hc, hCres, hCsp, hCframe⟩
    · have h0 : (sstoreCst entry v cold).state_credit = 0 := by simpa using hc
      refine ⟨ss, if_neg hc, ?_, ?_, fun _ _ _ => rfl⟩
      · rw [h0]
        simpa using hres
      · rw [h0]
        simpa using hsp
  have hcredval : (if ((sstoreCst entry v cold).state_credit != 0) = true then
        g + min (sstoreCst entry v cold).state_credit sp else g)
      = g + min (sstoreCst entry v cold).state_credit sp := by
    by_cases hc : ((sstoreCst entry v cold).state_credit != 0) = true
    · rw [if_pos hc]
    · rw [if_neg hc]
      have h0 : (sstoreCst entry v cold).state_credit = 0 := by simpa using hc
      rw [h0]
      simp
  -- the failing test, split into the three the extraction's charge needs
  have hlt : res + ((sstoreCst entry v cold).state_credit
      - min (sstoreCst entry v cold).state_credit sp)
      < (sstoreCst entry v cold).state_charge := by
    by_contra hcon
    exact hcharge (by
      rw [Nat.min_eq_left (Nat.le_of_not_lt hcon), Nat.sub_self]
      exact Nat.zero_le _)
  have hgt : g + min (sstoreCst entry v cold).state_credit sp
      - (sstoreCst entry v cold).execution
      < (sstoreCst entry v cold).state_charge
        - (res + ((sstoreCst entry v cold).state_credit
          - min (sstoreCst entry v cold).state_credit sp)) := by
    rw [Nat.min_eq_right (Nat.le_of_lt hlt)] at hcharge
    exact Nat.lt_of_not_le hcharge
  have hnz : (sstoreCst entry v cold).state_charge ≠ 0 := by
    intro h0
    rw [h0] at hlt
    exact Nat.not_lt_zero _ hlt
  have hprofCr : ssCr.regs.get? Register.k_execution_profile = some prof := by
    rw [hCrframe _ (by decide) (by decide)]
    exact hprof
  have hmsgCr : ssCr.regs.get? Register.message = some msg := by
    rw [hCrframe _ (by decide) (by decide)]
    exact hmsg
  have hbody : True → runS (Evm.Functions.execute_sstore top g) hs ss
      = .ok ((cursorDrop top 2, GAS_ZERO),
          hostAfter (sstoreWarmSlots hs msg.address x))
        { ssCr with regs := haltRegs ssCr msg .OutOfGas } := by
    intro _
    obtain ⟨fork, t, mx, dn, cl, il, ptl, prl, tbl, rd, bl, ttl, trl, epf⟩ :=
      prof
    simp only at hfork
    simp only [Evm.Functions.execute_sstore]
    refine runS_sailME_ok ?_
    refine runE_bind_ok (runE_lift (runS_readReg _ _ _ _ hprof)) ?_
    refine runE_bind_ok
      (runE_lift (runS_guard_static_ok g hs ss msg hmsg hstatic)) ?_
    rw [if_neg (by simp)]
    simp only [ProtocolProfileFields.fork, decide_eq_true_eq]
    rw [if_neg (by simp; omega)]
    refine runE_bind_ok
      (runE_lift (runS_pop top hs ss l frest x (v :: rest) hframe hpfx htop))
      ?_
    refine runE_bind_ok
      (runE_lift (runS_pop _ hs ss l frest v rest hframe hp1 ht1)) ?_
    refine runE_bind_ok (runE_lift (runS_self_addr msg hs ss hmsg)) ?_
    refine runE_bind_ok
      (runE_lift
        (show runS (k_slot_is_warm msg.address x) hs ss
            = .ok (!cold, hs) ss from by
          rw [show Evm.Functions.k_slot_is_warm msg.address x
            = Evm.Functions.storage_is_warm msg.address x from rfl,
            runS_storage_is_warm, hcold]
          simp)) ?_
    simp only [Bool.not_not]
    rw [if_pos (by simpa using hfork)]
    refine runE_bind_ok (b := ()) (hs' := hs) (ss' := ss) ?_ ?_
    · refine runE_bind_ok
        (runE_lift (runS_check_execution_gas_ok g _ hs ss hsentry)) ?_
      rw [if_neg (by simp)]
      exact runE_pure _ _ _
    refine runE_bind_ok
      (runE_lift
        (show runS (k_slot_mark_warm msg.address x) hs ss
            = .ok ((), { hs with warmSlots := sstoreWarmSlots hs msg.address x })
              ss from hmark)) ?_
    refine runE_bind_ok (runE_lift (hrun _)) ?_
    refine runE_bind_ok
      (runE_lift (runS_sstore_costs entry.orig entry.curr v cold _ ss _ hprof
        hfork)) ?_
    rw [show Evm.Functions.amsterdam_sstore_costs entry.orig entry.curr v cold
      = sstoreCst entry v cold from rfl]
    refine runE_bind_cond _ _ _ g _ hC ?_
    rw [hcredval, hCr, ite_self]
    refine runE_bind_ok
      (runE_lift
        (runS_charge_ok (g + min (sstoreCst entry v cold).state_credit sp) _
          _ ssCr hexec)) ?_
    rw [if_neg (by simp)]
    refine runE_bind_ok
      (runE_lift
        (runS_charge_state_gas_oog _ _ _ ssCr _ _ _ msg hprofCr hCrsp hmsgCr
          hCrres hfork hnz hlt hgt)) ?_
    rw [if_pos (by simp)]
    exact runE_pure _ _ _
  refine ⟨hostAfter (sstoreWarmSlots hs msg.address x),
    { ssCr with regs := haltRegs ssCr msg .OutOfGas }, ?_,
    haltRegs_frame_status ssCr msg .OutOfGas⟩
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.SSTORE ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, sstore_dispatch]
  exact runS_bind_ok (hbody trivial) (runS_pure _ _ _)

/-! ### The rest of the post-frame's projections

The credit and the two charges touch only gas, the refund block only the
counter, the warm mark only the access set: everything else passes
straight through the composition. -/

theorem sstorePostEvm_stack (e : Evm) (rest : List U256)
    (key : Address × Bytes32) (v o c : U256) (cold : Bool) :
    (sstorePostEvm e rest key v o c cold).stack = rest := by
  unfold sstorePostEvm pcBump chargeStateEvm chargeEvm sstorePreChargeEvm
    creditEvm sstoreRefundEvm sstoreRefundBody sstoreWarmedEvm sstoreWarmEvm
  repeat' split
  all_goals rfl

theorem sstorePostEvm_pc (e : Evm) (rest : List U256)
    (key : Address × Bytes32) (v o c : U256) (cold : Bool) :
    (sstorePostEvm e rest key v o c cold).pc = e.pc + 1 := by
  unfold sstorePostEvm pcBump chargeStateEvm chargeEvm sstorePreChargeEvm
    creditEvm sstoreRefundEvm sstoreRefundBody sstoreWarmedEvm sstoreWarmEvm
  repeat' split
  all_goals rfl

theorem sstorePostEvm_running (e : Evm) (rest : List U256)
    (key : Address × Bytes32) (v o c : U256) (cold : Bool) :
    (sstorePostEvm e rest key v o c cold).running = e.running
      ∧ (sstorePostEvm e rest key v o c cold).error = e.error := by
  unfold sstorePostEvm pcBump chargeStateEvm chargeEvm sstorePreChargeEvm
    creditEvm sstoreRefundEvm sstoreRefundBody sstoreWarmedEvm sstoreWarmEvm
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

theorem sstorePostEvm_accessed (e : Evm) (rest : List U256)
    (key : Address × Bytes32) (v o c : U256) (cold : Bool) :
    (sstorePostEvm e rest key v o c cold).accessedStorageKeys
      = (sstoreWarmEvm e cold key).accessedStorageKeys := by
  unfold sstorePostEvm pcBump chargeStateEvm chargeEvm sstorePreChargeEvm
    creditEvm sstoreRefundEvm sstoreRefundBody sstoreWarmedEvm sstoreWarmEvm
  repeat' split
  all_goals rfl

theorem sstorePostEvm_refundCounter (e : Evm) (rest : List U256)
    (key : Address × Bytes32) (v o c : U256) (cold : Bool) :
    (sstorePostEvm e rest key v o c cold).refundCounter
      = e.refundCounter + specRefundDelta o c v := by
  rw [show (sstorePostEvm e rest key v o c cold).refundCounter
      = (sstoreRefundEvm e o c v).refundCounter from by
    unfold sstorePostEvm pcBump chargeStateEvm chargeEvm sstorePreChargeEvm
      creditEvm sstoreRefundEvm sstoreRefundBody sstoreWarmedEvm sstoreWarmEvm
    repeat' split
    all_goals rfl]
  exact sstoreRefundEvm_refundCounter e o c v

/-! ### The two sides' affordability tests

The extraction tests the cost record against `(g, res, sp)`; SpecRef
tests its inlined quantities against the credited frame. These four
equalities are the whole translation, and `sub_min_le_iff` is the
`Nat`-subtraction shuffle between "charge what the reservoir cannot
cover" and "charge against reservoir plus live gas". -/

private theorem min_credit (cond : Bool) (sp : Nat) :
    min (if cond then StateGasCosts.STORAGE_SET else 0) sp
      = (if cond then min StateGasCosts.STORAGE_SET sp else 0) := by
  split <;> simp

theorem sstoreCstRef_live (e : Evm) (o c v : U256) (cold : Bool) :
    e.gasLeft + min (sstoreCstRef o c v cold).state_credit e.stateGasSpilled
      = sstoreLiveCredited e o c v := by
  show e.gasLeft
      + min (if sstoreCreditCond o c v then StateGasCosts.STORAGE_SET else 0)
          e.stateGasSpilled = _
  rw [min_credit]
  rfl

theorem sstoreCstRef_res (e : Evm) (o c v : U256) (cold : Bool) :
    e.stateGasLeft + ((sstoreCstRef o c v cold).state_credit
        - min (sstoreCstRef o c v cold).state_credit e.stateGasSpilled)
      = sstoreResCredited e o c v := by
  show e.stateGasLeft
      + ((if sstoreCreditCond o c v then StateGasCosts.STORAGE_SET else 0)
        - min (if sstoreCreditCond o c v then StateGasCosts.STORAGE_SET else 0)
            e.stateGasSpilled) = _
  rw [min_credit]
  unfold sstoreResCredited
  split <;> simp

private theorem sub_min_le_iff (a r b : Nat) : a - min a r ≤ b ↔ a ≤ r + b := by
  omega

/-- The step moves the recorded spill by at most the state charge, which
is what turns the pre-state form of the EIP-7825 cap into the
extraction's post-state check. -/
private theorem sstoreGasOut_spill_le (g res sp : Nat)
    (cst : Evm.Defs.SstoreCosts) :
    (sstoreGasOut g res sp cst).2.2 ≤ sp + cst.state_charge := by
  show sp - min cst.state_credit sp
      + (cst.state_charge
        - min cst.state_charge
            (res + (cst.state_credit - min cst.state_credit sp)))
    ≤ sp + cst.state_charge
  omega

theorem sstoreStateCharge_le (o c v : U256) :
    sstoreStateCharge o c v ≤ StateGasCosts.STORAGE_SET := by
  unfold sstoreStateCharge
  split
  · exact Nat.le_refl _
  · exact Nat.zero_le _

/-! ### The refund range

`record_refund` hard-aborts outside `±gas_refund_bound`
([`RefundInRange`](../Relations/Refund.lean)); one `SSTORE` moves the
counter by at most `REFUND_STORAGE_CLEAR + STORAGE_WRITE`, so the step
theorem takes the pre-state headroom and derives the post-state check. -/

/-- The pre-state form of the extraction's refund-range check: one
`SSTORE`'s worst-case movement still fits. -/
def SstoreRefundHeadroom (r : Int) : Prop :=
  -(Evm.Defs.gas_refund_bound : Int)
      + ((GasCosts.REFUND_STORAGE_CLEAR : Int) + (GasCosts.STORAGE_WRITE : Int))
      ≤ r
    ∧ r ≤ (Evm.Defs.gas_refund_bound : Int)
      - ((GasCosts.REFUND_STORAGE_CLEAR : Int) + (GasCosts.STORAGE_WRITE : Int))

/-- ... which is exactly what makes `record_refund`'s check pass. -/
theorem refundInRange_of_headroom {r d : Int} (h : SstoreRefundHeadroom r)
    (hlo : -(GasCosts.REFUND_STORAGE_CLEAR : Int) ≤ d)
    (hhi : d ≤ (GasCosts.REFUND_STORAGE_CLEAR : Int)
      + (GasCosts.STORAGE_WRITE : Int)) :
    RefundInRange (r + d) := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨by omega, by omega⟩

theorem specRefundDelta_bounds (o c n : U256) :
    -(GasCosts.REFUND_STORAGE_CLEAR : Int) ≤ specRefundDelta o c n
      ∧ specRefundDelta o c n
        ≤ (GasCosts.REFUND_STORAGE_CLEAR : Int)
          + (GasCosts.STORAGE_WRITE : Int) := by
  unfold specRefundDelta
  simp only [GasCosts.REFUND_STORAGE_CLEAR, GasCosts.STORAGE_WRITE,
    GasCosts.COLD_STORAGE_ACCESS]
  repeat' split
  all_goals omega

/-! ## The ledgered agreement hypothesis -/

/-- **Ledgered hypothesis** (see `Assumptions.lean`): the storage
sibling of [`SloadAgree`](Sload.lean) for the writer. It says the two
sides' three storage steps for the popped slot agree —
`getStorageOriginal` and `getStorage` against the row the extraction's
`k_sload` returns, and SpecRef's `setStorage` succeeds (its
account-existence rejection has no counterpart in `k_sstore`) — and
records `k_sload`'s framing: it leaves the stack, the warm stamps and the
transaction overlay alone, and when the overlay already holds a row for
the slot, that row is the one it returns. The world tranche discharges
it; `sstoreAgree_of_storageRel` discharges it today for a slot the
transaction has already written. -/
def SstoreAgree (sRef : Machine) (hs : Evm.HostState) (ss : SeqState)
    (aV : Evm.Defs.address) (x v : Nat) : Prop :=
  ∃ (ts₂ ts₃ : TransactionState) (entry : Evm.Defs.StorageValue)
    (hostAfter : List (Evm.Defs.StorageKey × Nat) → Evm.HostState),
    WordWf entry.curr ∧
    (getStorageOriginal sRef.evm.message.currentTarget (toBeBytes32 x)).run
        sRef.txState = .ok (entry.orig, ts₂) ∧
    (getStorage sRef.evm.message.currentTarget (toBeBytes32 x)).run ts₂
        = .ok (entry.curr, ts₃) ∧
    (∃ ts₄, (setStorage sRef.evm.message.currentTarget (toBeBytes32 x) v).run
      ts₃ = .ok ((), ts₄)) ∧
    (∀ ws, runS (Evm.Functions.k_sload aV x) { hs with warmSlots := ws } ss
      = .ok (entry, hostAfter ws) ss) ∧
    (∀ ws, (hostAfter ws).stackFrames = hs.stackFrames) ∧
    (∀ ws, (hostAfter ws).warmSlots = ws) ∧
    (∀ ws, (hostAfter ws).warmEpoch = hs.warmEpoch) ∧
    (∀ ws, (hostAfter ws).storageTx = hs.storageTx) ∧
    (∀ e, hostStorageSlot hs aV x = some e → e = entry)

/-- **`SstoreAgree` on the transaction-overlay regime.** A slot the
transaction has already written is a `storage_tx_get` hit, so `k_sload`
returns the stored row without touching any state, and SpecRef's two
reads resolve to the same pair through [`StorageRel`](../Relations/Storage.lean).
SpecRef's account-existence rejection stays a hypothesis: `k_sstore` has
no such check, so nothing on the extraction's side implies it. -/
theorem sstoreAgree_of_storageRel (sRef : Machine) (hs : Evm.HostState)
    (ss : SeqState) (aV : Evm.Defs.address) (x v : Nat) (hx : WordWf x)
    (e : Evm.Defs.StorageValue) (hrow : hostStorageSlot hs aV x = some e)
    (haddr : aV.toList = sRef.evm.message.currentTarget)
    (hsr : StorageRel sRef.txState hs)
    (hwrite : ∀ ts', StorageFieldsEq sRef.txState ts' →
      ∃ ts₄, (setStorage sRef.evm.message.currentTarget (toBeBytes32 x) v).run
        ts' = .ok ((), ts₄)) :
    SstoreAgree sRef hs ss aV x v := by
  obtain ⟨ts₂, horig, f1, f2, f3, f4⟩ := runTx_getStorageOriginal_ok
    sRef.txState sRef.evm.message.currentTarget (toBeBytes32 x) e.orig
    (by rw [← haddr]; exact hsr.orig aV x hx e hrow)
  have hfe2 : StorageFieldsEq sRef.txState ts₂ := ⟨f1, f2, f3, f4⟩
  have hcurr : (getStorage sRef.evm.message.currentTarget
        (toBeBytes32 x)).run ts₂
      = .ok (e.curr, specStorageReadOf ts₂ sRef.evm.message.currentTarget
        (toBeBytes32 x)) :=
    runTx_getStorage_tx_hit _ _ _ _ (by
      rw [storageFieldsEq_specTxSlot hfe2, ← haddr]
      exact hsr.curr aV x hx e hrow)
  refine ⟨ts₂, _, e, fun ws => { hs with warmSlots := ws },
    hsr.wf aV x hx e hrow, horig, hcurr,
    hwrite _ (storageFieldsEq_trans hfe2 (storageFieldsEq_readOf _ _ _)),
    fun ws => runS_k_sload_hit aV x e _ ss hrow,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_⟩
  intro e' he'
  rw [hrow] at he'
  exact (Option.some.inj he').symm

/-! ## The step equivalence -/

private theorem sstoreHostOut_frames (hs : Evm.HostState)
    (aV : Evm.Defs.address) (x v : Nat) (entry : Evm.Defs.StorageValue) :
    (sstoreHostOut hs aV x v entry).stackFrames = hs.stackFrames := by
  unfold sstoreHostOut hostStorageWrite
  split <;> rfl

private theorem sstoreHostOut_warmSlots (hs : Evm.HostState)
    (aV : Evm.Defs.address) (x v : Nat) (entry : Evm.Defs.StorageValue) :
    (sstoreHostOut hs aV x v entry).warmSlots = hs.warmSlots := by
  unfold sstoreHostOut hostStorageWrite
  split <;> rfl

private theorem sstoreHostOut_warmEpoch (hs : Evm.HostState)
    (aV : Evm.Defs.address) (x v : Nat) (entry : Evm.Defs.StorageValue) :
    (sstoreHostOut hs aV x v entry).warmEpoch = hs.warmEpoch := by
  unfold sstoreHostOut hostStorageWrite
  split <;> rfl

/-- Success post-relation for SSTORE: the storage post (base plus the
write itself) together with the warm marking and the refund counter —
the step's whole observable footprint. -/
def SstorePost (mem : EvmMemorySlice) (sR' : Machine) (step : EvmStep)
    (hs' : Evm.HostState) (ss' : SeqState) : Prop :=
  StoragePost mem sR' step hs' ss' ∧ WarmRel sR' hs' ∧ RefundRel sR'.evm ss'

open Evm.Functions in
/-- **SSTORE, all reachable outcomes**: the write (related by
`StorageRel`, the warm mark by `WarmRel` and the refund by `RefundRel`),
the static halt, the EIP-2200 sentry, the execution-gas and state-gas
out-of-gas halts, and the MM-14 double fault. The Amsterdam schedule is
proven outright (`sstoreCst_eq`); the values read and written are behind
the ledgered [`SstoreAgree`](#) hypothesis.

Two hypotheses are extraction-only hard aborts with no SpecRef
counterpart, threaded rather than eliminated: `hroom` is the EIP-7825 cap
on the recorded spill (`TX_MAX_GAS_LIMIT = 2^24` on both sides) and
`hhead` is `record_refund`'s validated range (see
[`RefundInRange`](../Relations/Refund.lean)). Both are stated on the
pre-state, so one `SSTORE`'s worst-case movement is what has to fit. -/
theorem sstore_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hwrel : WarmRel sRef hs)
    (hsrel : StorageRel sRef.txState hs)
    (hrfrel : RefundRel sRef.evm ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (hroom : sRef.evm.stateGasSpilled + StateGasCosts.STORAGE_SET ≤ 2 ^ 24)
    (hhead : SstoreRefundHeadroom sRef.evm.refundCounter)
    (haddr : ∀ m : Evm.Defs.Message,
      ss.regs.get? Register.message = some m →
      m.address.toList = sRef.evm.message.currentTarget)
    (hstatic : ∀ m : Evm.Defs.Message,
      ss.regs.get? Register.message = some m →
      m.is_static = sRef.evm.message.isStatic)
    (hagree : ∀ (m : Evm.Defs.Message) (x v : U256) (rest : List U256),
      ss.regs.get? Register.message = some m →
      sRef.evm.stack = x :: v :: rest →
      SstoreAgree sRef hs ss m.address x v) :
    StepResultRel (SstorePost mem) (runR iSstore sRef)
      (runS (Evm.Functions.execute (.SSTORE ()) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ :=
    hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  have hst : msg.is_static = sRef.evm.message.isStatic := hstatic msg hmsg
  have hax : msg.address.toList = sRef.evm.message.currentTarget :=
    haddr msg hmsg
  by_cases hunder : sRef.evm.stack.length < 2
  · -- MM-14: the extraction's hoisted stack check fires first either way
    rw [runS_execute_sstore_underflow pc_in top mem g hs ss prof
      sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
      (by rw [htop]; exact hunder)]
    by_cases hstat : sRef.evm.message.isStatic = true
    · rw [runR_iSstore_static sRef hstat]
      exact StepResultRel.haltedStaticFirst
        (haltRegs_frame_status ss msg .StackUnderflow)
    · obtain ⟨s', hs'⟩ :=
        runR_iSstore_underflow sRef (by simpa using hstat) hunder
      rw [hs']
      exact StepResultRel.halted ErrorRel.stackUnderflow
        (haltRegs_frame_status ss msg .StackUnderflow)
  · push Not at hunder
    obtain ⟨x, v, rest, hS⟩ :
        ∃ x v rest, sRef.evm.stack = x :: v :: rest := by
      match hSm : sRef.evm.stack with
      | [] => rw [hSm] at hunder; simp only [List.length_nil] at hunder; omega
      | [x] =>
        rw [hSm] at hunder
        simp only [List.length_cons, List.length_nil] at hunder
        omega
      | x :: v :: rest => exact ⟨x, v, rest, rfl⟩
    rw [hS] at hpfx htop hlim hwfS
    have hnn : top.toNat = rest.length + 2 := by
      simp only [List.length_cons] at htop; omega
    have hlim' : top.toNat ≤ 1024 := by
      simp only [List.length_cons] at hlim; omega
    have hlimR : rest.length ≤ 1024 := by omega
    have hwfx : WordWf x := hwfS x (by simp)
    have hwfv : WordWf v := hwfS v (by simp)
    by_cases hstat : sRef.evm.message.isStatic = true
    · rw [runR_iSstore_static sRef hstat,
        runS_execute_sstore_static pc_in top mem g hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega) hlim'
          (by rw [hst]; exact hstat)]
      exact StepResultRel.halted ErrorRel.writeInStaticContext
        (haltRegs_frame_status ss msg .WriteProtection)
    · have hstat0 : sRef.evm.message.isStatic = false := by simpa using hstat
      have hstat' : msg.is_static = false := by rw [hst]; exact hstat0
      -- the cold flag: SpecRef's set membership is the extraction's stamp
      have hiff := hwrel.rel msg.address x hwfx
      rw [hax] at hiff
      have hdec : decide (hs.warmEpoch ≤ (assocGet hs.warmSlots
            ({ addr := msg.address, slot := x } : Evm.Defs.StorageKey)).getD 0)
          = sRef.evm.accessedStorageKeys.contains
            (sRef.evm.message.currentTarget, toBeBytes32 x) := by
        by_cases hc : sRef.evm.accessedStorageKeys.contains
            (sRef.evm.message.currentTarget, toBeBytes32 x) = true
        · rw [hc]
          exact decide_eq_true (hiff.mp hc)
        · simp only [Bool.not_eq_true] at hc
          rw [hc]
          refine decide_eq_false (fun hh => ?_)
          rw [hiff.mpr hh] at hc
          cases hc
      obtain ⟨cold, hcoldR, hcoldE⟩ :
          ∃ cold : Bool,
            cold = !sRef.evm.accessedStorageKeys.contains
              (sRef.evm.message.currentTarget, toBeBytes32 x)
            ∧ cold = !decide (hs.warmEpoch ≤ (assocGet hs.warmSlots
              ({ addr := msg.address, slot := x } :
                Evm.Defs.StorageKey)).getD 0) :=
        ⟨_, rfl, by rw [hdec]⟩
      by_cases hsent : max (sstoreAccessCost cold) (GasCosts.CALL_STIPEND + 1)
          ≤ sRef.evm.gasLeft
      case neg =>
        obtain ⟨s', hs'⟩ := runR_iSstore_sentry_oog sRef x v rest cold hS
          hstat0 hcoldR (Nat.lt_of_not_le hsent)
        rw [hs', runS_execute_sstore_sentry_oog pc_in top mem g hs ss prof
          sRef.evm.stateGasSpilled msg l frest x v rest cold hprof hsp hmsg
          hfork hframe hpfx htop hlim' hstat' hcoldE
          (by rw [sstore_sentry_cost_eq, hlive]; exact Nat.lt_of_not_le hsent)]
        exact StepResultRel.halted ErrorRel.outOfGas
          (haltRegs_frame_status ss msg .OutOfGas)
      obtain ⟨ts₂, ts₃, entry, hostAfter, hwfc, horig, hcurr, ⟨ts₄, hset⟩,
        hrun, hframes, hslots, hepoch, hstx, hhit⟩ := hagree msg x v rest hmsg hS
      have hsentS : Evm.Functions.sstore_sentry_cost cold ≤ g := by
        rw [sstore_sentry_cost_eq, hlive]
        exact hsent
      -- the two sides' cost records, and the tests they drive
      have hcst : sstoreCst entry v cold
          = sstoreCstRef entry.orig entry.curr v cold := sstoreCst_eq entry v cold
      have hexecEq : (sstoreCst entry v cold).execution
          = sstoreExecCost entry.orig entry.curr v cold := by rw [hcst]; rfl
      have hchargeEq : (sstoreCst entry v cold).state_charge
          = sstoreStateCharge entry.orig entry.curr v := by rw [hcst]; rfl
      have hrefEq : (sstoreCst entry v cold).refund
          = specRefundDelta entry.orig entry.curr v := by rw [hcst]; rfl
      have hliveEq : g + min (sstoreCst entry v cold).state_credit
            sRef.evm.stateGasSpilled
          = sstoreLiveCredited sRef.evm entry.orig entry.curr v := by
        rw [hcst, hlive]
        exact sstoreCstRef_live sRef.evm entry.orig entry.curr v cold
      have hresEq : sRef.evm.stateGasLeft + ((sstoreCst entry v cold).state_credit
            - min (sstoreCst entry v cold).state_credit sRef.evm.stateGasSpilled)
          = sstoreResCredited sRef.evm entry.orig entry.curr v := by
        rw [hcst]
        exact sstoreCstRef_res sRef.evm entry.orig entry.curr v cold
      by_cases hexec : sstoreExecCost entry.orig entry.curr v cold
          ≤ sstoreLiveCredited sRef.evm entry.orig entry.curr v
      case neg =>
        obtain ⟨s', hs'⟩ := runR_iSstore_exec_oog sRef x v entry.orig entry.curr
          rest ts₂ ts₃ cold hS hstat0 hcoldR hsent horig hcurr hexec
        obtain ⟨hs2, ss2, hrunS, hstatus2⟩ :=
          runS_execute_sstore_exec_oog pc_in top mem g hs ss prof
            sRef.evm.stateGasLeft sRef.evm.stateGasSpilled msg l frest x v rest
            cold entry hostAfter hprof hres hsp hmsg hfork hframe hpfx htop
            hlim' hstat' hcoldE hsentS hrun
            (by rw [hexecEq, hliveEq]; exact hexec)
        rw [hs', hrunS]
        exact StepResultRel.halted ErrorRel.outOfGas hstatus2
      by_cases hstate : sstoreStateCharge entry.orig entry.curr v
          ≤ sstoreResCredited sRef.evm entry.orig entry.curr v
            + (sstoreLiveCredited sRef.evm entry.orig entry.curr v
              - sstoreExecCost entry.orig entry.curr v cold)
      case neg =>
        obtain ⟨s', hs'⟩ := runR_iSstore_state_oog sRef x v entry.orig
          entry.curr rest ts₂ ts₃ cold hS hstat0 hcoldR hsent horig hcurr hexec
          hstate
        obtain ⟨hs2, ss2, hrunS, hstatus2⟩ :=
          runS_execute_sstore_state_oog pc_in top mem g hs ss prof
            sRef.evm.stateGasLeft sRef.evm.stateGasSpilled msg l frest x v rest
            cold entry hostAfter hprof hres hsp hmsg hfork hframe hpfx htop
            hlim' hstat' hcoldE hsentS hrun
            (by rw [hexecEq, hliveEq]; exact hexec)
            (by rw [sub_min_le_iff, hchargeEq, hresEq, hliveEq, hexecEq]
                exact hstate)
        rw [hs', hrunS]
        exact StepResultRel.halted ErrorRel.outOfGas hstatus2
      -- success
      obtain ⟨hdlo, hdhi⟩ := specRefundDelta_bounds entry.orig entry.curr v
      obtain ⟨hreflo, hrefhi⟩ :=
        refundInRange_of_headroom hhead hdlo hdhi
      obtain ⟨ss', hrunS, hres', hsp', href', hstatus', hprof', hmsg'⟩ :=
        runS_execute_sstore_ok pc_in top mem g hs ss prof sRef.evm.stateGasLeft
          sRef.evm.stateGasSpilled sRef.evm.refundCounter msg l frest x v rest
          cold entry hostAfter hprof hres hsp hrfrel.rel hmsg hrunE hfork hframe
          hpfx htop hlim' hstat' hcoldE hsentS hrun
          (by rw [hexecEq, hliveEq]; exact hexec)
          (by rw [sub_min_le_iff, hchargeEq, hresEq, hliveEq, hexecEq]
              exact hstate)
          (by
            refine Nat.le_trans (sstoreGasOut_spill_le _ _ _ _) ?_
            rw [hchargeEq]
            exact Nat.le_trans
              (Nat.add_le_add_left (sstoreStateCharge_le entry.orig entry.curr v)
                sRef.evm.stateGasSpilled) hroom)
          (by rw [hrefEq]; exact hreflo) (by rw [hrefEq]; exact hrefhi)
      rw [runR_iSstore_success sRef x v entry.orig entry.curr rest ts₂ ts₃ ts₄
          cold hS hstat0 hcoldR hsent horig hcurr hexec hstate hset, hrunS]
      have hret2 : (cursorDrop top 2).toNat = rest.length := by
        rw [cursorDrop_toNat top 2 (by omega)]
        omega
      have hpfx2 : l.take rest.length = rest.reverse := by
        obtain ⟨hp1, ht1⟩ := cursor_pop_step l top x (v :: rest) hpfx htop
        obtain ⟨hp2, ht2⟩ := cursor_pop_step l _ v rest hp1 ht1
        rw [show rest.length = (cursorDrop top 2).toNat from hret2.symm]
        exact hp2
      obtain ⟨⟨hgl, hgr⟩, hgsp⟩ := sstorePostEvm_gas sRef.evm rest
        (sRef.evm.message.currentTarget, toBeBytes32 x) v entry.orig entry.curr
        cold
      obtain ⟨hrun1, hrun2⟩ := sstorePostEvm_running sRef.evm rest
        (sRef.evm.message.currentTarget, toBeBytes32 x) v entry.orig entry.curr
        cold
      refine StepResultRel.success
        ⟨⟨⟨⟨?_, ?_, ⟨?_, ?_⟩, hstatus', ⟨prof, hprof', hfork⟩, ⟨msg, hmsg'⟩⟩,
          ?_, rfl⟩, ?_⟩, ?_, ⟨?_⟩⟩
      · rw [sstorePostEvm_stack]
        exact ⟨⟨l, frest, by rw [sstoreHostOut_frames, hframes, hframe],
            by rw [hret2]; exact hpfx2, by rw [hret2]; omega⟩,
          by rw [hret2], hlimR, fun w hw => hwfS w (by simp [hw])⟩
      · refine ⟨?_, ?_, ?_⟩
        · rw [hgl, hcst, hlive]
        · rw [hres', hgr, hcst, hlive]
        · rw [hsp', hgsp, hcst, hlive]
      · rw [hrun1]; exact hrunR.1
      · rw [hrun2]; exact hrunR.2
      · rw [sstorePostEvm_pc]; exact hpc
      · -- the write itself
        have hfe3 : StorageFieldsEq sRef.txState ts₃ :=
          storageFieldsEq_trans
            (storageFieldsEq_getStorageOriginal _ _ _ _ _ horig)
            (storageFieldsEq_getStorage _ _ _ _ _ hcurr)
        have hrel3 : StorageRel ts₃
            (hostAfter (sstoreWarmSlots hs msg.address x)) :=
          storageRel_hostFrame (hstx _)
            (storageRel_frame hfe3.1 hfe3.2.1 hfe3.2.2.1 hfe3.2.2.2 hsrel)
        have horig3 : specOrig ts₃ msg.address.toList (toBeBytes32 x)
            = .ok entry.orig := by
          rw [hax, storageFieldsEq_specOrig hfe3]
          exact runTx_getStorageOriginal_val _ _ _ _ _ horig
        obtain ⟨w1, w2, w3, w4⟩ := runTx_setStorage_frame ts₃ ts₄ _ _ v hset
        by_cases hchanged : (entry.curr != v) = true
        · have hw := storageRel_write ts₃
            (hostAfter (sstoreWarmSlots hs msg.address x)) msg.address x
            { curr := v, orig := entry.orig } hwfx hwfv horig3 hrel3
          rw [hax] at hw
          rw [show sstoreHostOut (hostAfter (sstoreWarmSlots hs msg.address x))
                msg.address x v entry
              = hostStorageWrite (hostAfter (sstoreWarmSlots hs msg.address x))
                msg.address x { curr := v, orig := entry.orig } from by
            unfold sstoreHostOut
            rw [if_pos hchanged]]
          exact storageRel_frame w1 w2 w3 w4 hw
        · have hsame : ∀ e, hostStorageSlot
              (hostAfter (sstoreWarmSlots hs msg.address x)) msg.address x
              = some e → e.curr = v := by
            intro e' he'
            rw [show hostStorageSlot
                  (hostAfter (sstoreWarmSlots hs msg.address x)) msg.address x
                = hostStorageSlot hs msg.address x from by
              unfold hostStorageSlot
              rw [hstx]] at he'
            rw [hhit e' he']
            simpa using hchanged
          have hw := storageRel_write_noop ts₃
            (hostAfter (sstoreWarmSlots hs msg.address x)) msg.address x v hwfx
            hsame hrel3
          rw [hax] at hw
          rw [show sstoreHostOut (hostAfter (sstoreWarmSlots hs msg.address x))
                msg.address x v entry
              = hostAfter (sstoreWarmSlots hs msg.address x) from by
            unfold sstoreHostOut
            rw [if_neg hchanged]]
          exact storageRel_frame w1 w2 w3 w4 hw
      · -- the warm mark
        refine ⟨fun bV w hw => ?_⟩
        rw [sstoreHostOut_warmSlots, sstoreHostOut_warmEpoch, hslots, hepoch,
          sstorePostEvm_accessed]
        have hmark := warm_after_mark sRef.evm.accessedStorageKeys hs.warmSlots
          hs.warmEpoch msg.address x hwfx hwrel.rel bV w hw
        rw [hax] at hmark
        unfold sstoreWarmEvm sstoreWarmSlots
        by_cases hc : cold = true
        · rw [if_pos hc]
          exact hmark
        · rw [if_neg hc]
          have hcont : sRef.evm.accessedStorageKeys.contains
              (sRef.evm.message.currentTarget, toBeBytes32 x) = true := by
            simp only [Bool.not_eq_true] at hc
            rw [hcoldR] at hc
            simpa using hc
          rw [setAdd_eq_of_contains _ _ hcont] at hmark
          exact hmark
      · -- the refund counter
        rw [href', sstorePostEvm_refundCounter, hrefEq]

end EvmSpecsVerify
