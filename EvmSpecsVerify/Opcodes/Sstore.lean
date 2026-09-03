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
-/

open private pcAdd isWarmStorageKey warmStorageKey from
  EvmAsm.Stateless.SpecRef.InstructionsCore

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

end EvmSpecsVerify
