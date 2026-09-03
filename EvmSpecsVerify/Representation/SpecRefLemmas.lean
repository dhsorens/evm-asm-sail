import EvmAsm.Stateless.SpecRef

/-!
# Run-shape algebra for SpecRef's `EvmM`

`EvmM α = ExceptT EvmError (StateT Machine (Except SpecError)) α`
(SpecRef/Vm.lean:223). SpecRef's own primitives (`EvmM.getEvm`,
`EvmM.modifyEvm`, …) are raw state lambdas, so most run-shapes are `rfl`;
the value of this file is fixing one normal form (`runR`) and giving the
stack/gas primitives their case-split lemmas, which no upstream file states.

An `EvmM` computation, fully applied, yields
`Except SpecError (Except EvmError α × Machine)`:
the outer `Except` is the spec-abort layer (not an EVM outcome), the inner
one is the EVM exceptional layer — a `.error` there still carries the
mutated `Machine`, which is exactly what the halt-boundary comparison needs.
-/

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef

/-- Fully-applied run of a SpecRef `EvmM` action. -/
def runR (m : EvmM α) (s : Machine) :
    Except SpecError (Except EvmError α × Machine) :=
  (ExceptT.run m).run s

@[simp]
theorem runR_pure (a : α) (s : Machine) :
    runR (pure a) s = .ok (.ok a, s) := rfl

@[simp]
theorem runR_throw (e : EvmError) (s : Machine) :
    runR (throw e : EvmM α) s = .ok (.error e, s) := rfl

@[simp]
theorem runR_bind (m : EvmM α) (k : α → EvmM β) (s : Machine) :
    runR (m >>= k) s =
      match runR m s with
      | .ok (.ok a, s') => runR (k a) s'
      | .ok (.error e, s') => .ok (.error e, s')
      | .error e => .error e := by
  simp only [runR, ExceptT.run_bind, StateT.run_bind]
  cases h : (ExceptT.run m).run s with
  | ok p =>
    obtain ⟨a | a, s'⟩ := p <;> rfl
  | error e => rfl

/-- Fused bind: success step then continuation. Avoids match residue in
chained rewrites. -/
theorem runR_bind_ok {m : EvmM α} {k : α → EvmM β} {s s' : Machine} {a : α}
    {r : Except SpecError (Except EvmError β × Machine)}
    (h1 : runR m s = .ok (.ok a, s')) (h2 : runR (k a) s' = r) :
    runR (m >>= k) s = r := by
  rw [runR_bind, h1]; exact h2

/-- Fused bind: the first action throws, the continuation is skipped. -/
theorem runR_bind_err {m : EvmM α} {k : α → EvmM β} {s s' : Machine}
    {e : EvmError}
    (h1 : runR m s = .ok (.error e, s')) :
    runR (m >>= k) s = .ok (.error e, s') := by
  rw [runR_bind, h1]

@[simp]
theorem runR_getEvm (s : Machine) :
    runR EvmM.getEvm s = .ok (.ok s.evm, s) := rfl

/-- The functor-map reading shape (`f <$> getEvm`) that `chargeWithMemory`
and similar helpers compile to. -/
theorem runR_getEvm_map {α : Type} (f : EvmAsm.Stateless.SpecRef.Evm → α)
    (s : Machine) :
    runR ((f <$> EvmM.getEvm : EvmM α)) s = .ok (.ok (f s.evm), s) := rfl

@[simp]
theorem runR_modifyEvm (f : Evm → Evm) (s : Machine) :
    runR (EvmM.modifyEvm f) s = .ok (.ok (), { s with evm := f s.evm }) := rfl


/-- Run a state-tracker (`TxM`) action through `EvmM.liftTx`: on a
successful tracker run, the machine keeps everything but `txState`. -/
theorem runR_liftTx_ok (m : TxM α) (s : Machine) (a : α)
    (ts' : TransactionState) (h : m.run s.txState = .ok (a, ts')) :
    runR (EvmM.liftTx m) s = .ok (.ok a, { s with txState := ts' }) := by
  have hshape : runR (EvmM.liftTx m) s = (match m.run s.txState with
      | Except.error e => Except.error e
      | Except.ok (a, ts) =>
        Except.ok (Except.ok a, { s with txState := ts })) := rfl
  rw [hshape, h]

/-- Run a pure spec computation (`Except SpecError`) through
`EvmM.liftSpec`: on `.ok` the machine is untouched. The `.error` case is
an outer abort, outside the step-result boundary. -/
theorem runR_liftSpec_ok {α : Type} (m : Except SpecError α) (s : Machine)
    (a : α) (h : m = .ok a) :
    runR (EvmM.liftSpec m) s = .ok (.ok a, s) := by
  rw [h]
  rfl

/-! ## Stack primitives -/

theorem runR_stackPop_cons (s : Machine) (x : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: rest) :
    runR stackPop s = .ok (.ok x, { s with evm := { s.evm with stack := rest } }) := by
  simp only [stackPop, runR_bind, runR_getEvm, hstack]
  rfl

theorem runR_stackPop_nil (s : Machine) (hstack : s.evm.stack = []) :
    runR stackPop s = .ok (.error .stackUnderflow, s) := by
  simp only [stackPop, runR_bind, runR_getEvm, hstack]
  rfl

theorem runR_stackPush (s : Machine) (v : U256)
    (hlen : s.evm.stack.length ≠ 1024) :
    runR (stackPush v) s =
      .ok (.ok (), { s with evm := { s.evm with stack := v :: s.evm.stack } }) := by
  simp only [stackPush, runR_bind, runR_getEvm]
  simp [hlen]

theorem runR_stackPush_overflow (s : Machine) (v : U256)
    (hlen : s.evm.stack.length = 1024) :
    runR (stackPush v) s = .ok (.error .stackOverflow, s) := by
  simp only [stackPush, runR_bind, runR_getEvm]
  simp [hlen]

/-! ## Gas primitives -/

theorem runR_charge_gas (s : Machine) (amount : Uint)
    (hgas : amount ≤ s.evm.gasLeft) :
    runR (charge_gas amount) s =
      .ok (.ok (),
        { s with evm := { s.evm with
            gasLeft := s.evm.gasLeft - amount
            regularGasUsed := s.evm.regularGasUsed + amount } }) := by
  simp only [charge_gas, runR_bind, runR_getEvm]
  simp [Nat.not_lt.mpr hgas]

theorem runR_charge_gas_oog (s : Machine) (amount : Uint)
    (hgas : s.evm.gasLeft < amount) :
    runR (charge_gas amount) s = .ok (.error .outOfGas, s) := by
  simp only [charge_gas, runR_bind, runR_getEvm]
  simp [hgas]

/-! ## Two-dimensional gas (Amsterdam)

`check_gas` is a sentry — it reads the live gas without spending it.
`charge_state_gas` spends the frame's state-gas reservoir first and
spills the remainder into execution gas; `credit_state_gas_refund` is its
LIFO inverse (execution gas up to the recorded spill, then the
reservoir). SSTORE is the first opcode to use any of the three. -/

theorem runR_check_gas (s : Machine) (amount : Uint)
    (hgas : amount ≤ s.evm.gasLeft) :
    runR (check_gas amount) s = .ok (.ok (), s) := by
  simp only [check_gas, runR_bind, runR_getEvm]
  simp [Nat.not_lt.mpr hgas]

theorem runR_check_gas_oog (s : Machine) (amount : Uint)
    (hgas : s.evm.gasLeft < amount) :
    runR (check_gas amount) s = .ok (.error .outOfGas, s) := by
  simp only [check_gas, runR_bind, runR_getEvm]
  simp [hgas]

/-- The reservoir covers the charge. -/
theorem runR_charge_state_gas_reservoir (s : Machine) (amount : Uint)
    (h : amount ≤ s.evm.stateGasLeft) :
    runR (charge_state_gas amount) s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stateGasLeft := s.evm.stateGasLeft - amount } }) := by
  simp only [charge_state_gas, runR_bind, runR_getEvm]
  rw [if_pos h]
  exact runR_modifyEvm _ _

/-- The reservoir runs out and the remainder spills into execution gas. -/
theorem runR_charge_state_gas_spill (s : Machine) (amount : Uint)
    (h1 : s.evm.stateGasLeft < amount)
    (h2 : amount ≤ s.evm.stateGasLeft + s.evm.gasLeft) :
    runR (charge_state_gas amount) s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stateGasLeft := 0
            gasLeft := s.evm.gasLeft - (amount - s.evm.stateGasLeft)
            stateGasSpilled :=
              s.evm.stateGasSpilled + (amount - s.evm.stateGasLeft) } }) := by
  simp only [charge_state_gas, runR_bind, runR_getEvm]
  rw [if_neg (Nat.not_le.mpr h1), if_pos h2]
  exact runR_modifyEvm _ _

theorem runR_charge_state_gas_oog (s : Machine) (amount : Uint)
    (h : s.evm.stateGasLeft + s.evm.gasLeft < amount) :
    runR (charge_state_gas amount) s = .ok (.error .outOfGas, s) := by
  have key : ∀ a b c : Nat, a + b < c → ¬(c ≤ a) ∧ ¬(c ≤ a + b) :=
    fun _ _ _ hh => ⟨by omega, by omega⟩
  obtain ⟨h1, h2⟩ := key s.evm.stateGasLeft s.evm.gasLeft amount h
  simp only [charge_state_gas, runR_bind, runR_getEvm]
  rw [if_neg h1, if_neg h2]
  exact runR_throw _ _

/-- The credit is unconditional: `min amount spilled` goes back to
execution gas, the rest to the reservoir. -/
theorem runR_credit_state_gas_refund (s : Machine) (amount : Uint) :
    runR (credit_state_gas_refund amount) s =
      .ok (.ok (),
        { s with evm := { s.evm with
            gasLeft := s.evm.gasLeft + min amount s.evm.stateGasSpilled
            stateGasSpilled :=
              s.evm.stateGasSpilled - min amount s.evm.stateGasSpilled
            stateGasLeft :=
              s.evm.stateGasLeft
                + (amount - min amount s.evm.stateGasSpilled) } }) := by
  simp only [credit_state_gas_refund, runR_bind, runR_getEvm]
  exact runR_modifyEvm _ _

end EvmSpecsVerify
