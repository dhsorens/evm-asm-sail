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

end EvmSpecsVerify
