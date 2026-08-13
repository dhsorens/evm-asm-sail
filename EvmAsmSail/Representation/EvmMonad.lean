import Evm

/-!
# Run-shape algebra for the `Evm` extraction's monad

`Evm.SailM α = StateT HostState Evm.Defs.SailM α` with
`Evm.Defs.SailM = EStateM (Sail.Error exception) SeqState`
(HostAxioms.lean:1181, Defs.lean:3237). Neither lean-sail nor the extraction
provides reasoning lemmas about it; this file is the reusable layer everything
monadic on the `Evm` side goes through.

Convention: all lemmas are about `runS m hs ss`, the fully-applied run
(host state, then register state), normalized to an `EStateM.Result` whose
value part is `α × HostState`. Register reads take an explicit
`ss.regs.get? r = some v` hypothesis — the state relation supplies these,
so no global "all registers initialized" invariant is needed.
-/

namespace EvmAsmSail

open Evm (HostState)

/-- The register-file state of the extraction (lean-sail's sequential state
instantiated at the `Evm` model's registers). -/
abbrev SeqState :=
  PreSail.SequentialState Evm.Defs.RegisterType Sail.trivialChoiceSource

/-- The error type of the base monad. -/
abbrev SailError := Sail.Error Evm.Defs.exception

/-- Fully-applied run of an `Evm.SailM` action. -/
def runS (m : Evm.SailM α) (hs : HostState) (ss : SeqState) :
    EStateM.Result SailError SeqState (α × HostState) :=
  (m.run hs).run ss

@[simp]
theorem runS_pure (a : α) (hs : HostState) (ss : SeqState) :
    runS (pure a) hs ss = .ok (a, hs) ss := rfl

@[simp]
theorem runS_bind (m : Evm.SailM α) (k : α → Evm.SailM β) (hs : HostState)
    (ss : SeqState) :
    runS (m >>= k) hs ss =
      match runS m hs ss with
      | .ok (a, hs') ss' => runS (k a) hs' ss'
      | .error e ss' => .error e ss' := by
  simp only [runS, StateT.run_bind, EStateM.run_bind]
  cases (m.run hs).run ss with
  | ok p ss' => rfl
  | error e ss' => rfl

/-- Fused bind: success step then continuation. Avoids match residue in
chained rewrites. -/
theorem runS_bind_ok {m : Evm.SailM α} {k : α → Evm.SailM β}
    {hs hs' : HostState} {ss ss' : SeqState} {a : α}
    {r : EStateM.Result SailError SeqState (β × HostState)}
    (h1 : runS m hs ss = .ok (a, hs') ss') (h2 : runS (k a) hs' ss' = r) :
    runS (m >>= k) hs ss = r := by
  rw [runS_bind, h1]; exact h2

/-- `StateT.lift` of a base action: the host state is untouched. -/
@[simp]
theorem runS_lift (m : Evm.Defs.SailM α) (hs : HostState) (ss : SeqState) :
    runS (StateT.lift m : Evm.SailM α) hs ss =
      match m.run ss with
      | .ok a ss' => .ok (a, hs) ss'
      | .error e ss' => .error e ss' := by
  simp only [runS, StateT.run_lift, EStateM.run_bind]
  cases m.run ss with
  | ok a ss' => rfl
  | error e ss' => rfl

/-! ## Register file -/

@[simp]
theorem runS_readReg (r : Evm.Defs.Register) (v : Evm.Defs.RegisterType r)
    (hs : HostState) (ss : SeqState) (h : ss.regs.get? r = some v) :
    runS (Evm.readReg r) hs ss = .ok (v, hs) ss := by
  show runS (StateT.lift (PreSail.readReg r)) hs ss = _
  rw [runS_lift]
  simp [PreSail.readReg, EStateM.run_bind, EStateM.run_get, h]

@[simp]
theorem runS_writeReg (r : Evm.Defs.Register) (v : Evm.Defs.RegisterType r)
    (hs : HostState) (ss : SeqState) :
    runS (Evm.writeReg r v) hs ss =
      .ok (PUnit.unit, hs) { ss with regs := ss.regs.insert r v } := rfl

/-! ## Host state (`StateT` layer) -/

@[simp]
theorem runS_get (hs : HostState) (ss : SeqState) :
    runS (get : Evm.SailM HostState) hs ss = .ok (hs, hs) ss := rfl

@[simp]
theorem runS_set (hs' hs : HostState) (ss : SeqState) :
    runS (set hs' : Evm.SailM PUnit) hs ss = .ok (PUnit.unit, hs') ss := rfl

@[simp]
theorem runS_modify (f : HostState → HostState) (hs : HostState) (ss : SeqState) :
    runS (modify f : Evm.SailM PUnit) hs ss = .ok (PUnit.unit, f hs) ss := rfl

/-! ## Errors -/

@[simp]
theorem runS_throw (e : SailError) (hs : HostState) (ss : SeqState) :
    runS (throw e : Evm.SailM α) hs ss = .error e ss := rfl

end EvmAsmSail
