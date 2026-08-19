import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas
import Batteries.Tactic.OpenPrivate

/-!
# Base-cost `k_env` pusher shape (0-in/1-out)

The block-environment pushers (COINBASE, TIMESTAMP, NUMBER, PREVRANDAO,
GASLIMIT, CHAINID, BASEFEE, SLOTNUM) share one shape on both sides.

SpecRef: `i<Op> = pushConstOf OPCODE_<OP> f` — read the machine, charge
the base cost, push `f evm`, advance the pc (`pushConst`; charge-first,
so MM-5 applies to the double-fault states).
`Evm`: `execute_<op>` is `envPushShape F_<Field>` — charge `G_base`, read
the field through `k_env`, push.

[`envPush_step_equiv`](#envPush_step_equiv) is the full-outcome step
theorem, generic over the `k_env` read (supplied per opcode as `hval`, a
run shape producing exactly SpecRef's value) and the pushed word's
well-formedness (`hwf`). Reachable: success / stack overflow / OOG /
MM-5 double fault.
-/

open private pcNext pushConst from EvmAsm.Stateless.SpecRef.InstructionsEnv
open private writeListAt from Evm.HostAxioms

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## SpecRef side: `pushConst` of a machine read, generically -/

/-- The SpecRef block-env pusher shape: every `i<Op>` in the family is
definitionally `pushConstOf OPCODE_<OP> f` for its field reader `f`. -/
def pushConstOf (gas : Uint) (f : Evm → U256) : EvmM Unit := do
  pushConst gas (f (← EvmM.getEvm))

theorem runR_pushConstOf_success (gas : Uint) (f : Evm → U256) (s : Machine)
    (hlen : s.evm.stack.length ≠ 1024)
    (hgas : gas ≤ s.evm.gasLeft) :
    runR (pushConstOf gas f) s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := f s.evm :: s.evm.stack
            gasLeft := s.evm.gasLeft - gas
            regularGasUsed := s.evm.regularGasUsed + gas
            pc := s.evm.pc + 1 } }) := by
  simp only [pushConstOf, pushConst, pcNext]
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_stackPush _ _
    (by show s.evm.stack.length ≠ 1024; exact hlen)) ?_
  exact runR_modifyEvm _ _

theorem runR_pushConstOf_overflow (gas : Uint) (f : Evm → U256)
    (s : Machine)
    (hlen : s.evm.stack.length = 1024)
    (hgas : gas ≤ s.evm.gasLeft) :
    runR (pushConstOf gas f) s =
      .ok (.error .stackOverflow,
        { s with evm := { s.evm with
            gasLeft := s.evm.gasLeft - gas
            regularGasUsed := s.evm.regularGasUsed + gas } }) := by
  simp only [pushConstOf, pushConst]
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  exact runR_bind_err (runR_stackPush_overflow _ _
    (by show s.evm.stack.length = 1024; exact hlen))

/-- OOG fires at the leading charge, before the push (MM-5). -/
theorem runR_pushConstOf_oog (gas : Uint) (f : Evm → U256) (s : Machine)
    (hgas : s.evm.gasLeft < gas) :
    runR (pushConstOf gas f) s = .ok (.error .outOfGas, s) := by
  simp only [pushConstOf, pushConst]
  refine runR_bind_ok (runR_getEvm _) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _ hgas)

/-! ## `Evm` side: the handler shape, generically -/

/-- The shared body of every `Evm` block-env pusher: charge `G_base`,
read the field through `k_env`, push. Each generated `execute_<op>` is
definitionally `envPushShape F_<Field>`. -/
def envPushShape (fld : EnvField) (top : StackTop) (g : Nat) :
    Evm.SailM (StackTop × Nat) := do
  let (gas_charged, g1) ← do (Evm.Functions.charge g Evm.Functions.G_base)
  if ((! gas_charged) : Bool)
  then (pure (top, g1))
  else
    (do
      let v ← do (Evm.Functions.k_env fld)
      (pure ((← (Evm.Functions.push_word top v)), g1)))

/-- The dispatch equation every block-env pusher constructor satisfies by
`rfl`. -/
def EnvPushDispatch (op : ast) (fld : EnvField) : Prop :=
  Evm.Functions.opcode_stack_effect op = pure (0, 1) ∧
  ∀ (pc_in : Nat) (top : StackTop) (mem : EvmMemorySlice) (g : Nat),
    Evm.Functions.execute_opcode op pc_in top mem g =
      envPushShape fld top g >>= fun p => pure (pc_in, p.1, mem, p.2)

open Evm.Functions in
theorem runS_execute_envPush_success (op : ast) (fld : EnvField)
    (hop : EnvPushDispatch op fld)
    (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (v : word)
    (hframe : hs.stackFrames = l :: frest)
    (hval : runS (Evm.Functions.k_env fld) hs ss = .ok (v, hs) ss)
    (hlim : top.toNat + 1 ≤ 1024)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hgas : (G_base : Nat) ≤ g) :
    runS (Evm.Functions.execute op pc_in top mem g) hs ss =
      .ok ((pc_in, top + BitVec.ofNat 64 1, mem, g - G_base),
        { hs with stackFrames :=
            writeListAt l top.toNat v :: frest }) ss := by
  simp only [Evm.Functions.execute, hop.1]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 1 hs ss (by omega)
      (by have h : top.toNat - 0 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, hop.2]
  have hbody : runS (envPushShape fld top g) hs ss =
      .ok ((top + BitVec.ofNat 64 1, g - G_base),
        { hs with stackFrames :=
            writeListAt l top.toNat v :: frest }) ss := by
    simp only [envPushShape]
    refine runS_bind_ok (runS_charge_ok g G_base hs ss hgas) ?_
    rw [if_neg (by simp)]
    refine runS_bind_ok hval ?_
    refine runS_bind_ok
      (runS_push_word top v hs ss l frest hframe hbound) ?_
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
theorem runS_execute_envPush_overflow (op : ast) (fld : EnvField)
    (hop : EnvPushDispatch op fld)
    (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hover : 1024 < top.toNat + 1) :
    runS (Evm.Functions.execute op pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackOverflow } := by
  simp only [Evm.Functions.execute, hop.1]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_overflow g top 0 1 hs ss prof sp msg hprof hsp hmsg
      hfork (by omega)
      (by have h : (1024 : Nat) < top.toNat - 0 + 1 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_envPush_oog (op : ast) (fld : EnvField)
    (hop : EnvPushDispatch op fld)
    (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hlim : top.toNat + 1 ≤ 1024)
    (hgas : g < (G_base : Nat)) :
    runS (Evm.Functions.execute op pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute, hop.1]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 1 hs ss (by omega)
      (by have h : top.toNat - 0 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, hop.2]
  have hbody : runS (envPushShape fld top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [envPushShape]
    refine runS_bind_ok
      (runS_charge_oog g G_base hs ss prof sp msg hprof hsp hmsg hfork
        hgas) ?_
    rw [if_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

/-! ## The step equivalence, generically -/

open Evm.Functions in
/-- **The block-env pusher family, all reachable outcomes.** Per-opcode
content: the dispatch `rfl`s, the `k_env` run shape producing exactly
SpecRef's value (`hval`), and the pushed word's bound (`hwf`).
Double-fault states (full stack ∧ OOG) use the MM-5 constructor. -/
theorem envPush_step_equiv (op : ast) (fld : EnvField) (iOp : EvmM Unit)
    (specCost : Uint) (fSpec : EvmAsm.Stateless.SpecRef.Evm → U256)
    (hspec : iOp = pushConstOf specCost fSpec)
    (hcost : (specCost : Nat) = 2)
    (hop : EnvPushDispatch op fld)
    (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (hval : runS (Evm.Functions.k_env fld) hs ss =
      .ok (fSpec sRef.evm, hs) ss)
    (hwf : WordWf (fSpec sRef.evm)) :
    StepResultRel (BasePost mem) (runR iOp sRef)
      (runS (Evm.Functions.execute op pc_in top mem g) hs ss) := by
  subst hspec
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  have hgb : (G_base : Nat) = 2 := rfl
  by_cases hg : sRef.evm.gasLeft < specCost
  · rw [runR_pushConstOf_oog specCost fSpec sRef hg]
    have hgN : g < 2 := by
      rw [← hcost, hlive]
      exact hg
    by_cases hov : sRef.evm.stack.length = 1024
    · rw [runS_execute_envPush_overflow op fld hop pc_in top g mem hs ss
        prof sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.haltedChargeFirst (Or.inr rfl)
        (haltRegs_frame_status ss msg .StackOverflow)
    · rw [runS_execute_envPush_oog op fld hop pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)
        (by show g < (2 : Nat); omega)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
  · push Not at hg
    have hgN : (2 : Nat) ≤ g := by
      rw [← hcost, hlive]
      exact hg
    by_cases hov : sRef.evm.stack.length = 1024
    · rw [runR_pushConstOf_overflow specCost fSpec sRef hov hg,
        runS_execute_envPush_overflow op fld hop pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.halted ErrorRel.stackOverflow
        (haltRegs_frame_status ss msg .StackOverflow)
    · have hbound : top.toNat + 1 < 2 ^ 64 := by
        have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
        omega
      rw [runR_pushConstOf_success specCost fSpec sRef hov hg,
        runS_execute_envPush_success op fld hop pc_in top g mem hs ss l
          frest (fSpec sRef.evm) hframe hval (by omega) hbound
          (by show (2 : Nat) ≤ g; omega)]
      have hadv : (top + BitVec.ofNat 64 1).toNat = top.toNat + 1 :=
        cursor_advance_toNat top hbound
      have hgas' : g - (G_base : Nat) = sRef.evm.gasLeft - specCost := by
        rw [hlive, hgb, ← hcost]
      refine StepResultRel.success ?_
      refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
        ⟨msg, hmsg⟩⟩, by simp [hpc], rfl⟩
      · refine ⟨⟨writeListAt l top.toNat (fSpec sRef.evm), frest,
            rfl, ?_, ?_⟩, ?_, ?_, ?_⟩
        · rw [hadv, take_writeListAt l top.toNat _ (by omega), hpfx]
          simp
        · rw [hadv, length_writeListAt]
          omega
        · rw [hadv]
          simp
          omega
        · simp
          omega
        · intro w hw
          rcases List.mem_cons.mp hw with hw | hw
          · subst hw
            exact hwf
          · exact hwfS w hw
      · exact ⟨by rw [hgas'], hres, hsp⟩

end EvmSpecsVerify
