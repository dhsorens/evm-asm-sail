import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas
import Batteries.Tactic.OpenPrivate

/-!
# Live-state pusher shape (0-in/1-out, value read after the charge)

PC, GAS and MSIZE push a value taken from the **live step state** rather
than from a `k_env` block field, so they cannot go through
[`envPush_step_equiv`](EnvPusher.lean): the extraction computes their words
from `pc_in`, the carried gas, or the memory slice instead of reading a
register.

SpecRef's half is uniform across all three — `charge → stackPush (f evm) →
pc+1`, with `f` reading the machine *after* the charge (which is what makes
GAS push `gasLeft - 2`). That is [`livePushOf`](#livePushOf), and its three
run shapes below are shared.

The extraction's half is uniform for PC and GAS (`(top, g)`-returning
bodies, memory untouched) and captured by
[`LivePushDispatch`](#LivePushDispatch); MSIZE's body threads the memory
slice through its own return type, so it reuses only the SpecRef half.

Charge-first on both sides, so double-fault states (full stack ∧ out of
gas) land on mismatch ledger MM-5, exactly as for the env pushers.
Reachable: success / stack overflow / OOG / MM-5 double fault; underflow
is impossible for 0-in.
-/

open private pcAdd from EvmAsm.Stateless.SpecRef.InstructionsCore
open private writeListAt from Evm.HostAxioms

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## SpecRef side -/

/-- The machine after a successful `charge_gas amount`. The live-state
pushers read their value from *this* state, not the pre-charge one. -/
def chargedEvm (e : EvmAsm.Stateless.SpecRef.Evm) (amount : Uint) :
    EvmAsm.Stateless.SpecRef.Evm :=
  { e with
      gasLeft := e.gasLeft - amount
      regularGasUsed := e.regularGasUsed + amount }

/-- The SpecRef live-state pusher shape: `iPc`, `iGas` and `iMsize` are
each definitionally `livePushOf OPCODE_<OP> f` for their machine reader
`f`. Contrast [`pushConstOf`](EnvPusher.lean), which reads the machine
*before* charging. -/
def livePushOf (gas : Uint) (f : EvmAsm.Stateless.SpecRef.Evm → U256) :
    EvmM Unit := do
  charge_gas gas
  stackPush (f (← EvmM.getEvm))
  pcAdd 1

theorem runR_livePushOf_success (gas : Uint)
    (f : EvmAsm.Stateless.SpecRef.Evm → U256) (s : Machine)
    (hlen : s.evm.stack.length ≠ 1024)
    (hgas : gas ≤ s.evm.gasLeft) :
    runR (livePushOf gas f) s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := f (chargedEvm s.evm gas) :: s.evm.stack
            gasLeft := s.evm.gasLeft - gas
            regularGasUsed := s.evm.regularGasUsed + gas
            pc := s.evm.pc + 1 } }) := by
  simp only [livePushOf, pcAdd]
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_stackPush _ _
    (by show s.evm.stack.length ≠ 1024; exact hlen)) ?_
  exact runR_modifyEvm _ _

theorem runR_livePushOf_overflow (gas : Uint)
    (f : EvmAsm.Stateless.SpecRef.Evm → U256) (s : Machine)
    (hlen : s.evm.stack.length = 1024)
    (hgas : gas ≤ s.evm.gasLeft) :
    runR (livePushOf gas f) s =
      .ok (.error .stackOverflow,
        { s with evm := { s.evm with
            gasLeft := s.evm.gasLeft - gas
            regularGasUsed := s.evm.regularGasUsed + gas } }) := by
  simp only [livePushOf]
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  exact runR_bind_err (runR_stackPush_overflow _ _
    (by show s.evm.stack.length = 1024; exact hlen))

/-- OOG fires at the leading charge, before the push (MM-5). -/
theorem runR_livePushOf_oog (gas : Uint)
    (f : EvmAsm.Stateless.SpecRef.Evm → U256) (s : Machine)
    (hgas : s.evm.gasLeft < gas) :
    runR (livePushOf gas f) s = .ok (.error .outOfGas, s) := by
  simp only [livePushOf]
  exact runR_bind_err (runR_charge_gas_oog _ _ hgas)

/-- The word a live-state pusher writes: its machine reader applied to the
post-charge state. -/
def livePushWord (gas : Uint) (f : EvmAsm.Stateless.SpecRef.Evm → U256)
    (e : EvmAsm.Stateless.SpecRef.Evm) : U256 :=
  f (chargedEvm e gas)

/-- The host state after a live-state pusher's stack write. Named so the
generic run shapes below never carry a multi-line structure-update literal
(which does not parse). -/
def livePushHost (hs : Evm.HostState) (l : List word)
    (frest : List (List word)) (top : StackTop) (w : word) : Evm.HostState :=
  { hs with stackFrames := writeListAt l top.toNat w :: frest }

/-! ## `Evm` side -/

/-- The dispatch equation shared by the `(top, g)`-returning live-state
pushers: the incoming pc and the memory slice pass through untouched. -/
def LivePushDispatch (op : ast)
    (body : Nat → StackTop → Nat → Evm.SailM (StackTop × Nat)) : Prop :=
  Evm.Functions.opcode_stack_effect op = pure (0, 1) ∧
  ∀ (pc_in : Nat) (top : StackTop) (mem : EvmMemorySlice) (g : Nat),
    Evm.Functions.execute_opcode op pc_in top mem g =
      body pc_in top g >>= fun p => pure (pc_in, p.1, mem, p.2)

open Evm.Functions in
theorem runS_execute_livePush_success (op : ast)
    (body : Nat → StackTop → Nat → Evm.SailM (StackTop × Nat))
    (hop : LivePushDispatch op body)
    (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs hs' : Evm.HostState) (ss : SeqState)
    (hbody : runS (body pc_in top g) hs ss =
      .ok ((top + BitVec.ofNat 64 1, g - G_base), hs') ss)
    (hlim : top.toNat + 1 ≤ 1024) :
    runS (Evm.Functions.execute op pc_in top mem g) hs ss =
      .ok ((pc_in, top + BitVec.ofNat 64 1, mem, g - G_base), hs') ss := by
  simp only [Evm.Functions.execute, hop.1]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 1 hs ss (by omega)
      (by have h : top.toNat - 0 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, hop.2]
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
theorem runS_execute_livePush_overflow (op : ast)
    (body : Nat → StackTop → Nat → Evm.SailM (StackTop × Nat))
    (hop : LivePushDispatch op body)
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
theorem runS_execute_livePush_oog (op : ast)
    (body : Nat → StackTop → Nat → Evm.SailM (StackTop × Nat))
    (hop : LivePushDispatch op body)
    (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss ss' : SeqState)
    (hbody : runS (body pc_in top g) hs ss = .ok ((top, GAS_ZERO), hs) ss')
    (hlim : top.toNat + 1 ≤ 1024) :
    runS (Evm.Functions.execute op pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs) ss' := by
  simp only [Evm.Functions.execute, hop.1]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 1 hs ss (by omega)
      (by have h : top.toNat - 0 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, hop.2]
  exact runS_bind_ok hbody (runS_pure _ _ _)

/-! ## The step equivalence, generically -/

open Evm.Functions in
/-- **The `(top, g)`-returning live-state pusher family, all reachable
outcomes.** Per-opcode content: the dispatch `rfl`s (`hop`), the body's
success and OOG run shapes at exactly SpecRef's pushed value (`hbody`,
`hbodyOog`), and that value's word bound (`hwf`). Double-fault states
(full stack ∧ OOG) use the MM-5 constructor. -/
theorem livePush_step_equiv (op : ast)
    (body : Nat → StackTop → Nat → Evm.SailM (StackTop × Nat))
    (hop : LivePushDispatch op body)
    (iOp : EvmM Unit) (specCost : Uint)
    (fSpec : EvmAsm.Stateless.SpecRef.Evm → U256)
    (hspec : iOp = livePushOf specCost fSpec)
    (hcost : (specCost : Nat) = 2)
    (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (hbody : ∀ (l : List word) (frest : List (List word)),
      hs.stackFrames = l :: frest → top.toNat + 1 < 2 ^ 64 →
      (G_base : Nat) ≤ g →
      runS (body pc_in top g) hs ss =
        .ok ((top + BitVec.ofNat 64 1, g - G_base),
          livePushHost hs l frest top (livePushWord specCost fSpec sRef.evm))
          ss)
    (hbodyOog : ∀ (prof : ExecutionProfile) (sp : state_gas_spill)
      (msg : Evm.Defs.Message),
      ss.regs.get? Register.k_execution_profile = some prof →
      ss.regs.get? Register.state_gas_spilled = some sp →
      ss.regs.get? Register.message = some msg →
      Amsterdam ≤ prof.1 → g < (G_base : Nat) →
      runS (body pc_in top g) hs ss =
        .ok ((top, GAS_ZERO), hs)
          { ss with regs := haltRegs ss msg .OutOfGas })
    (hwf : WordWf (livePushWord specCost fSpec sRef.evm)) :
    StepResultRel (BasePost mem) (runR iOp sRef)
      (runS (Evm.Functions.execute op pc_in top mem g) hs ss) := by
  subst hspec
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  have hgb : (G_base : Nat) = specCost := by rw [hcost]; rfl
  by_cases hg : sRef.evm.gasLeft < specCost
  · rw [runR_livePushOf_oog specCost fSpec sRef hg]
    by_cases hov : sRef.evm.stack.length = 1024
    · rw [runS_execute_livePush_overflow op body hop pc_in top g mem hs ss
        prof sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.haltedChargeFirst (Or.inr rfl)
        (haltRegs_frame_status ss msg .StackOverflow)
    · rw [runS_execute_livePush_oog op body hop pc_in top g mem hs ss _
        (hbodyOog prof sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
          (by rw [hgb, hlive]; exact hg)) (by omega)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
  · push Not at hg
    by_cases hov : sRef.evm.stack.length = 1024
    · rw [runR_livePushOf_overflow specCost fSpec sRef hov hg,
        runS_execute_livePush_overflow op body hop pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.halted ErrorRel.stackOverflow
        (haltRegs_frame_status ss msg .StackOverflow)
    · have hbound : top.toNat + 1 < 2 ^ 64 := by
        have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
        omega
      rw [runR_livePushOf_success specCost fSpec sRef hov hg,
        runS_execute_livePush_success op body hop pc_in top g mem hs _ ss
          (hbody l frest hframe hbound (by rw [hgb, hlive]; exact hg))
          (by omega)]
      have hadv : (top + BitVec.ofNat 64 1).toNat = top.toNat + 1 :=
        cursor_advance_toNat top hbound
      refine StepResultRel.success ?_
      refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
        ⟨msg, hmsg⟩⟩, by simp [hpc], rfl⟩
      · refine ⟨⟨writeListAt l top.toNat (livePushWord specCost fSpec sRef.evm),
            frest, rfl, ?_, ?_⟩, ?_, ?_, ?_⟩
        · rw [hadv, take_writeListAt l top.toNat _ (by omega), hpfx]
          simp [livePushWord]
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
      · exact ⟨by rw [hlive, hgb], hres, hsp⟩

end EvmSpecsVerify
