import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# POP

First stack-manipulation opcode: `iPop` is `pop → charge → pc+1` (discarding
the popped word); `execute_pop` is `charge → pop`, cursor retreat only — no
write, so the host state passes through untouched. The success Post is
[`AluPost`](../Relations/Alu.lean) (same observation footprint: stack, gas,
pc, memory pass-through). Reachable outcomes: success / stack underflow /
out-of-gas (overflow unreachable: the height decreases).

The two sides order the pop and the charge differently; the difference is
unobservable — on OOG both halt (post-stack unobservable, mismatch ledger
MM-1), on success both end at the same stack.
-/

open private pcAdd from EvmAsm.Stateless.SpecRef.InstructionsCore

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## SpecRef run shapes -/

theorem runR_iPop_success (s : Machine) (x : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: rest)
    (hgas : GasCosts.OPCODE_POP ≤ s.evm.gasLeft) :
    runR iPop s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := rest
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_POP
            regularGasUsed := s.evm.regularGasUsed + GasCosts.OPCODE_POP
            pc := s.evm.pc + 1 } }) := by
  simp only [iPop, pcAdd]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  exact runR_modifyEvm _ _

theorem runR_iPop_underflow (s : Machine) (hstack : s.evm.stack = []) :
    runR iPop s = .ok (.error .stackUnderflow, s) := by
  simp only [iPop]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_iPop_oog (s : Machine) (x : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: rest)
    (hgas : s.evm.gasLeft < GasCosts.OPCODE_POP) :
    runR iPop s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [iPop]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _ (by simpa using hgas))

/-! ## `Evm` run shapes (at the `execute` dispatch level) -/

open Evm.Functions in
/-- The dispatch equation for POP (analogue of `TernopDispatch`). -/
theorem pop_dispatch (pc_in : Nat) (top : StackTop) (mem : EvmMemorySlice)
    (g : Nat) :
    Evm.Functions.execute_opcode (.POP ()) pc_in top mem g =
      Evm.Functions.execute_pop top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
theorem runS_pop_body_ok (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hgas : G_base ≤ g) :
    runS (Evm.Functions.execute_pop top g) hs ss =
      .ok ((top - BitVec.ofNat 64 1, g - G_base), hs) ss := by
  simp only [Evm.Functions.execute_pop]
  refine runS_bind_ok (runS_charge_ok g G_base hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_pop top hs ss l frest x rest hframe hpfx htop) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_pop_body_oog (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < G_base) :
    runS (Evm.Functions.execute_pop top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_pop]
  refine runS_bind_ok
    (runS_charge_oog g G_base hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_pop_success (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hgas : G_base ≤ g) :
    runS (Evm.Functions.execute (.POP ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1, mem, g - G_base), hs) ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.POP ()) = pure (1, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 0 hs ss (by simp at htop; omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, pop_dispatch]
  refine runS_bind_ok
    (runS_pop_body_ok top g hs ss l frest x rest hframe hpfx htop hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_pop_underflow (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 1) :
    runS (Evm.Functions.execute (.POP ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.POP ()) = pure (1, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 1 0 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_pop_oog (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hin : 1 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (hgas : g < G_base) :
    runS (Evm.Functions.execute (.POP ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.POP ()) = pure (1, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 0 hs ss hin
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, pop_dispatch]
  refine runS_bind_ok
    (runS_pop_body_oog top g hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **POP, all reachable outcomes.** -/
theorem pop_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iPop sRef)
      (runS (Evm.Functions.execute (.POP ()) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_iPop_underflow sRef hS,
      runS_execute_pop_underflow pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | x :: rest =>
    rw [hS] at hpfx htop hlim hwfS
    have hin1 : 1 ≤ top.toNat := by simp at htop; omega
    have hlim' : top.toNat ≤ 1024 := by simp at htop ⊢; simp at hlim; omega
    by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_POP
    · rw [runR_iPop_oog sRef x rest hS hg,
        runS_execute_pop_oog pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hin1 hlim'
          (by rw [hlive]; exact hg)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
    · push Not at hg
      rw [runR_iPop_success sRef x rest hS hg,
        runS_execute_pop_success pc_in top g mem hs ss l frest x rest hframe
          hpfx htop hlim' (by rw [hlive]; exact hg)]
      have hret : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
        cursor_retreat_toNat top (by omega)
      refine StepResultRel.success ?_
      refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
        ⟨msg, hmsg⟩⟩, by simp [hpc], rfl⟩
      · refine ⟨⟨l, frest, hframe, ?_, ?_⟩, ?_, ?_, ?_⟩
        · rw [hret]
          exact take_shrink l rest x (top.toNat - 1)
            (by rw [show top.toNat - 1 + 1 = top.toNat from by
              simp at htop; omega]; exact hpfx)
            (by simp at htop; omega)
        · rw [hret]; omega
        · rw [hret]; simp at htop ⊢; omega
        · simp at hlim ⊢; omega
        · intro w hw
          exact hwfS w (by simp [hw])
      · exact ⟨by simp [hlive, Evm.Functions.G_base, GasCosts.OPCODE_POP],
          hres, hsp⟩

end EvmSpecsVerify
