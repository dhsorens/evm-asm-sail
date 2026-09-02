import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# JUMPDEST

The no-op marker: SpecRef's `iJumpdest` charges `OPCODE_JUMPDEST` and
advances the pc; the extraction's `execute_jumpdest` charges `G_jumpdest`
and returns the remaining gas, discarding `charge`'s success flag — safe
because the charge is the handler's only effect, and `charge` already
performs the exceptional halt itself on failure.

Reachable outcomes: success and out-of-gas. Stack faults are impossible for
0-in/0-out (`validate_stack 0 0` passes under the 1024 invariant), so this
is the same outcome set as [`STOP`](Stop.lean) plus the gas charge.

Gas (mismatch ledger MM-2): `GasCosts.OPCODE_JUMPDEST = 1 = G_jumpdest`.
-/

open private pcAdd from EvmAsm.Stateless.SpecRef.InstructionsCore

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## SpecRef run shapes -/

theorem runR_iJumpdest_success (s : Machine)
    (hgas : GasCosts.OPCODE_JUMPDEST ≤ s.evm.gasLeft) :
    runR iJumpdest s =
      .ok (.ok (),
        { s with evm := { s.evm with
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_JUMPDEST
            regularGasUsed := s.evm.regularGasUsed + GasCosts.OPCODE_JUMPDEST
            pc := s.evm.pc + 1 } }) := by
  simp only [iJumpdest, pcAdd]
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  exact runR_modifyEvm _ _

theorem runR_iJumpdest_oog (s : Machine)
    (hgas : s.evm.gasLeft < GasCosts.OPCODE_JUMPDEST) :
    runR iJumpdest s = .ok (.error .outOfGas, s) := by
  simp only [iJumpdest]
  exact runR_bind_err (runR_charge_gas_oog _ _ (by simpa using hgas))

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for JUMPDEST: the pc, cursor and memory pass
through; only the gas is threaded. -/
theorem jumpdest_dispatch (pc_in : Nat) (top : StackTop) (mem : EvmMemorySlice)
    (g : Nat) :
    Evm.Functions.execute_opcode (.JUMPDEST ()) pc_in top mem g =
      Evm.Functions.execute_jumpdest g >>= fun g1 =>
        pure (pc_in, top, mem, g1) := rfl

open Evm.Functions in
theorem runS_jumpdest_body_ok (g : Nat) (hs : Evm.HostState) (ss : SeqState)
    (hgas : G_jumpdest ≤ g) :
    runS (Evm.Functions.execute_jumpdest g) hs ss =
      .ok (g - G_jumpdest, hs) ss := by
  simp only [Evm.Functions.execute_jumpdest]
  refine runS_bind_ok (runS_charge_ok g G_jumpdest hs ss hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_jumpdest_body_oog (g : Nat) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < G_jumpdest) :
    runS (Evm.Functions.execute_jumpdest g) hs ss =
      .ok (GAS_ZERO, hs) { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_jumpdest]
  refine runS_bind_ok
    (runS_charge_oog g G_jumpdest hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_jumpdest_success (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (hlim : top.toNat ≤ 1024) (hgas : G_jumpdest ≤ g) :
    runS (Evm.Functions.execute (.JUMPDEST ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, g - G_jumpdest), hs) ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.JUMPDEST ()) = pure (0, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 0 hs ss (by omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, jumpdest_dispatch]
  refine runS_bind_ok (runS_jumpdest_body_ok g hs ss hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_jumpdest_oog (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hlim : top.toNat ≤ 1024) (hgas : g < G_jumpdest) :
    runS (Evm.Functions.execute (.JUMPDEST ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.JUMPDEST ()) = pure (0, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 0 hs ss (by omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, jumpdest_dispatch]
  refine runS_bind_ok
    (runS_jumpdest_body_oog g hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **JUMPDEST, all reachable outcomes**: success and out-of-gas. Stack
faults are unreachable for 0-in/0-out. -/
theorem jumpdest_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (BasePost mem) (runR iJumpdest sRef)
      (runS (Evm.Functions.execute (.JUMPDEST ()) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨hframe, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  have hlim' : top.toNat ≤ 1024 := by omega
  by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_JUMPDEST
  · rw [runR_iJumpdest_oog sRef hg,
      runS_execute_jumpdest_oog pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hlim'
        (by rw [hlive]; exact hg)]
    exact StepResultRel.halted ErrorRel.outOfGas
      (haltRegs_frame_status ss msg .OutOfGas)
  · push Not at hg
    rw [runR_iJumpdest_success sRef hg,
      runS_execute_jumpdest_success pc_in top g mem hs ss hlim'
        (by rw [hlive]; exact hg)]
    refine StepResultRel.success ?_
    exact ⟨⟨⟨hframe, htop, hlim, hwfS⟩,
      ⟨by simp [hlive, Evm.Functions.G_jumpdest, GasCosts.OPCODE_JUMPDEST],
        hres, hsp⟩,
      ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩,
      by simp [hpc], rfl⟩

end EvmSpecsVerify
