import Evm
import EvmSpecsVerify.Representation.EvmMonad

/-!
# The `Evm` gas meter and exceptional halt, run

`charge` (Gas.lean:536) is pure on success; on failure it funnels through
`exc_halt` (Machine.lean:152), which refills the frame's state gas
(`refill_frame_state_gas`, Machine.lean:127 — reads the execution profile,
the spilled counter, and the message register; Amsterdam-gated), sets
`frame_status := Exceptional k`, and returns zero gas. `validate_stack`
(Machine.lean:168) is the Yellow-Paper stack guard in front of every
instruction.

Register reads are supplied as `ss.regs.get? r = some v` hypotheses; the
execution profile is destructured in the statements so the generated
13-Sigma match reduces.
-/

namespace EvmSpecsVerify

open Evm (HostState)
open Evm.Defs
open Evm.Functions

/-- The register file after an exceptional halt (Amsterdam profile): the
state-gas reservoir restored from the message, the spill zeroed, and the
frame status set. `exc_halt`'s complete register effect. -/
def haltRegs (ss : SeqState) (msg : Message) (k : ExceptionKind) :=
  ((ss.regs.insert Register.state_gas_remaining msg.state_gas_reservoir).insert
    Register.state_gas_spilled STATE_GAS_SPILL_ZERO).insert
    Register.frame_status (FrameStatus.Exceptional k)

/-- The register file after a state-gas refill alone (`refill_frame_state_gas`
under Amsterdam): reservoir restored, spill zeroed, status untouched. -/
def refillRegs (ss : SeqState) (msg : Message) :=
  (ss.regs.insert Register.state_gas_remaining msg.state_gas_reservoir).insert
    Register.state_gas_spilled STATE_GAS_SPILL_ZERO

/-- The halt register file reports the exceptional status. -/
theorem haltRegs_frame_status (ss : SeqState) (msg : Message)
    (k : ExceptionKind) :
    (haltRegs ss msg k).get? Register.frame_status =
      some (FrameStatus.Exceptional k) := by
  simp [haltRegs]

/-- Successful charge: pure, no state touched. -/
theorem runS_charge_ok (g amount : Nat) (hs : HostState) (ss : SeqState)
    (h : amount ≤ g) :
    runS (Evm.Functions.charge g amount) hs ss = .ok ((true, g - amount), hs) ss := by
  simp [Evm.Functions.charge, h]

/-- `refill_frame_state_gas` under an Amsterdam-or-later profile: returns
`g + spilled`, restores the reservoir from the message, zeroes the spill. -/
theorem runS_refill (g : Nat) (hs : HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1) :
    runS (Evm.Functions.refill_frame_state_gas g) hs ss =
      .ok (g + sp, hs)
        { ss with regs := refillRegs ss msg } := by
  obtain ⟨fork, t, mx, dn, cl, il, ptl, prl, tbl, rd, bl, ttl, trl, epf⟩ := prof
  simp only at hfork
  simp only [Evm.Functions.refill_frame_state_gas, runS_bind,
    runS_readReg _ _ _ _ hprof]
  simp only [ProtocolProfileFields.fork, decide_eq_true_eq]
  rw [if_pos (by simpa using hfork)]
  simp only [runS_bind, runS_readReg _ _ _ _ hsp, runS_readReg _ _ _ _ hmsg,
    runS_pure, runS_writeReg, Evm.Functions.conserved_gas_add]
  rfl

/-- `exc_halt` under an Amsterdam-or-later profile: zero gas out, status
`Exceptional k`, reservoir restored, spill zeroed. -/
theorem runS_exc_halt (g : Nat) (k : ExceptionKind) (hs : HostState)
    (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1) :
    runS (Evm.Functions.exc_halt g k) hs ss =
      .ok (GAS_ZERO, hs)
        { ss with regs := haltRegs ss msg (k) } := by
  simp only [Evm.Functions.exc_halt, runS_bind,
    runS_refill g hs ss prof sp msg hprof hsp hmsg hfork, runS_writeReg,
    runS_pure]
  rfl

/-- Failed charge: out-of-gas exceptional halt. -/
theorem runS_charge_oog (g amount : Nat) (hs : HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (h : g < amount) :
    runS (Evm.Functions.charge g amount) hs ss =
      .ok ((false, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg (.OutOfGas) } := by
  simp only [Evm.Functions.charge]
  rw [if_neg (by simpa using Nat.not_le.mpr h)]
  simp only [runS_bind,
    runS_exc_halt g .OutOfGas hs ss prof sp msg hprof hsp hmsg hfork, runS_pure]

/-! ## The stack guard -/

/-- `validate_stack`, success: enough operands, no overflow, gas untouched. -/
theorem runS_validate_stack_ok (g : Nat) (top : StackTop) (inputs outputs : Nat)
    (hs : HostState) (ss : SeqState)
    (hin : inputs ≤ top.toNat)
    (hout : top.toNat - inputs + outputs ≤ STACK_LIMIT) :
    runS (Evm.Functions.validate_stack g top inputs outputs) hs ss =
      .ok ((true, g), hs) ss := by
  simp only [Evm.Functions.validate_stack, Evm.Functions.stack_height,
    Evm.Functions.stack_top_height, runS_bind, runS_pure]
  rw [if_neg (by simpa using Nat.not_lt.mpr hin)]
  rw [if_neg (by simpa using Nat.not_lt.mpr hout)]
  rfl

/-- `validate_stack`, underflow. -/
theorem runS_validate_stack_underflow (g : Nat) (top : StackTop)
    (inputs outputs : Nat) (hs : HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hin : top.toNat < inputs) :
    runS (Evm.Functions.validate_stack g top inputs outputs) hs ss =
      .ok ((false, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg (.StackUnderflow) } := by
  simp only [Evm.Functions.validate_stack, Evm.Functions.stack_height,
    Evm.Functions.stack_top_height, runS_bind, runS_pure]
  rw [if_pos (by simpa using hin)]
  simp only [runS_bind,
    runS_exc_halt g .StackUnderflow hs ss prof sp msg hprof hsp hmsg hfork,
    runS_pure]

/-- `validate_stack`, overflow. -/
theorem runS_validate_stack_overflow (g : Nat) (top : StackTop)
    (inputs outputs : Nat) (hs : HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hin : inputs ≤ top.toNat)
    (hout : STACK_LIMIT < top.toNat - inputs + outputs) :
    runS (Evm.Functions.validate_stack g top inputs outputs) hs ss =
      .ok ((false, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg (.StackOverflow) } := by
  simp only [Evm.Functions.validate_stack, Evm.Functions.stack_height,
    Evm.Functions.stack_top_height, runS_bind, runS_pure]
  rw [if_neg (by simpa using Nat.not_lt.mpr hin)]
  rw [if_pos (by simpa using hout)]
  simp only [runS_bind,
    runS_exc_halt g .StackOverflow hs ss prof sp msg hprof hsp hmsg hfork,
    runS_pure]

end EvmSpecsVerify
