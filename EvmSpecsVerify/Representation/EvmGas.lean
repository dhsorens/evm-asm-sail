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

/-! ## Word-count embeddings and the copy charge -/

/-- The extraction's byte-count embedding is the identity below `2^256`
(`word_of_nat_byte_count`'s assert is unreachable for well-formed
lengths). -/
theorem runS_word_of_source_byte_count (v : Nat) (hs : HostState)
    (ss : SeqState) (h : v < 2 ^ 256) :
    runS (Evm.Functions.word_of_source_byte_count v) hs ss =
      .ok (v, hs) ss := by
  simp only [Evm.Functions.word_of_source_byte_count,
    Evm.Functions.word_of_nat_byte_count]
  rw [if_pos (by simp only [decide_eq_true_eq]; omega)]
  exact runS_pure _ _ _

/-- `memory_word_count_word` (no 257-bit intermediate) computes
`memory_word_count` on the word domain. -/
theorem memory_word_count_word_eq (n : Nat) (h : n < 2 ^ 256) :
    Evm.Functions.memory_word_count_word n
      = Evm.Functions.memory_word_count n := by
  have hq : n / 32 + 1 < 2 ^ 256 := by omega
  simp only [Evm.Functions.memory_word_count_word,
    Evm.Functions.memory_word_count, Evm.Functions.word_div_word,
    Evm.Functions.word_mod_word, Evm.Functions.word_add_word,
    Evm.Functions.u256, Evm.Functions.WORD_ZERO, Evm.Functions.WORD_ONE,
    Evm.Functions.word_from_bits,
    show (((32 : Nat) == 0) : Bool) = false from rfl, Bool.false_eq_true,
    if_false]
  rw [show (Sail.BitVec.toNatInt (0#256 : BitVec 256)).toNat = 0 from by
      decide,
    show (Sail.BitVec.toNatInt (1#256 : BitVec 256)).toNat = 1 from by
      decide,
    show (((2 : Int) ^ (256 : Int)).toNat) = 2 ^ 256 from by decide]
  by_cases h0 : (Nat.mod n 32 == 0) = true
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0]
    show (n / 32 + 1) % 2 ^ 256 = n / 32 + 1
    omega

/-- `Int` multiplication of embedded `Nat`s, back in `Nat` (the shape the
extraction's `*i` cost products take). -/
theorem intMul_toNat (a b : Nat) : ((a : Int) * (b : Int)).toNat = a * b := by
  rw [← Int.natCast_mul, Int.toNat_natCast]

/-- `charge_copy_gas`, success: the per-word charge
(`G_copy_word * memory_word_count size`) is affordable; zero words charge
nothing. -/
theorem runS_charge_copy_ok (g size : Nat) (hs : HostState) (ss : SeqState)
    (hsz : size < 2 ^ 256)
    (hgas : G_copy_word * Evm.Functions.memory_word_count size ≤ g) :
    runS (Evm.Functions.charge_copy_gas g size) hs ss =
      .ok ((true, g - G_copy_word * Evm.Functions.memory_word_count size),
        hs) ss := by
  simp only [Evm.Functions.G_copy_word] at hgas ⊢
  have hgas : (3 : Nat) * Evm.Functions.memory_word_count size ≤ g := hgas
  simp only [Evm.Functions.charge_copy_gas,
    Evm.Functions.charge_memory_word_gas, Evm.Functions.G_copy_word,
    Evm.Functions.GAS_CONSTANT_ZERO]
  refine runS_bind_ok (runS_charge_ok g 0 hs ss (Nat.zero_le g)) ?_
  rw [if_pos rfl]
  simp only [Nat.sub_zero, memory_word_count_word_eq size hsz,
    Evm.Functions.charge_word_scaled_gas, intMul_toNat]
  by_cases hwc : Evm.Functions.memory_word_count size = 0
  · rw [if_pos (by simp [hwc]), hwc, Nat.mul_zero, Nat.sub_zero]
    exact runS_pure _ _ _
  · rw [if_neg (by simp [hwc])]
    rw [if_pos (by simp only [decide_eq_true_eq]; omega)]
    rw [if_pos (by simp only [decide_eq_true_eq]; omega)]
    exact runS_charge_ok g _ hs ss hgas

/-- `charge_copy_gas`, out of gas (either the word count itself or the
exact per-word cost exceeds the remaining gas — both halt identically). -/
theorem runS_charge_copy_oog (g size : Nat) (hs : HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hsz : size < 2 ^ 256)
    (hgas : g < G_copy_word * Evm.Functions.memory_word_count size) :
    runS (Evm.Functions.charge_copy_gas g size) hs ss =
      .ok ((false, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg (.OutOfGas) } := by
  simp only [Evm.Functions.G_copy_word] at hgas
  have hgas : g < (3 : Nat) * Evm.Functions.memory_word_count size := hgas
  have hwc : Evm.Functions.memory_word_count size ≠ 0 := by
    intro hc
    rw [hc] at hgas
    omega
  simp only [Evm.Functions.charge_copy_gas,
    Evm.Functions.charge_memory_word_gas, Evm.Functions.G_copy_word,
    Evm.Functions.GAS_CONSTANT_ZERO]
  refine runS_bind_ok (runS_charge_ok g 0 hs ss (Nat.zero_le g)) ?_
  rw [if_pos rfl]
  simp only [Nat.sub_zero, memory_word_count_word_eq size hsz,
    Evm.Functions.charge_word_scaled_gas, intMul_toNat]
  rw [if_neg (by simp [hwc])]
  by_cases hunits : Evm.Functions.memory_word_count size ≤ g
  · rw [if_pos (by simp only [decide_eq_true_eq]; omega)]
    rw [if_neg (by simp only [decide_eq_true_eq]; omega)]
    refine runS_bind_ok
      (runS_exc_halt g .OutOfGas hs ss prof sp msg hprof hsp hmsg hfork) ?_
    exact runS_pure _ _ _
  · rw [if_neg (by simp only [decide_eq_true_eq]; omega)]
    refine runS_bind_ok
      (runS_exc_halt g .OutOfGas hs ss prof sp msg hprof hsp hmsg hfork) ?_
    exact runS_pure _ _ _


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

/-! ## The LOG charge

`charge_log_gas` is the only three-stage charge in the extraction: base,
then `G_logtopic * n`, then the per-byte payload cost through
`charge_word_scaled_gas`. SpecRef charges the three components in one
`charge_gas`, so a single SpecRef OOG state maps to whichever of the
three stages fails first — hence one lemma per stage.

The payload stage's two guards (`units ≤b g`, then `exact_cost ≤b g`)
exist only to avoid materializing an overflowing cost; both fall through
to the same `exc_halt OutOfGas`, and `8 * size ≥ size` makes the first
redundant, which is why `_oog_data` needs only the exact-cost bound. -/

theorem runS_charge_log_gas_ok (g n size : Nat) (hs : HostState)
    (ss : SeqState)
    (hgas : G_log + G_logtopic * n + G_logdata * size ≤ g) :
    runS (Evm.Functions.charge_log_gas g n size) hs ss =
      .ok ((true, g - G_log - G_logtopic * n - G_logdata * size), hs) ss := by
  simp only [Evm.Functions.G_log, Evm.Functions.G_logtopic,
    Evm.Functions.G_logdata] at hgas ⊢
  have hgas : (375 : Nat) + 375 * n + 8 * size ≤ g := hgas
  simp only [Evm.Functions.charge_log_gas, Evm.Functions.G_log,
    Evm.Functions.G_logtopic, Evm.Functions.G_logdata]
  refine runS_bind_ok (runS_charge_ok g 375 hs ss (by omega)) ?_
  rw [if_pos rfl]
  simp only [intMul_toNat]
  refine runS_bind_ok
    (runS_charge_ok (g - 375) (375 * n) hs ss (by omega)) ?_
  rw [if_pos rfl]
  simp only [Evm.Functions.charge_word_scaled_gas, intMul_toNat]
  by_cases hz : size = 0
  · subst hz
    rw [if_pos (by simp)]
    simp only [Nat.mul_zero, Nat.sub_zero]
    exact runS_pure _ _ _
  · rw [if_neg (by simp [hz])]
    rw [if_pos (by simp only [decide_eq_true_eq]; omega)]
    rw [if_pos (by simp only [decide_eq_true_eq]; omega)]
    exact runS_charge_ok _ _ hs ss (by omega)

theorem runS_charge_log_gas_oog_base (g n size : Nat) (hs : HostState)
    (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < G_log) :
    runS (Evm.Functions.charge_log_gas g n size) hs ss =
      .ok ((false, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg (.OutOfGas) } := by
  simp only [Evm.Functions.G_log] at hgas
  simp only [Evm.Functions.charge_log_gas, Evm.Functions.G_log]
  refine runS_bind_ok
    (runS_charge_oog g 375 hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  rw [if_neg (by simp)]
  exact runS_pure _ _ _

theorem runS_charge_log_gas_oog_topics (g n size : Nat) (hs : HostState)
    (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hbase : G_log ≤ g)
    (hgas : g - G_log < G_logtopic * n) :
    runS (Evm.Functions.charge_log_gas g n size) hs ss =
      .ok ((false, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg (.OutOfGas) } := by
  simp only [Evm.Functions.G_log, Evm.Functions.G_logtopic] at hbase hgas
  simp only [Evm.Functions.charge_log_gas, Evm.Functions.G_log,
    Evm.Functions.G_logtopic]
  refine runS_bind_ok (runS_charge_ok g 375 hs ss hbase) ?_
  rw [if_pos rfl]
  simp only [intMul_toNat]
  refine runS_bind_ok
    (runS_charge_oog (g - 375) (375 * n) hs ss prof sp msg hprof hsp hmsg
      hfork hgas) ?_
  rw [if_neg (by simp)]
  exact runS_pure _ _ _

theorem runS_charge_log_gas_oog_data (g n size : Nat) (hs : HostState)
    (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hbase : G_log + G_logtopic * n ≤ g)
    (hgas : g - G_log - G_logtopic * n < G_logdata * size) :
    runS (Evm.Functions.charge_log_gas g n size) hs ss =
      .ok ((false, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg (.OutOfGas) } := by
  simp only [Evm.Functions.G_log, Evm.Functions.G_logtopic,
    Evm.Functions.G_logdata] at hbase hgas
  have hbaseN : (375 : Nat) + 375 * n ≤ g := hbase
  have hgasN : g - 375 - 375 * n < 8 * size := hgas
  have hz : size ≠ 0 := by
    intro hc
    rw [hc] at hgasN
    omega
  simp only [Evm.Functions.charge_log_gas, Evm.Functions.G_log,
    Evm.Functions.G_logtopic, Evm.Functions.G_logdata]
  have hb1 : (375 : Nat) ≤ g := by omega
  have hb2 : (375 : Nat) * n ≤ g - 375 := by omega
  refine runS_bind_ok (runS_charge_ok g 375 hs ss hb1) ?_
  rw [if_pos rfl]
  simp only [intMul_toNat]
  refine runS_bind_ok
    (runS_charge_ok (g - 375) (375 * n) hs ss hb2) ?_
  rw [if_pos rfl]
  simp only [Evm.Functions.charge_word_scaled_gas, intMul_toNat]
  rw [if_neg (by simp [hz])]
  by_cases hunits : size ≤ g - 375 - 375 * n
  · rw [if_pos (by simp only [decide_eq_true_eq]; omega)]
    rw [if_neg (by simp only [decide_eq_true_eq]; omega)]
    refine runS_bind_ok
      (runS_exc_halt _ .OutOfGas hs ss prof sp msg hprof hsp hmsg hfork) ?_
    exact runS_pure _ _ _
  · rw [if_neg (by simp only [decide_eq_true_eq]; omega)]
    refine runS_bind_ok
      (runS_exc_halt _ .OutOfGas hs ss prof sp msg hprof hsp hmsg hfork) ?_
    exact runS_pure _ _ _

end EvmSpecsVerify
