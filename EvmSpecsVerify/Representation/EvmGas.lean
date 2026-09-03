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

/-! ## The static-context guard -/

open Evm.Functions in
/-- The static-context guard halts with `WriteProtection`, carrying the
frame's full gas into `exc_halt`. It is the first statement of every
write handler on this side, which is where MM-11 (LOG) and MM-14
(TSTORE/SSTORE/SELFDESTRUCT) come from. -/
theorem runS_guard_static_halt (g : Nat) (hs : Evm.HostState)
    (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hstatic : msg.is_static = true) :
    runS (Evm.Functions.guard_static g) hs ss =
      .ok ((true, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .WriteProtection } := by
  simp only [Evm.Functions.guard_static, runS_bind,
    runS_readReg _ _ _ _ hmsg]
  rw [if_pos (by simpa using hstatic)]
  simp only [runS_bind,
    runS_exc_halt g .WriteProtection hs ss prof sp msg hprof hsp hmsg hfork,
    runS_pure]

open Evm.Functions in
theorem runS_guard_static_ok (g : Nat) (hs : Evm.HostState) (ss : SeqState)
    (msg : Evm.Defs.Message)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hstatic : msg.is_static = false) :
    runS (Evm.Functions.guard_static g) hs ss = .ok ((false, g), hs) ss := by
  simp only [Evm.Functions.guard_static, runS_bind,
    runS_readReg _ _ _ _ hmsg]
  rw [if_neg (by simpa using hstatic)]
  exact runS_pure _ _ _

/-! ## Two-dimensional gas (Amsterdam)

The state-gas half of the schedule, first used by SSTORE.
`check_execution_gas` is a sentry (reads the live gas, spends nothing);
`debit_state_gas` draws on the frame's reservoir and spills the remainder
into execution gas; `credit_state_gas_refund` is its LIFO inverse.
`record_refund` accumulates the signed EIP-2200 refund in the frame
register. -/

/-- The sentry passes: nothing is spent and nothing moves. -/
theorem runS_check_execution_gas_ok (g amount : Nat) (hs : Evm.HostState)
    (ss : SeqState) (h : amount ≤ g) :
    runS (Evm.Functions.check_execution_gas g amount) hs ss =
      .ok ((true, g), hs) ss := by
  simp only [Evm.Functions.check_execution_gas]
  rw [if_neg (by simpa using Nat.not_lt.mpr h)]
  exact runS_pure _ _ _

/-- The sentry fails: an out-of-gas halt on the carried gas. -/
theorem runS_check_execution_gas_oog (g amount : Nat) (hs : Evm.HostState)
    (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (h : g < amount) :
    runS (Evm.Functions.check_execution_gas g amount) hs ss =
      .ok ((false, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.check_execution_gas]
  rw [if_pos (by simpa using h)]
  simp only [runS_bind,
    runS_exc_halt g .OutOfGas hs ss prof sp msg hprof hsp hmsg hfork,
    runS_pure]

/-! ### `debit_state_gas` -/

/-- A zero charge is a no-op — not even a register read. -/
theorem runS_debit_state_gas_zero (g : Nat) (hs : Evm.HostState)
    (ss : SeqState) :
    runS (Evm.Functions.debit_state_gas g 0) hs ss =
      .ok ((true, g), hs) ss := by
  simp only [Evm.Functions.debit_state_gas]
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

/-- The reservoir covers the charge: execution gas is untouched. -/
theorem runS_debit_state_gas_reservoir (g amount : Nat) (hs : Evm.HostState)
    (ss : SeqState) (sres : Nat)
    (hres : ss.regs.get? Register.state_gas_remaining = some sres)
    (hnz : amount ≠ 0) (h : amount ≤ sres) :
    runS (Evm.Functions.debit_state_gas g amount) hs ss =
      .ok ((true, g), hs)
        { ss with
            regs := ss.regs.insert Register.state_gas_remaining
              (sres - amount) } := by
  simp only [Evm.Functions.debit_state_gas]
  rw [if_neg (by simpa using hnz)]
  refine runS_bind_ok (runS_readReg _ _ _ _ hres) ?_
  rw [if_pos (by simpa using h)]
  refine runS_bind_ok (runS_writeReg _ _ _ _) ?_
  exact runS_pure _ _ _

/-- The reservoir runs out: the remainder is spilled out of execution gas
and recorded. `hroom` is the EIP-7825 transaction cap — the extraction
hard-aborts (`state_gas_spill_add` → `fatal_error ExecutionInvalid`) above
`2^24`, which is exactly `TX_MAX_GAS_LIMIT`, so no in-budget frame can
reach it. -/
theorem runS_debit_state_gas_spill (g amount : Nat) (hs : Evm.HostState)
    (ss : SeqState) (sres sp : Nat)
    (hres : ss.regs.get? Register.state_gas_remaining = some sres)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hnz : amount ≠ 0) (h1 : sres < amount) (h2 : amount - sres ≤ g)
    (hroom : sp + (amount - sres) ≤ 2 ^ 24) :
    runS (Evm.Functions.debit_state_gas g amount) hs ss =
      .ok ((true, g - (amount - sres)), hs)
        { ss with
            regs :=
              (ss.regs.insert Register.state_gas_remaining GAS_ZERO).insert
                Register.state_gas_spilled (sp + (amount - sres)) } := by
  simp only [Evm.Functions.debit_state_gas]
  rw [if_neg (by simpa using hnz)]
  refine runS_bind_ok (runS_readReg _ _ _ _ hres) ?_
  rw [if_neg (by simpa using Nat.not_le.mpr h1), if_pos (by simpa using h2)]
  refine runS_bind_ok (runS_readReg _ _ _ _ hsp) ?_
  refine runS_bind_ok (runS_writeReg _ _ _ _) ?_
  have hadd : runS (Evm.Functions.state_gas_spill_add sp (amount - sres)) hs
      { ss with
          regs := ss.regs.insert Register.state_gas_remaining GAS_ZERO } =
      .ok (sp + (amount - sres), hs)
        { ss with
            regs := ss.regs.insert Register.state_gas_remaining GAS_ZERO } := by
    simp only [Evm.Functions.state_gas_spill_add,
      Evm.Functions.state_gas_spill_room]
    rw [if_pos (by simpa using (by omega : amount - sres ≤ 2 ^ 24 - sp))]
    exact runS_pure _ _ _
  refine runS_bind_ok hadd ?_
  refine runS_bind_ok (runS_writeReg _ _ _ _) ?_
  exact runS_pure _ _ _

/-- Neither the reservoir nor the execution gas can cover the charge:
`debit` reports failure without touching any register. -/
theorem runS_debit_state_gas_short (g amount : Nat) (hs : Evm.HostState)
    (ss : SeqState) (sres : Nat)
    (hres : ss.regs.get? Register.state_gas_remaining = some sres)
    (hnz : amount ≠ 0) (h1 : sres < amount) (h2 : g < amount - sres) :
    runS (Evm.Functions.debit_state_gas g amount) hs ss =
      .ok ((false, g), hs) ss := by
  simp only [Evm.Functions.debit_state_gas]
  rw [if_neg (by simpa using hnz)]
  refine runS_bind_ok (runS_readReg _ _ _ _ hres) ?_
  rw [if_neg (by simpa using Nat.not_le.mpr h1),
    if_neg (by simpa using Nat.not_le.mpr h2)]
  exact runS_pure _ _ _

/-! ### `charge_state_gas` -/

theorem runS_charge_state_gas_zero (g : Nat) (hs : Evm.HostState)
    (ss : SeqState) :
    runS (Evm.Functions.charge_state_gas g 0) hs ss =
      .ok ((true, g), hs) ss := by
  simp only [Evm.Functions.charge_state_gas]
  refine runS_bind_ok (runS_debit_state_gas_zero g hs ss) ?_
  rw [if_pos rfl]
  exact runS_pure _ _ _

theorem runS_charge_state_gas_reservoir (g amount : Nat) (hs : Evm.HostState)
    (ss : SeqState) (sres : Nat)
    (hres : ss.regs.get? Register.state_gas_remaining = some sres)
    (hnz : amount ≠ 0) (h : amount ≤ sres) :
    runS (Evm.Functions.charge_state_gas g amount) hs ss =
      .ok ((true, g), hs)
        { ss with
            regs := ss.regs.insert Register.state_gas_remaining
              (sres - amount) } := by
  simp only [Evm.Functions.charge_state_gas]
  refine runS_bind_ok
    (runS_debit_state_gas_reservoir g amount hs ss sres hres hnz h) ?_
  rw [if_pos rfl]
  exact runS_pure _ _ _

theorem runS_charge_state_gas_spill (g amount : Nat) (hs : Evm.HostState)
    (ss : SeqState) (sres sp : Nat)
    (hres : ss.regs.get? Register.state_gas_remaining = some sres)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hnz : amount ≠ 0) (h1 : sres < amount) (h2 : amount - sres ≤ g)
    (hroom : sp + (amount - sres) ≤ 2 ^ 24) :
    runS (Evm.Functions.charge_state_gas g amount) hs ss =
      .ok ((true, g - (amount - sres)), hs)
        { ss with
            regs :=
              (ss.regs.insert Register.state_gas_remaining GAS_ZERO).insert
                Register.state_gas_spilled (sp + (amount - sres)) } := by
  simp only [Evm.Functions.charge_state_gas]
  refine runS_bind_ok
    (runS_debit_state_gas_spill g amount hs ss sres sp hres hsp hnz h1 h2
      hroom) ?_
  rw [if_pos rfl]
  exact runS_pure _ _ _

/-- The charge cannot be met: an out-of-gas halt on the undebited gas. -/
theorem runS_charge_state_gas_oog (g amount : Nat) (hs : Evm.HostState)
    (ss : SeqState) (sres : Nat)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hres : ss.regs.get? Register.state_gas_remaining = some sres)
    (hfork : Amsterdam ≤ prof.1)
    (hnz : amount ≠ 0) (h1 : sres < amount) (h2 : g < amount - sres) :
    runS (Evm.Functions.charge_state_gas g amount) hs ss =
      .ok ((false, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.charge_state_gas]
  refine runS_bind_ok
    (runS_debit_state_gas_short g amount hs ss sres hres hnz h1 h2) ?_
  rw [if_neg (by simp)]
  simp only [runS_bind,
    runS_exc_halt g .OutOfGas hs ss prof sp msg hprof hsp hmsg hfork,
    runS_pure]

/-! ### `credit_state_gas_refund` -/

theorem runS_credit_state_gas_refund_zero (g : Nat) (hs : Evm.HostState)
    (ss : SeqState) (sp : Nat)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp) :
    runS (Evm.Functions.credit_state_gas_refund g 0) hs ss =
      .ok (g, hs) ss := by
  simp only [Evm.Functions.credit_state_gas_refund]
  refine runS_bind_ok (runS_readReg _ _ _ _ hsp) ?_
  rw [if_pos (by simp), if_neg (by simp)]
  exact runS_pure _ _ _

/-- The credit fits inside the recorded spill: it all goes back to
execution gas. -/
theorem runS_credit_state_gas_refund_spill (g amount : Nat)
    (hs : Evm.HostState) (ss : SeqState) (sp : Nat)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hnz : amount ≠ 0) (h : amount ≤ sp) :
    runS (Evm.Functions.credit_state_gas_refund g amount) hs ss =
      .ok (g + amount, hs)
        { ss with
            regs := ss.regs.insert Register.state_gas_spilled
              (sp - amount) } := by
  simp only [Evm.Functions.credit_state_gas_refund]
  refine runS_bind_ok (runS_readReg _ _ _ _ hsp) ?_
  rw [if_pos (by simpa using h), if_pos (by simpa using hnz)]
  exact runS_bind_ok (runS_writeReg _ _ _ _) (runS_pure _ _ _)

/-- The credit exceeds the recorded spill: the spill is returned to
execution gas and the excess to the reservoir. -/
theorem runS_credit_state_gas_refund_mixed (g amount : Nat)
    (hs : Evm.HostState) (ss : SeqState) (sres sp : Nat)
    (hres : ss.regs.get? Register.state_gas_remaining = some sres)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hnz : sp ≠ 0) (h : sp < amount) :
    runS (Evm.Functions.credit_state_gas_refund g amount) hs ss =
      .ok (g + sp, hs)
        { ss with
            regs :=
              (ss.regs.insert Register.state_gas_spilled
                STATE_GAS_SPILL_ZERO).insert Register.state_gas_remaining
                  (sres + (amount - sp)) } := by
  simp only [Evm.Functions.credit_state_gas_refund]
  refine runS_bind_ok (runS_readReg _ _ _ _ hsp) ?_
  rw [if_neg (by simpa using Nat.not_le.mpr h), if_pos (by simpa using hnz)]
  have hcred : runS
      (do
        Evm.writeReg Register.state_gas_spilled STATE_GAS_SPILL_ZERO
        pure (Evm.Functions.conserved_gas_add g sp)) hs ss =
      .ok (g + sp, hs)
        { ss with
            regs := ss.regs.insert Register.state_gas_spilled
              STATE_GAS_SPILL_ZERO } :=
    runS_bind_ok (runS_writeReg _ _ _ _) (runS_pure _ _ _)
  refine runS_bind_ok hcred ?_
  refine runS_bind_ok
    (runS_readReg _ _ _ _
      (by simp only [Std.ExtDHashMap.get?_insert]; simpa using hres)) ?_
  refine runS_bind_ok (runS_writeReg _ _ _ _) ?_
  exact runS_pure _ _ _

/-- Nothing was spilled: the whole credit goes to the reservoir. -/
theorem runS_credit_state_gas_refund_reservoir (g amount : Nat)
    (hs : Evm.HostState) (ss : SeqState) (sres : Nat)
    (hres : ss.regs.get? Register.state_gas_remaining = some sres)
    (hsp : ss.regs.get? Register.state_gas_spilled = some 0)
    (hnz : amount ≠ 0) :
    runS (Evm.Functions.credit_state_gas_refund g amount) hs ss =
      .ok (g, hs)
        { ss with
            regs := ss.regs.insert Register.state_gas_remaining
              (sres + amount) } := by
  simp only [Evm.Functions.credit_state_gas_refund]
  refine runS_bind_ok (runS_readReg _ _ _ _ hsp) ?_
  rw [if_neg (by simpa using Nat.not_le.mpr (by omega : 0 < amount)),
    if_neg (by simp)]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok (runS_readReg _ _ _ _ hres) ?_
  refine runS_bind_ok (runS_writeReg _ _ _ _) ?_
  exact runS_pure _ _ _

/-- Reading a register other than the one just written. -/
theorem regs_get?_insert_ne {r k : Register}
    (m : Std.ExtDHashMap Register Evm.Defs.RegisterType)
    (v : Evm.Defs.RegisterType k) (h : r ≠ k) :
    (m.insert k v).get? r = m.get? r := by
  simp only [Std.ExtDHashMap.get?_insert]
  refine dif_neg (fun hh => h ?_)
  have : k = r := by simpa using hh
  exact this.symm

/-! ### Closed forms

The three credit branches and the three state-charge branches each
collapse to one `min`-shaped formula, which is what lets a step theorem
chain through them without case analysis. -/

/-- The credit, in closed form: `min amount spilled` back to execution
gas, the rest to the reservoir. -/
theorem runS_credit_closed (g amount : Nat) (hs : Evm.HostState)
    (ss : SeqState) (res sp : Nat)
    (hres : ss.regs.get? Register.state_gas_remaining = some res)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp) :
    ∃ ss', runS (Evm.Functions.credit_state_gas_refund g amount) hs ss
        = .ok (g + min amount sp, hs) ss'
      ∧ ss'.regs.get? Register.state_gas_remaining
          = some (res + (amount - min amount sp))
      ∧ ss'.regs.get? Register.state_gas_spilled = some (sp - min amount sp)
      ∧ ∀ (r : Register), r ≠ Register.state_gas_remaining →
          r ≠ Register.state_gas_spilled →
          ss'.regs.get? r = ss.regs.get? r := by
  by_cases hz : amount = 0
  · subst hz
    simp only [Nat.zero_min, Nat.add_zero, Nat.sub_zero]
    exact ⟨ss, runS_credit_state_gas_refund_zero g hs ss sp hsp, hres, hsp,
      fun _ _ _ => rfl⟩
  · by_cases hle : amount ≤ sp
    · rw [Nat.min_eq_left hle]
      refine ⟨_, runS_credit_state_gas_refund_spill g amount hs ss sp hsp hz
        hle, ?_, ?_, ?_⟩
      · simp only [Std.ExtDHashMap.get?_insert]
        simpa using hres
      · simp only [Std.ExtDHashMap.get?_insert]
        simp
      · intro r _ h2
        exact regs_get?_insert_ne _ _ h2
    · have hlt : sp < amount := Nat.lt_of_not_le hle
      rw [Nat.min_eq_right (Nat.le_of_lt hlt)]
      by_cases hsp0 : sp = 0
      · subst hsp0
        simp only [Nat.add_zero, Nat.sub_zero]
        refine ⟨_, runS_credit_state_gas_refund_reservoir g amount hs ss res
          hres hsp hz, ?_, ?_, ?_⟩
        · simp only [Std.ExtDHashMap.get?_insert]
          simp
        · simp only [Std.ExtDHashMap.get?_insert]
          simpa using hsp
        · intro r h1 _
          exact regs_get?_insert_ne _ _ h1
      · refine ⟨_, runS_credit_state_gas_refund_mixed g amount hs ss res sp
          hres hsp hsp0 hlt, ?_, ?_, ?_⟩
        · simp only [Std.ExtDHashMap.get?_insert]
          simp
        · simp only [Std.ExtDHashMap.get?_insert]
          simp [Evm.Functions.STATE_GAS_SPILL_ZERO]
        · intro r h1 h2
          rw [regs_get?_insert_ne _ _ h1, regs_get?_insert_ne _ _ h2]

/-- The state charge, in closed form: the reservoir first, then a spill
out of execution gas. -/
theorem runS_charge_state_closed (g amount : Nat) (hs : Evm.HostState)
    (ss : SeqState) (res sp : Nat)
    (hres : ss.regs.get? Register.state_gas_remaining = some res)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hafford : amount - min amount res ≤ g)
    (hroom : sp + (amount - min amount res) ≤ 2 ^ 24) :
    ∃ ss', runS (Evm.Functions.charge_state_gas g amount) hs ss
        = .ok ((true, g - (amount - min amount res)), hs) ss'
      ∧ ss'.regs.get? Register.state_gas_remaining
          = some (res - min amount res)
      ∧ ss'.regs.get? Register.state_gas_spilled
          = some (sp + (amount - min amount res))
      ∧ ∀ (r : Register), r ≠ Register.state_gas_remaining →
          r ≠ Register.state_gas_spilled →
          ss'.regs.get? r = ss.regs.get? r := by
  by_cases hz : amount = 0
  · subst hz
    simp only [Nat.zero_min, Nat.sub_zero, Nat.sub_self, Nat.add_zero]
    exact ⟨ss, runS_charge_state_gas_zero g hs ss, hres, hsp,
      fun _ _ _ => rfl⟩
  · by_cases hle : amount ≤ res
    · rw [Nat.min_eq_left hle, Nat.sub_self, Nat.sub_zero, Nat.add_zero]
      refine ⟨_, runS_charge_state_gas_reservoir g amount hs ss res hres hz
        hle, ?_, ?_, ?_⟩
      · simp only [Std.ExtDHashMap.get?_insert]
        simp
      · simp only [Std.ExtDHashMap.get?_insert]
        simpa using hsp
      · intro r h1 _
        exact regs_get?_insert_ne _ _ h1
    · have hlt : res < amount := Nat.lt_of_not_le hle
      rw [Nat.min_eq_right (Nat.le_of_lt hlt)] at hafford hroom ⊢
      refine ⟨_, runS_charge_state_gas_spill g amount hs ss res sp hres hsp hz
        hlt hafford hroom, ?_, ?_, ?_⟩
      · simp only [Std.ExtDHashMap.get?_insert]
        simp [Evm.Functions.GAS_ZERO]
      · simp only [Std.ExtDHashMap.get?_insert]
        simp
      · intro r h1 h2
        rw [regs_get?_insert_ne _ _ h2, regs_get?_insert_ne _ _ h1]

/-! ### `record_refund` -/

/-- The signed refund accumulator. The extraction validates the sum
against `±199 · (2^64 − 1)` and hard-aborts outside it — unreachable for
a transaction under the EIP-7825 gas cap, and carried as
`RefundRel.room`. -/
theorem runS_record_refund (delta : Int) (hs : Evm.HostState)
    (ss : SeqState) (r : Int)
    (hr : ss.regs.get? Register.frame_refund = some r)
    (hlo : -(199 * (2 ^ 64 - 1) : Int) ≤ r + delta)
    (hhi : r + delta ≤ (199 * (2 ^ 64 - 1) : Int)) :
    runS (Evm.Functions.record_refund delta) hs ss =
      .ok ((), hs)
        { ss with
            regs := ss.regs.insert Register.frame_refund (r + delta) } := by
  simp only [Evm.Functions.record_refund, Evm.Functions.validated_refund_add]
  refine runS_bind_ok (runS_readReg _ _ _ _ hr) ?_
  refine runS_bind_ok ?_ (runS_writeReg _ _ _ _)
  rw [if_pos (by simpa using ⟨hlo, hhi⟩)]
  exact runS_pure _ _ _

end EvmSpecsVerify
