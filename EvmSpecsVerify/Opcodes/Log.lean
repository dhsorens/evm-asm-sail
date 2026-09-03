import EvmSpecsVerify.Opcodes.Mcopy
import EvmSpecsVerify.Opcodes.Return
import EvmSpecsVerify.Relations.Log

/-!
# LOG0

The first log-emitting opcode. It combines three things already proven
separately — the copy family's memory expansion, RETURN's payload slice
(`active_memory_slice`), and the log store correspondence
([`LogRel`](../Relations/Log.lean)) — with one genuinely new order
divergence.

## MM-11: where the static guard sits

SpecRef's `iLogN` pops, charges base + topics + payload + expansion,
extends memory, and **then** tests `message.isStatic`. The extraction's
`execute_log` calls `guard_static` as its **first** statement. So:

* in a static frame with enough gas both report the same kind
  (`.writeInStaticContext` ↔ `WriteProtection`, the new
  `ErrorRel.writeInStaticContext`);
* in a static frame **without** enough gas SpecRef reports `outOfGas`
  and the extraction `WriteProtection` — the fourth admitted kind of
  `StepResultRel.haltedChargeFirst`;
* with an underflowing stack the extraction's hoisted `validate_stack`
  fires before `guard_static`, so underflow wins on both sides and the
  kinds agree.

LOG is the only outlier among the four write-guarded opcodes; SSTORE,
TSTORE and SELFDESTRUCT check static first on both sides. SpecRef matches
upstream here — EELS' `log.py` charges before raising.

## The charge split

SpecRef charges base + `8 * size` + `375 * n` + expansion in one
`charge_gas`. The extraction charges in **four** stages: `G_log`,
`G_logtopic * n`, the payload through `charge_word_scaled_gas`, then
expansion (`runS_charge_log_gas_*` in Representation/EvmGas.lean). For
`n = 0` the topic stage is `charge g 0` and always succeeds, so three
OOG states are reachable.

Reachable outcomes: success ×2 (zero size / grow / in-window — three
lemmas), underflow ×2, the static halt, OOG at any of the three live
charge stages, plus the MM-11 double fault. Overflow is unreachable
(2-in/0-out).

Gas (MM-2): `OPCODE_LOG_BASE = 375 = G_log`,
`OPCODE_LOG_DATA_PER_BYTE = 8 = G_logdata`,
`OPCODE_LOG_TOPIC = 375 = G_logtopic`.
-/

open private pcAdd from EvmAsm.Stateless.SpecRef.InstructionsCore
open private writeArrayBytes readArrayBytes zeroMemoryRange memoryBytesOf
  from Evm.HostAxioms

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- The SpecRef LOG charge for offset `x`, size `z`, `n` topics against
memory size `msz`. -/
def logCost (msz x z n : Nat) : Nat :=
  GasCosts.OPCODE_LOG_BASE
    + GasCosts.OPCODE_LOG_DATA_PER_BYTE * z
    + GasCosts.OPCODE_LOG_TOPIC * n
    + (calculate_gas_extend_memory msz [(x, z)]).cost

/-! ## SpecRef run shapes -/

theorem runR_iLog0_underflow_nil (s : Machine) (hstack : s.evm.stack = []) :
    runR (iLogN 0) s = .ok (.error .stackUnderflow, s) := by
  simp only [iLogN]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_iLog0_underflow_one (s : Machine) (x : U256)
    (hstack : s.evm.stack = [x]) :
    runR (iLogN 0) s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with stack := [] } }) := by
  simp only [iLogN]
  refine runR_bind_ok (runR_stackPop_cons s x [] hstack) ?_
  exact runR_bind_err (runR_stackPop_nil _ (by simp))

theorem runR_iLog0_oog (s : Machine) (x z : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: z :: rest)
    (hgas : s.evm.gasLeft < logCost s.evm.memory.length x z 0) :
    runR (iLogN 0) s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [iLogN]
  refine runR_bind_ok (runR_stackPop_cons s x (z :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ z rest (by simp)) ?_
  refine runR_bind_ok (runR_pure _ _) ?_
  refine runR_bind_ok (runR_getEvm_map _ _) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _
    (by simpa [logCost] using hgas))

/-- SpecRef's memory after the metered extension: the state the payload
read and the log append see. -/
def logExtMemory (s : Machine) (x z : U256) : Bytes :=
  s.evm.memory ++ List.replicate
    (calculate_gas_extend_memory s.evm.memory.length [(x, z)]).expandBy
    0x00

/-- The record SpecRef appends (LOG0: no topics). -/
def log0Of (s : Machine) (x z : U256) : Log :=
  { address := s.evm.message.currentTarget
    topics := []
    data := memory_read_bytes (logExtMemory s x z) x z }

/-- MM-11: the static throw fires **after** the charge and the extension. -/
theorem runR_iLog0_static (s : Machine) (x z : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: z :: rest)
    (hgas : logCost s.evm.memory.length x z 0 ≤ s.evm.gasLeft)
    (hstatic : s.evm.message.isStatic = true) :
    runR (iLogN 0) s =
      .ok (.error .writeInStaticContext,
        { s with evm := { s.evm with
            stack := rest
            memory := logExtMemory s x z
            gasLeft := s.evm.gasLeft - logCost s.evm.memory.length x z 0
            regularGasUsed :=
              s.evm.regularGasUsed
                + logCost s.evm.memory.length x z 0 } }) := by
  simp only [iLogN, extendMemory]
  refine runR_bind_ok (runR_stackPop_cons s x (z :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ z rest (by simp)) ?_
  refine runR_bind_ok (runR_pure _ _) ?_
  refine runR_bind_ok (runR_getEvm_map _ _) ?_
  refine runR_bind_ok (runR_charge_gas _ _
    (by simpa [logCost] using hgas)) ?_
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_pos (by simpa using hstatic)]
  exact runR_bind_err (runR_throw _ _)

theorem runR_iLog0_success (s : Machine) (x z : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: z :: rest)
    (hgas : logCost s.evm.memory.length x z 0 ≤ s.evm.gasLeft)
    (hstatic : s.evm.message.isStatic = false) :
    runR (iLogN 0) s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := rest
            memory := logExtMemory s x z
            logs := s.evm.logs ++ [log0Of s x z]
            gasLeft := s.evm.gasLeft - logCost s.evm.memory.length x z 0
            regularGasUsed :=
              s.evm.regularGasUsed + logCost s.evm.memory.length x z 0
            pc := s.evm.pc + 1 } }) := by
  simp only [iLogN, extendMemory, pcAdd]
  refine runR_bind_ok (runR_stackPop_cons s x (z :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ z rest (by simp)) ?_
  refine runR_bind_ok (runR_pure _ _) ?_
  refine runR_bind_ok (runR_getEvm_map _ _) ?_
  refine runR_bind_ok (runR_charge_gas _ _
    (by simpa [logCost] using hgas)) ?_
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_neg (by simpa using hstatic)]
  refine runR_bind_ok (runR_pure _ _) ?_
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  exact runR_modifyEvm _ _

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for the LOG family. -/
theorem log_dispatch (n : Nat) (pc_in : Nat) (top : StackTop)
    (off len : Nat) (msf : EvmMemorySliceFields off len) (g : Nat) :
    Evm.Functions.execute_opcode (.LOG n) pc_in top ⟨off, len, msf⟩ g =
      Evm.Functions.execute_log n top ⟨off, len, msf⟩ g >>= fun p =>
        pure (pc_in, p.1, p.2.1, p.2.2) := rfl

open Evm.Functions in
/-- MM-11: the static guard runs before anything else, so it carries the
frame's full gas into `exc_halt`. (First consumer of `guard_static`; the
two shapes move down beside `exc_halt` when SSTORE/TSTORE arrive.) -/
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

open Evm.Functions in
theorem runS_pop_log_topics_zero (top : StackTop) (hs : Evm.HostState)
    (ss : SeqState) :
    runS (Evm.Functions.pop_log_topics 0 top) hs ss =
      .ok ((LogTopics.LogTopics0 (), top), hs) ss := runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_log0_underflow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 2) :
    runS (Evm.Functions.execute (.LOG 0) pc_in top ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, top, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.LOG 0) = pure (2, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 2 0 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
/-- MM-11: in a static frame the extraction halts before popping or
charging. -/
theorem runS_execute_log0_static (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hin : 2 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (hstatic : msg.is_static = true) :
    runS (Evm.Functions.execute (.LOG 0) pc_in top ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, top, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .WriteProtection } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.LOG 0) = pure (2, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss hin
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, log_dispatch]
  have hbody : runS (Evm.Functions.execute_log 0 top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top, (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .WriteProtection } := by
    simp only [Evm.Functions.execute_log]
    refine runS_bind_ok
      (runS_guard_static_halt g hs ss prof sp msg hprof hsp hmsg hfork
        hstatic) ?_
    rw [dif_pos rfl]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

/-- The pop/topic prologue shared by every non-static outcome. -/
private theorem log0_prologue_pfx (l : List word) (top : StackTop)
    (x z : Nat) (rest : List word)
    (hpfx : l.take top.toNat = (x :: z :: rest).reverse)
    (htop : top.toNat = (x :: z :: rest).length) :
    l.take (top.toNat - 1) = (z :: rest).reverse :=
  take_shrink l _ x _
    (by rw [show top.toNat - 1 + 1 = top.toNat from by simp at htop; omega]
        exact hpfx)
    (by simp at htop ⊢; omega)

open Evm.Functions in
theorem runS_execute_log0_oog_base (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x z : Nat)
    (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: z :: rest).reverse)
    (htop : top.toNat = (x :: z :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hstatic : msg.is_static = false)
    (hgas : g < G_log) :
    runS (Evm.Functions.execute (.LOG 0) pc_in top ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hpfx1 := log0_prologue_pfx l top x z rest hpfx htop
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.LOG 0) = pure (2, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, log_dispatch]
  have hbody : runS (Evm.Functions.execute_log 0 top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_log]
    refine runS_bind_ok (runS_guard_static_ok g hs ss msg hmsg hstatic) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (z :: rest) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest z rest hframe
        (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
    refine runS_bind_ok (runS_pop_log_topics_zero _ hs ss) ?_
    refine runS_bind_ok
      (runS_charge_log_gas_oog_base g 0 z hs ss prof sp msg hprof hsp hmsg
        hfork hgas) ?_
    rw [dif_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
theorem runS_execute_log0_oog_data (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x z : Nat)
    (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: z :: rest).reverse)
    (htop : top.toNat = (x :: z :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hstatic : msg.is_static = false)
    (hbase : G_log + G_logtopic * 0 ≤ g)
    (hgas : g - G_log - G_logtopic * 0 < G_logdata * z) :
    runS (Evm.Functions.execute (.LOG 0) pc_in top ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hpfx1 := log0_prologue_pfx l top x z rest hpfx htop
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.LOG 0) = pure (2, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, log_dispatch]
  have hbody : runS (Evm.Functions.execute_log 0 top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_log]
    refine runS_bind_ok (runS_guard_static_ok g hs ss msg hmsg hstatic) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (z :: rest) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest z rest hframe
        (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
    refine runS_bind_ok (runS_pop_log_topics_zero _ hs ss) ?_
    refine runS_bind_ok
      (runS_charge_log_gas_oog_data g 0 z hs ss prof sp msg hprof hsp hmsg
        hfork hbase hgas) ?_
    rw [dif_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
theorem runS_execute_log0_oog_exp (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x z : Nat)
    (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: z :: rest).reverse)
    (htop : top.toNat = (x :: z :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hstatic : msg.is_static = false)
    (hcharge : G_log + G_logtopic * 0 + G_logdata * z ≤ g)
    (hgas : g - G_log - G_logtopic * 0 - G_logdata * z
      < Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
          (Evm.Functions.memory_required_size x z)) :
    runS (Evm.Functions.execute (.LOG 0) pc_in top ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hpfx1 := log0_prologue_pfx l top x z rest hpfx htop
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.LOG 0) = pure (2, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, log_dispatch]
  have hbody : runS (Evm.Functions.execute_log 0 top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_log]
    refine runS_bind_ok (runS_guard_static_ok g hs ss msg hmsg hstatic) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (z :: rest) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest z rest hframe
        (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
    refine runS_bind_ok (runS_pop_log_topics_zero _ hs ss) ?_
    refine runS_bind_ok
      (runS_charge_log_gas_ok g 0 z hs ss hcharge) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_charge_oog _ _ hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
    rw [dif_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

/-- The host state after LOG0's emission: one row appended, its payload
copied out of the (already expanded) memory window. -/
def log0Host (hs : Evm.HostState) (a : Evm.Defs.address) (b z : Nat) :
    Evm.HostState :=
  logAppend hs a [] (readArrayBytes hs.memoryBytes b z)

open Evm.Functions in
/-- Zero-size success: no expansion, and the emitted payload is empty on
both sides. -/
theorem runS_execute_log0_ok_zero (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : Nat)
    (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: (0 : Nat) :: rest).reverse)
    (htop : top.toNat = (x :: (0 : Nat) :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (msg : Evm.Defs.Message)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hstatic : msg.is_static = false)
    (hcharge : G_log + G_logtopic * 0 + G_logdata * 0 ≤ g) :
    runS (Evm.Functions.execute (.LOG 0) pc_in top ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          ⟨off, len, msf⟩,
          g - G_log - G_logtopic * 0 - G_logdata * 0),
        log0Host hs msg.address 0 0) ss := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hpfx1 := log0_prologue_pfx l top x 0 rest hpfx htop
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.LOG 0) = pure (2, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, log_dispatch]
  have hbody : runS (Evm.Functions.execute_log 0 top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice),
          g - G_log - G_logtopic * 0 - G_logdata * 0),
        log0Host hs msg.address 0 0) ss := by
    simp only [Evm.Functions.execute_log]
    refine runS_bind_ok (runS_guard_static_ok g hs ss msg hmsg hstatic) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x ((0 : Nat) :: rest) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest (0 : Nat) rest hframe
        (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
    refine runS_bind_ok (runS_pop_log_topics_zero _ hs ss) ?_
    refine runS_bind_ok (runS_charge_log_gas_ok g 0 0 hs ss hcharge) ?_
    rw [dif_neg (by simp)]
    rw [show Evm.Functions.memory_required_size x 0 = 0 from rfl]
    refine runS_bind_ok
      (runS_charge_ok _ _ hs ss
        (by simp [Evm.Functions.memory_expansion_cost,
          memory_high_water_eq, memory_word_count_eq])) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok (runS_memory_access_zero x hs ss) ?_
    refine runS_bind_ok
      (runS_expand_memory_le off len 0 msf hs ss (Nat.zero_le len)) ?_
    refine runS_bind_ok (runS_active_memory_slice_zero off len msf 0 hs ss) ?_
    refine runS_bind_ok (runS_self_addr msg hs ss hmsg) ?_
    refine runS_bind_ok
      (runS_k_log_memory msg.address (LogTopics.LogTopics0 ())
        ⟨0, 0, evm_memory_slice 0 0⟩ (readArrayBytes hs.memoryBytes 0 0) hs
        ss rfl) ?_
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
/-- Success with expansion: the window grows to `x + z`, then the payload
is read out of it and emitted. -/
theorem runS_execute_log0_ok_grow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x z : Nat)
    (rest : List word) (mfrest : List Evm.MemoryFrame)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: z :: rest).reverse)
    (htop : top.toNat = (x :: z :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hmframe : hs.memoryFrames
      = ({ base := off, established := len } : Evm.MemoryFrame) :: mfrest)
    (msg : Evm.Defs.Message)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hstatic : msg.is_static = false)
    (hz : (z == 0) = false)
    (hcharge : G_log + G_logtopic * 0 + G_logdata * z ≤ g)
    (hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + z)
      ≤ g - G_log - G_logtopic * 0 - G_logdata * z)
    (hreq : x + z ≤ 2 ^ 32 - 32)
    (hgrow : len < x + z) :
    runS (Evm.Functions.execute (.LOG 0) pc_in top ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, x + z, {}⟩ : EvmMemorySlice),
          g - G_log - G_logtopic * 0 - G_logdata * z
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + z)),
        log0Host (expandedHost hs off len (x + z) mfrest) msg.address
          (off + 0 + x) z) ss := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hpfx1 := log0_prologue_pfx l top x z rest hpfx htop
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.LOG 0) = pure (2, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, log_dispatch]
  have hbody : runS (Evm.Functions.execute_log 0 top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, x + z, {}⟩ : EvmMemorySlice),
          g - G_log - G_logtopic * 0 - G_logdata * z
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + z)),
        log0Host (expandedHost hs off len (x + z) mfrest) msg.address
          (off + 0 + x) z) ss := by
    simp only [Evm.Functions.execute_log]
    refine runS_bind_ok (runS_guard_static_ok g hs ss msg hmsg hstatic) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (z :: rest) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest z rest hframe
        (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
    refine runS_bind_ok (runS_pop_log_topics_zero _ hs ss) ?_
    refine runS_bind_ok (runS_charge_log_gas_ok g 0 z hs ss hcharge) ?_
    rw [dif_neg (by simp)]
    rw [mcopy_required_size_pos x z hz]
    refine runS_bind_ok (runS_charge_ok _ _ hs ss hexp) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_memory_access_ok x z hs ss hz
        (show x ≤ 2 ^ 32 - 1 by omega)
        (show z ≤ 2 ^ 32 - 1 - x by omega)) ?_
    simp only [Evm.Defs.MemoryAccessFields.required_size,
      Evm.Defs.MemoryRangeFields.off, Evm.Defs.MemoryRangeFields.len]
    refine runS_bind_ok
      (runS_expand_memory_grow off len (x + z) msf hs ss len mfrest hmframe
        rfl hgrow) ?_
    refine runS_bind_ok
      (runS_active_memory_slice_le off (x + z) x z {} _ ss hz
        (le_refl _)) ?_
    refine runS_bind_ok (runS_self_addr msg _ ss hmsg) ?_
    refine runS_bind_ok
      (runS_k_log_memory msg.address (LogTopics.LogTopics0 ())
        ⟨off + 0 + x, z, evm_memory_slice (off + 0 + x) z⟩
        (readArrayBytes (expandedHost hs off len (x + z) mfrest).memoryBytes
          (off + 0 + x) z)
        (expandedHost hs off len (x + z) mfrest) ss rfl) ?_
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
/-- Success inside the established window: no expansion. -/
theorem runS_execute_log0_ok_nogrow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x z : Nat)
    (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: z :: rest).reverse)
    (htop : top.toNat = (x :: z :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (msg : Evm.Defs.Message)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hstatic : msg.is_static = false)
    (hz : (z == 0) = false)
    (hcharge : G_log + G_logtopic * 0 + G_logdata * z ≤ g)
    (hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + z)
      ≤ g - G_log - G_logtopic * 0 - G_logdata * z)
    (hreq : x + z ≤ 2 ^ 32 - 32)
    (hgrow : x + z ≤ len) :
    runS (Evm.Functions.execute (.LOG 0) pc_in top ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice),
          g - G_log - G_logtopic * 0 - G_logdata * z
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + z)),
        log0Host hs msg.address (off + 0 + x) z) ss := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hpfx1 := log0_prologue_pfx l top x z rest hpfx htop
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.LOG 0) = pure (2, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, log_dispatch]
  have hbody : runS (Evm.Functions.execute_log 0 top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice),
          g - G_log - G_logtopic * 0 - G_logdata * z
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + z)),
        log0Host hs msg.address (off + 0 + x) z) ss := by
    simp only [Evm.Functions.execute_log]
    refine runS_bind_ok (runS_guard_static_ok g hs ss msg hmsg hstatic) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (z :: rest) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest z rest hframe
        (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
    refine runS_bind_ok (runS_pop_log_topics_zero _ hs ss) ?_
    refine runS_bind_ok (runS_charge_log_gas_ok g 0 z hs ss hcharge) ?_
    rw [dif_neg (by simp)]
    rw [mcopy_required_size_pos x z hz]
    refine runS_bind_ok (runS_charge_ok _ _ hs ss hexp) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_memory_access_ok x z hs ss hz
        (show x ≤ 2 ^ 32 - 1 by omega)
        (show z ≤ 2 ^ 32 - 1 - x by omega)) ?_
    simp only [Evm.Defs.MemoryAccessFields.required_size,
      Evm.Defs.MemoryRangeFields.off, Evm.Defs.MemoryRangeFields.len]
    refine runS_bind_ok
      (runS_expand_memory_le off len (x + z) msf hs ss hgrow) ?_
    refine runS_bind_ok
      (runS_active_memory_slice_le off len x z msf hs ss hz hgrow) ?_
    refine runS_bind_ok (runS_self_addr msg hs ss hmsg) ?_
    refine runS_bind_ok
      (runS_k_log_memory msg.address (LogTopics.LogTopics0 ())
        ⟨off + 0 + x, z, evm_memory_slice (off + 0 + x) z⟩
        (readArrayBytes hs.memoryBytes (off + 0 + x) z) hs ss rfl) ?_
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

/-! ## The step equivalence -/

open Evm.Functions in
/-- **LOG0, all reachable outcomes**: success (zero size / grow /
in-window), underflow ×2, the static halt, OOG at any of the three live
charge stages, and the MM-11 double fault. `hstatic` and `haddr` are
`message`-register ties (the same `haddr` ADDRESS and SLOAD use);
`base` is the frame's log-store base index. -/
theorem log0_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (off len : Nat)
    (msf : EvmMemorySliceFields off len) (pc_in : Nat) (base : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hmem : MemoryRel sRef.evm.memory hs off len)
    (hsafe : MemGasSafe sRef.evm.memory sRef.evm.gasLeft)
    (hlog : LogRel sRef.evm.logs hs base)
    (hpc : pc_in = sRef.evm.pc + 1)
    (haddr : ∀ m : Evm.Defs.Message,
      ss.regs.get? Register.message = some m →
      m.address.toList = sRef.evm.message.currentTarget)
    (hstatic : ∀ m : Evm.Defs.Message,
      ss.regs.get? Register.message = some m →
      m.is_static = sRef.evm.message.isStatic) :
    StepResultRel (LogPost base) (runR (iLogN 0) sRef)
      (runS (Evm.Functions.execute (.LOG 0) pc_in top ⟨off, len, msf⟩ g)
        hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  have hst : msg.is_static = sRef.evm.message.isStatic := hstatic msg hmsg
  have hax : msg.address.toList = sRef.evm.message.currentTarget :=
    haddr msg hmsg
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_iLog0_underflow_nil sRef hS,
      runS_execute_log0_underflow pc_in top off len g msf hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | [x] =>
    rw [hS] at hpfx htop
    rw [runR_iLog0_underflow_one sRef x hS,
      runS_execute_log0_underflow pc_in top off len g msf hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | x :: z :: rest =>
    rw [hS] at hpfx htop hlim hwfS
    have hin2 : 2 ≤ top.toNat := by simp at htop; omega
    have hlim' : top.toNat ≤ 1024 := by simp at htop ⊢; simp at hlim; omega
    have hzw : z < 2 ^ 256 := hwfS z (by simp)
    obtain ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩ := hmem
    have hcost : (calculate_gas_extend_memory sRef.evm.memory.length
        [(x, z)]).cost
        = Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
            (Evm.Functions.memory_required_size x z) :=
      extend_cost_eq sRef.evm.memory off len x z msf haligned
    have hTsplit : logCost sRef.evm.memory.length x z 0
        = 375 + 8 * z + 375 * 0
          + Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
              (Evm.Functions.memory_required_size x z) := by
      rw [logCost, ← hcost]
      rfl
    -- MM-11: the static guard fires first on the extraction side
    by_cases hstat : sRef.evm.message.isStatic = true
    · have hstat' : msg.is_static = true := by rw [hst]; exact hstat
      rw [runS_execute_log0_static pc_in top off len g msf hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hin2 hlim' hstat']
      by_cases hg : sRef.evm.gasLeft < logCost sRef.evm.memory.length x z 0
      · rw [runR_iLog0_oog sRef x z rest hS hg]
        exact StepResultRel.haltedChargeFirst
          (Or.inr (Or.inr (Or.inr rfl)))
          (haltRegs_frame_status ss msg .WriteProtection)
      · push Not at hg
        rw [runR_iLog0_static sRef x z rest hS hg hstat]
        exact StepResultRel.halted ErrorRel.writeInStaticContext
          (haltRegs_frame_status ss msg .WriteProtection)
    · have hstat0 : sRef.evm.message.isStatic = false := by
        simpa using hstat
      have hstat' : msg.is_static = false := by rw [hst]; exact hstat0
      by_cases hg : sRef.evm.gasLeft < logCost sRef.evm.memory.length x z 0
      · rw [runR_iLog0_oog sRef x z rest hS hg]
        rw [hTsplit, ← hlive] at hg
        have hgN : g < 375 + 8 * z + 375 * 0
            + Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                (Evm.Functions.memory_required_size x z) := hg
        by_cases hb : g < G_log
        · rw [runS_execute_log0_oog_base pc_in top off len g msf hs ss l
            frest x z rest hframe hpfx htop hlim' prof
            sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hstat' hb]
          exact StepResultRel.halted ErrorRel.outOfGas
            (haltRegs_frame_status ss msg .OutOfGas)
        · push Not at hb
          have hbN : (375 : Nat) ≤ g := hb
          by_cases hc : g - G_log - G_logtopic * 0 < G_logdata * z
          · rw [runS_execute_log0_oog_data pc_in top off len g msf hs ss l
              frest x z rest hframe hpfx htop hlim' prof
              sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hstat'
              (by show (375 : Nat) + 375 * 0 ≤ g; omega) hc]
            exact StepResultRel.halted ErrorRel.outOfGas
              (haltRegs_frame_status ss msg .OutOfGas)
          · push Not at hc
            have hcN : (8 : Nat) * z ≤ g - 375 - 375 * 0 := hc
            rw [runS_execute_log0_oog_exp pc_in top off len g msf hs ss l
              frest x z rest hframe hpfx htop hlim' prof
              sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hstat'
              (by show (375 : Nat) + 375 * 0 + 8 * z ≤ g; omega)
              (by
                show g - 375 - 375 * 0 - 8 * z < _
                rw [show g - 375 - 375 * 0 - 8 * z
                    = g - (375 + 8 * z + 375 * 0) from by omega,
                  Nat.sub_lt_iff_lt_add (by omega)]
                exact lt_of_lt_of_le hgN (le_of_eq (by ring)))]
            exact StepResultRel.halted ErrorRel.outOfGas
              (haltRegs_frame_status ss msg .OutOfGas)
      · push Not at hg
        have hgT : 375 + 8 * z + 375 * 0
            + Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                (Evm.Functions.memory_required_size x z) ≤ g := by
          rw [← hTsplit]
          show logCost sRef.evm.memory.length x z 0 ≤ g
          rw [hlive]
          exact hg
        have hcharge : G_log + G_logtopic * 0 + G_logdata * z ≤ g := by
          show (375 : Nat) + 375 * 0 + 8 * z ≤ g
          rw [show (375 : Nat) + 375 * 0 + 8 * z = 375 + 8 * z + 375 * 0
            from by ring]
          exact Nat.le_trans (Nat.le_add_right _ _) hgT
        have hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
            (Evm.Functions.memory_required_size x z)
            ≤ g - G_log - G_logtopic * 0 - G_logdata * z := by
          show _ ≤ g - 375 - 375 * 0 - 8 * z
          rw [show g - 375 - 375 * 0 - 8 * z = g - (375 + 8 * z + 375 * 0)
            from by omega]
          exact Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hgT)
        have hnn : top.toNat = rest.length + 2 := by simpa using htop
        have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
          cursor_retreat_toNat top (by omega)
        have hret2 : (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1).toNat
            = top.toNat - 2 := by
          rw [cursor_retreat_toNat _ (by rw [hret1]; omega), hret1]
          omega
        have hpfx2 : l.take (top.toNat - 2) = rest.reverse := by
          have hview : l.take (top.toNat - 2) =
              (l.take top.toNat).take (top.toNat - 2) := by
            rw [List.take_take, Nat.min_eq_left (by omega)]
          rw [hview, hpfx]
          have hrl : rest.reverse.length = top.toNat - 2 := by simp; omega
          calc ((x :: z :: rest).reverse).take (top.toNat - 2)
              = (rest.reverse ++ [z, x]).take (top.toNat - 2) := by simp
            _ = rest.reverse := by
                rw [List.take_append_of_le_length (by omega), ← hrl,
                  List.take_length]
        have hpost := fun (hs' : Evm.HostState)
            (hframe' : hs'.stackFrames = l :: frest) =>
          (⟨⟨l, frest, hframe', by rw [hret2]; exact hpfx2, by
              rw [hret2]; omega⟩,
            by rw [hret2]; omega,
            by omega,
            fun w hw => hwfS w (by simp [hw])⟩ :
            StackRel rest hs'
              (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1))
        have hgas' : g - 375 - 375 * 0 - 8 * z
              - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                  (Evm.Functions.memory_required_size x z)
            = (sRef.evm.gasLeft : Nat)
              - logCost sRef.evm.memory.length x z 0 := by
          rw [hTsplit, ← hlive, Nat.sub_sub, Nat.sub_sub, Nat.sub_sub]
          congr 1
          ring
        rw [runR_iLog0_success sRef x z rest hS hg hstat0]
        by_cases hz0 : z = 0
        · subst hz0
          have hzero : (calculate_gas_extend_memory sRef.evm.memory.length
              [(x, 0)]) = { cost := 0, expandBy := 0 } := by
            rw [calc_extend_single]
            rfl
          have hcost0 : logCost sRef.evm.memory.length x 0 0 = 375 := by
            rw [logCost, hzero]
            rfl
          have hmem0 : logExtMemory sRef x 0 = sRef.evm.memory := by
            rw [logExtMemory, hzero,
              show (({ cost := 0, expandBy := 0 } :
                EvmAsm.Stateless.SpecRef.ExtendMemory).expandBy : Nat) = 0
                from rfl,
              show List.replicate 0 (0x00 : EvmAsm.EL.RLP.Byte) = [] from rfl,
              List.append_nil]
          rw [runS_execute_log0_ok_zero pc_in top off len g msf hs ss l
            frest x rest hframe hpfx htop hlim' msg hmsg hstat' hcharge]
          refine StepResultRel.success ⟨?_, ?_⟩
          · refine ⟨⟨hpost _ hframe, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
              ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, by simp [hpc], ?_⟩
            · refine ⟨?_, hres, hsp⟩
              show g - 375 - 375 * 0 - 8 * 0
                = sRef.evm.gasLeft - logCost sRef.evm.memory.length x 0 0
              rw [hcost0, ← hlive]
              omega
            · refine ⟨off, len, msf, rfl, ?_, ?_⟩
              · rw [hmem0]
                exact memoryRel_logAppend _ _ off len _ _ _
                  ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩
              · rw [hmem0]
                exact memGasSafe_mono_gas sRef.evm.memory (Nat.sub_le _ _)
                  hsafe
          · have happ := logRel_append sRef.evm.logs hs base msg.address []
              (readArrayBytes hs.memoryBytes 0 0) hlog
            rw [show logOf msg.address [] (readArrayBytes hs.memoryBytes 0 0)
                = log0Of sRef x 0 from by
              rw [logOf, log0Of, hax, hmem0]
              simp [readArrayBytes, memory_read_bytes]] at happ
            exact happ
        · have hz : (z == 0) = false := by simpa using hz0
          rw [mcopy_required_size_pos x z hz] at hcost hTsplit hexp hgas'
          have hreq : x + z ≤ 2 ^ 32 - 32 :=
            safe_required_bound sRef.evm.memory off len (x + z)
              (g - G_log - G_logtopic * 0 - G_logdata * z)
              sRef.evm.gasLeft msf haligned hsafe
              (by show g - 375 - 375 * 0 - 8 * z ≤ sRef.evm.gasLeft
                  rw [← hlive]
                  omega) hexp
          have hexpandBy : ((calculate_gas_extend_memory
              sRef.evm.memory.length [(x, z)]).expandBy : Nat)
              = 32 * Evm.Functions.memory_word_count (x + z)
                - sRef.evm.memory.length := by
            have hiff0 : ∀ a b : Nat, (32 * a ≤ 32 * b) ↔ (a ≤ b) :=
              fun a b => by omega
            have hwcM : Evm.Functions.memory_word_count
                sRef.evm.memory.length
                = Evm.Functions.memory_word_count len := by
              rw [haligned, memory_word_count_eq, memory_word_count_eq]
              omega
            have hiff : ((ceil32 (x + z) : Nat)
                ≤ ceil32 sRef.evm.memory.length)
                ↔ (Evm.Functions.memory_word_count (x + z)
                    ≤ Evm.Functions.memory_word_count len) := by
              rw [ceil32_eq, ceil32_eq, hwcM]
              exact hiff0 _ _
            rw [calc_extend_single, if_neg (by simpa using hz0)]
            by_cases hle : Evm.Functions.memory_word_count (x + z)
                ≤ Evm.Functions.memory_word_count len
            · rw [if_pos (hiff.mpr hle)]
              show (0 : Nat) = _
              have h1 : 32 * Evm.Functions.memory_word_count (x + z)
                  ≤ sRef.evm.memory.length := by
                rw [haligned]
                omega
              omega
            · rw [if_neg (fun hc => hle (hiff.mp hc))]
              show ((ceil32 (x + z) : Nat)
                - ceil32 sRef.evm.memory.length) = _
              rw [ceil32_eq, ceil32_eq, hwcM, ← haligned]
          by_cases hgrow : len < x + z
          · have hmemE : logExtMemory sRef x z
                = sRef.evm.memory ++ List.replicate
                  (32 * Evm.Functions.memory_word_count (x + z)
                    - sRef.evm.memory.length) 0x00 := by
              rw [logExtMemory, hexpandBy]
            rw [runS_execute_log0_ok_grow pc_in top off len g msf hs ss l
              frest x z rest mfrest hframe hpfx htop hlim' hmframe msg hmsg
              hstat' hz hcharge hexp hreq hgrow]
            have hrel' := memoryRel_expand sRef.evm.memory hs off len
              (x + z) mfrest
              ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩ hgrow
            have hread := memoryRel_read _
              (expandedHost hs off len (x + z) mfrest) off (x + z) x z
              hrel' (le_refl _)
            refine StepResultRel.success ⟨?_, ?_⟩
            · refine ⟨⟨hpost _ hframe, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
                ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, by simp [hpc], ?_⟩
              · exact ⟨hgas', hres, hsp⟩
              · refine ⟨off, x + z, {}, rfl, ?_, ?_⟩
                · rw [hmemE]
                  exact memoryRel_logAppend _ _ off (x + z) _ _ _ hrel'
                · show MemGasSafe _ (sRef.evm.gasLeft
                    - logCost sRef.evm.memory.length x z 0)
                  rw [hmemE]
                  exact memGasSafe_after_expand sRef.evm.memory off len
                    (x + z) sRef.evm.gasLeft
                    (logCost sRef.evm.memory.length x z 0) msf haligned
                    hsafe
                    (by
                      rw [hTsplit]
                      exact Nat.le_trans (Nat.le_add_left _ _)
                        (Nat.le_refl _)) hg
            · have happ := logRel_append sRef.evm.logs
                (expandedHost hs off len (x + z) mfrest) base msg.address []
                (readArrayBytes
                  (expandedHost hs off len (x + z) mfrest).memoryBytes
                  (off + 0 + x) z)
                (logRel_expandedHost sRef.evm.logs hs base off len (x + z)
                  mfrest hlog)
              rw [show logOf msg.address []
                  (readArrayBytes
                    (expandedHost hs off len (x + z) mfrest).memoryBytes
                    (off + 0 + x) z)
                  = log0Of sRef x z from by
                rw [logOf, log0Of, hax]
                simp only [List.map_nil, Nat.add_zero]
                rw [hread, hmemE]] at happ
              exact happ
          · push Not at hgrow
            have hzeroB : (0 : Nat) = (calculate_gas_extend_memory
                sRef.evm.memory.length [(x, z)]).expandBy := by
              rw [hexpandBy]
              have hwc := wc_mono hgrow
              have hal := haligned
              rw [memory_word_count_eq] at hwc hal ⊢
              omega
            have hmemE : logExtMemory sRef x z = sRef.evm.memory := by
              rw [logExtMemory, ← hzeroB,
                show List.replicate 0 (0x00 : EvmAsm.EL.RLP.Byte) = []
                  from rfl,
                List.append_nil]
            rw [runS_execute_log0_ok_nogrow pc_in top off len g msf hs ss l
              frest x z rest hframe hpfx htop hlim' msg hmsg hstat' hz
              hcharge hexp hreq hgrow]
            have hread := memoryRel_read sRef.evm.memory hs off len x z
              ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩ hgrow
            refine StepResultRel.success ⟨?_, ?_⟩
            · refine ⟨⟨hpost _ hframe, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
                ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, by simp [hpc], ?_⟩
              · exact ⟨hgas', hres, hsp⟩
              · refine ⟨off, len, msf, rfl, ?_, ?_⟩
                · rw [hmemE]
                  exact memoryRel_logAppend _ _ off len _ _ _
                    ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩
                · rw [hmemE]
                  exact memGasSafe_mono_gas sRef.evm.memory (Nat.sub_le _ _)
                    hsafe
            · have happ := logRel_append sRef.evm.logs hs base msg.address []
                (readArrayBytes hs.memoryBytes (off + 0 + x) z) hlog
              rw [show logOf msg.address []
                  (readArrayBytes hs.memoryBytes (off + 0 + x) z)
                  = log0Of sRef x z from by
                rw [logOf, log0Of, hax]
                simp only [List.map_nil, Nat.add_zero]
                rw [hread, hmemE]] at happ
              exact happ

end EvmSpecsVerify
