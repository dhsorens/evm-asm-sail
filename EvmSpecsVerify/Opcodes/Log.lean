import EvmSpecsVerify.Opcodes.Mcopy
import EvmSpecsVerify.Opcodes.Return
import EvmSpecsVerify.Relations.Log

/-!
# LOG0 … LOG4

The log-emitting family, proved in one step theorem over the arity `n`.
It combines three things already proven separately — the copy family's
memory expansion, RETURN's payload slice (`active_memory_slice`), and the
log store correspondence ([`LogRel`](../Relations/Log.lean)) — with one
genuinely new order divergence.

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

## The topic operands

The two sides pop the `n` topics through different code: SpecRef runs
`(List.range n).mapM` over `stackPop`, the extraction matches on the
arity in `pop_log_topics` and builds one of the five `LogTopics`
constructors. `runR_mapM_topics_ok` handles the first by induction on the
operand list, `runS_pop_log_topics` the second by its five cases, and
`topicWords_logTopicsOf` collapses the constructor back to a list — after
which the arity is just a number and the family shares one proof.

## The charge split

SpecRef charges base + `8 * size` + `375 * n` + expansion in one
`charge_gas`. The extraction charges in **four** stages: `G_log`,
`G_logtopic * n`, the payload through `charge_word_scaled_gas`, then
expansion (`runS_charge_log_gas_*` in Representation/EvmGas.lean). For
`n = 0` the topic stage is `charge g 0` and always succeeds; for `n ≥ 1`
it is a reachable OOG state of its own.

Reachable outcomes: success ×3 (zero size / grow / in-window), underflow
(any height below `n + 2`), the static halt, OOG at any live charge
stage, plus the MM-11 double fault. Overflow is unreachable
(`n+2`-in/0-out).

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

/-! ## SpecRef run shapes

The topic pops first: SpecRef's `(List.range n).mapM` ignores its index,
so both outcomes are inductions on the operand list. -/

/-- All `n` topic operands available. -/
theorem runR_mapM_topics_ok {α : Type} (l : List α) (s : Machine)
    (ts rest : List U256) (hlen : ts.length = l.length)
    (hstack : s.evm.stack = ts ++ rest) :
    runR (l.mapM (fun _ => do pure (toBeBytes32 (← stackPop)))) s
      = .ok (.ok (ts.map toBeBytes32),
          { s with evm := { s.evm with stack := rest } }) := by
  induction l generalizing ts s with
  | nil =>
    have hts : ts = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hts
    simp only [List.mapM_nil, List.map_nil, List.nil_append] at *
    rw [runR_pure]
    rw [← hstack]
  | cons a l ih =>
    match ts with
    | [] => simp at hlen
    | t :: ts' =>
      simp only [List.mapM_cons, List.map_cons]
      have h1 : runR (do pure (toBeBytes32 (← stackPop))) s
          = .ok (.ok (toBeBytes32 t),
              { s with evm := { s.evm with stack := ts' ++ rest } }) :=
        runR_bind_ok
          (runR_stackPop_cons s t (ts' ++ rest) (by simpa using hstack))
          (runR_pure _ _)
      refine runR_bind_ok h1 ?_
      refine runR_bind_ok (ih _ _ (by simpa using hlen) (by simp)) ?_
      rw [runR_pure]

/-- The operands run out mid-block. The post-state is unobservable past
the halt, so it is existential. -/
theorem runR_mapM_topics_under {α : Type} (l : List α) (s : Machine)
    (ts : List U256) (hlen : ts.length < l.length)
    (hstack : s.evm.stack = ts) :
    ∃ s', runR (l.mapM (fun _ => do pure (toBeBytes32 (← stackPop)))) s
      = .ok (.error .stackUnderflow, s') := by
  induction l generalizing ts s with
  | nil => simp at hlen
  | cons a l ih =>
    match ts with
    | [] =>
      refine ⟨s, ?_⟩
      simp only [List.mapM_cons]
      exact runR_bind_err (runR_bind_err (runR_stackPop_nil s hstack))
    | t :: ts' =>
      have h1 : runR (do pure (toBeBytes32 (← stackPop))) s
          = .ok (.ok (toBeBytes32 t),
              { s with evm := { s.evm with stack := ts' } }) :=
        runR_bind_ok (runR_stackPop_cons s t ts' (by simpa using hstack))
          (runR_pure _ _)
      obtain ⟨s', hs'⟩ := ih { s with evm := { s.evm with stack := ts' } } ts'
        (by simpa using hlen) rfl
      refine ⟨s', ?_⟩
      simp only [List.mapM_cons]
      exact runR_bind_ok h1 (runR_bind_err hs')

/-- Underflow at any of the `n + 2` heights, in one lemma: the halt
discards the machine, so which pop failed is not observable. -/
theorem runR_iLogN_underflow (n : Nat) (s : Machine)
    (hlen : s.evm.stack.length < n + 2) :
    ∃ s', runR (iLogN n) s = .ok (.error .stackUnderflow, s') := by
  simp only [iLogN]
  match hS : s.evm.stack with
  | [] => exact ⟨s, runR_bind_err (runR_stackPop_nil s hS)⟩
  | [x] =>
    refine ⟨{ s with evm := { s.evm with stack := [] } }, ?_⟩
    refine runR_bind_ok (runR_stackPop_cons s x [] hS) ?_
    exact runR_bind_err (runR_stackPop_nil _ rfl)
  | x :: z :: tail =>
    have htail : tail.length < n := by
      rw [hS] at hlen; simp at hlen; omega
    obtain ⟨s', hs'⟩ :=
      runR_mapM_topics_under (List.range n)
        { { s with evm := { s.evm with stack := z :: tail } } with
            evm :=
              { { s.evm with stack := z :: tail } with stack := tail } }
        tail (by simpa using htail) rfl
    refine ⟨s', ?_⟩
    refine runR_bind_ok (runR_stackPop_cons s x (z :: tail) hS) ?_
    refine runR_bind_ok (runR_stackPop_cons _ z tail rfl) ?_
    exact runR_bind_err hs'

theorem runR_iLogN_oog (n : Nat) (s : Machine) (x z : U256)
    (ts rest : List U256) (hlen : ts.length = n)
    (hstack : s.evm.stack = x :: z :: (ts ++ rest))
    (hgas : s.evm.gasLeft < logCost s.evm.memory.length x z n) :
    runR (iLogN n) s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [iLogN]
  refine runR_bind_ok (runR_stackPop_cons s x (z :: (ts ++ rest)) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ z (ts ++ rest) rfl) ?_
  refine runR_bind_ok
    (runR_mapM_topics_ok (List.range n) _ ts rest (by simp [hlen]) rfl) ?_
  refine runR_bind_ok (runR_getEvm_map _ _) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _
    (by simpa [logCost] using hgas))

/-- SpecRef's memory after the metered extension: the state the payload
read and the log append see. -/
def logExtMemory (s : Machine) (x z : U256) : Bytes :=
  s.evm.memory ++ List.replicate
    (calculate_gas_extend_memory s.evm.memory.length [(x, z)]).expandBy
    0x00

/-- The record SpecRef appends. -/
def logNOf (s : Machine) (x z : U256) (ts : List U256) : Log :=
  { address := s.evm.message.currentTarget
    topics := ts.map toBeBytes32
    data := memory_read_bytes (logExtMemory s x z) x z }

/-- MM-11: the static throw fires **after** the charge and the extension. -/
theorem runR_iLogN_static (n : Nat) (s : Machine) (x z : U256)
    (ts rest : List U256) (hlen : ts.length = n)
    (hstack : s.evm.stack = x :: z :: (ts ++ rest))
    (hgas : logCost s.evm.memory.length x z n ≤ s.evm.gasLeft)
    (hstatic : s.evm.message.isStatic = true) :
    runR (iLogN n) s =
      .ok (.error .writeInStaticContext,
        { s with evm := { s.evm with
            stack := rest
            memory := logExtMemory s x z
            gasLeft := s.evm.gasLeft - logCost s.evm.memory.length x z n
            regularGasUsed :=
              s.evm.regularGasUsed
                + logCost s.evm.memory.length x z n } }) := by
  simp only [iLogN, extendMemory]
  refine runR_bind_ok (runR_stackPop_cons s x (z :: (ts ++ rest)) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ z (ts ++ rest) rfl) ?_
  refine runR_bind_ok
    (runR_mapM_topics_ok (List.range n) _ ts rest (by simp [hlen]) rfl) ?_
  refine runR_bind_ok (runR_getEvm_map _ _) ?_
  refine runR_bind_ok (runR_charge_gas _ _
    (by simpa [logCost] using hgas)) ?_
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_pos (by simpa using hstatic)]
  exact runR_bind_err (runR_throw _ _)

theorem runR_iLogN_success (n : Nat) (s : Machine) (x z : U256)
    (ts rest : List U256) (hlen : ts.length = n)
    (hstack : s.evm.stack = x :: z :: (ts ++ rest))
    (hgas : logCost s.evm.memory.length x z n ≤ s.evm.gasLeft)
    (hstatic : s.evm.message.isStatic = false) :
    runR (iLogN n) s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := rest
            memory := logExtMemory s x z
            logs := s.evm.logs ++ [logNOf s x z ts]
            gasLeft := s.evm.gasLeft - logCost s.evm.memory.length x z n
            regularGasUsed :=
              s.evm.regularGasUsed + logCost s.evm.memory.length x z n
            pc := s.evm.pc + 1 } }) := by
  simp only [iLogN, extendMemory, pcAdd]
  refine runR_bind_ok (runR_stackPop_cons s x (z :: (ts ++ rest)) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ z (ts ++ rest) rfl) ?_
  refine runR_bind_ok
    (runR_mapM_topics_ok (List.range n) _ ts rest (by simp [hlen]) rfl) ?_
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
theorem runS_execute_logn_underflow (n : Nat) (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < n + 2) :
    runS (Evm.Functions.execute (.LOG n) pc_in top ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, top, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.LOG n) = pure (n + 2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top (n + 2) 0 hs ss prof sp msg hprof
      hsp hmsg hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
/-- MM-11: in a static frame the extraction halts before popping or
charging. -/
theorem runS_execute_logn_static (n : Nat) (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hin : n + 2 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (hstatic : msg.is_static = true) :
    runS (Evm.Functions.execute (.LOG n) pc_in top ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, top, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .WriteProtection } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.LOG n) = pure (n + 2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top (n + 2) 0 hs ss hin
      (by have h : top.toNat - (n + 2) + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, log_dispatch]
  have hbody : runS (Evm.Functions.execute_log n top ⟨off, len, msf⟩ g)
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

/-- The `(offset, size)` pops that precede the topic block: the prefix and
height hypotheses for the second pop and for `pop_log_topics`. -/
private theorem logn_prologue (l : List word) (top : StackTop) (x z : word)
    (S : List word)
    (hpfx : l.take top.toNat = (x :: z :: S).reverse)
    (htop : top.toNat = (x :: z :: S).length) :
    (l.take (cursorDrop top 1).toNat = (z :: S).reverse
      ∧ (cursorDrop top 1).toNat = (z :: S).length)
    ∧ (l.take (cursorDrop top 2).toNat = S.reverse
      ∧ (cursorDrop top 2).toNat = S.length) := by
  obtain ⟨hp1, ht1⟩ := cursor_pop_step l top x (z :: S) hpfx htop
  obtain ⟨hp2, ht2⟩ := cursor_pop_step l _ z S hp1 ht1
  exact ⟨⟨hp1, ht1⟩, ⟨hp2, ht2⟩⟩

open Evm.Functions in
/-- OOG on the base charge. -/
theorem runS_execute_logn_oog_base (n : Nat) (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x z : Nat)
    (ts rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: z :: (ts ++ rest)).reverse)
    (htop : top.toNat = (x :: z :: (ts ++ rest)).length)
    (hlen : ts.length = n) (hn : n ≤ 4)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hstatic : msg.is_static = false)
    (hgas : g < G_log) :
    runS (Evm.Functions.execute (.LOG n) pc_in top ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, cursorDrop top (n + 2), ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  subst hlen
  have hnn : top.toNat = rest.length + ts.length + 2 := by simp at htop; omega
  obtain ⟨⟨hp1, ht1⟩, hp2⟩ := logn_prologue l top x z (ts ++ rest) hpfx htop
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.LOG ts.length)
      = pure (ts.length + 2, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top (ts.length + 2) 0 hs ss (by omega)
      (by have h : top.toNat - (ts.length + 2) + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, log_dispatch]
  have hbody : runS (Evm.Functions.execute_log ts.length top
      ⟨off, len, msf⟩ g) hs ss =
      .ok ((cursorDrop top (ts.length + 2),
          (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_log]
    refine runS_bind_ok (runS_guard_static_ok g hs ss msg hmsg hstatic) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (z :: (ts ++ rest)) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest z (ts ++ rest) hframe hp1 ht1) ?_
    refine runS_bind_ok
      (runS_pop_log_topics _ hs ss l frest ts rest hframe hp2.1 hp2.2 hn) ?_
    refine runS_bind_ok
      (runS_charge_log_gas_oog_base g ts.length z hs ss prof sp msg hprof hsp
        hmsg hfork hgas) ?_
    rw [dif_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
/-- OOG on the topic charge — unreachable for LOG0, where the stage
charges zero. -/
theorem runS_execute_logn_oog_topics (n : Nat) (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x z : Nat)
    (ts rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: z :: (ts ++ rest)).reverse)
    (htop : top.toNat = (x :: z :: (ts ++ rest)).length)
    (hlen : ts.length = n) (hn : n ≤ 4)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hstatic : msg.is_static = false)
    (hbase : G_log ≤ g)
    (hgas : g - G_log < G_logtopic * n) :
    runS (Evm.Functions.execute (.LOG n) pc_in top ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, cursorDrop top (n + 2), ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  subst hlen
  have hnn : top.toNat = rest.length + ts.length + 2 := by simp at htop; omega
  obtain ⟨⟨hp1, ht1⟩, hp2⟩ := logn_prologue l top x z (ts ++ rest) hpfx htop
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.LOG ts.length)
      = pure (ts.length + 2, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top (ts.length + 2) 0 hs ss (by omega)
      (by have h : top.toNat - (ts.length + 2) + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, log_dispatch]
  have hbody : runS (Evm.Functions.execute_log ts.length top
      ⟨off, len, msf⟩ g) hs ss =
      .ok ((cursorDrop top (ts.length + 2),
          (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_log]
    refine runS_bind_ok (runS_guard_static_ok g hs ss msg hmsg hstatic) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (z :: (ts ++ rest)) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest z (ts ++ rest) hframe hp1 ht1) ?_
    refine runS_bind_ok
      (runS_pop_log_topics _ hs ss l frest ts rest hframe hp2.1 hp2.2 hn) ?_
    refine runS_bind_ok
      (runS_charge_log_gas_oog_topics g ts.length z hs ss prof sp msg hprof
        hsp hmsg hfork hbase hgas) ?_
    rw [dif_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
/-- OOG on the payload charge. -/
theorem runS_execute_logn_oog_data (n : Nat) (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x z : Nat)
    (ts rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: z :: (ts ++ rest)).reverse)
    (htop : top.toNat = (x :: z :: (ts ++ rest)).length)
    (hlen : ts.length = n) (hn : n ≤ 4)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hstatic : msg.is_static = false)
    (hbase : G_log + G_logtopic * n ≤ g)
    (hgas : g - G_log - G_logtopic * n < G_logdata * z) :
    runS (Evm.Functions.execute (.LOG n) pc_in top ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, cursorDrop top (n + 2), ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  subst hlen
  have hnn : top.toNat = rest.length + ts.length + 2 := by simp at htop; omega
  obtain ⟨⟨hp1, ht1⟩, hp2⟩ := logn_prologue l top x z (ts ++ rest) hpfx htop
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.LOG ts.length)
      = pure (ts.length + 2, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top (ts.length + 2) 0 hs ss (by omega)
      (by have h : top.toNat - (ts.length + 2) + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, log_dispatch]
  have hbody : runS (Evm.Functions.execute_log ts.length top
      ⟨off, len, msf⟩ g) hs ss =
      .ok ((cursorDrop top (ts.length + 2),
          (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_log]
    refine runS_bind_ok (runS_guard_static_ok g hs ss msg hmsg hstatic) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (z :: (ts ++ rest)) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest z (ts ++ rest) hframe hp1 ht1) ?_
    refine runS_bind_ok
      (runS_pop_log_topics _ hs ss l frest ts rest hframe hp2.1 hp2.2 hn) ?_
    refine runS_bind_ok
      (runS_charge_log_gas_oog_data g ts.length z hs ss prof sp msg hprof hsp
        hmsg hfork hbase hgas) ?_
    rw [dif_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
/-- OOG on the expansion charge, the last of the three (four for `n ≥ 1`)
stages. -/
theorem runS_execute_logn_oog_exp (n : Nat) (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x z : Nat)
    (ts rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: z :: (ts ++ rest)).reverse)
    (htop : top.toNat = (x :: z :: (ts ++ rest)).length)
    (hlen : ts.length = n) (hn : n ≤ 4)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hstatic : msg.is_static = false)
    (hcharge : G_log + G_logtopic * n + G_logdata * z ≤ g)
    (hgas : g - G_log - G_logtopic * n - G_logdata * z
      < Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
          (Evm.Functions.memory_required_size x z)) :
    runS (Evm.Functions.execute (.LOG n) pc_in top ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, cursorDrop top (n + 2), ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  subst hlen
  have hnn : top.toNat = rest.length + ts.length + 2 := by simp at htop; omega
  obtain ⟨⟨hp1, ht1⟩, hp2⟩ := logn_prologue l top x z (ts ++ rest) hpfx htop
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.LOG ts.length)
      = pure (ts.length + 2, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top (ts.length + 2) 0 hs ss (by omega)
      (by have h : top.toNat - (ts.length + 2) + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, log_dispatch]
  have hbody : runS (Evm.Functions.execute_log ts.length top
      ⟨off, len, msf⟩ g) hs ss =
      .ok ((cursorDrop top (ts.length + 2),
          (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_log]
    refine runS_bind_ok (runS_guard_static_ok g hs ss msg hmsg hstatic) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (z :: (ts ++ rest)) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest z (ts ++ rest) hframe hp1 ht1) ?_
    refine runS_bind_ok
      (runS_pop_log_topics _ hs ss l frest ts rest hframe hp2.1 hp2.2 hn) ?_
    refine runS_bind_ok
      (runS_charge_log_gas_ok g ts.length z hs ss hcharge) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_charge_oog _ _ hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
    rw [dif_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

/-- The host state after an emission: one row appended, its payload copied
out of the (already expanded) memory window. -/
def logNHost (hs : Evm.HostState) (a : Evm.Defs.address) (ts : List word)
    (b z : Nat) : Evm.HostState :=
  logAppend hs a ts (readArrayBytes hs.memoryBytes b z)

open Evm.Functions in
/-- Zero-size success: no expansion, and the emitted payload is empty on
both sides. -/
theorem runS_execute_logn_ok_zero (n : Nat) (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : Nat)
    (ts rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: (0 : Nat) :: (ts ++ rest)).reverse)
    (htop : top.toNat = (x :: (0 : Nat) :: (ts ++ rest)).length)
    (hlen : ts.length = n) (hn : n ≤ 4)
    (hlim : top.toNat ≤ 1024)
    (msg : Evm.Defs.Message)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hstatic : msg.is_static = false)
    (hcharge : G_log + G_logtopic * n + G_logdata * 0 ≤ g) :
    runS (Evm.Functions.execute (.LOG n) pc_in top ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, cursorDrop top (n + 2), ⟨off, len, msf⟩,
          g - G_log - G_logtopic * n - G_logdata * 0),
        logNHost hs msg.address ts 0 0) ss := by
  subst hlen
  have htw : topicWords (logTopicsOf ts) = ts := topicWords_logTopicsOf ts hn
  have hnn : top.toNat = rest.length + ts.length + 2 := by simp at htop; omega
  obtain ⟨⟨hp1, ht1⟩, hp2⟩ :=
    logn_prologue l top x 0 (ts ++ rest) hpfx htop
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.LOG ts.length)
      = pure (ts.length + 2, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top (ts.length + 2) 0 hs ss (by omega)
      (by have h : top.toNat - (ts.length + 2) + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, log_dispatch]
  have hbody : runS (Evm.Functions.execute_log ts.length top
      ⟨off, len, msf⟩ g) hs ss =
      .ok ((cursorDrop top (ts.length + 2),
          (⟨off, len, msf⟩ : EvmMemorySlice),
          g - G_log - G_logtopic * ts.length - G_logdata * 0),
        logNHost hs msg.address ts 0 0) ss := by
    simp only [Evm.Functions.execute_log]
    refine runS_bind_ok (runS_guard_static_ok g hs ss msg hmsg hstatic) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x ((0 : Nat) :: (ts ++ rest)) hframe hpfx
        htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest (0 : Nat) (ts ++ rest) hframe hp1 ht1) ?_
    refine runS_bind_ok
      (runS_pop_log_topics _ hs ss l frest ts rest hframe hp2.1 hp2.2 hn) ?_
    refine runS_bind_ok
      (runS_charge_log_gas_ok g ts.length 0 hs ss hcharge) ?_
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
      (runS_k_log_memory msg.address (logTopicsOf ts)
        ⟨0, 0, evm_memory_slice 0 0⟩ (readArrayBytes hs.memoryBytes 0 0) hs
        ss rfl) ?_
    rw [htw]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
/-- Success with expansion: the window grows to `x + z`, then the payload
is read out of it and emitted. -/
theorem runS_execute_logn_ok_grow (n : Nat) (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x z : Nat)
    (ts rest : List word) (mfrest : List Evm.MemoryFrame)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: z :: (ts ++ rest)).reverse)
    (htop : top.toNat = (x :: z :: (ts ++ rest)).length)
    (hlen : ts.length = n) (hn : n ≤ 4)
    (hlim : top.toNat ≤ 1024)
    (hmframe : hs.memoryFrames
      = ({ base := off, established := len } : Evm.MemoryFrame) :: mfrest)
    (msg : Evm.Defs.Message)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hstatic : msg.is_static = false)
    (hz : (z == 0) = false)
    (hcharge : G_log + G_logtopic * n + G_logdata * z ≤ g)
    (hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + z)
      ≤ g - G_log - G_logtopic * n - G_logdata * z)
    (hreq : x + z ≤ 2 ^ 32 - 32)
    (hgrow : len < x + z) :
    runS (Evm.Functions.execute (.LOG n) pc_in top ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, cursorDrop top (n + 2),
          (⟨off, x + z, {}⟩ : EvmMemorySlice),
          g - G_log - G_logtopic * n - G_logdata * z
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + z)),
        logNHost (expandedHost hs off len (x + z) mfrest) msg.address ts
          (off + 0 + x) z) ss := by
  subst hlen
  have htw : topicWords (logTopicsOf ts) = ts := topicWords_logTopicsOf ts hn
  have hnn : top.toNat = rest.length + ts.length + 2 := by simp at htop; omega
  obtain ⟨⟨hp1, ht1⟩, hp2⟩ :=
    logn_prologue l top x z (ts ++ rest) hpfx htop
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.LOG ts.length)
      = pure (ts.length + 2, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top (ts.length + 2) 0 hs ss (by omega)
      (by have h : top.toNat - (ts.length + 2) + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, log_dispatch]
  have hbody : runS (Evm.Functions.execute_log ts.length top
      ⟨off, len, msf⟩ g) hs ss =
      .ok ((cursorDrop top (ts.length + 2),
          (⟨off, x + z, {}⟩ : EvmMemorySlice),
          g - G_log - G_logtopic * ts.length - G_logdata * z
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + z)),
        logNHost (expandedHost hs off len (x + z) mfrest) msg.address ts
          (off + 0 + x) z) ss := by
    simp only [Evm.Functions.execute_log]
    refine runS_bind_ok (runS_guard_static_ok g hs ss msg hmsg hstatic) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (z :: (ts ++ rest)) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest z (ts ++ rest) hframe hp1 ht1) ?_
    refine runS_bind_ok
      (runS_pop_log_topics _ hs ss l frest ts rest hframe hp2.1 hp2.2 hn) ?_
    refine runS_bind_ok
      (runS_charge_log_gas_ok g ts.length z hs ss hcharge) ?_
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
      (runS_k_log_memory msg.address (logTopicsOf ts)
        ⟨off + 0 + x, z, evm_memory_slice (off + 0 + x) z⟩
        (readArrayBytes (expandedHost hs off len (x + z) mfrest).memoryBytes
          (off + 0 + x) z)
        (expandedHost hs off len (x + z) mfrest) ss rfl) ?_
    rw [htw]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
/-- Success inside the established window: no expansion. -/
theorem runS_execute_logn_ok_nogrow (n : Nat) (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x z : Nat)
    (ts rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: z :: (ts ++ rest)).reverse)
    (htop : top.toNat = (x :: z :: (ts ++ rest)).length)
    (hlen : ts.length = n) (hn : n ≤ 4)
    (hlim : top.toNat ≤ 1024)
    (msg : Evm.Defs.Message)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hstatic : msg.is_static = false)
    (hz : (z == 0) = false)
    (hcharge : G_log + G_logtopic * n + G_logdata * z ≤ g)
    (hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + z)
      ≤ g - G_log - G_logtopic * n - G_logdata * z)
    (hreq : x + z ≤ 2 ^ 32 - 32)
    (hgrow : x + z ≤ len) :
    runS (Evm.Functions.execute (.LOG n) pc_in top ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, cursorDrop top (n + 2), (⟨off, len, msf⟩ : EvmMemorySlice),
          g - G_log - G_logtopic * n - G_logdata * z
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + z)),
        logNHost hs msg.address ts (off + 0 + x) z) ss := by
  subst hlen
  have htw : topicWords (logTopicsOf ts) = ts := topicWords_logTopicsOf ts hn
  have hnn : top.toNat = rest.length + ts.length + 2 := by simp at htop; omega
  obtain ⟨⟨hp1, ht1⟩, hp2⟩ :=
    logn_prologue l top x z (ts ++ rest) hpfx htop
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.LOG ts.length)
      = pure (ts.length + 2, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top (ts.length + 2) 0 hs ss (by omega)
      (by have h : top.toNat - (ts.length + 2) + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, log_dispatch]
  have hbody : runS (Evm.Functions.execute_log ts.length top
      ⟨off, len, msf⟩ g) hs ss =
      .ok ((cursorDrop top (ts.length + 2),
          (⟨off, len, msf⟩ : EvmMemorySlice),
          g - G_log - G_logtopic * ts.length - G_logdata * z
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + z)),
        logNHost hs msg.address ts (off + 0 + x) z) ss := by
    simp only [Evm.Functions.execute_log]
    refine runS_bind_ok (runS_guard_static_ok g hs ss msg hmsg hstatic) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (z :: (ts ++ rest)) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest z (ts ++ rest) hframe hp1 ht1) ?_
    refine runS_bind_ok
      (runS_pop_log_topics _ hs ss l frest ts rest hframe hp2.1 hp2.2 hn) ?_
    refine runS_bind_ok
      (runS_charge_log_gas_ok g ts.length z hs ss hcharge) ?_
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
      (runS_k_log_memory msg.address (logTopicsOf ts)
        ⟨off + 0 + x, z, evm_memory_slice (off + 0 + x) z⟩
        (readArrayBytes hs.memoryBytes (off + 0 + x) z) hs ss rfl) ?_
    rw [htw]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

/-! ## The step equivalence -/

open Evm.Functions in
/-- **LOG0 … LOG4, all reachable outcomes**: success (zero size / grow /
in-window), underflow at any height below `n + 2`, the static halt, OOG at
any live charge stage, and the MM-11 double fault. `hstatic` and `haddr`
are `message`-register ties (the same `haddr` ADDRESS and SLOAD use);
`base` is the frame's log-store base index. -/
theorem logn_step_equiv (n : Nat) (hn : n ≤ 4) (sRef : Machine)
    (top : StackTop) (g : Nat)
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
    StepResultRel (LogPost base) (runR (iLogN n) sRef)
      (runS (Evm.Functions.execute (.LOG n) pc_in top ⟨off, len, msf⟩ g)
        hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ :=
    hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  have hst : msg.is_static = sRef.evm.message.isStatic := hstatic msg hmsg
  have hax : msg.address.toList = sRef.evm.message.currentTarget :=
    haddr msg hmsg
  by_cases hunder : sRef.evm.stack.length < n + 2
  · obtain ⟨s', hs'⟩ := runR_iLogN_underflow n sRef hunder
    rw [hs',
      runS_execute_logn_underflow n pc_in top off len g msf hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by rw [htop]; exact hunder)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  · push Not at hunder
    obtain ⟨x, z, tail, hS⟩ :
        ∃ x z tail, sRef.evm.stack = x :: z :: tail := by
      match hSm : sRef.evm.stack with
      | [] => rw [hSm] at hunder; simp only [List.length_nil] at hunder; omega
      | [x] =>
        rw [hSm] at hunder
        simp only [List.length_cons, List.length_nil] at hunder
        omega
      | x :: z :: tail => exact ⟨x, z, tail, rfl⟩
    have htlen : n ≤ tail.length := by
      rw [hS] at hunder; simp only [List.length_cons] at hunder; omega
    obtain ⟨ts, rest, htsl, htail⟩ :
        ∃ ts rest, ts.length = n ∧ tail = ts ++ rest :=
      ⟨tail.take n, tail.drop n, by simp; omega,
        (List.take_append_drop n tail).symm⟩
    rw [htail] at hS
    rw [hS] at hpfx htop hlim hwfS
    have hnn : top.toNat = ts.length + rest.length + 2 := by
      simp only [List.length_cons, List.length_append] at htop; omega
    have hin2 : n + 2 ≤ top.toNat := by omega
    have hlim' : top.toNat ≤ 1024 := by
      simp only [List.length_cons, List.length_append] at hlim; omega
    obtain ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail'⟩ := hmem
    have hcost : (calculate_gas_extend_memory sRef.evm.memory.length
        [(x, z)]).cost
        = Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
            (Evm.Functions.memory_required_size x z) :=
      extend_cost_eq sRef.evm.memory off len x z msf haligned
    have hTsplit : logCost sRef.evm.memory.length x z n
        = 375 + 8 * z + 375 * n
          + Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
              (Evm.Functions.memory_required_size x z) := by
      rw [logCost, ← hcost]
      rfl
    -- MM-11: the static guard fires first on the extraction side
    by_cases hstat : sRef.evm.message.isStatic = true
    · have hstat' : msg.is_static = true := by rw [hst]; exact hstat
      rw [runS_execute_logn_static n pc_in top off len g msf hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hin2 hlim' hstat']
      by_cases hg : sRef.evm.gasLeft < logCost sRef.evm.memory.length x z n
      · rw [runR_iLogN_oog n sRef x z ts rest htsl hS hg]
        exact StepResultRel.haltedChargeFirst
          (Or.inr (Or.inr (Or.inr rfl)))
          (haltRegs_frame_status ss msg .WriteProtection)
      · push Not at hg
        rw [runR_iLogN_static n sRef x z ts rest htsl hS hg hstat]
        exact StepResultRel.halted ErrorRel.writeInStaticContext
          (haltRegs_frame_status ss msg .WriteProtection)
    · have hstat0 : sRef.evm.message.isStatic = false := by
        simpa using hstat
      have hstat' : msg.is_static = false := by rw [hst]; exact hstat0
      by_cases hg : sRef.evm.gasLeft < logCost sRef.evm.memory.length x z n
      · rw [runR_iLogN_oog n sRef x z ts rest htsl hS hg]
        rw [hTsplit, ← hlive] at hg
        have hgN : g < 375 + 8 * z + 375 * n
            + Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                (Evm.Functions.memory_required_size x z) := hg
        by_cases hb : g < G_log
        · rw [runS_execute_logn_oog_base n pc_in top off len g msf hs ss l
            frest x z ts rest hframe hpfx htop htsl hn hlim' prof
            sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hstat' hb]
          exact StepResultRel.halted ErrorRel.outOfGas
            (haltRegs_frame_status ss msg .OutOfGas)
        · push Not at hb
          have hbN : (375 : Nat) ≤ g := hb
          by_cases htp : g - G_log < G_logtopic * n
          · rw [runS_execute_logn_oog_topics n pc_in top off len g msf hs ss l
              frest x z ts rest hframe hpfx htop htsl hn hlim' prof
              sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hstat' hb htp]
            exact StepResultRel.halted ErrorRel.outOfGas
              (haltRegs_frame_status ss msg .OutOfGas)
          · push Not at htp
            have htpN : (375 : Nat) * n ≤ g - 375 := htp
            by_cases hc : g - G_log - G_logtopic * n < G_logdata * z
            · rw [runS_execute_logn_oog_data n pc_in top off len g msf hs ss l
                frest x z ts rest hframe hpfx htop htsl hn hlim' prof
                sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hstat'
                (by show (375 : Nat) + 375 * n ≤ g; omega) hc]
              exact StepResultRel.halted ErrorRel.outOfGas
                (haltRegs_frame_status ss msg .OutOfGas)
            · push Not at hc
              have hcN : (8 : Nat) * z ≤ g - 375 - 375 * n := hc
              rw [runS_execute_logn_oog_exp n pc_in top off len g msf hs ss l
                frest x z ts rest hframe hpfx htop htsl hn hlim' prof
                sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hstat'
                (by show (375 : Nat) + 375 * n + 8 * z ≤ g; omega)
                (by
                  show g - 375 - 375 * n - 8 * z < _
                  rw [show g - 375 - 375 * n - 8 * z
                      = g - (375 + 8 * z + 375 * n) from by omega,
                    Nat.sub_lt_iff_lt_add (by omega)]
                  exact lt_of_lt_of_le hgN (le_of_eq (by ring)))]
              exact StepResultRel.halted ErrorRel.outOfGas
                (haltRegs_frame_status ss msg .OutOfGas)
      · push Not at hg
        have hgT : 375 + 8 * z + 375 * n
            + Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                (Evm.Functions.memory_required_size x z) ≤ g := by
          rw [← hTsplit]
          show logCost sRef.evm.memory.length x z n ≤ g
          rw [hlive]
          exact hg
        have hcharge : G_log + G_logtopic * n + G_logdata * z ≤ g := by
          show (375 : Nat) + 375 * n + 8 * z ≤ g
          rw [show (375 : Nat) + 375 * n + 8 * z = 375 + 8 * z + 375 * n
            from by ring]
          exact Nat.le_trans (Nat.le_add_right _ _) hgT
        have hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
            (Evm.Functions.memory_required_size x z)
            ≤ g - G_log - G_logtopic * n - G_logdata * z := by
          show _ ≤ g - 375 - 375 * n - 8 * z
          rw [show g - 375 - 375 * n - 8 * z = g - (375 + 8 * z + 375 * n)
            from by omega]
          exact Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hgT)
        have hretN : (cursorDrop top (n + 2)).toNat = rest.length := by
          rw [cursorDrop_toNat top (n + 2) (by omega)]
          omega
        obtain ⟨⟨hp1, ht1⟩, hp2⟩ :=
          logn_prologue l top x z (ts ++ rest) hpfx htop
        have hp2' : l.take (rest.length + ts.length)
            = (ts ++ rest).reverse := by
          rw [show rest.length + ts.length = (cursorDrop top 2).toNat from by
            rw [hp2.2]; simp; omega]
          exact hp2.1
        have hpfxN : l.take rest.length = rest.reverse :=
          take_shrink_list l ts rest rest.length hp2' rfl
        have hpost := fun (hs' : Evm.HostState)
            (hframe' : hs'.stackFrames = l :: frest) =>
          (⟨⟨l, frest, hframe', by rw [hretN]; exact hpfxN, by
              rw [hretN]; omega⟩,
            by rw [hretN],
            by
              simp only [List.length_cons, List.length_append] at hlim
              omega,
            fun w hw => hwfS w (by simp [hw])⟩ :
            StackRel rest hs' (cursorDrop top (n + 2)))
        have hgas' : g - 375 - 375 * n - 8 * z
              - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                  (Evm.Functions.memory_required_size x z)
            = (sRef.evm.gasLeft : Nat)
              - logCost sRef.evm.memory.length x z n := by
          rw [hTsplit, ← hlive, Nat.sub_sub, Nat.sub_sub, Nat.sub_sub]
          congr 1
          ring
        rw [runR_iLogN_success n sRef x z ts rest htsl hS hg hstat0]
        by_cases hz0 : z = 0
        · subst hz0
          have hzero : (calculate_gas_extend_memory sRef.evm.memory.length
              [(x, 0)]) = { cost := 0, expandBy := 0 } := by
            rw [calc_extend_single]
            rfl
          have hcost0 : logCost sRef.evm.memory.length x 0 n
              = 375 + 375 * n := by
            rw [logCost, hzero]
            show 375 + 8 * 0 + 375 * n + 0 = 375 + 375 * n
            omega
          have hmem0 : logExtMemory sRef x 0 = sRef.evm.memory := by
            rw [logExtMemory, hzero,
              show (({ cost := 0, expandBy := 0 } :
                EvmAsm.Stateless.SpecRef.ExtendMemory).expandBy : Nat) = 0
                from rfl,
              show List.replicate 0 (0x00 : EvmAsm.EL.RLP.Byte) = [] from rfl,
              List.append_nil]
          rw [runS_execute_logn_ok_zero n pc_in top off len g msf hs ss l
            frest x ts rest hframe hpfx htop htsl hn hlim' msg hmsg hstat'
            hcharge]
          refine StepResultRel.success ⟨?_, ?_⟩
          · refine ⟨⟨hpost _ hframe, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
              ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, by simp [hpc], ?_⟩
            · refine ⟨?_, hres, hsp⟩
              show g - 375 - 375 * n - 8 * 0
                = sRef.evm.gasLeft - logCost sRef.evm.memory.length x 0 n
              rw [hcost0, ← hlive]
              omega
            · refine ⟨off, len, msf, rfl, ?_, ?_⟩
              · rw [hmem0]
                exact memoryRel_logAppend _ _ off len _ _ _
                  ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail'⟩
              · rw [hmem0]
                exact memGasSafe_mono_gas sRef.evm.memory (Nat.sub_le _ _)
                  hsafe
          · have happ := logRel_append sRef.evm.logs hs base msg.address ts
              (readArrayBytes hs.memoryBytes 0 0) hlog
            rw [show logOf msg.address ts (readArrayBytes hs.memoryBytes 0 0)
                = logNOf sRef x 0 ts from by
              rw [logOf, logNOf, hax, hmem0]
              simp [readArrayBytes, memory_read_bytes]] at happ
            exact happ
        · have hz : (z == 0) = false := by simpa using hz0
          rw [mcopy_required_size_pos x z hz] at hcost hTsplit hexp hgas'
          have hreq : x + z ≤ 2 ^ 32 - 32 :=
            safe_required_bound sRef.evm.memory off len (x + z)
              (g - G_log - G_logtopic * n - G_logdata * z)
              sRef.evm.gasLeft msf haligned hsafe
              (by show g - 375 - 375 * n - 8 * z ≤ sRef.evm.gasLeft
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
            rw [runS_execute_logn_ok_grow n pc_in top off len g msf hs ss l
              frest x z ts rest mfrest hframe hpfx htop htsl hn hlim' hmframe
              msg hmsg hstat' hz hcharge hexp hreq hgrow]
            have hrel' := memoryRel_expand sRef.evm.memory hs off len
              (x + z) mfrest
              ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail'⟩ hgrow
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
                    - logCost sRef.evm.memory.length x z n)
                  rw [hmemE]
                  exact memGasSafe_after_expand sRef.evm.memory off len
                    (x + z) sRef.evm.gasLeft
                    (logCost sRef.evm.memory.length x z n) msf haligned
                    hsafe
                    (by
                      rw [hTsplit]
                      exact Nat.le_trans (Nat.le_add_left _ _)
                        (Nat.le_refl _)) hg
            · have happ := logRel_append sRef.evm.logs
                (expandedHost hs off len (x + z) mfrest) base msg.address ts
                (readArrayBytes
                  (expandedHost hs off len (x + z) mfrest).memoryBytes
                  (off + 0 + x) z)
                (logRel_expandedHost sRef.evm.logs hs base off len (x + z)
                  mfrest hlog)
              rw [show logOf msg.address ts
                  (readArrayBytes
                    (expandedHost hs off len (x + z) mfrest).memoryBytes
                    (off + 0 + x) z)
                  = logNOf sRef x z ts from by
                rw [logOf, logNOf, hax]
                simp only [Nat.add_zero]
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
            rw [runS_execute_logn_ok_nogrow n pc_in top off len g msf hs ss l
              frest x z ts rest hframe hpfx htop htsl hn hlim' msg hmsg
              hstat' hz hcharge hexp hreq hgrow]
            have hread := memoryRel_read sRef.evm.memory hs off len x z
              ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail'⟩ hgrow
            refine StepResultRel.success ⟨?_, ?_⟩
            · refine ⟨⟨hpost _ hframe, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
                ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, by simp [hpc], ?_⟩
              · exact ⟨hgas', hres, hsp⟩
              · refine ⟨off, len, msf, rfl, ?_, ?_⟩
                · rw [hmemE]
                  exact memoryRel_logAppend _ _ off len _ _ _
                    ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail'⟩
                · rw [hmemE]
                  exact memGasSafe_mono_gas sRef.evm.memory (Nat.sub_le _ _)
                    hsafe
            · have happ := logRel_append sRef.evm.logs hs base msg.address ts
                (readArrayBytes hs.memoryBytes (off + 0 + x) z) hlog
              rw [show logOf msg.address ts
                  (readArrayBytes hs.memoryBytes (off + 0 + x) z)
                  = logNOf sRef x z ts from by
                rw [logOf, logNOf, hax]
                simp only [Nat.add_zero]
                rw [hread, hmemE]] at happ
              exact happ

/-- LOG0, the arity with no topic operands. -/
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
        hs ss) :=
  logn_step_equiv 0 (by omega) sRef top g hs ss off len msf pc_in base hrel
    hmem hsafe hlog hpc haddr hstatic

end EvmSpecsVerify
