import EvmSpecsVerify.Opcodes.Shapes.LivePusher
import EvmSpecsVerify.Relations.Memory

/-!
# MSIZE

The third [`live-state pusher`](Shapes/LivePusher.lean) on the SpecRef side
(`iMsize = livePushOf OPCODE_MSIZE (·.memory.length)`), but its extraction
handler threads the memory slice through its own return type, so the
`Evm`-side plumbing is written out here rather than through
`LivePushDispatch`.

The interesting content is that the two sides compute the pushed size
differently and still agree:

* SpecRef pushes `evm.memory.length` — a raw byte count that happens to be
  32-aligned, because every `extendMemory` grows by a `ceil32` block.
* The extraction pushes `32 * memory_word_count (memory_high_water mem)` —
  it rounds the *exact* established high-water mark up to whole words.

[`MemoryRel.aligned`](../Relations/Memory.lean) is exactly the bridge:
`M.length = 32 * memory_word_count len`. Without SpecRef's alignment
invariant the two would disagree on any frame whose memory is not a
multiple of 32, so this opcode is where that invariant earns its keep.

Reachable outcomes: success / stack overflow / OOG / MM-5 double fault
(charge-first on both sides); underflow is impossible for 0-in. The
success post is [`MemPost`](../Relations/Memory.lean): MSIZE reads memory
but never grows it, so the relation and the MM-6 budget both carry through
unchanged.

Gas (MM-2): `GasCosts.OPCODE_MSIZE = 2 = G_base`.
-/

open private writeListAt from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- `iMsize` is the live-state pusher for the memory size. -/
theorem iMsize_eq :
    iMsize = livePushOf GasCosts.OPCODE_MSIZE (fun e => e.memory.length) :=
  rfl

/-! ## The size both sides push -/

theorem memory_high_water_slice (off len : Nat)
    (msf : EvmMemorySliceFields off len) :
    Evm.Functions.memory_high_water ⟨off, len, msf⟩ = len := rfl

/-- Under the MM-6 budget the memory word count stays below `2^27`, so the
byte size the extraction embeds is far inside the word range. -/
theorem msize_word_bound (M : Bytes) (len gLeft : Nat)
    (haligned : M.length = 32 * Evm.Functions.memory_word_count len)
    (hsafe : MemGasSafe M gLeft) :
    Evm.Functions.memory_word_count len * 32 < 2 ^ 256 := by
  have hwlen : Evm.Functions.memory_word_count M.length
      = Evm.Functions.memory_word_count len := by
    rw [haligned, memory_word_count_eq, memory_word_count_eq]
    omega
  unfold MemGasSafe at hsafe
  rw [hwlen] at hsafe
  have hlt : Evm.Functions.memory_word_count len < 2 ^ 27 := by
    by_contra hc
    push Not at hc
    have := mem_cost_mono hc
    omega
  have : (2 : Nat) ^ 27 * 32 < 2 ^ 256 := by decide
  calc Evm.Functions.memory_word_count len * 32 < 2 ^ 27 * 32 := by omega
    _ < 2 ^ 256 := this

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- MSIZE's dispatch: the pc passes through and the handler returns the
memory slice it was given. -/
theorem msize_dispatch (pc_in : Nat) (top : StackTop) (off len : Nat)
    (msf : EvmMemorySliceFields off len) (g : Nat) :
    Evm.Functions.execute_opcode (.MSIZE ()) pc_in top ⟨off, len, msf⟩ g =
      Evm.Functions.execute_msize top ⟨off, len, msf⟩ g >>= fun p =>
        pure (pc_in, p.1, p.2.1, p.2.2) := rfl

open Evm.Functions in
theorem runS_msize_body_ok (top : StackTop) (off len : Nat)
    (msf : EvmMemorySliceFields off len) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word))
    (hframe : hs.stackFrames = l :: frest)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hwf : Evm.Functions.memory_word_count len * 32 < 2 ^ 256)
    (hgas : (G_base : Nat) ≤ g) :
    runS (Evm.Functions.execute_msize top ⟨off, len, msf⟩ g) hs ss =
      .ok ((top + BitVec.ofNat 64 1, ⟨off, len, msf⟩,
          g - G_base),
        livePushHost hs l frest top
          (Evm.Functions.memory_word_count len * 32)) ss := by
  simp only [Evm.Functions.execute_msize]
  refine runS_bind_ok (runS_charge_ok g G_base hs ss hgas) ?_
  rw [dif_neg (by simp)]
  rw [show Evm.Functions.memory_high_water ⟨off, len, msf⟩ = len from rfl]
  rw [show ((Evm.Functions.memory_word_count len : Int) * (32 : Int)).toNat
      = Evm.Functions.memory_word_count len * 32 from
    intMul_toNat _ _]
  refine runS_bind_ok
    (runS_word_of_source_byte_count _ hs ss hwf) ?_
  refine runS_bind_ok (runS_push_word top _ hs ss l frest hframe hbound) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_msize_body_oog (top : StackTop) (off len : Nat)
    (msf : EvmMemorySliceFields off len) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < (G_base : Nat)) :
    runS (Evm.Functions.execute_msize top ⟨off, len, msf⟩ g) hs ss =
      .ok ((top, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_msize]
  refine runS_bind_ok
    (runS_charge_oog g G_base hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  rw [dif_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_msize_success (pc_in : Nat) (top : StackTop)
    (off len : Nat) (msf : EvmMemorySliceFields off len) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word))
    (hframe : hs.stackFrames = l :: frest)
    (hlim : top.toNat + 1 ≤ 1024)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hwf : Evm.Functions.memory_word_count len * 32 < 2 ^ 256)
    (hgas : (G_base : Nat) ≤ g) :
    runS (Evm.Functions.execute (.MSIZE ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top + BitVec.ofNat 64 1, ⟨off, len, msf⟩, g - G_base),
        livePushHost hs l frest top
          (Evm.Functions.memory_word_count len * 32)) ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.MSIZE ()) = pure (0, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 1 hs ss (by omega)
      (by have h : top.toNat - 0 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, msize_dispatch]
  refine runS_bind_ok
    (runS_msize_body_ok top off len msf g hs ss l frest hframe hbound hwf
      hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_msize_overflow (pc_in : Nat) (top : StackTop)
    (off len : Nat) (msf : EvmMemorySliceFields off len) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hover : 1024 < top.toNat + 1) :
    runS (Evm.Functions.execute (.MSIZE ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackOverflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.MSIZE ()) = pure (0, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_overflow g top 0 1 hs ss prof sp msg hprof hsp hmsg
      hfork (by omega)
      (by have h : (1024 : Nat) < top.toNat - 0 + 1 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_msize_oog (pc_in : Nat) (top : StackTop)
    (off len : Nat) (msf : EvmMemorySliceFields off len) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hlim : top.toNat + 1 ≤ 1024)
    (hgas : g < (G_base : Nat)) :
    runS (Evm.Functions.execute (.MSIZE ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.MSIZE ()) = pure (0, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 1 hs ss (by omega)
      (by have h : top.toNat - 0 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, msize_dispatch]
  refine runS_bind_ok
    (runS_msize_body_oog top off len msf g hs ss prof sp msg hprof hsp hmsg
      hfork hgas) ?_
  exact runS_pure _ _ _

/-! ## Memory relation transfer -/

private theorem livePushHost_memoryFrames (hs : Evm.HostState)
    (l : List word) (frest : List (List word)) (top : StackTop) (w : word) :
    (livePushHost hs l frest top w).memoryFrames = hs.memoryFrames := rfl

private theorem livePushHost_memoryBytes (hs : Evm.HostState)
    (l : List word) (frest : List (List word)) (top : StackTop) (w : word) :
    (livePushHost hs l frest top w).memoryBytes = hs.memoryBytes := rfl

/-- A stack push leaves the memory window untouched, so the memory
relation transfers verbatim. -/
theorem memoryRel_livePush (M : Bytes) (hs : Evm.HostState) (off len : Nat)
    (l : List word) (frest : List (List word)) (top : StackTop) (w : word)
    (h : MemoryRel M hs off len) :
    MemoryRel M (livePushHost hs l frest top w) off len where
  frame := by rw [livePushHost_memoryFrames]; exact h.frame
  aligned := h.aligned
  bytes := by
    intro i hi
    rw [livePushHost_memoryBytes]
    exact h.bytes i hi
  tail := h.tail

/-! ## The step equivalence -/

open Evm.Functions in
/-- **MSIZE, all reachable outcomes**: success / stack overflow / OOG /
MM-5 double fault. Underflow is impossible for 0-in. SpecRef's raw
`memory.length` and the extraction's word-rounded high-water mark agree
exactly by `MemoryRel.aligned`. -/
theorem msize_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (off len : Nat)
    (msf : EvmMemorySliceFields off len) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hmem : MemoryRel sRef.evm.memory hs off len)
    (hsafe : MemGasSafe sRef.evm.memory sRef.evm.gasLeft)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel MemPost (runR iMsize sRef)
      (runS (Evm.Functions.execute (.MSIZE ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss) := by
  rw [iMsize_eq]
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  have haligned := hmem.aligned
  have hwf := msize_word_bound sRef.evm.memory len sRef.evm.gasLeft haligned
    hsafe
  have hsize : Evm.Functions.memory_word_count len * 32
      = sRef.evm.memory.length := by omega
  have hgb : (G_base : Nat) = GasCosts.OPCODE_MSIZE := rfl
  by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_MSIZE
  · rw [runR_livePushOf_oog _ _ sRef hg]
    by_cases hov : sRef.evm.stack.length = 1024
    · rw [runS_execute_msize_overflow pc_in top off len msf g hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.haltedChargeFirst (Or.inr rfl)
        (haltRegs_frame_status ss msg .StackOverflow)
    · rw [runS_execute_msize_oog pc_in top off len msf g hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)
        (by rw [hgb, hlive]; exact hg)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
  · push Not at hg
    by_cases hov : sRef.evm.stack.length = 1024
    · rw [runR_livePushOf_overflow _ _ sRef hov hg,
        runS_execute_msize_overflow pc_in top off len msf g hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.halted ErrorRel.stackOverflow
        (haltRegs_frame_status ss msg .StackOverflow)
    · have hbound : top.toNat + 1 < 2 ^ 64 := by
        have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
        omega
      rw [runR_livePushOf_success _ _ sRef hov hg,
        runS_execute_msize_success pc_in top off len msf g hs ss l frest
          hframe (by omega) hbound hwf (by rw [hgb, hlive]; exact hg)]
      have hadv : (top + BitVec.ofNat 64 1).toNat = top.toNat + 1 :=
        cursor_advance_toNat top hbound
      refine StepResultRel.success ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
        ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, by simp [hpc],
        off, len, msf, rfl, ?_, ?_⟩
      · refine ⟨⟨writeListAt l top.toNat
            (Evm.Functions.memory_word_count len * 32), frest, rfl, ?_, ?_⟩,
          ?_, ?_, ?_⟩
        · rw [hadv, take_writeListAt l top.toNat _ (by omega), hpfx]
          simp only [List.reverse_cons]
          rw [hsize]
          rfl
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
            show WordWf sRef.evm.memory.length
            unfold WordWf
            omega
          · exact hwfS w hw
      · exact ⟨by rw [hlive, hgb], hres, hsp⟩
      · exact memoryRel_livePush sRef.evm.memory hs off len l frest top _ hmem
      · exact memGasSafe_mono_gas _
          (show sRef.evm.gasLeft - GasCosts.OPCODE_MSIZE ≤ sRef.evm.gasLeft
            from Nat.sub_le _ _) hsafe

end EvmSpecsVerify
