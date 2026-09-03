import EvmSpecsVerify.Relations.Calldata

/-!
# Return-data relation

SpecRef stores the previous call's returndata inline; the extraction keeps an
`OutputSlice` in the `returndata` register and bytes in `HostState.outputBytes`.
`ReturnDataRel` ties the slice window to the inline bytes. RETURNDATASIZE reads
the length, while RETURNDATACOPY first checks that the requested source range
is wholly inside this window.
-/

open private readArrayBytes outputBytesOf writeArrayBytes copySpanIntoMemory
  copyIntoMemory establishMemory from Evm.HostAxioms

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- The extraction's returndata window reads back SpecRef's bytes. -/
def ReturnDataRel (D : Bytes) (hs : Evm.HostState) (ss : SeqState) : Prop :=
  ∃ off len : Nat, ∃ f : OutputSliceFields off len,
    ss.regs.get? Register.returndata = some ⟨off, len, f⟩ ∧
    len = D.length ∧
    ∀ i, i < len → hs.outputBytes.getD (off + i) 0 = D.getD i 0

theorem returnDataRel_length (D : Bytes) (hs : Evm.HostState) (ss : SeqState)
    (hrel : ReturnDataRel D hs ss) :
    ∃ off len : Nat, ∃ f : OutputSliceFields off len,
      ss.regs.get? Register.returndata = some ⟨off, len, f⟩ ∧ len = D.length := by
  obtain ⟨off, len, f, hreg, hlen, _⟩ := hrel
  exact ⟨off, len, f, hreg, hlen⟩

/-- The host memory after copying a SpecRef returndata subrange. -/
def rdWrite (hs : Evm.HostState) (base dst : Nat) (D : Bytes)
    (src size : Nat) : Evm.HostState :=
  { hs with memoryBytes := writeArrayBytes hs.memoryBytes (base + dst) ((D.drop src).take size) }

theorem buffer_read_eq_drop_take (D : Bytes) (src size : Nat)
    (hsrc : src + size ≤ D.length) :
    buffer_read D src size = (D.drop src).take size := by
  have htakeLen : ((D.drop src).take size).length = size := by
    simp only [List.length_take, List.length_drop]
    omega
  simp [buffer_read, htakeLen]

open Evm.Functions in
/-- A bounds-checked extraction copy writes exactly the requested SpecRef
returndata bytes into the established destination range. -/
theorem returnDataRel_copy (D : Bytes) (hs : Evm.HostState) (ss : SeqState)
    (off len : Nat) (f : OutputSliceFields off len)
    (dst src size : Nat) (fr : Evm.MemoryFrame)
    (mfrest : List Evm.MemoryFrame)
    (hreg : ss.regs.get? Register.returndata = some ⟨off, len, f⟩)
    (hlen : len = D.length)
    (hbytes : ∀ i, i < len → hs.outputBytes.getD (off + i) 0 = D.getD i 0)
    (hframe : hs.memoryFrames = fr :: mfrest)
    (hest : dst + size ≤ fr.established)
    (hsrc : src + size ≤ D.length) :
    runS (Evm.Functions.returndata_copy dst src size) hs ss =
      .ok ((), rdWrite hs fr.base dst D src size) ss := by
  simp only [Evm.Functions.returndata_copy, runS_bind,
    runS_readReg _ _ _ _ hreg, Evm.Functions.output_slice_copy]
  unfold Evm.Functions.output_slice_copy_to_memory copySpanIntoMemory
    copyIntoMemory
  refine runS_bind_ok (runS_get hs ss) ?_
  simp only [outputBytesOf, OutputSliceFields.bytes, OutputSliceFields.len]
  have hwindow := window_pad_eq hs.outputBytes off len D src size hlen hbytes
  have htake := buffer_read_eq_drop_take D src size hsrc
  rw [hwindow, htake]
  refine runS_bind_ok
    (runS_establishMemory_le _ hs ss fr mfrest hframe (by
      rw [List.length_take, List.length_drop]
      omega)) ?_
  unfold rdWrite
  exact runS_modify _ _ _

open Evm.Functions in
theorem runS_returndata_size (hs : Evm.HostState) (ss : SeqState)
    (off len : Nat) (f : OutputSliceFields off len)
    (hreg : ss.regs.get? Register.returndata = some ⟨off, len, f⟩) :
    runS (Evm.Functions.returndata_size ()) hs ss = .ok (len, hs) ss := by
  simp only [Evm.Functions.returndata_size, runS_bind,
    runS_readReg _ _ _ _ hreg, OutputSliceFields.len, runS_pure]

open Evm.Functions in
theorem runS_returndata_copy_words_ok (D : Bytes) (hs : Evm.HostState)
    (ss : SeqState) (off len : Nat) (f : OutputSliceFields off len)
    (g dst src size : Nat) (fr : Evm.MemoryFrame)
    (mfrest : List Evm.MemoryFrame)
    (hreg : ss.regs.get? Register.returndata = some ⟨off, len, f⟩)
    (hlen : len = D.length)
    (hbytes : ∀ i, i < len → hs.outputBytes.getD (off + i) 0 = D.getD i 0)
    (hframe : hs.memoryFrames = fr :: mfrest)
    (hest : dst + size ≤ fr.established)
    (hsrc : src + size ≤ D.length) :
    runS (Evm.Functions.returndata_copy_words g dst src size) hs ss =
      .ok (g, rdWrite hs fr.base dst D src size) ss := by
  simp only [Evm.Functions.returndata_copy_words,
    Evm.Functions.validated_returndata_copy]
  refine runS_bind_ok (runS_returndata_size hs ss off len f hreg) ?_
  have hoff : decide (src ≤ len) = true := by
    simp only [decide_eq_true_eq]
    omega
  rw [if_pos hoff]
  have hsize : decide (size ≤ Evm.Functions.returndata_remaining len src) = true := by
    simp only [decide_eq_true_eq]
    unfold Evm.Functions.returndata_remaining
    omega
  rw [if_pos hsize]
  refine runS_bind_ok
    (returnDataRel_copy D hs ss off len f dst src size fr mfrest hreg hlen
      hbytes hframe hest hsrc) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_returndata_copy_words_oob (D : Bytes) (hs : Evm.HostState)
    (ss : SeqState) (off len : Nat) (f : OutputSliceFields off len)
    (g dst src size : Nat) (prof : ExecutionProfile)
    (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hreg : ss.regs.get? Register.returndata = some ⟨off, len, f⟩)
    (hlen : len = D.length)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hoob : D.length < src + size) :
    runS (Evm.Functions.returndata_copy_words g dst src size) hs ss =
      .ok (GAS_ZERO, hs) { ss with regs := haltRegs ss msg .InvalidOpcode } := by
  simp only [Evm.Functions.returndata_copy_words,
    Evm.Functions.validated_returndata_copy]
  refine runS_bind_ok (runS_returndata_size hs ss off len f hreg) ?_
  by_cases hoff : src ≤ D.length
  · have hoff' : decide (src ≤ len) = true := by
      simp only [decide_eq_true_eq]
      omega
    rw [if_pos hoff']
    have hsize : ¬ decide (size ≤ Evm.Functions.returndata_remaining len src) := by
      simp only [decide_eq_true_eq, not_le]
      unfold Evm.Functions.returndata_remaining
      omega
    rw [if_neg hsize]
    exact runS_exc_halt g .InvalidOpcode hs ss prof sp msg hprof hsp hmsg hfork
  · have hoff' : ¬ decide (src ≤ len) := by
      simp only [decide_eq_true_eq, not_le]
      omega
    rw [if_neg hoff']
    exact runS_exc_halt g .InvalidOpcode hs ss prof sp msg hprof hsp hmsg hfork

end EvmSpecsVerify
