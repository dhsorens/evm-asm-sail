import EvmSpecsVerify.Relations.Memory
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# MLOAD

First memory opcode. `iMload` pops the offset, charges base + quadratic
expansion in one `charge_gas`, extends by SpecRef's ceil32 block, reads 32
bytes and pushes; `execute_mload` charges the base *before* popping, then
charges the expansion separately, establishes the exact byte mark, and reads
through the frame window. The single vs split charge is unobservable
(`g < base + cost ↔ g < base ∨ g - base < cost`), the ceil32 vs exact growth
is bridged by [`MemoryRel`](../Relations/Memory.lean)'s alignment tail, and
the expansion charges agree by `extend_cost_eq`. The u32 range check in
`memory_access` is discharged from the **MM-6** `MemGasSafe` budget
(`safe_required_bound`). Reachable outcomes: success (grow / in-window) /
underflow / OOG at either charge; overflow unreachable for 1-in/1-out.
-/

open private pcAdd chargeWithMemory from EvmAsm.Stateless.SpecRef.InstructionsCore
open private writeListAt from Evm.HostAxioms
open private bytesToWord zeroMemoryRange from Evm.HostAxioms

set_option maxHeartbeats 4000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- The SpecRef MLOAD charge for offset `x` against memory size `msz`. -/
def mloadCost (msz x : Nat) : Nat :=
  GasCosts.OPCODE_MLOAD_BASE
    + (calculate_gas_extend_memory msz [(x, 32)]).cost

theorem memory_required_size_32 (x : Nat) :
    Evm.Functions.memory_required_size x (Evm.Functions.u256 32)
      = x + 32 := rfl

/-- A 32-byte in-range read decodes to a well-formed word. -/
theorem loadVal_wf (M : Bytes) (pos : Nat) (h : pos + 32 ≤ M.length) :
    WordWf (bytesBEtoNat (memory_read_bytes M pos 32)) := by
  unfold WordWf
  have h1 := EvmAsm.EL.RLP.Nat.fromBytesBE_lt (memory_read_bytes M pos 32)
  rw [memory_read_bytes_length M pos 32 h] at h1
  calc bytesBEtoNat (memory_read_bytes M pos 32) < 256 ^ 32 := h1
    _ = 2 ^ 256 := by decide

/-! ## SpecRef run shapes -/

theorem runR_iMload_underflow (s : Machine) (hstack : s.evm.stack = []) :
    runR iMload s = .ok (.error .stackUnderflow, s) := by
  simp only [iMload]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_iMload_oog (s : Machine) (x : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: rest)
    (hgas : s.evm.gasLeft < mloadCost s.evm.memory.length x) :
    runR iMload s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [iMload, chargeWithMemory]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  exact runR_bind_err (runR_bind_ok (runR_getEvm_map _ _)
    (runR_bind_err (runR_charge_gas_oog _ _
      (by simpa [mloadCost] using hgas))))

theorem runR_iMload_success (s : Machine) (x : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: rest)
    (hlim : s.evm.stack.length ≤ 1024)
    (hgas : mloadCost s.evm.memory.length x ≤ s.evm.gasLeft) :
    runR iMload s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := bytesBEtoNat (memory_read_bytes
              (s.evm.memory ++ List.replicate
                (calculate_gas_extend_memory s.evm.memory.length
                  [(x, 32)]).expandBy 0x00) x 32) :: rest
            memory := s.evm.memory ++ List.replicate
              (calculate_gas_extend_memory s.evm.memory.length
                [(x, 32)]).expandBy 0x00
            gasLeft := s.evm.gasLeft - mloadCost s.evm.memory.length x
            regularGasUsed :=
              s.evm.regularGasUsed + mloadCost s.evm.memory.length x
            pc := s.evm.pc + 1 } }) := by
  have hlen : rest.length ≠ 1024 := by
    rw [hstack] at hlim
    simp at hlim
    omega
  simp only [iMload, chargeWithMemory, extendMemory, pcAdd]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_bind_ok (runR_getEvm_map _ _)
    (runR_bind_ok (runR_charge_gas _ _ (by simpa [mloadCost] using hgas))
      (runR_modifyEvm _ _))) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_stackPush _ _ (by simpa using hlen)) ?_
  exact runR_modifyEvm _ _

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for MLOAD (threads its own memory cursor). -/
theorem mload_dispatch (pc_in : Nat) (top : StackTop) (off len : Nat)
    (msf : EvmMemorySliceFields off len) (g : Nat) :
    Evm.Functions.execute_opcode (.MLOAD ()) pc_in top ⟨off, len, msf⟩ g =
      Evm.Functions.execute_mload top ⟨off, len, msf⟩ g >>= fun p =>
        pure (pc_in, p.1, p.2.1, p.2.2) := rfl

open Evm.Functions in
theorem runS_execute_mload_underflow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 1) :
    runS (Evm.Functions.execute (.MLOAD ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.MLOAD ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 1 1 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_mload_oog_base (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hin : 1 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (hgas : g < G_verylow) :
    runS (Evm.Functions.execute (.MLOAD ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.MLOAD ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 1 hs ss hin
      (by have h : top.toNat - 1 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, mload_dispatch]
  have hbody : runS (Evm.Functions.execute_mload top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top, (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_mload]
    refine runS_bind_ok
      (runS_charge_oog g G_verylow hs ss prof sp msg hprof hsp hmsg hfork
        hgas) ?_
    rw [dif_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
theorem runS_execute_mload_oog_exp (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : Nat) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hbase : G_verylow ≤ g)
    (hgas : g - G_verylow
      < Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + 32)) :
    runS (Evm.Functions.execute (.MLOAD ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.MLOAD ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 1 hs ss (by simp at htop; omega)
      (by have h : top.toNat - 1 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, mload_dispatch]
  have hbody : runS (Evm.Functions.execute_mload top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1, (⟨off, len, msf⟩ : EvmMemorySlice),
          GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_mload]
    refine runS_bind_ok (runS_charge_ok g G_verylow hs ss hbase) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x rest hframe hpfx htop) ?_
    rw [memory_required_size_32]
    refine runS_bind_ok
      (runS_charge_oog (g - G_verylow) _ hs ss prof sp msg hprof hsp hmsg
        hfork hgas) ?_
    rw [dif_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
theorem runS_execute_mload_ok_grow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : Nat) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (mfrest : List Evm.MemoryFrame)
    (hmframe : hs.memoryFrames
      = ({ base := off, established := len } : Evm.MemoryFrame) :: mfrest)
    (hbase : G_verylow ≤ g)
    (hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + 32)
      ≤ g - G_verylow)
    (hreq : x + 32 ≤ 2 ^ 32 - 32)
    (hgrow : len < x + 32) :
    runS (Evm.Functions.execute (.MLOAD ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top, (⟨off, x + 32, {}⟩ : EvmMemorySlice),
          g - G_verylow
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + 32)),
        { hs with
          memoryBytes :=
            zeroMemoryRange hs.memoryBytes (off + len) (x + 32 - len)
          memoryFrames :=
            ({ base := off, established := x + 32 } : Evm.MemoryFrame)
              :: mfrest
          stackFrames := writeListAt l (top.toNat - 1)
            (bytesToWord ((List.range 32).map fun i =>
              if x + i < x + 32 then
                (zeroMemoryRange hs.memoryBytes (off + len)
                  (x + 32 - len)).getD (off + x + i) 0
              else 0)) :: frest }) ss := by
  have hn : top.toNat = rest.length + 1 := by simpa using htop
  have hbound := top.isLt
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.MLOAD ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 1 hs ss (by omega)
      (by have h : top.toNat - 1 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, mload_dispatch]
  have hbody : runS (Evm.Functions.execute_mload top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top, (⟨off, x + 32, {}⟩ : EvmMemorySlice),
          g - G_verylow
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + 32)),
        { hs with
          memoryBytes :=
            zeroMemoryRange hs.memoryBytes (off + len) (x + 32 - len)
          memoryFrames :=
            ({ base := off, established := x + 32 } : Evm.MemoryFrame)
              :: mfrest
          stackFrames := writeListAt l (top.toNat - 1)
            (bytesToWord ((List.range 32).map fun i =>
              if x + i < x + 32 then
                (zeroMemoryRange hs.memoryBytes (off + len)
                  (x + 32 - len)).getD (off + x + i) 0
              else 0)) :: frest }) ss := by
    simp only [Evm.Functions.execute_mload]
    refine runS_bind_ok (runS_charge_ok g G_verylow hs ss hbase) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x rest hframe hpfx htop) ?_
    rw [memory_required_size_32]
    refine runS_bind_ok (runS_charge_ok (g - G_verylow) _ hs ss hexp) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_memory_access_ok x 32 hs ss (by decide)
        (show x ≤ 2 ^ 32 - 1 by omega)
        (show (32 : Nat) ≤ 2 ^ 32 - 1 - x by omega)) ?_
    refine runS_bind_ok
      (runS_expand_memory_grow off len (x + 32) msf hs ss len mfrest hmframe
        rfl hgrow) ?_
    refine runS_bind_ok
      (runS_mem_load_word x _ ss
        ({ base := off, established := x + 32 } : Evm.MemoryFrame) mfrest
        rfl) ?_
    refine runS_bind_ok
      (runS_push_word (top - BitVec.ofNat 64 1) _ _ ss l frest hframe
        (by rw [hret1]; omega)) ?_
    rw [BitVec.sub_add_cancel, hret1]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
theorem runS_execute_mload_ok_nogrow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : Nat) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (mfrest : List Evm.MemoryFrame)
    (hmframe : hs.memoryFrames
      = ({ base := off, established := len } : Evm.MemoryFrame) :: mfrest)
    (hbase : G_verylow ≤ g)
    (hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + 32)
      ≤ g - G_verylow)
    (hreq : x + 32 ≤ 2 ^ 32 - 32)
    (hgrow : x + 32 ≤ len) :
    runS (Evm.Functions.execute (.MLOAD ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top, (⟨off, len, msf⟩ : EvmMemorySlice),
          g - G_verylow
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + 32)),
        { hs with
          stackFrames := writeListAt l (top.toNat - 1)
            (bytesToWord ((List.range 32).map fun i =>
              if x + i < len then
                hs.memoryBytes.getD (off + x + i) 0
              else 0)) :: frest }) ss := by
  have hn : top.toNat = rest.length + 1 := by simpa using htop
  have hbound := top.isLt
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.MLOAD ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 1 hs ss (by omega)
      (by have h : top.toNat - 1 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, mload_dispatch]
  have hbody : runS (Evm.Functions.execute_mload top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top, (⟨off, len, msf⟩ : EvmMemorySlice),
          g - G_verylow
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + 32)),
        { hs with
          stackFrames := writeListAt l (top.toNat - 1)
            (bytesToWord ((List.range 32).map fun i =>
              if x + i < len then
                hs.memoryBytes.getD (off + x + i) 0
              else 0)) :: frest }) ss := by
    simp only [Evm.Functions.execute_mload]
    refine runS_bind_ok (runS_charge_ok g G_verylow hs ss hbase) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x rest hframe hpfx htop) ?_
    rw [memory_required_size_32]
    refine runS_bind_ok (runS_charge_ok (g - G_verylow) _ hs ss hexp) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_memory_access_ok x 32 hs ss (by decide)
        (show x ≤ 2 ^ 32 - 1 by omega)
        (show (32 : Nat) ≤ 2 ^ 32 - 1 - x by omega)) ?_
    refine runS_bind_ok
      (runS_expand_memory_le off len (x + 32) msf hs ss hgrow) ?_
    refine runS_bind_ok
      (runS_mem_load_word x hs ss
        ({ base := off, established := len } : Evm.MemoryFrame) mfrest
        hmframe) ?_
    refine runS_bind_ok
      (runS_push_word (top - BitVec.ofNat 64 1) _ hs ss l frest hframe
        (by rw [hret1]; omega)) ?_
    rw [BitVec.sub_add_cancel, hret1]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)


private theorem hostState_mem2_bytes (hs : Evm.HostState) (a : Array byte)
    (mf : List Evm.MemoryFrame) :
    ({ hs with memoryBytes := a, memoryFrames := mf } : Evm.HostState).memoryBytes = a := rfl

/-! ## The step equivalence -/

open Evm.Functions in
/-- **MLOAD, all reachable outcomes** (success splits on whether the frame
window grows). Requires the memory relation and the MM-6 gas budget. -/
theorem mload_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (off len : Nat)
    (msf : EvmMemorySliceFields off len) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hmem : MemoryRel sRef.evm.memory hs off len)
    (hsafe : MemGasSafe sRef.evm.memory sRef.evm.gasLeft)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel MemPost (runR iMload sRef)
      (runS (Evm.Functions.execute (.MLOAD ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_iMload_underflow sRef hS,
      runS_execute_mload_underflow pc_in top off len g msf hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | x :: rest =>
    rw [hS] at hpfx htop hlim hwfS
    have hwx : WordWf x := hwfS x (by simp)
    have hin1 : 1 ≤ top.toNat := by simp at htop; omega
    have hlim' : top.toNat ≤ 1024 := by simp at htop ⊢; simp at hlim; omega
    obtain ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩ := hmem
    have hcost : (calculate_gas_extend_memory sRef.evm.memory.length
        [(x, 32)]).cost
        = Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + 32) := by
      have h1 := extend_cost_eq sRef.evm.memory off len x 32 msf haligned
      rwa [show Evm.Functions.memory_required_size x 32 = x + 32 from rfl]
        at h1
    have hwcM : Evm.Functions.memory_word_count sRef.evm.memory.length
        = Evm.Functions.memory_word_count len := by
      rw [haligned, memory_word_count_eq, memory_word_count_eq]
      omega
    have hexpandBy : ((calculate_gas_extend_memory sRef.evm.memory.length
        [(x, 32)]).expandBy : Nat)
        = 32 * Evm.Functions.memory_word_count (x + 32)
          - sRef.evm.memory.length := by
      have hiff0 : ∀ a b : Nat, (32 * a ≤ 32 * b) ↔ (a ≤ b) :=
        fun a b => by omega
      have hiff : ((ceil32 (x + 32) : Nat) ≤ ceil32 sRef.evm.memory.length)
          ↔ (Evm.Functions.memory_word_count (x + 32)
              ≤ Evm.Functions.memory_word_count len) := by
        rw [ceil32_eq, ceil32_eq, hwcM]
        exact hiff0 _ _
      rw [calc_extend_single]
      rw [if_neg (by decide)]
      by_cases hle : Evm.Functions.memory_word_count (x + 32)
          ≤ Evm.Functions.memory_word_count len
      · rw [if_pos (hiff.mpr hle)]
        show (0 : Nat) = _
        have h1 : 32 * Evm.Functions.memory_word_count (x + 32)
            ≤ sRef.evm.memory.length := by
          rw [haligned]
          omega
        omega
      · rw [if_neg (fun hc => hle (hiff.mp hc))]
        show ((ceil32 (x + 32) : Nat) - ceil32 sRef.evm.memory.length) = _
        rw [ceil32_eq, ceil32_eq, hwcM, ← haligned]
    by_cases hg : sRef.evm.gasLeft < mloadCost sRef.evm.memory.length x
    · rw [runR_iMload_oog sRef x rest hS hg]
      by_cases hb : g < G_verylow
      · rw [runS_execute_mload_oog_base pc_in top off len g msf hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hin1 hlim' hb]
        exact StepResultRel.halted ErrorRel.outOfGas
          (haltRegs_frame_status ss msg .OutOfGas)
      · push Not at hb
        have hbN : (3 : Nat) ≤ g := hb
        have hgg : g < 3 + ((calculate_gas_extend_memory
            sRef.evm.memory.length [(x, 32)]).cost : Nat) := by
          rw [hlive]
          exact hg
        have hb2 : g - G_verylow
            < Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                (x + 32) := by
          rw [← hcost]
          have key : g - 3 < ((calculate_gas_extend_memory
              sRef.evm.memory.length [(x, 32)]).cost : Nat) := by omega
          exact key
        rw [runS_execute_mload_oog_exp pc_in top off len g msf hs ss l frest
          x rest hframe hpfx htop hlim' prof sRef.evm.stateGasSpilled msg
          hprof hsp hmsg hfork hb hb2]
        exact StepResultRel.halted ErrorRel.outOfGas
          (haltRegs_frame_status ss msg .OutOfGas)
    · push Not at hg
      have hgc : g ≥ 3 + ((calculate_gas_extend_memory
          sRef.evm.memory.length [(x, 32)]).cost : Nat) := by
        rw [hlive]
        exact hg
      have hbase : G_verylow ≤ g := by
        have h3 : (3 : Nat) ≤ g := by omega
        exact h3
      have hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
          (x + 32) ≤ g - G_verylow := by
        rw [← hcost]
        have key : g - 3 ≥ ((calculate_gas_extend_memory
            sRef.evm.memory.length [(x, 32)]).cost : Nat) := by omega
        exact key
      have hreq : x + 32 ≤ 2 ^ 32 - 32 :=
        safe_required_bound sRef.evm.memory off len (x + 32)
          (g - G_verylow) sRef.evm.gasLeft msf haligned hsafe
          (le_trans (Nat.sub_le _ _) (le_of_eq hlive)) hexp
      have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
        cursor_retreat_toNat top (by omega)
      have hpfx' : l.take ((top.toNat - 1) + 1) = (x :: rest).reverse := by
        rw [show top.toNat - 1 + 1 = top.toNat from by simp at htop; omega]
        exact hpfx
      have hpfx1 : l.take (top.toNat - 1) = rest.reverse :=
        take_shrink l _ x _ hpfx' (by simp at htop ⊢; omega)
      rw [runR_iMload_success sRef x rest hS (by rw [hS]; exact hlim) hg]
      by_cases hgrow : len < x + 32
      · rw [runS_execute_mload_ok_grow pc_in top off len g msf hs ss l frest
          x rest hframe hpfx htop hlim' mfrest hmframe hbase hexp hreq hgrow]
        have hrel' := memoryRel_expand sRef.evm.memory hs off len (x + 32)
          mfrest ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩ hgrow
        have hread := memoryRel_read_word _ _ off (x + 32) x hrel'
          (le_refl _)
        rw [hostState_mem2_bytes] at hread
        rw [hexpandBy]
        refine StepResultRel.success ?_
        refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
          ⟨msg, hmsg⟩⟩, by simp [hpc], ?_⟩
        · refine ⟨⟨writeListAt l (top.toNat - 1) _, frest, rfl, ?_, ?_⟩,
            ?_, ?_, ?_⟩
          · have hk : top.toNat - 1 = rest.length := by simp at htop; omega
            rw [hk] at hpfx1 ⊢
            rw [show (top : StackTop).toNat = rest.length + 1 from by
                simp at htop; omega,
              take_writeListAt l rest.length _ (by omega), hpfx1, hread]
            simp
          · show BitVec.toNat top ≤ _
            rw [length_writeListAt]
            omega
          · show BitVec.toNat top = _
            simp at htop ⊢
            omega
          · simp at hlim ⊢
            omega
          · intro w hw
            rcases List.mem_cons.mp hw with hw | hw
            · subst hw
              refine loadVal_wf _ x ?_
              simp only [List.length_append, List.length_replicate]
              have h32 := le_32_wc (x + 32)
              have hwc := wc_mono (Nat.le_of_lt hgrow)
              omega
            · exact hwfS w (by simp [hw])
        · refine ⟨?_, hres, hsp⟩
          rw [← hcost, hlive]
          have key : ∀ a c : Nat, a - 3 - c = a - (3 + c) :=
            fun a c => by omega
          exact key _ _
        · refine ⟨off, x + 32, {}, rfl, ?_, ?_⟩
          · exact ⟨hrel'.frame, hrel'.aligned, hrel'.bytes, hrel'.tail⟩
          · show MemGasSafe _ (sRef.evm.gasLeft - mloadCost
              sRef.evm.memory.length x)
            refine memGasSafe_after_expand sRef.evm.memory off len (x + 32)
              sRef.evm.gasLeft (mloadCost sRef.evm.memory.length x) msf
              haligned hsafe ?_ hg
            rw [← hcost]
            have key : ∀ c : Nat, c ≤ 3 + c := fun c => by omega
            exact key _
      · push Not at hgrow
        rw [runS_execute_mload_ok_nogrow pc_in top off len g msf hs ss l
          frest x rest hframe hpfx htop hlim' mfrest hmframe hbase hexp hreq
          hgrow]
        have hread := memoryRel_read_word sRef.evm.memory hs off len x
          ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩ hgrow
        have hzero : (0 : Nat) = (calculate_gas_extend_memory
            sRef.evm.memory.length [(x, 32)]).expandBy := by
          rw [hexpandBy]
          have hwc := wc_mono hgrow
          have hal := haligned
          rw [memory_word_count_eq] at hwc hal ⊢
          omega
        rw [← hzero]
        rw [show List.replicate 0 (0x00 : EvmAsm.EL.RLP.Byte) = [] from rfl,
          List.append_nil]
        refine StepResultRel.success ?_
        refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
          ⟨msg, hmsg⟩⟩, by simp [hpc], ?_⟩
        · refine ⟨⟨writeListAt l (top.toNat - 1) _, frest, rfl, ?_, ?_⟩,
            ?_, ?_, ?_⟩
          · have hk : top.toNat - 1 = rest.length := by simp at htop; omega
            rw [hk] at hpfx1 ⊢
            rw [show (top : StackTop).toNat = rest.length + 1 from by
                simp at htop; omega,
              take_writeListAt l rest.length _ (by omega), hpfx1, hread]
            simp
          · show BitVec.toNat top ≤ _
            rw [length_writeListAt]
            omega
          · show BitVec.toNat top = _
            simp at htop ⊢
            omega
          · simp at hlim ⊢
            omega
          · intro w hw
            rcases List.mem_cons.mp hw with hw | hw
            · subst hw
              refine loadVal_wf _ x ?_
              have h32 := le_32_wc len
              omega
            · exact hwfS w (by simp [hw])
        · refine ⟨?_, hres, hsp⟩
          rw [← hcost, hlive]
          have key : ∀ a c : Nat, a - 3 - c = a - (3 + c) :=
            fun a c => by omega
          exact key _ _
        · refine ⟨off, len, msf, rfl, ?_, ?_⟩
          · exact ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩
          · exact memGasSafe_mono_gas sRef.evm.memory (Nat.sub_le _ _) hsafe

end EvmSpecsVerify
