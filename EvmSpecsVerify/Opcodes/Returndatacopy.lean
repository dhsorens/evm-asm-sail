import EvmSpecsVerify.Relations.ReturnData
import EvmSpecsVerify.Relations.Memory
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas
import EvmSpecsVerify.Opcodes.Calldatacopy

/-!
# RETURNDATACOPY

Pop destination / source / size, charge base + per-word copy + memory
expansion (the extraction's three-stage charge against SpecRef's single
`charge_gas`), validate the source range, extend memory, and copy the exact
returndata slice. `ReturnDataRel` ties SpecRef's inline bytes to the
extraction's output-slice window. MM-6 (`MemGasSafe`) discharges the u32
`memory_access` guard; MM-7 records SpecRef's `outOfBoundsRead` versus Sail's
`InvalidOpcode` diagnostic. Reachable outcomes: success ×3 (zero size / grow /
in-window), underflow ×3, OOG at any charge, and out-of-bounds after charges
and expansion; overflow is unreachable (3-in/0-out).
-/

open private pcNext from EvmAsm.Stateless.SpecRef.InstructionsEnv
open private writeArrayBytes zeroMemoryRange from Evm.HostAxioms

set_option maxHeartbeats 4000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- The SpecRef RETURNDATACOPY charge for destination `x`, size `z` against
memory size `msz` (same shape as `cdcopyCost`; the bases agree at 3). -/
def returndatacopyCost (msz x z : Nat) : Nat :=
  GasCosts.OPCODE_RETURNDATACOPY_BASE
    + GasCosts.OPCODE_RETURNDATACOPY_PER_WORD * (ceil32 z / 32)
    + (calculate_gas_extend_memory msz [(x, z)]).cost

/-! ## SpecRef run shapes -/

theorem runR_iReturndatacopy_underflow_nil (s : Machine)
    (hstack : s.evm.stack = []) :
    runR iReturndatacopy s = .ok (.error .stackUnderflow, s) := by
  simp only [iReturndatacopy]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_iReturndatacopy_underflow_one (s : Machine) (x : U256)
    (hstack : s.evm.stack = [x]) :
    runR iReturndatacopy s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with stack := [] } }) := by
  simp only [iReturndatacopy]
  refine runR_bind_ok (runR_stackPop_cons s x [] hstack) ?_
  exact runR_bind_err (runR_stackPop_nil _ (by simp))

theorem runR_iReturndatacopy_underflow_two (s : Machine) (x y : U256)
    (hstack : s.evm.stack = [x, y]) :
    runR iReturndatacopy s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with stack := [] } }) := by
  simp only [iReturndatacopy]
  refine runR_bind_ok (runR_stackPop_cons s x [y] hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y [] (by simp)) ?_
  exact runR_bind_err (runR_stackPop_nil _ (by simp))

theorem runR_iReturndatacopy_oog (s : Machine) (x y z : U256)
    (rest : List U256)
    (hstack : s.evm.stack = x :: y :: z :: rest)
    (hgas : s.evm.gasLeft < returndatacopyCost s.evm.memory.length x z) :
    runR iReturndatacopy s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [iReturndatacopy]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: z :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y (z :: rest) (by simp)) ?_
  refine runR_bind_ok (runR_stackPop_cons _ z rest (by simp)) ?_
  refine runR_bind_ok (runR_getEvm_map _ _) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _
    (by simpa [returndatacopyCost] using hgas))

theorem runR_iReturndatacopy_success (s : Machine) (x y z : U256)
    (rest : List U256)
    (hstack : s.evm.stack = x :: y :: z :: rest)
    (hgas : returndatacopyCost s.evm.memory.length x z ≤ s.evm.gasLeft)
    (hsrc : y + z ≤ s.evm.returnData.length) :
    runR iReturndatacopy s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := rest
            memory := memory_write
              (s.evm.memory ++ List.replicate
                (calculate_gas_extend_memory s.evm.memory.length
                  [(x, z)]).expandBy 0x00) x
              ((s.evm.returnData.drop y).take z)
            gasLeft := s.evm.gasLeft - returndatacopyCost s.evm.memory.length x z
            regularGasUsed :=
              s.evm.regularGasUsed + returndatacopyCost s.evm.memory.length x z
            pc := s.evm.pc + 1 } }) := by
  simp only [iReturndatacopy, extendMemory, pcNext]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: z :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y (z :: rest) (by simp)) ?_
  refine runR_bind_ok (runR_stackPop_cons _ z rest (by simp)) ?_
  refine runR_bind_ok (runR_getEvm_map _ _) ?_
  refine runR_bind_ok (runR_charge_gas _ _
    (by simpa [returndatacopyCost] using hgas)) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_neg (by simpa only [gt_iff_lt, not_lt] using hsrc)]
  refine runR_bind_ok (runR_pure _ _) ?_
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  exact runR_modifyEvm _ _

theorem runR_iReturndatacopy_oob (s : Machine) (x y z : U256)
    (rest : List U256)
    (hstack : s.evm.stack = x :: y :: z :: rest)
    (hgas : returndatacopyCost s.evm.memory.length x z ≤ s.evm.gasLeft)
    (hsrc : s.evm.returnData.length < y + z) :
    runR iReturndatacopy s =
      .ok (.error .outOfBoundsRead,
        { s with evm := { s.evm with
            stack := rest
            gasLeft := s.evm.gasLeft - returndatacopyCost s.evm.memory.length x z
            regularGasUsed :=
              s.evm.regularGasUsed + returndatacopyCost s.evm.memory.length x z } }) := by
  simp only [iReturndatacopy]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: z :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y (z :: rest) (by simp)) ?_
  refine runR_bind_ok (runR_stackPop_cons _ z rest (by simp)) ?_
  refine runR_bind_ok (runR_getEvm_map _ _) ?_
  refine runR_bind_ok (runR_charge_gas _ _
    (by simpa [returndatacopyCost] using hgas)) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_pos (by omega)]
  rfl

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for RETURNDATACOPY. -/
theorem returndatacopy_dispatch (pc_in : Nat) (top : StackTop) (off len : Nat)
    (msf : EvmMemorySliceFields off len) (g : Nat) :
    Evm.Functions.execute_opcode (.RETURNDATACOPY ()) pc_in top
        ⟨off, len, msf⟩ g =
      Evm.Functions.execute_returndatacopy top ⟨off, len, msf⟩ g >>= fun p =>
        pure (pc_in, p.1, p.2.1, p.2.2) := rfl

open Evm.Functions in
theorem runS_execute_returndatacopy_underflow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 3) :
    runS (Evm.Functions.execute (.RETURNDATACOPY ()) pc_in top
        ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, top, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.RETURNDATACOPY ()) = pure (3, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 3 0 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_returndatacopy_oog_base (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hin : 3 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (hgas : g < G_verylow) :
    runS (Evm.Functions.execute (.RETURNDATACOPY ()) pc_in top
        ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, top, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.RETURNDATACOPY ()) = pure (3, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 3 0 hs ss hin
      (by have h : top.toNat - 3 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, returndatacopy_dispatch]
  have hbody : runS
      (Evm.Functions.execute_returndatacopy top ⟨off, len, msf⟩ g) hs ss =
      .ok ((top, (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_returndatacopy]
    refine runS_bind_ok
      (runS_charge_oog g G_verylow hs ss prof sp msg hprof hsp hmsg hfork
        hgas) ?_
    rw [dif_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
theorem runS_execute_returndatacopy_oog_copy (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y z : Nat)
    (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: z :: rest).reverse)
    (htop : top.toNat = (x :: y :: z :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hzw : z < 2 ^ 256)
    (hbase : G_verylow ≤ g)
    (hgas : g - G_verylow
      < G_copy_word * Evm.Functions.memory_word_count z) :
    runS (Evm.Functions.execute (.RETURNDATACOPY ()) pc_in top
        ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1
            - BitVec.ofNat 64 1, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  have hn : top.toNat = rest.length + 3 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hret2 : (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1).toNat
      = top.toNat - 2 := by
    rw [cursor_retreat_toNat _ (by rw [hret1]; omega), hret1]
    omega
  have hpfx1 : l.take (top.toNat - 1) = (y :: z :: rest).reverse :=
    take_shrink l _ x _
      (by rw [show top.toNat - 1 + 1 = top.toNat from by omega]; exact hpfx)
      (by simp; omega)
  have hpfx2 : l.take (top.toNat - 2) = (z :: rest).reverse :=
    take_shrink l _ y _
      (by rw [show top.toNat - 2 + 1 = top.toNat - 1 from by omega]
          exact hpfx1)
      (by simp; omega)
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.RETURNDATACOPY ()) = pure (3, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 3 0 hs ss (by omega)
      (by have h : top.toNat - 3 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, returndatacopy_dispatch]
  have hbody : runS
      (Evm.Functions.execute_returndatacopy top ⟨off, len, msf⟩ g) hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_returndatacopy]
    refine runS_bind_ok (runS_charge_ok g G_verylow hs ss hbase) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (y :: z :: rest) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest y (z :: rest) hframe
        (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest z rest hframe
        (by rw [hret2]; exact hpfx2) (by rw [hret2]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_charge_copy_oog (g - G_verylow) z hs ss prof sp msg hprof hsp
        hmsg hfork hzw hgas) ?_
    rw [dif_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
theorem runS_execute_returndatacopy_oog_exp (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y z : Nat)
    (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: z :: rest).reverse)
    (htop : top.toNat = (x :: y :: z :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hzw : z < 2 ^ 256)
    (hbase : G_verylow ≤ g)
    (hcopy : G_copy_word * Evm.Functions.memory_word_count z
      ≤ g - G_verylow)
    (hgas : g - G_verylow - G_copy_word * Evm.Functions.memory_word_count z
      < Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
          (Evm.Functions.memory_required_size x z)) :
    runS (Evm.Functions.execute (.RETURNDATACOPY ()) pc_in top
        ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1
            - BitVec.ofNat 64 1, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  have hn : top.toNat = rest.length + 3 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hret2 : (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1).toNat
      = top.toNat - 2 := by
    rw [cursor_retreat_toNat _ (by rw [hret1]; omega), hret1]
    omega
  have hpfx1 : l.take (top.toNat - 1) = (y :: z :: rest).reverse :=
    take_shrink l _ x _
      (by rw [show top.toNat - 1 + 1 = top.toNat from by omega]; exact hpfx)
      (by simp; omega)
  have hpfx2 : l.take (top.toNat - 2) = (z :: rest).reverse :=
    take_shrink l _ y _
      (by rw [show top.toNat - 2 + 1 = top.toNat - 1 from by omega]
          exact hpfx1)
      (by simp; omega)
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.RETURNDATACOPY ()) = pure (3, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 3 0 hs ss (by omega)
      (by have h : top.toNat - 3 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, returndatacopy_dispatch]
  have hbody : runS
      (Evm.Functions.execute_returndatacopy top ⟨off, len, msf⟩ g) hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_returndatacopy]
    refine runS_bind_ok (runS_charge_ok g G_verylow hs ss hbase) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (y :: z :: rest) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest y (z :: rest) hframe
        (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest z rest hframe
        (by rw [hret2]; exact hpfx2) (by rw [hret2]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_charge_copy_ok (g - G_verylow) z hs ss hzw hcopy) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_charge_oog _ _ hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
    rw [dif_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
/-- Zero-size success: no charge beyond base + zero-word copy, no
expansion, and the copy itself is a no-op. -/
theorem runS_execute_returndatacopy_ok_zero (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y : Nat)
    (rest : List word) (D : Bytes)
    (roff rlen : Nat) (rf : OutputSliceFields roff rlen)
    (mfrest : List Evm.MemoryFrame)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: (0 : Nat) :: rest).reverse)
    (htop : top.toNat = (x :: y :: (0 : Nat) :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hmframe : hs.memoryFrames
      = ({ base := off, established := len } : Evm.MemoryFrame) :: mfrest)
    (hrreg : ss.regs.get? Register.returndata = some ⟨roff, rlen, rf⟩)
    (hrlen : rlen = D.length)
    (hrbytes : ∀ i, i < rlen → hs.outputBytes.getD (roff + i) 0 = D.getD i 0)
    (hsrc : y ≤ D.length)
    (hbase : G_verylow ≤ g) :
    runS (Evm.Functions.execute (.RETURNDATACOPY ()) pc_in top
        ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1
            - BitVec.ofNat 64 1, ⟨off, len, msf⟩, g - G_verylow), hs) ss := by
  have hn : top.toNat = rest.length + 3 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hret2 : (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1).toNat
      = top.toNat - 2 := by
    rw [cursor_retreat_toNat _ (by rw [hret1]; omega), hret1]
    omega
  have hpfx1 : l.take (top.toNat - 1) = (y :: (0 : Nat) :: rest).reverse :=
    take_shrink l _ x _
      (by rw [show top.toNat - 1 + 1 = top.toNat from by omega]; exact hpfx)
      (by simp; omega)
  have hpfx2 : l.take (top.toNat - 2) = ((0 : Nat) :: rest).reverse :=
    take_shrink l _ y _
      (by rw [show top.toNat - 2 + 1 = top.toNat - 1 from by omega]
          exact hpfx1)
      (by simp; omega)
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.RETURNDATACOPY ()) = pure (3, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 3 0 hs ss (by omega)
      (by have h : top.toNat - 3 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, returndatacopy_dispatch]
  have hbody : runS
      (Evm.Functions.execute_returndatacopy top ⟨off, len, msf⟩ g) hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice), g - G_verylow), hs) ss := by
    simp only [Evm.Functions.execute_returndatacopy]
    refine runS_bind_ok (runS_charge_ok g G_verylow hs ss hbase) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (y :: (0 : Nat) :: rest) hframe hpfx
        htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest y ((0 : Nat) :: rest) hframe
        (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest (0 : Nat) rest hframe
        (by rw [hret2]; exact hpfx2) (by rw [hret2]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_charge_copy_ok (g - G_verylow) 0 hs ss (by decide)
        (by simp [memory_word_count_eq])) ?_
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
    refine runS_bind_ok
      (runS_returndata_copy_words_ok D hs ss roff rlen rf
        (g - G_verylow) 0 y 0
        ({ base := off, established := len } : Evm.MemoryFrame) mfrest
        hrreg hrlen hrbytes hmframe (by omega) (by omega)) ?_
    unfold rdWrite writeArrayBytes
    simp
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
/-- Success with expansion: the frame window grows to `x + z` and the exact
returndata subrange lands at `x`. -/
theorem runS_execute_returndatacopy_ok_grow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y z : Nat)
    (rest : List word) (D : Bytes)
    (roff rlen : Nat) (rf : OutputSliceFields roff rlen)
    (mfrest : List Evm.MemoryFrame)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: z :: rest).reverse)
    (htop : top.toNat = (x :: y :: z :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hmframe : hs.memoryFrames
      = ({ base := off, established := len } : Evm.MemoryFrame) :: mfrest)
    (hrreg : ss.regs.get? Register.returndata = some ⟨roff, rlen, rf⟩)
    (hrlen : rlen = D.length)
    (hrbytes : ∀ i, i < rlen → hs.outputBytes.getD (roff + i) 0 = D.getD i 0)
    (hz : (z == 0) = false)
    (hzw : z < 2 ^ 256)
    (hbase : G_verylow ≤ g)
    (hcopy : G_copy_word * Evm.Functions.memory_word_count z
      ≤ g - G_verylow)
    (hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + z)
      ≤ g - G_verylow - G_copy_word * Evm.Functions.memory_word_count z)
    (hreq : x + z ≤ 2 ^ 32 - 32)
    (hgrow : len < x + z)
    (hsrc : y + z ≤ D.length) :
    runS (Evm.Functions.execute (.RETURNDATACOPY ()) pc_in top
        ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1
            - BitVec.ofNat 64 1,
          (⟨off, x + z, {}⟩ : EvmMemorySlice),
          g - G_verylow - G_copy_word * Evm.Functions.memory_word_count z
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + z)),
        { hs with
          memoryBytes := writeArrayBytes
            (zeroMemoryRange hs.memoryBytes (off + len) (x + z - len))
            (off + x) ((D.drop y).take z)
          memoryFrames :=
            ({ base := off, established := x + z } : Evm.MemoryFrame)
              :: mfrest }) ss := by
  have hn : top.toNat = rest.length + 3 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hret2 : (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1).toNat
      = top.toNat - 2 := by
    rw [cursor_retreat_toNat _ (by rw [hret1]; omega), hret1]
    omega
  have hpfx1 : l.take (top.toNat - 1) = (y :: z :: rest).reverse :=
    take_shrink l _ x _
      (by rw [show top.toNat - 1 + 1 = top.toNat from by omega]; exact hpfx)
      (by simp; omega)
  have hpfx2 : l.take (top.toNat - 2) = (z :: rest).reverse :=
    take_shrink l _ y _
      (by rw [show top.toNat - 2 + 1 = top.toNat - 1 from by omega]
          exact hpfx1)
      (by simp; omega)
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.RETURNDATACOPY ()) = pure (3, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 3 0 hs ss (by omega)
      (by have h : top.toNat - 3 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, returndatacopy_dispatch]
  have hbody : runS
      (Evm.Functions.execute_returndatacopy top ⟨off, len, msf⟩ g) hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, x + z, {}⟩ : EvmMemorySlice),
          g - G_verylow - G_copy_word * Evm.Functions.memory_word_count z
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + z)),
        { hs with
          memoryBytes := writeArrayBytes
            (zeroMemoryRange hs.memoryBytes (off + len) (x + z - len))
            (off + x) ((D.drop y).take z)
          memoryFrames :=
            ({ base := off, established := x + z } : Evm.MemoryFrame)
              :: mfrest }) ss := by
    simp only [Evm.Functions.execute_returndatacopy]
    refine runS_bind_ok (runS_charge_ok g G_verylow hs ss hbase) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (y :: z :: rest) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest y (z :: rest) hframe
        (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest z rest hframe
        (by rw [hret2]; exact hpfx2) (by rw [hret2]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_charge_copy_ok (g - G_verylow) z hs ss hzw hcopy) ?_
    rw [dif_neg (by simp)]
    rw [memory_required_size_pos x z hz]
    refine runS_bind_ok (runS_charge_ok _ _ hs ss hexp) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_memory_access_ok x z hs ss hz
        (show x ≤ 2 ^ 32 - 1 by omega)
        (show z ≤ 2 ^ 32 - 1 - x by omega)) ?_
    refine runS_bind_ok
      (runS_expand_memory_grow off len (x + z) msf hs ss len mfrest hmframe
        rfl hgrow) ?_
    refine runS_bind_ok
      (runS_returndata_copy_words_ok D _ ss roff rlen rf
        (g - G_verylow - G_copy_word * Evm.Functions.memory_word_count z
          - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + z))
        x y z ({ base := off, established := x + z } : Evm.MemoryFrame)
        mfrest hrreg hrlen hrbytes rfl (le_refl _) hsrc) ?_
    simp [rdWrite]
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
/-- Success inside the established window: no expansion. -/
theorem runS_execute_returndatacopy_ok_nogrow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y z : Nat)
    (rest : List word) (D : Bytes)
    (roff rlen : Nat) (rf : OutputSliceFields roff rlen)
    (mfrest : List Evm.MemoryFrame)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: z :: rest).reverse)
    (htop : top.toNat = (x :: y :: z :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hmframe : hs.memoryFrames
      = ({ base := off, established := len } : Evm.MemoryFrame) :: mfrest)
    (hrreg : ss.regs.get? Register.returndata = some ⟨roff, rlen, rf⟩)
    (hrlen : rlen = D.length)
    (hrbytes : ∀ i, i < rlen → hs.outputBytes.getD (roff + i) 0 = D.getD i 0)
    (hz : (z == 0) = false)
    (hzw : z < 2 ^ 256)
    (hbase : G_verylow ≤ g)
    (hcopy : G_copy_word * Evm.Functions.memory_word_count z
      ≤ g - G_verylow)
    (hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + z)
      ≤ g - G_verylow - G_copy_word * Evm.Functions.memory_word_count z)
    (hreq : x + z ≤ 2 ^ 32 - 32)
    (hgrow : x + z ≤ len)
    (hsrc : y + z ≤ D.length) :
    runS (Evm.Functions.execute (.RETURNDATACOPY ()) pc_in top
        ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1
            - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice),
          g - G_verylow - G_copy_word * Evm.Functions.memory_word_count z
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + z)),
        { hs with
          memoryBytes := writeArrayBytes hs.memoryBytes (off + x)
            ((D.drop y).take z) }) ss := by
  have hn : top.toNat = rest.length + 3 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hret2 : (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1).toNat
      = top.toNat - 2 := by
    rw [cursor_retreat_toNat _ (by rw [hret1]; omega), hret1]
    omega
  have hpfx1 : l.take (top.toNat - 1) = (y :: z :: rest).reverse :=
    take_shrink l _ x _
      (by rw [show top.toNat - 1 + 1 = top.toNat from by omega]; exact hpfx)
      (by simp; omega)
  have hpfx2 : l.take (top.toNat - 2) = (z :: rest).reverse :=
    take_shrink l _ y _
      (by rw [show top.toNat - 2 + 1 = top.toNat - 1 from by omega]
          exact hpfx1)
      (by simp; omega)
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.RETURNDATACOPY ()) = pure (3, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 3 0 hs ss (by omega)
      (by have h : top.toNat - 3 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, returndatacopy_dispatch]
  have hbody : runS
      (Evm.Functions.execute_returndatacopy top ⟨off, len, msf⟩ g) hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice),
          g - G_verylow - G_copy_word * Evm.Functions.memory_word_count z
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + z)),
        { hs with
          memoryBytes := writeArrayBytes hs.memoryBytes (off + x)
            ((D.drop y).take z) }) ss := by
    simp only [Evm.Functions.execute_returndatacopy]
    refine runS_bind_ok (runS_charge_ok g G_verylow hs ss hbase) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (y :: z :: rest) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest y (z :: rest) hframe
        (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest z rest hframe
        (by rw [hret2]; exact hpfx2) (by rw [hret2]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_charge_copy_ok (g - G_verylow) z hs ss hzw hcopy) ?_
    rw [dif_neg (by simp)]
    rw [memory_required_size_pos x z hz]
    refine runS_bind_ok (runS_charge_ok _ _ hs ss hexp) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_memory_access_ok x z hs ss hz
        (show x ≤ 2 ^ 32 - 1 by omega)
        (show z ≤ 2 ^ 32 - 1 - x by omega)) ?_
    refine runS_bind_ok
      (runS_expand_memory_le off len (x + z) msf hs ss hgrow) ?_
    refine runS_bind_ok
      (runS_returndata_copy_words_ok D hs ss roff rlen rf
        (g - G_verylow - G_copy_word * Evm.Functions.memory_word_count z
          - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + z))
        x y z ({ base := off, established := len } : Evm.MemoryFrame)
        mfrest hrreg hrlen hrbytes hmframe (by omega) hsrc) ?_
    simp [rdWrite]
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
/-- An in-gas, out-of-bounds copy with positive size. Memory expansion has
already been characterized by `hexpand`; the final validation exceptionally
halts with Sail's `InvalidOpcode`. -/
theorem runS_execute_returndatacopy_oob_pos (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs hs' : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y z : Nat)
    (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: z :: rest).reverse)
    (htop : top.toNat = (x :: y :: z :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (mem' : EvmMemorySlice)
    (hexpand : runS (Evm.Functions.expand_memory ⟨off, len, msf⟩ (x + z)) hs ss
      = .ok (mem', hs') ss)
    (D : Bytes) (roff rlen : Nat) (rf : OutputSliceFields roff rlen)
    (hrreg : ss.regs.get? Register.returndata = some ⟨roff, rlen, rf⟩)
    (hrlen : rlen = D.length)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hz : (z == 0) = false) (hzw : z < 2 ^ 256)
    (hbase : G_verylow ≤ g)
    (hcopy : G_copy_word * Evm.Functions.memory_word_count z ≤ g - G_verylow)
    (hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (x + z)
      ≤ g - G_verylow - G_copy_word * Evm.Functions.memory_word_count z)
    (hreq : x + z ≤ 2 ^ 32 - 32)
    (hoob : D.length < y + z) :
    runS (Evm.Functions.execute (.RETURNDATACOPY ()) pc_in top
        ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1
          - BitVec.ofNat 64 1, mem', GAS_ZERO), hs')
        { ss with regs := haltRegs ss msg .InvalidOpcode } := by
  have hn : top.toNat = rest.length + 3 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hret2 : (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1).toNat
      = top.toNat - 2 := by
    rw [cursor_retreat_toNat _ (by rw [hret1]; omega), hret1]
    omega
  have hpfx1 : l.take (top.toNat - 1) = (y :: z :: rest).reverse :=
    take_shrink l _ x _
      (by rw [show top.toNat - 1 + 1 = top.toNat from by omega]; exact hpfx)
      (by simp; omega)
  have hpfx2 : l.take (top.toNat - 2) = (z :: rest).reverse :=
    take_shrink l _ y _
      (by rw [show top.toNat - 2 + 1 = top.toNat - 1 from by omega]
          exact hpfx1)
      (by simp; omega)
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.RETURNDATACOPY ()) = pure (3, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 3 0 hs ss (by omega)
      (by have h : top.toNat - 3 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, returndatacopy_dispatch]
  have hbody : runS
      (Evm.Functions.execute_returndatacopy top ⟨off, len, msf⟩ g) hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1
          - BitVec.ofNat 64 1, mem', GAS_ZERO), hs')
        { ss with regs := haltRegs ss msg .InvalidOpcode } := by
    simp only [Evm.Functions.execute_returndatacopy]
    refine runS_bind_ok (runS_charge_ok g G_verylow hs ss hbase) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (y :: z :: rest) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest y (z :: rest) hframe
        (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest z rest hframe
        (by rw [hret2]; exact hpfx2) (by rw [hret2]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_charge_copy_ok (g - G_verylow) z hs ss hzw hcopy) ?_
    rw [dif_neg (by simp), memory_required_size_pos x z hz]
    refine runS_bind_ok (runS_charge_ok _ _ hs ss hexp) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_memory_access_ok x z hs ss hz
        (show x ≤ 2 ^ 32 - 1 by omega)
        (show z ≤ 2 ^ 32 - 1 - x by omega)) ?_
    refine runS_bind_ok hexpand ?_
    refine runS_bind_ok
      (runS_returndata_copy_words_oob D hs' ss roff rlen rf _ x y z prof sp
        msg hrreg hrlen hprof hsp hmsg hfork hoob) ?_
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
/-- Zero-size out-of-bounds is reachable when the source offset itself is
past the returndata end. -/
theorem runS_execute_returndatacopy_oob_zero (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y : Nat)
    (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: (0 : Nat) :: rest).reverse)
    (htop : top.toNat = (x :: y :: (0 : Nat) :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (D : Bytes) (roff rlen : Nat) (rf : OutputSliceFields roff rlen)
    (hrreg : ss.regs.get? Register.returndata = some ⟨roff, rlen, rf⟩)
    (hrlen : rlen = D.length)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hbase : G_verylow ≤ g) (hoob : D.length < y) :
    runS (Evm.Functions.execute (.RETURNDATACOPY ()) pc_in top
        ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1
          - BitVec.ofNat 64 1, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .InvalidOpcode } := by
  have hn : top.toNat = rest.length + 3 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hret2 : (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1).toNat
      = top.toNat - 2 := by
    rw [cursor_retreat_toNat _ (by rw [hret1]; omega), hret1]
    omega
  have hpfx1 : l.take (top.toNat - 1) = (y :: (0 : Nat) :: rest).reverse :=
    take_shrink l _ x _
      (by rw [show top.toNat - 1 + 1 = top.toNat from by omega]; exact hpfx)
      (by simp; omega)
  have hpfx2 : l.take (top.toNat - 2) = ((0 : Nat) :: rest).reverse :=
    take_shrink l _ y _
      (by rw [show top.toNat - 2 + 1 = top.toNat - 1 from by omega]
          exact hpfx1)
      (by simp; omega)
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.RETURNDATACOPY ()) = pure (3, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 3 0 hs ss (by omega)
      (by have h : top.toNat - 3 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, returndatacopy_dispatch]
  have hbody : runS
      (Evm.Functions.execute_returndatacopy top ⟨off, len, msf⟩ g) hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1
          - BitVec.ofNat 64 1, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .InvalidOpcode } := by
    simp only [Evm.Functions.execute_returndatacopy]
    refine runS_bind_ok (runS_charge_ok g G_verylow hs ss hbase) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (y :: (0 : Nat) :: rest) hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest y ((0 : Nat) :: rest) hframe
        (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest (0 : Nat) rest hframe
        (by rw [hret2]; exact hpfx2) (by rw [hret2]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_charge_copy_ok (g - G_verylow) 0 hs ss (by decide)
        (by simp [memory_word_count_eq])) ?_
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
    refine runS_bind_ok
      (runS_returndata_copy_words_oob D hs ss roff rlen rf _ 0 y 0 prof sp
        msg hrreg hrlen hprof hsp hmsg hfork (by omega)) ?_
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

/-! ## The step equivalence -/

open Evm.Functions in
/-- **RETURNDATACOPY, all reachable outcomes** (success splits on zero size and
on whether the frame window grows). Requires the memory/returndata relations
and the MM-6 gas budget; MM-7 relates the two OOB diagnostic kinds. -/
theorem returndatacopy_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (off len : Nat)
    (msf : EvmMemorySliceFields off len) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hmem : MemoryRel sRef.evm.memory hs off len)
    (hsafe : MemGasSafe sRef.evm.memory sRef.evm.gasLeft)
    (hpc : pc_in = sRef.evm.pc + 1)
    (hret : ReturnDataRel sRef.evm.returnData hs ss) :
    StepResultRel MemPost (runR iReturndatacopy sRef)
      (runS (Evm.Functions.execute (.RETURNDATACOPY ()) pc_in top
        ⟨off, len, msf⟩ g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  obtain ⟨roff, rlen, rf, hrreg, hrlen, hrbytes⟩ := hret
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_iReturndatacopy_underflow_nil sRef hS,
      runS_execute_returndatacopy_underflow pc_in top off len g msf hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | [x] =>
    rw [hS] at hpfx htop
    rw [runR_iReturndatacopy_underflow_one sRef x hS,
      runS_execute_returndatacopy_underflow pc_in top off len g msf hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | [x, y] =>
    rw [hS] at hpfx htop
    rw [runR_iReturndatacopy_underflow_two sRef x y hS,
      runS_execute_returndatacopy_underflow pc_in top off len g msf hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | x :: y :: z :: rest =>
    rw [hS] at hpfx htop hlim hwfS
    have hin3 : 3 ≤ top.toNat := by simp at htop; omega
    have hlim' : top.toNat ≤ 1024 := by simp at htop ⊢; simp at hlim; omega
    have hzw : z < 2 ^ 256 := hwfS z (by simp)
    obtain ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩ := hmem
    have hwcz : (ceil32 z : Nat) / 32 = Evm.Functions.memory_word_count z := by
      rw [ceil32_eq]
      show (32 * Evm.Functions.memory_word_count z : Nat) / 32
        = Evm.Functions.memory_word_count z
      omega
    have hcost : (calculate_gas_extend_memory sRef.evm.memory.length
        [(x, z)]).cost
        = Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
            (Evm.Functions.memory_required_size x z) :=
      extend_cost_eq sRef.evm.memory off len x z msf haligned
    have hTsplit : returndatacopyCost sRef.evm.memory.length x z
        = 3 + 3 * Evm.Functions.memory_word_count z
          + Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
              (Evm.Functions.memory_required_size x z) := by
      rw [returndatacopyCost, hwcz, ← hcost]
      rfl
    by_cases hg : sRef.evm.gasLeft < returndatacopyCost sRef.evm.memory.length x z
    · rw [runR_iReturndatacopy_oog sRef x y z rest hS hg]
      rw [hTsplit, ← hlive] at hg
      have hgN : g < 3 + 3 * Evm.Functions.memory_word_count z
          + Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
              (Evm.Functions.memory_required_size x z) := hg
      by_cases hb : g < G_verylow
      · rw [runS_execute_returndatacopy_oog_base pc_in top off len g msf hs ss
          prof sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hin3 hlim'
          hb]
        exact StepResultRel.halted ErrorRel.outOfGas
          (haltRegs_frame_status ss msg .OutOfGas)
      · push Not at hb
        have hbN : (3 : Nat) ≤ g := hb
        by_cases hc : g - G_verylow
            < G_copy_word * Evm.Functions.memory_word_count z
        · rw [runS_execute_returndatacopy_oog_copy pc_in top off len g msf hs
            ss l frest x y z rest hframe hpfx htop hlim' prof
            sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hzw hb hc]
          exact StepResultRel.halted ErrorRel.outOfGas
            (haltRegs_frame_status ss msg .OutOfGas)
        · push Not at hc
          have hcN : (3 : Nat) * Evm.Functions.memory_word_count z
              ≤ g - 3 := hc
          rw [runS_execute_returndatacopy_oog_exp pc_in top off len g msf hs
            ss l frest x y z rest hframe hpfx htop hlim' prof
            sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hzw hb hc
            (by
              show g - 3 - 3 * Evm.Functions.memory_word_count z < _
              omega)]
          exact StepResultRel.halted ErrorRel.outOfGas
            (haltRegs_frame_status ss msg .OutOfGas)
    · push Not at hg
      have hgT : 3 + 3 * Evm.Functions.memory_word_count z
          + Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
              (Evm.Functions.memory_required_size x z) ≤ g := by
        rw [← hTsplit]
        show returndatacopyCost sRef.evm.memory.length x z ≤ g
        rw [hlive]
        exact hg
      have hbase : G_verylow ≤ g := by
        show (3 : Nat) ≤ g
        omega
      have hcopy : G_copy_word * Evm.Functions.memory_word_count z
          ≤ g - G_verylow := by
        show (3 : Nat) * Evm.Functions.memory_word_count z ≤ g - 3
        omega
      have hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
          (Evm.Functions.memory_required_size x z)
          ≤ g - G_verylow - G_copy_word
              * Evm.Functions.memory_word_count z := by
        show _ ≤ g - 3 - 3 * Evm.Functions.memory_word_count z
        omega
      have hnn : top.toNat = rest.length + 3 := by simpa using htop
      have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
        cursor_retreat_toNat top (by omega)
      have hret2 : (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1).toNat
          = top.toNat - 2 := by
        rw [cursor_retreat_toNat _ (by rw [hret1]; omega), hret1]
        omega
      have hret3 : (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1
          - BitVec.ofNat 64 1).toNat = top.toNat - 3 := by
        rw [cursor_retreat_toNat _ (by rw [hret2]; omega), hret2]
        omega
      have hpfx3 : l.take (top.toNat - 3) = rest.reverse := by
        have hview : l.take (top.toNat - 3) =
            (l.take top.toNat).take (top.toNat - 3) := by
          rw [List.take_take, Nat.min_eq_left (by omega)]
        rw [hview, hpfx]
        have hrl : rest.reverse.length = top.toNat - 3 := by simp; omega
        calc ((x :: y :: z :: rest).reverse).take (top.toNat - 3)
            = (rest.reverse ++ [z, y, x]).take (top.toNat - 3) := by simp
          _ = rest.reverse := by
              rw [List.take_append_of_le_length (by omega), ← hrl,
                List.take_length]
      have hpost := fun (hs' : Evm.HostState)
          (hframe' : hs'.stackFrames = l :: frest) =>
        (⟨⟨l, frest, hframe', by rw [hret3]; exact hpfx3, by
            rw [hret3]; omega⟩,
          by rw [hret3]; omega,
          by omega,
          fun w hw => hwfS w (by simp [hw])⟩ :
          StackRel rest hs'
            (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1
              - BitVec.ofNat 64 1))
      have hgas' : g - 3 - 3 * Evm.Functions.memory_word_count z
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                (Evm.Functions.memory_required_size x z)
          = (sRef.evm.gasLeft : Nat)
            - returndatacopyCost sRef.evm.memory.length x z := by
        rw [hTsplit, ← hlive]
        omega
      by_cases hsrc : y + z ≤ sRef.evm.returnData.length
      · have hvlen : ((sRef.evm.returnData.drop y).take z).length = z := by
          simp only [List.length_take, List.length_drop]
          rw [Nat.min_eq_left (Nat.le_sub_of_add_le (by
            simpa [Nat.add_comm] using hsrc))]
        have hsrc' := hsrc
        rw [runR_iReturndatacopy_success sRef x y z rest hS hg hsrc]
        by_cases hz0 : z = 0
        · subst hz0
          have hzero : (calculate_gas_extend_memory sRef.evm.memory.length
              [(x, 0)]) = { cost := 0, expandBy := 0 } := by
            rw [calc_extend_single]
            rfl
          rw [runS_execute_returndatacopy_ok_zero pc_in top off len g msf hs ss
            l frest x y rest sRef.evm.returnData roff rlen rf mfrest hframe hpfx
            htop hlim' hmframe hrreg hrlen hrbytes (by omega) hbase]
          rw [hzero, show
            (({ cost := 0, expandBy := 0 } :
              EvmAsm.Stateless.SpecRef.ExtendMemory).expandBy : Nat) = 0
            from rfl]
          rw [show List.replicate 0 (0x00 : EvmAsm.EL.RLP.Byte) = [] from rfl,
            List.append_nil, List.take_zero, memory_write_nil]
          have hcost0 : returndatacopyCost sRef.evm.memory.length x 0 = 3 := by
            rw [returndatacopyCost, hzero]
            rfl
          refine StepResultRel.success ?_
          refine ⟨⟨hpost hs hframe, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
            ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, by simp [hpc], ?_⟩
          · refine ⟨?_, hres, hsp⟩
            show g - 3
              = sRef.evm.gasLeft - returndatacopyCost sRef.evm.memory.length x 0
            rw [hcost0, hlive]
          · refine ⟨off, len, msf, rfl, ?_, ?_⟩
            · exact ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩
            · exact memGasSafe_mono_gas sRef.evm.memory (Nat.sub_le _ _) hsafe
        · have hz : (z == 0) = false := by simpa using hz0
          rw [memory_required_size_pos x z hz] at hcost hTsplit hexp hgas'
          have hreq : x + z ≤ 2 ^ 32 - 32 :=
            safe_required_bound sRef.evm.memory off len (x + z)
              (g - G_verylow - G_copy_word
                * Evm.Functions.memory_word_count z)
              sRef.evm.gasLeft msf haligned hsafe
              (le_trans (Nat.sub_le _ _) (le_trans (Nat.sub_le _ _)
                (le_of_eq hlive))) hexp
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
            rw [calc_extend_single]
            rw [if_neg (by simpa using hz0)]
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
              show ((ceil32 (x + z) : Nat) - ceil32 sRef.evm.memory.length)
                = _
              rw [ceil32_eq, ceil32_eq, hwcM, ← haligned]
          by_cases hgrow : len < x + z
          · rw [runS_execute_returndatacopy_ok_grow pc_in top off len g msf hs
              ss l frest x y z rest sRef.evm.returnData roff rlen rf mfrest
              hframe hpfx htop hlim' hmframe hrreg hrlen hrbytes hz hzw hbase
              hcopy hexp hreq hgrow hsrc']
            have hrel' := memoryRel_expand sRef.evm.memory hs off len (x + z)
              mfrest ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩ hgrow
            have hrelStored := memoryRel_write _ _ off (x + z) x
              ((sRef.evm.returnData.drop y).take z) hrel'
              (by rw [hvlen])
            rw [hexpandBy]
            refine StepResultRel.success ?_
            refine ⟨⟨hpost _ hframe, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
              ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, by simp [hpc], ?_⟩
            · refine ⟨?_, hres, hsp⟩
              show g - 3 - 3 * Evm.Functions.memory_word_count z
                  - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                      (x + z)
                = sRef.evm.gasLeft - returndatacopyCost sRef.evm.memory.length x z
              exact hgas'
            · refine ⟨off, x + z, {}, rfl, ?_, ?_⟩
              · exact ⟨hrelStored.frame, hrelStored.aligned,
                  hrelStored.bytes, hrelStored.tail⟩
              · show MemGasSafe _ (sRef.evm.gasLeft - returndatacopyCost
                  sRef.evm.memory.length x z)
                have hsafe2 := memGasSafe_after_expand sRef.evm.memory off
                  len (x + z) sRef.evm.gasLeft
                  (returndatacopyCost sRef.evm.memory.length x z) msf haligned
                  hsafe (by rw [hTsplit]; omega) hg
                unfold MemGasSafe at hsafe2 ⊢
                rw [memory_write_length _ _ _ (by
                  rw [hvlen]
                  simp only [List.length_append, List.length_replicate]
                  have h32 := le_32_wc (x + z)
                  have hwc := wc_mono (Nat.le_of_lt hgrow)
                  have hal := haligned
                  omega)]
                exact hsafe2
          · push Not at hgrow
            rw [runS_execute_returndatacopy_ok_nogrow pc_in top off len g msf
              hs ss l frest x y z rest sRef.evm.returnData roff rlen rf mfrest
              hframe hpfx htop hlim' hmframe hrreg hrlen hrbytes hz hzw hbase
              hcopy hexp hreq hgrow hsrc']
            have hrelStored := memoryRel_write sRef.evm.memory hs off len x
              ((sRef.evm.returnData.drop y).take z)
              ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩
              (by rw [hvlen]; exact hgrow)
            have hzero : (0 : Nat) = (calculate_gas_extend_memory
                sRef.evm.memory.length [(x, z)]).expandBy := by
              rw [hexpandBy]
              have hwc := wc_mono hgrow
              have hal := haligned
              rw [memory_word_count_eq] at hwc hal ⊢
              omega
            rw [← hzero]
            rw [show List.replicate 0 (0x00 : EvmAsm.EL.RLP.Byte) = []
                from rfl,
              List.append_nil]
            refine StepResultRel.success ?_
            refine ⟨⟨hpost _ hframe, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
              ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, by simp [hpc], ?_⟩
            · refine ⟨?_, hres, hsp⟩
              show g - 3 - 3 * Evm.Functions.memory_word_count z
                  - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                      (x + z)
                = sRef.evm.gasLeft - returndatacopyCost sRef.evm.memory.length x z
              exact hgas'
            · refine ⟨off, len, msf, rfl, ?_, ?_⟩
              · exact ⟨hrelStored.frame, hrelStored.aligned,
                  hrelStored.bytes, hrelStored.tail⟩
              · show MemGasSafe _ (sRef.evm.gasLeft - returndatacopyCost
                  sRef.evm.memory.length x z)
                have hsafe2 := memGasSafe_mono_gas sRef.evm.memory
                  (g' := sRef.evm.gasLeft
                    - returndatacopyCost sRef.evm.memory.length x z)
                  (Nat.sub_le _ _) hsafe
                unfold MemGasSafe at hsafe2 ⊢
                rw [memory_write_length _ _ _ (by
                  rw [hvlen]
                  have h32 := le_32_wc len
                  have hal := haligned
                  omega)]
                exact hsafe2
      · push Not at hsrc
        rw [runR_iReturndatacopy_oob sRef x y z rest hS hg (by omega)]
        by_cases hz0 : z = 0
        · subst hz0
          rw [runS_execute_returndatacopy_oob_zero pc_in top off len g msf hs ss
            l frest x y rest hframe hpfx htop hlim' sRef.evm.returnData roff
            rlen rf hrreg hrlen prof sRef.evm.stateGasSpilled msg hprof hsp
            hmsg hfork hbase (by omega)]
          exact StepResultRel.halted ErrorRel.outOfBoundsRead
            (haltRegs_frame_status ss msg .InvalidOpcode)
        · have hz : (z == 0) = false := by simpa using hz0
          rw [memory_required_size_pos x z hz] at hexp
          have hreq : x + z ≤ 2 ^ 32 - 32 :=
            safe_required_bound sRef.evm.memory off len (x + z)
              (g - G_verylow - G_copy_word
                * Evm.Functions.memory_word_count z)
              sRef.evm.gasLeft msf haligned hsafe
              (le_trans (Nat.sub_le _ _) (le_trans (Nat.sub_le _ _)
                (le_of_eq hlive))) hexp
          by_cases hgrow : len < x + z
          · have hexpand := runS_expand_memory_grow off len (x + z) msf hs ss
              len mfrest hmframe rfl hgrow
            rw [runS_execute_returndatacopy_oob_pos pc_in top off len g msf hs
              { hs with
                memoryBytes := zeroMemoryRange hs.memoryBytes (off + len)
                  (x + z - len)
                memoryFrames :=
                  ({ base := off, established := x + z } : Evm.MemoryFrame)
                    :: mfrest }
              ss l frest x y z rest hframe hpfx htop hlim'
              (⟨off, x + z, {}⟩ : EvmMemorySlice) hexpand
              sRef.evm.returnData roff rlen rf hrreg hrlen prof
              sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hz hzw hbase
              hcopy hexp hreq (by omega)]
            exact StepResultRel.halted ErrorRel.outOfBoundsRead
              (haltRegs_frame_status ss msg .InvalidOpcode)
          · push Not at hgrow
            have hexpand := runS_expand_memory_le off len (x + z) msf hs ss hgrow
            rw [runS_execute_returndatacopy_oob_pos pc_in top off len g msf hs hs
              ss l frest x y z rest hframe hpfx htop hlim'
              (⟨off, len, msf⟩ : EvmMemorySlice) hexpand
              sRef.evm.returnData roff rlen rf hrreg hrlen prof
              sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hz hzw hbase
              hcopy hexp hreq (by omega)]
            exact StepResultRel.halted ErrorRel.outOfBoundsRead
              (haltRegs_frame_status ss msg .InvalidOpcode)

end EvmSpecsVerify
