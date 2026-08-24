import EvmSpecsVerify.Relations.ExternalCode
import EvmSpecsVerify.Opcodes.Extcodesize
import EvmSpecsVerify.Opcodes.Codecopy

/-!
# EXTCODECOPY

EXTCODECOPY combines the arbitrary-account lookup and warm/cold accounting of
EXTCODESIZE with CODECOPY's copy and memory-expansion pipeline. The
`ExternalCodeRel` hypothesis is deliberately limited to the world/code-store
seam: it says which bytes `k_code_copy` resolves and what that primitive
preserves. Stack behavior, all three staged charges, memory growth, warmth, and
every reachable halt are proved here.
-/

open private pcNext from EvmAsm.Stateless.SpecRef.InstructionsEnv
open private writeArrayBytes zeroMemoryRange assocGet assocPut
  from Evm.HostAxioms

set_option maxHeartbeats 6000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- SpecRef's single EXTCODECOPY charge, split into the extraction's access,
copy-word, and expansion stages. -/
def extcodecopyCost (warm : Bool) (msz dst size : Nat) : Nat :=
  extcodesizeCost warm
    + GasCosts.OPCODE_COPY_PER_WORD * (ceil32 size / 32)
    + (calculate_gas_extend_memory msz [(dst, size)]).cost

/-! ## SpecRef run shapes -/

theorem runR_iExtcodecopy_underflow_nil (s : Machine)
    (hstack : s.evm.stack = []) :
    runR iExtcodecopy s = .ok (.error .stackUnderflow, s) := by
  simp only [iExtcodecopy]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_iExtcodecopy_underflow_one (s : Machine) (a : U256)
    (hstack : s.evm.stack = [a]) :
    runR iExtcodecopy s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with stack := [] } }) := by
  simp only [iExtcodecopy]
  refine runR_bind_ok (runR_stackPop_cons s a [] hstack) ?_
  exact runR_bind_err (runR_stackPop_nil _ (by simp))

theorem runR_iExtcodecopy_underflow_two (s : Machine) (a dst : U256)
    (hstack : s.evm.stack = [a, dst]) :
    runR iExtcodecopy s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with stack := [] } }) := by
  simp only [iExtcodecopy]
  refine runR_bind_ok (runR_stackPop_cons s a [dst] hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ dst [] (by simp)) ?_
  exact runR_bind_err (runR_stackPop_nil _ (by simp))

theorem runR_iExtcodecopy_underflow_three (s : Machine) (a dst src : U256)
    (hstack : s.evm.stack = [a, dst, src]) :
    runR iExtcodecopy s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with stack := [] } }) := by
  simp only [iExtcodecopy]
  refine runR_bind_ok (runR_stackPop_cons s a [dst, src] hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ dst [src] (by simp)) ?_
  refine runR_bind_ok (runR_stackPop_cons _ src [] (by simp)) ?_
  exact runR_bind_err (runR_stackPop_nil _ (by simp))

theorem runR_iExtcodecopy_warm_oog (s : Machine)
    (a dst src size : U256) (rest : List U256)
    (hstack : s.evm.stack = a :: dst :: src :: size :: rest)
    (hwarm : s.evm.accessedAddresses.contains (to_address_masked a) = true)
    (hgas : s.evm.gasLeft <
      extcodecopyCost true s.evm.memory.length dst size) :
    runR iExtcodecopy s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [iExtcodecopy]
  refine runR_bind_ok
    (runR_stackPop_cons s a (dst :: src :: size :: rest) hstack) ?_
  refine runR_bind_ok
    (runR_stackPop_cons _ dst (src :: size :: rest) (by simp)) ?_
  refine runR_bind_ok
    (runR_stackPop_cons _ src (size :: rest) (by simp)) ?_
  refine runR_bind_ok (runR_stackPop_cons _ size rest (by simp)) ?_
  refine runR_bind_ok (runR_getEvm_map _ _) ?_
  refine runR_bind_ok (runR_accessGasCost_warm _ _ hwarm) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _
    (by simpa [extcodecopyCost, extcodesizeCost] using hgas))

theorem runR_iExtcodecopy_cold_oog (s : Machine)
    (a dst src size : U256) (rest : List U256)
    (hstack : s.evm.stack = a :: dst :: src :: size :: rest)
    (hcold : s.evm.accessedAddresses.contains (to_address_masked a) = false)
    (hgas : s.evm.gasLeft <
      extcodecopyCost false s.evm.memory.length dst size) :
    runR iExtcodecopy s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with
            stack := rest
            accessedAddresses := setAdd s.evm.accessedAddresses
              (to_address_masked a) } }) := by
  simp only [iExtcodecopy]
  refine runR_bind_ok
    (runR_stackPop_cons s a (dst :: src :: size :: rest) hstack) ?_
  refine runR_bind_ok
    (runR_stackPop_cons _ dst (src :: size :: rest) (by simp)) ?_
  refine runR_bind_ok
    (runR_stackPop_cons _ src (size :: rest) (by simp)) ?_
  refine runR_bind_ok (runR_stackPop_cons _ size rest (by simp)) ?_
  refine runR_bind_ok (runR_getEvm_map _ _) ?_
  refine runR_bind_ok (runR_accessGasCost_cold _ _ hcold) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _
    (by simpa [extcodecopyCost, extcodesizeCost] using hgas))

theorem runR_iExtcodecopy_warm_success (s : Machine)
    (a dst src size : U256) (rest : List U256)
    (acct : EvmAsm.Stateless.SpecRef.Account) (code : Bytes)
    (ts1 ts2 : TransactionState)
    (hstack : s.evm.stack = a :: dst :: src :: size :: rest)
    (hwarm : s.evm.accessedAddresses.contains (to_address_masked a) = true)
    (hgas : extcodecopyCost true s.evm.memory.length dst size ≤
      s.evm.gasLeft)
    (hacc : (getAccount (to_address_masked a)).run s.txState = .ok (acct, ts1))
    (hcode : (getCode acct.codeHash (to_address_masked a)).run ts1
      = .ok (code, ts2)) :
    runR iExtcodecopy s =
      .ok (.ok (), { s with
        evm := { s.evm with
          stack := rest
          memory := memory_write
            (s.evm.memory ++ List.replicate
              (calculate_gas_extend_memory s.evm.memory.length
                [(dst, size)]).expandBy 0x00) dst
            (buffer_read code src size)
          gasLeft := s.evm.gasLeft -
            extcodecopyCost true s.evm.memory.length dst size
          regularGasUsed := s.evm.regularGasUsed +
            extcodecopyCost true s.evm.memory.length dst size
          pc := s.evm.pc + 1 }
        txState := ts2 }) := by
  simp only [iExtcodecopy, extendMemory, pcNext]
  refine runR_bind_ok
    (runR_stackPop_cons s a (dst :: src :: size :: rest) hstack) ?_
  refine runR_bind_ok
    (runR_stackPop_cons _ dst (src :: size :: rest) (by simp)) ?_
  refine runR_bind_ok
    (runR_stackPop_cons _ src (size :: rest) (by simp)) ?_
  refine runR_bind_ok (runR_stackPop_cons _ size rest (by simp)) ?_
  refine runR_bind_ok (runR_getEvm_map _ _) ?_
  refine runR_bind_ok (runR_accessGasCost_warm _ _ hwarm) ?_
  refine runR_bind_ok (runR_charge_gas _ _
    (by simpa [extcodecopyCost, extcodesizeCost] using hgas)) ?_
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  refine runR_bind_ok (runR_extCodeOf_ok _ _ acct code ts1 ts2 hacc hcode) ?_
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  exact runR_modifyEvm _ _

theorem runR_iExtcodecopy_cold_success (s : Machine)
    (a dst src size : U256) (rest : List U256)
    (acct : EvmAsm.Stateless.SpecRef.Account) (code : Bytes)
    (ts1 ts2 : TransactionState)
    (hstack : s.evm.stack = a :: dst :: src :: size :: rest)
    (hcold : s.evm.accessedAddresses.contains (to_address_masked a) = false)
    (hgas : extcodecopyCost false s.evm.memory.length dst size ≤
      s.evm.gasLeft)
    (hacc : (getAccount (to_address_masked a)).run s.txState = .ok (acct, ts1))
    (hcode : (getCode acct.codeHash (to_address_masked a)).run ts1
      = .ok (code, ts2)) :
    runR iExtcodecopy s =
      .ok (.ok (), { s with
        evm := { s.evm with
          stack := rest
          memory := memory_write
            (s.evm.memory ++ List.replicate
              (calculate_gas_extend_memory s.evm.memory.length
                [(dst, size)]).expandBy 0x00) dst
            (buffer_read code src size)
          gasLeft := s.evm.gasLeft -
            extcodecopyCost false s.evm.memory.length dst size
          regularGasUsed := s.evm.regularGasUsed +
            extcodecopyCost false s.evm.memory.length dst size
          pc := s.evm.pc + 1
          accessedAddresses := setAdd s.evm.accessedAddresses
            (to_address_masked a) }
        txState := ts2 }) := by
  simp only [iExtcodecopy, extendMemory, pcNext]
  refine runR_bind_ok
    (runR_stackPop_cons s a (dst :: src :: size :: rest) hstack) ?_
  refine runR_bind_ok
    (runR_stackPop_cons _ dst (src :: size :: rest) (by simp)) ?_
  refine runR_bind_ok
    (runR_stackPop_cons _ src (size :: rest) (by simp)) ?_
  refine runR_bind_ok (runR_stackPop_cons _ size rest (by simp)) ?_
  refine runR_bind_ok (runR_getEvm_map _ _) ?_
  refine runR_bind_ok (runR_accessGasCost_cold _ _ hcold) ?_
  refine runR_bind_ok (runR_charge_gas _ _
    (by simpa [extcodecopyCost, extcodesizeCost] using hgas)) ?_
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  refine runR_bind_ok (runR_extCodeOf_ok _ _ acct code ts1 ts2 hacc hcode) ?_
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  exact runR_modifyEvm _ _

/-! ## `Evm` run shapes -/

open Evm.Functions in
theorem extcodecopy_dispatch (pc_in : Nat) (top : StackTop) (off len : Nat)
    (msf : EvmMemorySliceFields off len) (g : Nat) :
    Evm.Functions.execute_opcode (.EXTCODECOPY ()) pc_in top
        ⟨off, len, msf⟩ g =
      Evm.Functions.execute_extcodecopy top ⟨off, len, msf⟩ g >>= fun p =>
        pure (pc_in, p.1, p.2.1, p.2.2) := rfl

private def retreat4 (top : StackTop) : StackTop :=
  top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1 -
    BitVec.ofNat 64 1 - BitVec.ofNat 64 1

private def withMemoryBytes (h : Evm.HostState) (bytes : Array byte) :
    Evm.HostState :=
  { h with memoryBytes := bytes }

private theorem pop4_view (top : StackTop) (l : List word)
    (a dst src size : word) (rest : List word)
    (hpfx : l.take top.toNat = (a :: dst :: src :: size :: rest).reverse)
    (htop : top.toNat = (a :: dst :: src :: size :: rest).length) :
    (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 ∧
    (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1).toNat = top.toNat - 2 ∧
    (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1 -
      BitVec.ofNat 64 1).toNat = top.toNat - 3 ∧
    (retreat4 top).toNat = top.toNat - 4 ∧
    l.take (top.toNat - 1) = (dst :: src :: size :: rest).reverse ∧
    l.take (top.toNat - 2) = (src :: size :: rest).reverse ∧
    l.take (top.toNat - 3) = (size :: rest).reverse := by
  have hn : top.toNat = rest.length + 4 := by simpa using htop
  have h1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have h2 : (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1).toNat
      = top.toNat - 2 := by
    rw [cursor_retreat_toNat _ (by rw [h1]; omega), h1]
    omega
  have h3 : (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1 -
      BitVec.ofNat 64 1).toNat = top.toNat - 3 := by
    rw [cursor_retreat_toNat _ (by rw [h2]; omega), h2]
    omega
  have h4 : (retreat4 top).toNat = top.toNat - 4 := by
    unfold retreat4
    rw [cursor_retreat_toNat _ (by rw [h3]; omega), h3]
    omega
  have p1 : l.take (top.toNat - 1) =
      (dst :: src :: size :: rest).reverse :=
    take_shrink l _ a _
      (by rw [show top.toNat - 1 + 1 = top.toNat from by omega]; exact hpfx)
      (by simp; omega)
  have p2 : l.take (top.toNat - 2) = (src :: size :: rest).reverse :=
    take_shrink l _ dst _
      (by rw [show top.toNat - 2 + 1 = top.toNat - 1 from by omega]; exact p1)
      (by simp; omega)
  have p3 : l.take (top.toNat - 3) = (size :: rest).reverse :=
    take_shrink l _ src _
      (by rw [show top.toNat - 3 + 1 = top.toNat - 2 from by omega]; exact p2)
      (by simp; omega)
  exact ⟨h1, h2, h3, h4, p1, p2, p3⟩

open Evm.Functions in
theorem runS_execute_extcodecopy_underflow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 4) :
    runS (Evm.Functions.execute (.EXTCODECOPY ()) pc_in top
        ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, top, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.EXTCODECOPY ()) = pure (4, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 4 0 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_extcodecopy_oog_access (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word))
    (a dst src size : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (a :: dst :: src :: size :: rest).reverse)
    (htop : top.toNat = (a :: dst :: src :: size :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (pid : Evm.Defs.address → PrecompileId)
    (hpid : runS (Evm.Functions.precompile_id_for_address
        (Evm.Functions.word_to_address a)) hs ss =
      .ok (pid (Evm.Functions.word_to_address a), hs) ss)
    (warmb : Bool)
    (hwarmb : (if (pid (Evm.Functions.word_to_address a)
          != PrecompileId.NotPrecompile) then true
        else decide (hs.warmEpoch ≤ (assocGet hs.warmAddresses
          (Evm.Functions.word_to_address a)).getD 0)) = warmb)
    (hgas : g < extcodesizeCost warmb) :
    runS (Evm.Functions.execute (.EXTCODECOPY ()) pc_in top
        ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, retreat4 top, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  obtain ⟨h1, h2, h3, h4, p1, p2, p3⟩ :=
    pop4_view top l a dst src size rest hpfx htop
  have hin : 4 ≤ top.toNat := by simp at htop; omega
  have hn : top.toNat = rest.length + 4 := by simpa using htop
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.EXTCODECOPY ()) = pure (4, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 4 0 hs ss hin
      (by have h : top.toNat - 4 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, extcodecopy_dispatch]
  have hbody : runS
      (Evm.Functions.execute_extcodecopy top ⟨off, len, msf⟩ g) hs ss =
      .ok ((retreat4 top, (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_extcodecopy]
    refine runS_bind_ok
      (runS_pop top hs ss l frest a (dst :: src :: size :: rest)
        hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest dst (src :: size :: rest) hframe
        (by rw [h1]; exact p1) (by rw [h1]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest src (size :: rest) hframe
        (by rw [h2]; exact p2) (by rw [h2]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest size rest hframe
        (by rw [h3]; exact p3) (by rw [h3]; simp; omega)) ?_
    refine runS_bind_ok
      (by rw [runS_k_account_is_warm pid _ hs ss hpid, hwarmb]) ?_
    refine runS_bind_ok (runS_account_cost warmb hs ss prof hprof hfork) ?_
    refine runS_bind_ok
      (runS_external_code_read_cost hs ss prof hprof hfork) ?_
    refine runS_bind_ok
      (runS_charge_oog g _ hs ss prof sp msg hprof hsp hmsg hfork
        (by simpa [extcodesizeCost] using hgas)) ?_
    rw [dif_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
theorem runS_execute_extcodecopy_oog_copy (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word))
    (a dst src size : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (a :: dst :: src :: size :: rest).reverse)
    (htop : top.toNat = (a :: dst :: src :: size :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (pid : Evm.Defs.address → PrecompileId)
    (hpid : runS (Evm.Functions.precompile_id_for_address
        (Evm.Functions.word_to_address a)) hs ss =
      .ok (pid (Evm.Functions.word_to_address a), hs) ss)
    (warmb : Bool) (hwarmb : (if (pid (Evm.Functions.word_to_address a)
          != PrecompileId.NotPrecompile) then true
        else decide (hs.warmEpoch ≤ (assocGet hs.warmAddresses
          (Evm.Functions.word_to_address a)).getD 0)) = warmb)
    (haccess : extcodesizeCost warmb ≤ g)
    (hswf : size < 2 ^ 256)
    (hgas : g - extcodesizeCost warmb <
      G_copy_word * Evm.Functions.memory_word_count size) :
    runS (Evm.Functions.execute (.EXTCODECOPY ()) pc_in top
        ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, retreat4 top, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  obtain ⟨h1, h2, h3, h4, p1, p2, p3⟩ :=
    pop4_view top l a dst src size rest hpfx htop
  have hin : 4 ≤ top.toNat := by simp at htop; omega
  have hn : top.toNat = rest.length + 4 := by simpa using htop
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.EXTCODECOPY ()) = pure (4, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 4 0 hs ss hin
      (by have h : top.toNat - 4 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, extcodecopy_dispatch]
  have hbody : runS
      (Evm.Functions.execute_extcodecopy top ⟨off, len, msf⟩ g) hs ss =
      .ok ((retreat4 top, (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_extcodecopy]
    refine runS_bind_ok
      (runS_pop top hs ss l frest a (dst :: src :: size :: rest)
        hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest dst (src :: size :: rest) hframe
        (by rw [h1]; exact p1) (by rw [h1]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest src (size :: rest) hframe
        (by rw [h2]; exact p2) (by rw [h2]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest size rest hframe
        (by rw [h3]; exact p3) (by rw [h3]; simp; omega)) ?_
    refine runS_bind_ok
      (by rw [runS_k_account_is_warm pid _ hs ss hpid, hwarmb]) ?_
    refine runS_bind_ok (runS_account_cost warmb hs ss prof hprof hfork) ?_
    refine runS_bind_ok
      (runS_external_code_read_cost hs ss prof hprof hfork) ?_
    refine runS_bind_ok (runS_charge_ok g _ hs ss
      (by simpa [extcodesizeCost] using haccess)) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_charge_copy_oog (g - extcodesizeCost warmb) size hs ss prof sp
        msg hprof hsp hmsg hfork hswf hgas) ?_
    rw [dif_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
theorem runS_execute_extcodecopy_oog_exp (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word))
    (a dst src size : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (a :: dst :: src :: size :: rest).reverse)
    (htop : top.toNat = (a :: dst :: src :: size :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (pid : Evm.Defs.address → PrecompileId)
    (hpid : runS (Evm.Functions.precompile_id_for_address
        (Evm.Functions.word_to_address a)) hs ss =
      .ok (pid (Evm.Functions.word_to_address a), hs) ss)
    (warmb : Bool) (hwarmb : (if (pid (Evm.Functions.word_to_address a)
          != PrecompileId.NotPrecompile) then true
        else decide (hs.warmEpoch ≤ (assocGet hs.warmAddresses
          (Evm.Functions.word_to_address a)).getD 0)) = warmb)
    (haccess : extcodesizeCost warmb ≤ g)
    (hswf : size < 2 ^ 256)
    (hcopy : G_copy_word * Evm.Functions.memory_word_count size
      ≤ g - extcodesizeCost warmb)
    (hgas : g - extcodesizeCost warmb -
        G_copy_word * Evm.Functions.memory_word_count size <
      Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
        (Evm.Functions.memory_required_size dst size)) :
    runS (Evm.Functions.execute (.EXTCODECOPY ()) pc_in top
        ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, retreat4 top, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  obtain ⟨h1, h2, h3, h4, p1, p2, p3⟩ :=
    pop4_view top l a dst src size rest hpfx htop
  have hin : 4 ≤ top.toNat := by simp at htop; omega
  have hn : top.toNat = rest.length + 4 := by simpa using htop
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.EXTCODECOPY ()) = pure (4, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 4 0 hs ss hin
      (by have h : top.toNat - 4 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, extcodecopy_dispatch]
  have hbody : runS
      (Evm.Functions.execute_extcodecopy top ⟨off, len, msf⟩ g) hs ss =
      .ok ((retreat4 top, (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_extcodecopy]
    refine runS_bind_ok
      (runS_pop top hs ss l frest a (dst :: src :: size :: rest)
        hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest dst (src :: size :: rest) hframe
        (by rw [h1]; exact p1) (by rw [h1]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest src (size :: rest) hframe
        (by rw [h2]; exact p2) (by rw [h2]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest size rest hframe
        (by rw [h3]; exact p3) (by rw [h3]; simp; omega)) ?_
    refine runS_bind_ok
      (by rw [runS_k_account_is_warm pid _ hs ss hpid, hwarmb]) ?_
    refine runS_bind_ok (runS_account_cost warmb hs ss prof hprof hfork) ?_
    refine runS_bind_ok
      (runS_external_code_read_cost hs ss prof hprof hfork) ?_
    refine runS_bind_ok (runS_charge_ok g _ hs ss
      (by simpa [extcodesizeCost] using haccess)) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_charge_copy_ok (g - extcodesizeCost warmb) size hs ss hswf
        hcopy) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_charge_oog _ _ hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
    rw [dif_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
/-- Zero-size success. The account lookup may update caches, while the
memory splice is empty and the active window is unchanged. -/
theorem runS_execute_extcodecopy_ok_zero (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word))
    (a dst src : word) (rest : List word) (code : Bytes)
    (mfrest : List Evm.MemoryFrame)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat =
      (a :: dst :: src :: (0 : word) :: rest).reverse)
    (htop : top.toNat = (a :: dst :: src :: (0 : word) :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hmframe : hs.memoryFrames =
      ({ base := off, established := len } : Evm.MemoryFrame) :: mfrest)
    (prof : ExecutionProfile)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hfork : Amsterdam ≤ prof.1)
    (pid : Evm.Defs.address → PrecompileId)
    (hpid : ∀ hs', runS (Evm.Functions.precompile_id_for_address
        (Evm.Functions.word_to_address a)) hs' ss =
      .ok (pid (Evm.Functions.word_to_address a), hs') ss)
    (warmb : Bool) (hwarmb : (if (pid (Evm.Functions.word_to_address a)
          != PrecompileId.NotPrecompile) then true
        else decide (hs.warmEpoch ≤ (assocGet hs.warmAddresses
          (Evm.Functions.word_to_address a)).getD 0)) = warmb)
    (haccess : extcodesizeCost warmb ≤ g)
    (hostAfter : List (Evm.Defs.address × Nat) → Array byte →
      List Evm.MemoryFrame → Evm.HostState)
    (hrun : ∀ ws memoryBytes fr mfrest dst src size,
      dst + size ≤ fr.established →
      runS (Evm.Functions.k_code_copy
          (Evm.Functions.word_to_address a) dst src size)
        { hs with
          warmAddresses := ws
          memoryBytes := memoryBytes
          memoryFrames := fr :: mfrest } ss =
        .ok ((), { hostAfter ws memoryBytes (fr :: mfrest) with
          memoryBytes := writeArrayBytes memoryBytes (fr.base + dst)
            (buffer_read code src size) }) ss) :
    runS (Evm.Functions.execute (.EXTCODECOPY ()) pc_in top
        ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, retreat4 top, ⟨off, len, msf⟩,
          g - extcodesizeCost warmb),
        withMemoryBytes
          (hostAfter (wsAfterMark pid (Evm.Functions.word_to_address a) hs)
            hs.memoryBytes
            (({ base := off, established := len } : Evm.MemoryFrame) :: mfrest))
          (writeArrayBytes hs.memoryBytes off (buffer_read code src 0))) ss := by
  obtain ⟨h1, h2, h3, h4, p1, p2, p3⟩ :=
    pop4_view top l a dst src 0 rest hpfx htop
  have hin : 4 ≤ top.toNat := by simp at htop; omega
  have hn : top.toNat = rest.length + 4 := by simpa using htop
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.EXTCODECOPY ()) = pure (4, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 4 0 hs ss hin
      (by have h : top.toNat - 4 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, extcodecopy_dispatch]
  have hbody : runS
      (Evm.Functions.execute_extcodecopy top ⟨off, len, msf⟩ g) hs ss =
      .ok ((retreat4 top, (⟨off, len, msf⟩ : EvmMemorySlice),
          g - extcodesizeCost warmb),
        withMemoryBytes
          (hostAfter (wsAfterMark pid (Evm.Functions.word_to_address a) hs)
            hs.memoryBytes
            (({ base := off, established := len } : Evm.MemoryFrame) :: mfrest))
          (writeArrayBytes hs.memoryBytes off (buffer_read code src 0))) ss := by
    simp only [Evm.Functions.execute_extcodecopy]
    refine runS_bind_ok
      (runS_pop top hs ss l frest a (dst :: src :: 0 :: rest)
        hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest dst (src :: 0 :: rest) hframe
        (by rw [h1]; exact p1) (by rw [h1]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest src (0 :: rest) hframe
        (by rw [h2]; exact p2) (by rw [h2]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest 0 rest hframe
        (by rw [h3]; exact p3) (by rw [h3]; simp; omega)) ?_
    refine runS_bind_ok
      (by rw [runS_k_account_is_warm pid _ hs ss (hpid hs), hwarmb]) ?_
    refine runS_bind_ok (runS_account_cost warmb hs ss prof hprof hfork) ?_
    refine runS_bind_ok
      (runS_external_code_read_cost hs ss prof hprof hfork) ?_
    refine runS_bind_ok (runS_charge_ok g _ hs ss
      (by simpa [extcodesizeCost] using haccess)) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_charge_copy_ok (g - extcodesizeCost warmb) 0 hs ss
        (by decide) (by simp [memory_word_count_eq])) ?_
    rw [dif_neg (by simp)]
    rw [show Evm.Functions.memory_required_size dst 0 = 0 from rfl]
    refine runS_bind_ok
      (runS_charge_ok _ _ hs ss (by
        simp [Evm.Functions.memory_expansion_cost, memory_high_water_eq,
          memory_word_count_eq])) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok (runS_memory_access_zero dst hs ss) ?_
    refine runS_bind_ok
      (runS_expand_memory_le off len 0 msf hs ss (Nat.zero_le len)) ?_
    refine runS_bind_ok
      (runS_k_account_mark_warm pid _ hs ss (hpid hs)) ?_
    rw [hmframe]
    refine runS_bind_ok (hrun
      (wsAfterMark pid (Evm.Functions.word_to_address a) hs)
      hs.memoryBytes
      ({ base := off, established := len } : Evm.MemoryFrame)
      mfrest 0 src 0 (by omega)) ?_
    simp [retreat4, withMemoryBytes, memory_word_count_eq,
      Evm.Functions.memory_expansion_cost, memory_high_water_eq]
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
/-- Success with expansion: grow, mark the address warm, then resolve and
copy the exact external-code bytes into the expanded frame. -/
theorem runS_execute_extcodecopy_ok_grow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word))
    (a dst src size : word) (rest : List word) (code : Bytes)
    (mfrest : List Evm.MemoryFrame)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (a :: dst :: src :: size :: rest).reverse)
    (htop : top.toNat = (a :: dst :: src :: size :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hmframe : hs.memoryFrames =
      ({ base := off, established := len } : Evm.MemoryFrame) :: mfrest)
    (prof : ExecutionProfile)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hfork : Amsterdam ≤ prof.1)
    (pid : Evm.Defs.address → PrecompileId)
    (hpid : ∀ hs', runS (Evm.Functions.precompile_id_for_address
        (Evm.Functions.word_to_address a)) hs' ss =
      .ok (pid (Evm.Functions.word_to_address a), hs') ss)
    (warmb : Bool) (hwarmb : (if (pid (Evm.Functions.word_to_address a)
          != PrecompileId.NotPrecompile) then true
        else decide (hs.warmEpoch ≤ (assocGet hs.warmAddresses
          (Evm.Functions.word_to_address a)).getD 0)) = warmb)
    (haccess : extcodesizeCost warmb ≤ g)
    (hswf : size < 2 ^ 256)
    (hcopy : G_copy_word * Evm.Functions.memory_word_count size
      ≤ g - extcodesizeCost warmb)
    (hz : size ≠ 0)
    (hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (dst + size)
      ≤ g - extcodesizeCost warmb -
        G_copy_word * Evm.Functions.memory_word_count size)
    (hreq : dst + size ≤ 2 ^ 32 - 32)
    (hgrow : len < dst + size)
    (hostAfter : List (Evm.Defs.address × Nat) → Array byte →
      List Evm.MemoryFrame → Evm.HostState)
    (hrun : ∀ ws memoryBytes fr mfrest dst src size,
      dst + size ≤ fr.established →
      runS (Evm.Functions.k_code_copy
          (Evm.Functions.word_to_address a) dst src size)
        { hs with
          warmAddresses := ws
          memoryBytes := memoryBytes
          memoryFrames := fr :: mfrest } ss =
        .ok ((), { hostAfter ws memoryBytes (fr :: mfrest) with
          memoryBytes := writeArrayBytes memoryBytes (fr.base + dst)
            (buffer_read code src size) }) ss) :
    runS (Evm.Functions.execute (.EXTCODECOPY ()) pc_in top
        ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, retreat4 top, (⟨off, dst + size, {}⟩ : EvmMemorySlice),
          g - extcodesizeCost warmb -
            G_copy_word * Evm.Functions.memory_word_count size -
            Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
              (dst + size)),
        withMemoryBytes
          (hostAfter (wsAfterMark pid (Evm.Functions.word_to_address a) hs)
            (zeroMemoryRange hs.memoryBytes (off + len) (dst + size - len))
            (({ base := off, established := dst + size } : Evm.MemoryFrame)
              :: mfrest))
          (writeArrayBytes
            (zeroMemoryRange hs.memoryBytes (off + len) (dst + size - len))
            (off + dst) (buffer_read code src size))) ss := by
  obtain ⟨h1, h2, h3, h4, p1, p2, p3⟩ :=
    pop4_view top l a dst src size rest hpfx htop
  have hin : 4 ≤ top.toNat := by simp at htop; omega
  have hn : top.toNat = rest.length + 4 := by simpa using htop
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.EXTCODECOPY ()) = pure (4, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 4 0 hs ss hin
      (by have h : top.toNat - 4 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, extcodecopy_dispatch]
  have hbody : runS
      (Evm.Functions.execute_extcodecopy top ⟨off, len, msf⟩ g) hs ss =
      .ok ((retreat4 top, (⟨off, dst + size, {}⟩ : EvmMemorySlice),
          g - extcodesizeCost warmb -
            G_copy_word * Evm.Functions.memory_word_count size -
            Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
              (dst + size)),
        withMemoryBytes
          (hostAfter (wsAfterMark pid (Evm.Functions.word_to_address a) hs)
            (zeroMemoryRange hs.memoryBytes (off + len) (dst + size - len))
            (({ base := off, established := dst + size } : Evm.MemoryFrame)
              :: mfrest))
          (writeArrayBytes
            (zeroMemoryRange hs.memoryBytes (off + len) (dst + size - len))
            (off + dst) (buffer_read code src size))) ss := by
    simp only [Evm.Functions.execute_extcodecopy]
    refine runS_bind_ok
      (runS_pop top hs ss l frest a (dst :: src :: size :: rest)
        hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest dst (src :: size :: rest) hframe
        (by rw [h1]; exact p1) (by rw [h1]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest src (size :: rest) hframe
        (by rw [h2]; exact p2) (by rw [h2]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest size rest hframe
        (by rw [h3]; exact p3) (by rw [h3]; simp; omega)) ?_
    refine runS_bind_ok
      (by rw [runS_k_account_is_warm pid _ hs ss (hpid hs), hwarmb]) ?_
    refine runS_bind_ok (runS_account_cost warmb hs ss prof hprof hfork) ?_
    refine runS_bind_ok
      (runS_external_code_read_cost hs ss prof hprof hfork) ?_
    refine runS_bind_ok (runS_charge_ok g _ hs ss
      (by simpa [extcodesizeCost] using haccess)) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_charge_copy_ok (g - extcodesizeCost warmb) size hs ss hswf
        hcopy) ?_
    rw [dif_neg (by simp)]
    rw [memory_required_size_pos dst size (by simpa using hz)]
    refine runS_bind_ok (runS_charge_ok _ _ hs ss hexp) ?_
    rw [dif_neg (by simp)]
    have hreq' : dst + size ≤ 2 ^ 32 - 1 :=
      le_trans hreq (by norm_num)
    refine runS_bind_ok
      (runS_memory_access_ok dst size hs ss (by simpa using hz)
        (le_trans (Nat.le_add_right dst size) hreq')
        (Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hreq'))) ?_
    refine runS_bind_ok
      (runS_expand_memory_grow off len (dst + size) msf hs ss len mfrest
        hmframe rfl hgrow) ?_
    let expanded : Evm.HostState :=
      { hs with
        memoryBytes := zeroMemoryRange hs.memoryBytes (off + len)
          (dst + size - len)
        memoryFrames :=
          ({ base := off, established := dst + size } : Evm.MemoryFrame)
            :: mfrest }
    refine runS_bind_ok
      (runS_k_account_mark_warm pid _ expanded ss (hpid expanded)) ?_
    have hws : wsAfterMark pid (Evm.Functions.word_to_address a) expanded =
        wsAfterMark pid (Evm.Functions.word_to_address a) hs := rfl
    rw [hws]
    refine runS_bind_ok (hrun
      (wsAfterMark pid (Evm.Functions.word_to_address a) hs)
      (zeroMemoryRange hs.memoryBytes (off + len) (dst + size - len))
      ({ base := off, established := dst + size } : Evm.MemoryFrame)
      mfrest dst src size (le_refl _)) ?_
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
/-- Success inside the established window. -/
theorem runS_execute_extcodecopy_ok_nogrow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word))
    (a dst src size : word) (rest : List word) (code : Bytes)
    (mfrest : List Evm.MemoryFrame)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (a :: dst :: src :: size :: rest).reverse)
    (htop : top.toNat = (a :: dst :: src :: size :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hmframe : hs.memoryFrames =
      ({ base := off, established := len } : Evm.MemoryFrame) :: mfrest)
    (prof : ExecutionProfile)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hfork : Amsterdam ≤ prof.1)
    (pid : Evm.Defs.address → PrecompileId)
    (hpid : ∀ hs', runS (Evm.Functions.precompile_id_for_address
        (Evm.Functions.word_to_address a)) hs' ss =
      .ok (pid (Evm.Functions.word_to_address a), hs') ss)
    (warmb : Bool) (hwarmb : (if (pid (Evm.Functions.word_to_address a)
          != PrecompileId.NotPrecompile) then true
        else decide (hs.warmEpoch ≤ (assocGet hs.warmAddresses
          (Evm.Functions.word_to_address a)).getD 0)) = warmb)
    (haccess : extcodesizeCost warmb ≤ g)
    (hswf : size < 2 ^ 256)
    (hcopy : G_copy_word * Evm.Functions.memory_word_count size
      ≤ g - extcodesizeCost warmb)
    (hz : size ≠ 0)
    (hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩ (dst + size)
      ≤ g - extcodesizeCost warmb -
        G_copy_word * Evm.Functions.memory_word_count size)
    (hreq : dst + size ≤ 2 ^ 32 - 32)
    (hgrow : dst + size ≤ len)
    (hostAfter : List (Evm.Defs.address × Nat) → Array byte →
      List Evm.MemoryFrame → Evm.HostState)
    (hrun : ∀ ws memoryBytes fr mfrest dst src size,
      dst + size ≤ fr.established →
      runS (Evm.Functions.k_code_copy
          (Evm.Functions.word_to_address a) dst src size)
        { hs with
          warmAddresses := ws
          memoryBytes := memoryBytes
          memoryFrames := fr :: mfrest } ss =
        .ok ((), { hostAfter ws memoryBytes (fr :: mfrest) with
          memoryBytes := writeArrayBytes memoryBytes (fr.base + dst)
            (buffer_read code src size) }) ss) :
    runS (Evm.Functions.execute (.EXTCODECOPY ()) pc_in top
        ⟨off, len, msf⟩ g) hs ss =
      .ok ((pc_in, retreat4 top, (⟨off, len, msf⟩ : EvmMemorySlice),
          g - extcodesizeCost warmb -
            G_copy_word * Evm.Functions.memory_word_count size -
            Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
              (dst + size)),
        withMemoryBytes
          (hostAfter (wsAfterMark pid (Evm.Functions.word_to_address a) hs)
            hs.memoryBytes
            (({ base := off, established := len } : Evm.MemoryFrame) :: mfrest))
          (writeArrayBytes hs.memoryBytes (off + dst)
            (buffer_read code src size))) ss := by
  obtain ⟨h1, h2, h3, h4, p1, p2, p3⟩ :=
    pop4_view top l a dst src size rest hpfx htop
  have hin : 4 ≤ top.toNat := by simp at htop; omega
  have hn : top.toNat = rest.length + 4 := by simpa using htop
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.EXTCODECOPY ()) = pure (4, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 4 0 hs ss hin
      (by have h : top.toNat - 4 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, extcodecopy_dispatch]
  have hbody : runS
      (Evm.Functions.execute_extcodecopy top ⟨off, len, msf⟩ g) hs ss =
      .ok ((retreat4 top, (⟨off, len, msf⟩ : EvmMemorySlice),
          g - extcodesizeCost warmb -
            G_copy_word * Evm.Functions.memory_word_count size -
            Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
              (dst + size)),
        withMemoryBytes
          (hostAfter (wsAfterMark pid (Evm.Functions.word_to_address a) hs)
            hs.memoryBytes
            (({ base := off, established := len } : Evm.MemoryFrame) :: mfrest))
          (writeArrayBytes hs.memoryBytes (off + dst)
            (buffer_read code src size))) ss := by
    simp only [Evm.Functions.execute_extcodecopy]
    refine runS_bind_ok
      (runS_pop top hs ss l frest a (dst :: src :: size :: rest)
        hframe hpfx htop) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest dst (src :: size :: rest) hframe
        (by rw [h1]; exact p1) (by rw [h1]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest src (size :: rest) hframe
        (by rw [h2]; exact p2) (by rw [h2]; simp; omega)) ?_
    refine runS_bind_ok
      (runS_pop _ hs ss l frest size rest hframe
        (by rw [h3]; exact p3) (by rw [h3]; simp; omega)) ?_
    refine runS_bind_ok
      (by rw [runS_k_account_is_warm pid _ hs ss (hpid hs), hwarmb]) ?_
    refine runS_bind_ok (runS_account_cost warmb hs ss prof hprof hfork) ?_
    refine runS_bind_ok
      (runS_external_code_read_cost hs ss prof hprof hfork) ?_
    refine runS_bind_ok (runS_charge_ok g _ hs ss
      (by simpa [extcodesizeCost] using haccess)) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_charge_copy_ok (g - extcodesizeCost warmb) size hs ss hswf
        hcopy) ?_
    rw [dif_neg (by simp)]
    rw [memory_required_size_pos dst size (by simpa using hz)]
    refine runS_bind_ok (runS_charge_ok _ _ hs ss hexp) ?_
    rw [dif_neg (by simp)]
    have hreq' : dst + size ≤ 2 ^ 32 - 1 :=
      le_trans hreq (by norm_num)
    refine runS_bind_ok
      (runS_memory_access_ok dst size hs ss (by simpa using hz)
        (le_trans (Nat.le_add_right dst size) hreq')
        (Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hreq'))) ?_
    refine runS_bind_ok
      (runS_expand_memory_le off len (dst + size) msf hs ss hgrow) ?_
    refine runS_bind_ok
      (runS_k_account_mark_warm pid _ hs ss (hpid hs)) ?_
    rw [hmframe]
    refine runS_bind_ok (hrun
      (wsAfterMark pid (Evm.Functions.word_to_address a) hs)
      hs.memoryBytes
      ({ base := off, established := len } : Evm.MemoryFrame)
      mfrest dst src size hgrow) ?_
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

/-! ## The step equivalence -/

/-- Success post-relation: memory/state plus address warmth. -/
def ExtcodecopyPost (pid : Evm.Defs.address → PrecompileId)
    (sR' : Machine) (step : EvmStep)
    (hs' : Evm.HostState) (ss' : SeqState) : Prop :=
  MemPost sR' step hs' ss' ∧ WarmAddrRel pid sR' hs'

open Evm.Functions in
/-- **EXTCODECOPY, all reachable outcomes.** The theorem covers four stack
underflows, access/copy/expansion OOG, and zero/grow/in-window success for
both warm and cold targets. The only world-state premise is
`ExternalCodeRel`, which fixes the exact arbitrary-account bytes. -/
theorem extcodecopy_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (off len : Nat)
    (msf : EvmMemorySliceFields off len) (pc_in : Nat)
    (pid : Evm.Defs.address → PrecompileId)
    (hrel : StateRel sRef top g hs ss)
    (hmem : MemoryRel sRef.evm.memory hs off len)
    (hsafe : MemGasSafe sRef.evm.memory sRef.evm.gasLeft)
    (hwrel : WarmAddrRel pid sRef hs)
    (hpc : pc_in = sRef.evm.pc + 1)
    (hpid : ∀ aV hs', runS
      (Evm.Functions.precompile_id_for_address aV) hs' ss =
        .ok (pid aV, hs') ss)
    (hagree : ∀ (a dst src size : U256) (rest : List U256),
      sRef.evm.stack = a :: dst :: src :: size :: rest →
      ExternalCodeRel sRef hs ss a) :
    StepResultRel (ExtcodecopyPost pid) (runR iExtcodecopy sRef)
      (runS (Evm.Functions.execute (.EXTCODECOPY ()) pc_in top
        ⟨off, len, msf⟩ g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩,
    ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_iExtcodecopy_underflow_nil sRef hS,
      runS_execute_extcodecopy_underflow pc_in top off len g msf hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | [a] =>
    rw [hS] at hpfx htop
    rw [runR_iExtcodecopy_underflow_one sRef a hS,
      runS_execute_extcodecopy_underflow pc_in top off len g msf hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | [a, dst] =>
    rw [hS] at hpfx htop
    rw [runR_iExtcodecopy_underflow_two sRef a dst hS,
      runS_execute_extcodecopy_underflow pc_in top off len g msf hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | [a, dst, src] =>
    rw [hS] at hpfx htop
    rw [runR_iExtcodecopy_underflow_three sRef a dst src hS,
      runS_execute_extcodecopy_underflow pc_in top off len g msf hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | a :: dst :: src :: size :: rest =>
    rw [hS] at hpfx htop hlim hwfS
    obtain ⟨acct, code, ts1, ts2, hostAfter, hacc, hcode, hkcode,
      hframes, hmframes, hslots, hepoch⟩ := hagree a dst src size rest hS
    obtain ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩ := hmem
    have hin : 4 ≤ top.toNat := by simp at htop; omega
    have hlim' : top.toNat ≤ 1024 := by simp at htop hlim; omega
    have hsize : size < 2 ^ 256 := hwfS size (by simp)
    obtain ⟨hret1, hret2, hret3, hret4, hpfx1, hpfx2, hpfx3⟩ :=
      pop4_view top l a dst src size rest hpfx htop
    have hn : top.toNat = rest.length + 4 := by simpa using htop
    have hpfx4 : l.take (top.toNat - 4) = rest.reverse :=
      take_shrink l _ size _
        (by rw [show top.toNat - 4 + 1 = top.toNat - 3 from by omega]
            exact hpfx3)
        (by omega)
    have hpost := fun (hs' : Evm.HostState)
        (hframe' : hs'.stackFrames = l :: frest) =>
      (⟨⟨l, frest, hframe', by rw [hret4]; exact hpfx4, by
          rw [hret4]; omega⟩,
        by rw [hret4]; omega,
        by omega,
        fun w hw => hwfS w (by simp [hw])⟩ : StackRel rest hs' (retreat4 top))
    have hwcSize : (ceil32 size : Nat) / 32 =
        Evm.Functions.memory_word_count size := by
      rw [ceil32_eq]
      show (32 * Evm.Functions.memory_word_count size : Nat) / 32 = _
      omega
    have hcost : (calculate_gas_extend_memory sRef.evm.memory.length
        [(dst, size)]).cost =
        Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
          (Evm.Functions.memory_required_size dst size) :=
      extend_cost_eq sRef.evm.memory off len dst size msf haligned
    have hsplit (warmb : Bool) :
        extcodecopyCost warmb sRef.evm.memory.length dst size =
          extcodesizeCost warmb +
            3 * Evm.Functions.memory_word_count size +
            Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
              (Evm.Functions.memory_required_size dst size) := by
      rw [extcodecopyCost, hwcSize, ← hcost]
      rfl
    have hiff := hwrel (Evm.Functions.word_to_address a)
    rw [word_to_address_toList] at hiff
    set aV := Evm.Functions.word_to_address a with haV
    cases hwc : sRef.evm.accessedAddresses.contains (to_address_masked a) with
    | true =>
      have heff := hiff.mp hwc
      have hwb : (if (pid aV != PrecompileId.NotPrecompile) then true
          else decide (hs.warmEpoch ≤
            (assocGet hs.warmAddresses aV).getD 0)) = true := by
        by_cases hp : (pid aV != PrecompileId.NotPrecompile) = true
        · rw [if_pos hp]
        · rw [if_neg hp]
          rcases heff with hpre | hle
          · exact absurd (bne_iff_ne.mpr hpre) hp
          · exact decide_eq_true hle
      by_cases hg : sRef.evm.gasLeft <
          extcodecopyCost true sRef.evm.memory.length dst size
      · rw [runR_iExtcodecopy_warm_oog sRef a dst src size rest hS hwc hg]
        have hgN : g < extcodesizeCost true +
            3 * Evm.Functions.memory_word_count size +
            Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
              (Evm.Functions.memory_required_size dst size) := by
          rw [← hsplit true, hlive]
          exact hg
        by_cases ha : g < extcodesizeCost true
        · rw [runS_execute_extcodecopy_oog_access pc_in top off len g msf hs
            ss l frest a dst src size rest hframe hpfx htop hlim' prof
            sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork pid
            (hpid aV hs) true hwb ha]
          exact StepResultRel.halted ErrorRel.outOfGas
            (haltRegs_frame_status ss msg .OutOfGas)
        · push Not at ha
          by_cases hc : g - extcodesizeCost true <
              G_copy_word * Evm.Functions.memory_word_count size
          · rw [runS_execute_extcodecopy_oog_copy pc_in top off len g msf hs
              ss l frest a dst src size rest hframe hpfx htop hlim' prof
              sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork pid
              (hpid aV hs) true hwb ha hsize hc]
            exact StepResultRel.halted ErrorRel.outOfGas
              (haltRegs_frame_status ss msg .OutOfGas)
          · push Not at hc
            unfold Evm.Functions.G_copy_word at hc
            rw [runS_execute_extcodecopy_oog_exp pc_in top off len g msf hs
              ss l frest a dst src size rest hframe hpfx htop hlim' prof
              sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork pid
              (hpid aV hs) true hwb ha hsize hc (by
                show g - extcodesizeCost true -
                    3 * Evm.Functions.memory_word_count size < _
                omega)]
            exact StepResultRel.halted ErrorRel.outOfGas
              (haltRegs_frame_status ss msg .OutOfGas)
      · push Not at hg
        have htotal : extcodecopyCost true sRef.evm.memory.length dst size
            ≤ g := by rw [hlive]; exact hg
        have htotal' : extcodesizeCost true +
              3 * Evm.Functions.memory_word_count size +
              Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                (Evm.Functions.memory_required_size dst size) ≤ g := by
          rw [← hsplit true]
          exact htotal
        have ha : extcodesizeCost true ≤ g := by
          rw [hsplit true] at htotal
          omega
        have hc : G_copy_word * Evm.Functions.memory_word_count size ≤
            g - extcodesizeCost true := by
          unfold Evm.Functions.G_copy_word
          apply Nat.le_sub_of_add_le
          exact le_trans (by omega :
            3 * Evm.Functions.memory_word_count size +
              extcodesizeCost true ≤
            extcodesizeCost true +
              3 * Evm.Functions.memory_word_count size +
              Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                (Evm.Functions.memory_required_size dst size)) htotal'
        have he : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
              (Evm.Functions.memory_required_size dst size) ≤
            g - extcodesizeCost true -
              G_copy_word * Evm.Functions.memory_word_count size := by
          unfold Evm.Functions.G_copy_word
          apply Nat.le_sub_of_add_le
          apply Nat.le_sub_of_add_le
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal'
        rw [runR_iExtcodecopy_warm_success sRef a dst src size rest acct code
          ts1 ts2 hS hwc hg hacc hcode]
        by_cases hz0 : size = 0
        · subst size
          have hzero : (calculate_gas_extend_memory sRef.evm.memory.length
              [(dst, 0)]) = { cost := 0, expandBy := 0 } := by
            rw [calc_extend_single]
            rfl
          rw [runS_execute_extcodecopy_ok_zero pc_in top off len g msf hs ss
            l frest a dst src rest code mfrest hframe hpfx htop hlim'
            hmframe prof hprof hfork pid (hpid aV) true hwb ha hostAfter
            hkcode]
          rw [hzero, buffer_read_nil, show
            (({ cost := 0, expandBy := 0 } :
              EvmAsm.Stateless.SpecRef.ExtendMemory).expandBy : Nat) = 0
            from rfl]
          simp only [List.replicate_zero, List.append_nil, memory_write_nil]
          have hcost0 : extcodecopyCost true sRef.evm.memory.length dst 0 =
              extcodesizeCost true := by
            rw [extcodecopyCost, hzero]
            rfl
          simp only [withMemoryBytes, writeArrayBytes]
          refine StepResultRel.success ?_
          refine ⟨⟨⟨hpost _ (by rw [hframes]; exact hframe), ?_,
            ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
            ⟨msg, hmsg⟩⟩, by simp [hpc], ?_⟩, ?_⟩
          · refine ⟨?_, hres, hsp⟩
            rw [hcost0, hlive]
          · refine ⟨off, len, msf, rfl, ?_, ?_⟩
            · apply memoryRel_host_congr sRef.evm.memory hs _ off len
                ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩
              · rfl
              · rw [hmframes]
                exact hmframe.symm
            · exact memGasSafe_mono_gas sRef.evm.memory (Nat.sub_le _ _)
                hsafe
          · intro bV
            rw [hslots, hepoch]
            by_cases hp : (pid aV != PrecompileId.NotPrecompile) = true
            · rw [show wsAfterMark pid aV hs = hs.warmAddresses from by
                unfold wsAfterMark; rw [if_pos hp]]
              exact hwrel bV
            · rw [show wsAfterMark pid aV hs =
                  assocPut hs.warmAddresses aV hs.warmEpoch from by
                unfold wsAfterMark; rw [if_neg hp]]
              have hmark := warmaddr_after_mark pid
                sRef.evm.accessedAddresses hs.warmAddresses hs.warmEpoch aV
                hwrel bV
              rw [word_to_address_toList,
                setAdd_eq_of_contains _ _ hwc] at hmark
              exact hmark
        · have hz : (size == 0) = false := by simpa using hz0
          rw [memory_required_size_pos dst size hz] at hcost he
          have hreq : dst + size ≤ 2 ^ 32 - 32 :=
            safe_required_bound sRef.evm.memory off len (dst + size)
              (g - extcodesizeCost true -
                G_copy_word * Evm.Functions.memory_word_count size)
              sRef.evm.gasLeft msf haligned hsafe
              (le_trans (Nat.sub_le _ _) (le_trans (Nat.sub_le _ _)
                (le_of_eq hlive))) he
          have hexpandBy : ((calculate_gas_extend_memory
              sRef.evm.memory.length [(dst, size)]).expandBy : Nat) =
              32 * Evm.Functions.memory_word_count (dst + size) -
                sRef.evm.memory.length := by
            have hiff0 : ∀ x y : Nat, (32 * x ≤ 32 * y) ↔ (x ≤ y) :=
              fun x y => by omega
            have hwcM : Evm.Functions.memory_word_count
                sRef.evm.memory.length =
                Evm.Functions.memory_word_count len := by
              rw [haligned, memory_word_count_eq, memory_word_count_eq]
              omega
            have hiff : ((ceil32 (dst + size) : Nat) ≤
                ceil32 sRef.evm.memory.length) ↔
                (Evm.Functions.memory_word_count (dst + size) ≤
                  Evm.Functions.memory_word_count len) := by
              rw [ceil32_eq, ceil32_eq, hwcM]
              exact hiff0 _ _
            rw [calc_extend_single]
            rw [if_neg (by simpa using hz0)]
            by_cases hle : Evm.Functions.memory_word_count (dst + size) ≤
                Evm.Functions.memory_word_count len
            · rw [if_pos (hiff.mpr hle)]
              show (0 : Nat) = _
              have h1 : 32 * Evm.Functions.memory_word_count (dst + size) ≤
                  sRef.evm.memory.length := by rw [haligned]; omega
              omega
            · rw [if_neg (fun hc => hle (hiff.mp hc))]
              show ((ceil32 (dst + size) : Nat) -
                  ceil32 sRef.evm.memory.length) = _
              rw [ceil32_eq, ceil32_eq, hwcM, ← haligned]
          have hvlen : (buffer_read code src size).length = size :=
            buffer_read_length _ _ _
          have hgas' : g - extcodesizeCost true -
                G_copy_word * Evm.Functions.memory_word_count size -
                Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                  (dst + size) =
              (sRef.evm.gasLeft : Nat) -
                extcodecopyCost true sRef.evm.memory.length dst size := by
            unfold Evm.Functions.G_copy_word
            rw [hsplit true, ← hlive,
              memory_required_size_pos dst size hz]
            omega
          by_cases hgrow : len < dst + size
          · rw [runS_execute_extcodecopy_ok_grow pc_in top off len g msf hs
              ss l frest a dst src size rest code mfrest hframe hpfx htop
              hlim' hmframe prof hprof hfork pid (hpid aV) true hwb ha
              hsize hc hz0 he hreq hgrow hostAfter hkcode]
            have hrel' := memoryRel_expand sRef.evm.memory hs off len
              (dst + size) mfrest
              ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩ hgrow
            have hrelStored := memoryRel_write _ _ off (dst + size) dst
              (buffer_read code src size) hrel' (by rw [hvlen])
            rw [hexpandBy]
            refine StepResultRel.success ?_
            refine ⟨⟨⟨hpost _ (by simp only [withMemoryBytes]; rw [hframes]; exact hframe), ?_,
              ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
              ⟨msg, hmsg⟩⟩, by simp [hpc], ?_⟩, ?_⟩
            · exact ⟨hgas', hres, hsp⟩
            · refine ⟨off, dst + size, {}, rfl, ?_, ?_⟩
              · apply memoryRel_host_congr _ _ _ off (dst + size) hrelStored
                · rfl
                · simp only [withMemoryBytes]
                  exact hmframes _ _ _
              · show MemGasSafe _ (sRef.evm.gasLeft - extcodecopyCost true
                    sRef.evm.memory.length dst size)
                have hsafe2 := memGasSafe_after_expand sRef.evm.memory off
                  len (dst + size) sRef.evm.gasLeft
                  (extcodecopyCost true sRef.evm.memory.length dst size)
                  msf haligned hsafe (by rw [hsplit true,
                    memory_required_size_pos dst size hz]; omega) hg
                unfold MemGasSafe at hsafe2 ⊢
                rw [memory_write_length _ _ _ (by
                  rw [hvlen]
                  simp only [List.length_append, List.length_replicate]
                  have h32 := le_32_wc (dst + size)
                  have hwcm := wc_mono (Nat.le_of_lt hgrow)
                  omega)]
                exact hsafe2
            · intro bV
              simp only [withMemoryBytes]
              rw [hslots, hepoch]
              by_cases hp : (pid aV != PrecompileId.NotPrecompile) = true
              · rw [show wsAfterMark pid aV hs = hs.warmAddresses from by
                    unfold wsAfterMark; rw [if_pos hp]]
                exact hwrel bV
              · rw [show wsAfterMark pid aV hs =
                      assocPut hs.warmAddresses aV hs.warmEpoch from by
                    unfold wsAfterMark; rw [if_neg hp]]
                have hmark := warmaddr_after_mark pid
                  sRef.evm.accessedAddresses hs.warmAddresses hs.warmEpoch aV
                  hwrel bV
                rw [word_to_address_toList,
                  setAdd_eq_of_contains _ _ hwc] at hmark
                exact hmark
          · push Not at hgrow
            rw [runS_execute_extcodecopy_ok_nogrow pc_in top off len g msf
              hs ss l frest a dst src size rest code mfrest hframe hpfx htop
              hlim' hmframe prof hprof hfork pid (hpid aV) true hwb ha
              hsize hc hz0 he hreq hgrow hostAfter hkcode]
            have hrelStored := memoryRel_write sRef.evm.memory hs off len dst
              (buffer_read code src size)
              ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩
              (by rw [hvlen]; exact hgrow)
            have hzero : (0 : Nat) = (calculate_gas_extend_memory
                sRef.evm.memory.length [(dst, size)]).expandBy := by
              rw [hexpandBy]
              have hwcm := wc_mono hgrow
              have hal := haligned
              rw [memory_word_count_eq] at hwcm hal ⊢
              omega
            rw [← hzero]
            simp only [List.replicate_zero, List.append_nil]
            refine StepResultRel.success ?_
            refine ⟨⟨⟨hpost _ (by simp only [withMemoryBytes]; rw [hframes]; exact hframe), ?_,
              ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
              ⟨msg, hmsg⟩⟩, by simp [hpc], ?_⟩, ?_⟩
            · exact ⟨hgas', hres, hsp⟩
            · refine ⟨off, len, msf, rfl, ?_, ?_⟩
              · apply memoryRel_host_congr _ _ _ off len hrelStored
                · rfl
                · simp only [withMemoryBytes]
                  rw [hmframes]
                  exact hmframe.symm
              · show MemGasSafe _ (sRef.evm.gasLeft - extcodecopyCost true
                    sRef.evm.memory.length dst size)
                have hsafe2 := memGasSafe_mono_gas sRef.evm.memory
                  (g' := sRef.evm.gasLeft - extcodecopyCost true
                    sRef.evm.memory.length dst size)
                  (Nat.sub_le _ _) hsafe
                unfold MemGasSafe at hsafe2 ⊢
                rw [memory_write_length _ _ _ (by
                  rw [hvlen]
                  have h32 := le_32_wc len
                  omega)]
                exact hsafe2
            · intro bV
              simp only [withMemoryBytes]
              rw [hslots, hepoch]
              by_cases hp : (pid aV != PrecompileId.NotPrecompile) = true
              · rw [show wsAfterMark pid aV hs = hs.warmAddresses from by
                    unfold wsAfterMark; rw [if_pos hp]]
                exact hwrel bV
              · rw [show wsAfterMark pid aV hs =
                      assocPut hs.warmAddresses aV hs.warmEpoch from by
                    unfold wsAfterMark; rw [if_neg hp]]
                have hmark := warmaddr_after_mark pid
                  sRef.evm.accessedAddresses hs.warmAddresses hs.warmEpoch aV
                  hwrel bV
                rw [word_to_address_toList,
                  setAdd_eq_of_contains _ _ hwc] at hmark
                exact hmark
    | false =>
      have hnot : pid aV = PrecompileId.NotPrecompile ∧
          ¬ hs.warmEpoch ≤ (assocGet hs.warmAddresses aV).getD 0 := by
        by_cases hp : pid aV = PrecompileId.NotPrecompile
        · refine ⟨hp, fun hle => ?_⟩
          rw [hiff.mpr (Or.inr hle)] at hwc
          cases hwc
        · exfalso
          rw [hiff.mpr (Or.inl hp)] at hwc
          cases hwc
      have hwb : (if (pid aV != PrecompileId.NotPrecompile) then true
          else decide (hs.warmEpoch ≤
            (assocGet hs.warmAddresses aV).getD 0)) = false := by
        rw [if_neg (by simp [hnot.1]), decide_eq_false hnot.2]
      have hws : wsAfterMark pid aV hs =
          assocPut hs.warmAddresses aV hs.warmEpoch := by
        unfold wsAfterMark
        rw [if_neg (by simp [hnot.1])]
      by_cases hg : sRef.evm.gasLeft <
          extcodecopyCost false sRef.evm.memory.length dst size
      · rw [runR_iExtcodecopy_cold_oog sRef a dst src size rest hS hwc hg]
        have hgN : g < extcodesizeCost false +
            3 * Evm.Functions.memory_word_count size +
            Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
              (Evm.Functions.memory_required_size dst size) := by
          rw [← hsplit false, hlive]
          exact hg
        by_cases ha : g < extcodesizeCost false
        · rw [runS_execute_extcodecopy_oog_access pc_in top off len g msf hs
            ss l frest a dst src size rest hframe hpfx htop hlim' prof
            sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork pid
            (hpid aV hs) false hwb ha]
          exact StepResultRel.halted ErrorRel.outOfGas
            (haltRegs_frame_status ss msg .OutOfGas)
        · push Not at ha
          by_cases hc : g - extcodesizeCost false <
              G_copy_word * Evm.Functions.memory_word_count size
          · rw [runS_execute_extcodecopy_oog_copy pc_in top off len g msf hs
              ss l frest a dst src size rest hframe hpfx htop hlim' prof
              sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork pid
              (hpid aV hs) false hwb ha hsize hc]
            exact StepResultRel.halted ErrorRel.outOfGas
              (haltRegs_frame_status ss msg .OutOfGas)
          · push Not at hc
            unfold Evm.Functions.G_copy_word at hc
            rw [runS_execute_extcodecopy_oog_exp pc_in top off len g msf hs
              ss l frest a dst src size rest hframe hpfx htop hlim' prof
              sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork pid
              (hpid aV hs) false hwb ha hsize hc (by
                show g - extcodesizeCost false -
                    3 * Evm.Functions.memory_word_count size < _
                omega)]
            exact StepResultRel.halted ErrorRel.outOfGas
              (haltRegs_frame_status ss msg .OutOfGas)
      · push Not at hg
        have htotal : extcodecopyCost false sRef.evm.memory.length dst size
            ≤ g := by rw [hlive]; exact hg
        have htotal' : extcodesizeCost false +
              3 * Evm.Functions.memory_word_count size +
              Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                (Evm.Functions.memory_required_size dst size) ≤ g := by
          rw [← hsplit false]
          exact htotal
        have ha : extcodesizeCost false ≤ g := by
          rw [hsplit false] at htotal
          omega
        have hc : G_copy_word * Evm.Functions.memory_word_count size ≤
            g - extcodesizeCost false := by
          unfold Evm.Functions.G_copy_word
          apply Nat.le_sub_of_add_le
          exact le_trans (by omega :
            3 * Evm.Functions.memory_word_count size +
              extcodesizeCost false ≤
            extcodesizeCost false +
              3 * Evm.Functions.memory_word_count size +
              Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                (Evm.Functions.memory_required_size dst size)) htotal'
        have he : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
              (Evm.Functions.memory_required_size dst size) ≤
            g - extcodesizeCost false -
              G_copy_word * Evm.Functions.memory_word_count size := by
          unfold Evm.Functions.G_copy_word
          apply Nat.le_sub_of_add_le
          apply Nat.le_sub_of_add_le
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal'
        rw [runR_iExtcodecopy_cold_success sRef a dst src size rest acct code
          ts1 ts2 hS hwc hg hacc hcode]
        by_cases hz0 : size = 0
        · subst size
          have hzero : (calculate_gas_extend_memory sRef.evm.memory.length
              [(dst, 0)]) = { cost := 0, expandBy := 0 } := by
            rw [calc_extend_single]
            rfl
          rw [runS_execute_extcodecopy_ok_zero pc_in top off len g msf hs ss
            l frest a dst src rest code mfrest hframe hpfx htop hlim'
            hmframe prof hprof hfork pid (hpid aV) false hwb ha hostAfter
            hkcode]
          rw [hzero, buffer_read_nil, show
            (({ cost := 0, expandBy := 0 } :
              EvmAsm.Stateless.SpecRef.ExtendMemory).expandBy : Nat) = 0
            from rfl]
          simp only [List.replicate_zero, List.append_nil, memory_write_nil]
          have hcost0 : extcodecopyCost false sRef.evm.memory.length dst 0 =
              extcodesizeCost false := by
            rw [extcodecopyCost, hzero]
            rfl
          simp only [withMemoryBytes, writeArrayBytes]
          refine StepResultRel.success ?_
          refine ⟨⟨⟨hpost _ (by rw [hframes]; exact hframe), ?_,
            ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
            ⟨msg, hmsg⟩⟩, by simp [hpc], ?_⟩, ?_⟩
          · refine ⟨?_, hres, hsp⟩
            rw [hcost0, hlive]
          · refine ⟨off, len, msf, rfl, ?_, ?_⟩
            · apply memoryRel_host_congr sRef.evm.memory hs _ off len
                ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩
              · rfl
              · rw [hmframes]
                exact hmframe.symm
            · exact memGasSafe_mono_gas sRef.evm.memory (Nat.sub_le _ _)
                hsafe
          · intro bV
            rw [hslots, hepoch]
            rw [hws]
            have hmark := warmaddr_after_mark pid
              sRef.evm.accessedAddresses hs.warmAddresses hs.warmEpoch aV
              hwrel bV
            rw [word_to_address_toList] at hmark
            exact hmark
        · have hz : (size == 0) = false := by simpa using hz0
          rw [memory_required_size_pos dst size hz] at hcost he
          have hreq : dst + size ≤ 2 ^ 32 - 32 :=
            safe_required_bound sRef.evm.memory off len (dst + size)
              (g - extcodesizeCost false -
                G_copy_word * Evm.Functions.memory_word_count size)
              sRef.evm.gasLeft msf haligned hsafe
              (le_trans (Nat.sub_le _ _) (le_trans (Nat.sub_le _ _)
                (le_of_eq hlive))) he
          have hexpandBy : ((calculate_gas_extend_memory
              sRef.evm.memory.length [(dst, size)]).expandBy : Nat) =
              32 * Evm.Functions.memory_word_count (dst + size) -
                sRef.evm.memory.length := by
            have hiff0 : ∀ x y : Nat, (32 * x ≤ 32 * y) ↔ (x ≤ y) :=
              fun x y => by omega
            have hwcM : Evm.Functions.memory_word_count
                sRef.evm.memory.length =
                Evm.Functions.memory_word_count len := by
              rw [haligned, memory_word_count_eq, memory_word_count_eq]
              omega
            have hiff : ((ceil32 (dst + size) : Nat) ≤
                ceil32 sRef.evm.memory.length) ↔
                (Evm.Functions.memory_word_count (dst + size) ≤
                  Evm.Functions.memory_word_count len) := by
              rw [ceil32_eq, ceil32_eq, hwcM]
              exact hiff0 _ _
            rw [calc_extend_single]
            rw [if_neg (by simpa using hz0)]
            by_cases hle : Evm.Functions.memory_word_count (dst + size) ≤
                Evm.Functions.memory_word_count len
            · rw [if_pos (hiff.mpr hle)]
              show (0 : Nat) = _
              have h1 : 32 * Evm.Functions.memory_word_count (dst + size) ≤
                  sRef.evm.memory.length := by rw [haligned]; omega
              omega
            · rw [if_neg (fun hc => hle (hiff.mp hc))]
              show ((ceil32 (dst + size) : Nat) -
                  ceil32 sRef.evm.memory.length) = _
              rw [ceil32_eq, ceil32_eq, hwcM, ← haligned]
          have hvlen : (buffer_read code src size).length = size :=
            buffer_read_length _ _ _
          have hgas' : g - extcodesizeCost false -
                G_copy_word * Evm.Functions.memory_word_count size -
                Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                  (dst + size) =
              (sRef.evm.gasLeft : Nat) -
                extcodecopyCost false sRef.evm.memory.length dst size := by
            unfold Evm.Functions.G_copy_word
            rw [hsplit false, ← hlive,
              memory_required_size_pos dst size hz]
            omega
          by_cases hgrow : len < dst + size
          · rw [runS_execute_extcodecopy_ok_grow pc_in top off len g msf hs
              ss l frest a dst src size rest code mfrest hframe hpfx htop
              hlim' hmframe prof hprof hfork pid (hpid aV) false hwb ha
              hsize hc hz0 he hreq hgrow hostAfter hkcode]
            have hrel' := memoryRel_expand sRef.evm.memory hs off len
              (dst + size) mfrest
              ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩ hgrow
            have hrelStored := memoryRel_write _ _ off (dst + size) dst
              (buffer_read code src size) hrel' (by rw [hvlen])
            rw [hexpandBy]
            refine StepResultRel.success ?_
            refine ⟨⟨⟨hpost _ (by simp only [withMemoryBytes]; rw [hframes]; exact hframe), ?_,
              ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
              ⟨msg, hmsg⟩⟩, by simp [hpc], ?_⟩, ?_⟩
            · exact ⟨hgas', hres, hsp⟩
            · refine ⟨off, dst + size, {}, rfl, ?_, ?_⟩
              · apply memoryRel_host_congr _ _ _ off (dst + size) hrelStored
                · rfl
                · simp only [withMemoryBytes]
                  exact hmframes _ _ _
              · show MemGasSafe _ (sRef.evm.gasLeft - extcodecopyCost false
                    sRef.evm.memory.length dst size)
                have hsafe2 := memGasSafe_after_expand sRef.evm.memory off
                  len (dst + size) sRef.evm.gasLeft
                  (extcodecopyCost false sRef.evm.memory.length dst size)
                  msf haligned hsafe (by rw [hsplit false,
                    memory_required_size_pos dst size hz]; omega) hg
                unfold MemGasSafe at hsafe2 ⊢
                rw [memory_write_length _ _ _ (by
                  rw [hvlen]
                  simp only [List.length_append, List.length_replicate]
                  have h32 := le_32_wc (dst + size)
                  have hwcm := wc_mono (Nat.le_of_lt hgrow)
                  omega)]
                exact hsafe2
            · intro bV
              simp only [withMemoryBytes]
              rw [hslots, hepoch]
              rw [hws]
              have hmark := warmaddr_after_mark pid
                sRef.evm.accessedAddresses hs.warmAddresses hs.warmEpoch aV
                hwrel bV
              rw [word_to_address_toList] at hmark
              exact hmark
          · push Not at hgrow
            rw [runS_execute_extcodecopy_ok_nogrow pc_in top off len g msf
              hs ss l frest a dst src size rest code mfrest hframe hpfx htop
              hlim' hmframe prof hprof hfork pid (hpid aV) false hwb ha
              hsize hc hz0 he hreq hgrow hostAfter hkcode]
            have hrelStored := memoryRel_write sRef.evm.memory hs off len dst
              (buffer_read code src size)
              ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩
              (by rw [hvlen]; exact hgrow)
            have hzero : (0 : Nat) = (calculate_gas_extend_memory
                sRef.evm.memory.length [(dst, size)]).expandBy := by
              rw [hexpandBy]
              have hwcm := wc_mono hgrow
              have hal := haligned
              rw [memory_word_count_eq] at hwcm hal ⊢
              omega
            rw [← hzero]
            simp only [List.replicate_zero, List.append_nil]
            refine StepResultRel.success ?_
            refine ⟨⟨⟨hpost _ (by simp only [withMemoryBytes]; rw [hframes]; exact hframe), ?_,
              ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
              ⟨msg, hmsg⟩⟩, by simp [hpc], ?_⟩, ?_⟩
            · exact ⟨hgas', hres, hsp⟩
            · refine ⟨off, len, msf, rfl, ?_, ?_⟩
              · apply memoryRel_host_congr _ _ _ off len hrelStored
                · rfl
                · simp only [withMemoryBytes]
                  rw [hmframes]
                  exact hmframe.symm
              · show MemGasSafe _ (sRef.evm.gasLeft - extcodecopyCost false
                    sRef.evm.memory.length dst size)
                have hsafe2 := memGasSafe_mono_gas sRef.evm.memory
                  (g' := sRef.evm.gasLeft - extcodecopyCost false
                    sRef.evm.memory.length dst size)
                  (Nat.sub_le _ _) hsafe
                unfold MemGasSafe at hsafe2 ⊢
                rw [memory_write_length _ _ _ (by
                  rw [hvlen]
                  have h32 := le_32_wc len
                  omega)]
                exact hsafe2
            · intro bV
              simp only [withMemoryBytes]
              rw [hslots, hepoch]
              rw [hws]
              have hmark := warmaddr_after_mark pid
                sRef.evm.accessedAddresses hs.warmAddresses hs.warmEpoch aV
                hwrel bV
              rw [word_to_address_toList] at hmark
              exact hmark


end EvmSpecsVerify
