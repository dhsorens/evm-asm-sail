import EvmSpecsVerify.Relations.Memory
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# MCOPY

The last unblocked memory opcode, and the only one whose **source is
memory itself**. Two things are new relative to
[`CALLDATACOPY`](Calldatacopy.lean):

* **Two extension ranges.** SpecRef asks for
  `[(source, length), (destination, length)]` in one
  `calculate_gas_extend_memory` fold; the extraction takes
  `max (memory_required_size destination length)
       (memory_required_size source length)`.
  [`calc_extend_pair_eq_single`](../Relations/Memory.lean) proves the
  fold telescopes — the pair is the single extension at
  `max destination source` — which is what lets this slice reuse
  `calc_extend_single` / `extend_cost_eq` unchanged.
* **An overlapping-safe copy.** Both sides snapshot the source *before*
  writing: SpecRef evaluates `memory_read_bytes e.memory source length`
  inside the same `modifyEvm` that writes, and the host's `mem_move`
  binds `values` from the pre-write array. So the two agree even when the
  ranges overlap, and no disjointness hypothesis is needed — this was
  worth checking, since a naive byte-at-a-time forward copy on either
  side would have diverged from the other on an overlap.
  [`memoryRel_read`](../Relations/Memory.lean) is the read direction of
  `memoryRel_write`; both read the *post-expansion* memory, because both
  sides expand before copying.

Charge split as for the rest of the copy family: SpecRef charges base +
per-word + expansion in **one** `charge_gas`, the extraction in three
stages, so one SpecRef OOG state maps to whichever stage fails first.
MM-6 (`MemGasSafe`) discharges the u32 `memory_access` guard.

Reachable outcomes: success ×3 (zero length / grow / in-window),
underflow ×3, OOG at any of the three charges; overflow is unreachable
(3-in/0-out).

Gas (MM-2): `OPCODE_MCOPY_BASE = 3 = G_verylow` and
`OPCODE_COPY_PER_WORD = 3 = G_copy_word`.
-/

open private pcAdd chargeWithMemory
  from EvmAsm.Stateless.SpecRef.InstructionsCore
open private writeArrayBytes readArrayBytes zeroMemoryRange
  from Evm.HostAxioms

set_option maxHeartbeats 4000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- The SpecRef MCOPY charge, with the two extension ranges already
collapsed to their upper bound by `calc_extend_pair_eq_single`. -/
def mcopyCost (msz x y z : Nat) : Nat :=
  GasCosts.OPCODE_MCOPY_BASE
    + GasCosts.OPCODE_COPY_PER_WORD * (ceil32 z / 32)
    + (calculate_gas_extend_memory msz [(max x y, z)]).cost

/-- The extraction's `if a <b b then b else a` idiom is `max`. -/
theorem blt_if_max (a b : Nat) :
    (if ((a <b b) : Bool) = true then b else a) = max a b := by
  by_cases h : a < b
  · rw [if_pos (by simpa using h)]
    omega
  · rw [if_neg (by simpa using h)]
    omega

/-- SpecRef's pair of ranges is the extraction's single upper range. -/
theorem mcopy_extend_collapse (msz x y z : Nat) :
    calculate_gas_extend_memory msz [(y, z), (x, z)]
      = calculate_gas_extend_memory msz [(max x y, z)] := by
  rw [calc_extend_pair_eq_single msz y x z, Nat.max_comm]

/-! ## SpecRef run shapes -/

theorem runR_iMcopy_underflow_nil (s : Machine)
    (hstack : s.evm.stack = []) :
    runR iMcopy s = .ok (.error .stackUnderflow, s) := by
  simp only [iMcopy]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_iMcopy_underflow_one (s : Machine) (x : U256)
    (hstack : s.evm.stack = [x]) :
    runR iMcopy s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with stack := [] } }) := by
  simp only [iMcopy]
  refine runR_bind_ok (runR_stackPop_cons s x [] hstack) ?_
  exact runR_bind_err (runR_stackPop_nil _ (by simp))

theorem runR_iMcopy_underflow_two (s : Machine) (x y : U256)
    (hstack : s.evm.stack = [x, y]) :
    runR iMcopy s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with stack := [] } }) := by
  simp only [iMcopy]
  refine runR_bind_ok (runR_stackPop_cons s x [y] hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y [] (by simp)) ?_
  exact runR_bind_err (runR_stackPop_nil _ (by simp))

theorem runR_iMcopy_oog (s : Machine) (x y z : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: y :: z :: rest)
    (hgas : s.evm.gasLeft < mcopyCost s.evm.memory.length x y z) :
    runR iMcopy s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [iMcopy, chargeWithMemory, bind_assoc]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: z :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y (z :: rest) (by simp)) ?_
  refine runR_bind_ok (runR_stackPop_cons _ z rest (by simp)) ?_
  refine runR_bind_ok (runR_getEvm_map _ _) ?_
  refine runR_bind_err (runR_charge_gas_oog _ _ ?_)
  rw [mcopy_extend_collapse]
  simpa [mcopyCost] using hgas

theorem runR_iMcopy_success (s : Machine) (x y z : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: y :: z :: rest)
    (hgas : mcopyCost s.evm.memory.length x y z ≤ s.evm.gasLeft) :
    runR iMcopy s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := rest
            memory := memory_write
              (s.evm.memory ++ List.replicate
                (calculate_gas_extend_memory s.evm.memory.length
                  [(max x y, z)]).expandBy 0x00) x
              (memory_read_bytes
                (s.evm.memory ++ List.replicate
                  (calculate_gas_extend_memory s.evm.memory.length
                    [(max x y, z)]).expandBy 0x00) y z)
            gasLeft := s.evm.gasLeft - mcopyCost s.evm.memory.length x y z
            regularGasUsed :=
              s.evm.regularGasUsed + mcopyCost s.evm.memory.length x y z
            pc := s.evm.pc + 1 } }) := by
  simp only [iMcopy, chargeWithMemory, extendMemory, pcAdd, bind_assoc]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: z :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y (z :: rest) (by simp)) ?_
  refine runR_bind_ok (runR_stackPop_cons _ z rest (by simp)) ?_
  refine runR_bind_ok (runR_getEvm_map _ _) ?_
  rw [mcopy_extend_collapse]
  refine runR_bind_ok (runR_charge_gas _ _
    (by simpa [mcopyCost] using hgas)) ?_
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  exact runR_modifyEvm _ _

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for MCOPY. -/
theorem mcopy_dispatch (pc_in : Nat) (top : StackTop) (off len : Nat)
    (msf : EvmMemorySliceFields off len) (g : Nat) :
    Evm.Functions.execute_opcode (.MCOPY ()) pc_in top ⟨off, len, msf⟩ g =
      Evm.Functions.execute_mcopy top ⟨off, len, msf⟩ g >>= fun p =>
        pure (pc_in, p.1, p.2.1, p.2.2) := rfl

/-- `memory_required_size` for a nonzero size. -/
theorem mcopy_required_size_pos (x z : Nat) (hz : (z == 0) = false) :
    Evm.Functions.memory_required_size x z = x + z := by
  simp only [Evm.Functions.memory_required_size, hz, Bool.false_eq_true,
    if_false]

open Evm.Functions in
theorem runS_execute_mcopy_underflow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 3) :
    runS (Evm.Functions.execute (.MCOPY ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.MCOPY ()) = pure (3, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 3 0 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_mcopy_oog_base (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hin : 3 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (hgas : g < G_verylow) :
    runS (Evm.Functions.execute (.MCOPY ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top, ⟨off, len, msf⟩, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.MCOPY ()) = pure (3, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 3 0 hs ss hin
      (by have h : top.toNat - 3 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, mcopy_dispatch]
  have hbody : runS (Evm.Functions.execute_mcopy top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top, (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_mcopy]
    refine runS_bind_ok
      (runS_charge_oog g G_verylow hs ss prof sp msg hprof hsp hmsg hfork
        hgas) ?_
    rw [dif_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
theorem runS_execute_mcopy_oog_copy (pc_in : Nat) (top : StackTop)
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
    runS (Evm.Functions.execute (.MCOPY ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
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
    show Evm.Functions.opcode_stack_effect (.MCOPY ()) = pure (3, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 3 0 hs ss (by omega)
      (by have h : top.toNat - 3 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, mcopy_dispatch]
  have hbody : runS (Evm.Functions.execute_mcopy top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_mcopy]
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
theorem runS_execute_mcopy_oog_exp (pc_in : Nat) (top : StackTop)
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
    (hz : (z == 0) = false)
    (hzw : z < 2 ^ 256)
    (hbase : G_verylow ≤ g)
    (hcopy : G_copy_word * Evm.Functions.memory_word_count z
      ≤ g - G_verylow)
    (hgas : g - G_verylow - G_copy_word * Evm.Functions.memory_word_count z
      < Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
          (max x y + z)) :
    runS (Evm.Functions.execute (.MCOPY ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
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
    show Evm.Functions.opcode_stack_effect (.MCOPY ()) = pure (3, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 3 0 hs ss (by omega)
      (by have h : top.toNat - 3 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, mcopy_dispatch]
  have hbody : runS (Evm.Functions.execute_mcopy top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice), GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_mcopy]
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
    rw [mcopy_required_size_pos x z hz, mcopy_required_size_pos y z hz,
      blt_if_max, show max (x + z) (y + z) = max x y + z from by omega]
    refine runS_bind_ok
      (runS_charge_oog _ _ hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
    rw [dif_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
/-- Zero-length success: the copy is a no-op on both sides (SpecRef's
`memory_write _ _ []`, the extraction's `mem_mcopy` guard). -/
theorem runS_execute_mcopy_ok_zero (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y : Nat)
    (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: (0 : Nat) :: rest).reverse)
    (htop : top.toNat = (x :: y :: (0 : Nat) :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hbase : G_verylow ≤ g) :
    runS (Evm.Functions.execute (.MCOPY ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
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
    show Evm.Functions.opcode_stack_effect (.MCOPY ()) = pure (3, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 3 0 hs ss (by omega)
      (by have h : top.toNat - 3 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, mcopy_dispatch]
  have hbody : runS (Evm.Functions.execute_mcopy top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice), g - G_verylow), hs) ss := by
    simp only [Evm.Functions.execute_mcopy]
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
    rw [show Evm.Functions.memory_required_size x 0 = 0 from rfl,
      show Evm.Functions.memory_required_size y 0 = 0 from rfl]
    refine runS_bind_ok
      (runS_charge_ok _ _ hs ss
        (by simp [Evm.Functions.memory_expansion_cost,
          memory_high_water_eq, memory_word_count_eq])) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok (runS_memory_access_zero x hs ss) ?_
    refine runS_bind_ok (runS_memory_access_zero y hs ss) ?_
    refine runS_bind_ok
      (runS_expand_memory_le off len 0 msf hs ss (Nat.zero_le len)) ?_
    refine runS_bind_ok (runS_mem_mcopy_zero 0 0 hs ss) ?_
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

/-- The expanded host state, named to keep the run shapes free of
multi-line structure-update literals. -/
def mcopyExpanded (hs : Evm.HostState) (off len R : Nat)
    (mfrest : List Evm.MemoryFrame) : Evm.HostState :=
  { hs with
      memoryBytes := zeroMemoryRange hs.memoryBytes (off + len) (R - len)
      memoryFrames :=
        ({ base := off, established := R } : Evm.MemoryFrame) :: mfrest }

open Evm.Functions in
/-- Success with expansion: the window grows to `max destination source +
length`, then the memmove runs inside it. -/
theorem runS_execute_mcopy_ok_grow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y z : Nat)
    (rest : List word) (mfrest : List Evm.MemoryFrame)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: z :: rest).reverse)
    (htop : top.toNat = (x :: y :: z :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hmframe : hs.memoryFrames
      = ({ base := off, established := len } : Evm.MemoryFrame) :: mfrest)
    (hz : (z == 0) = false)
    (hzw : z < 2 ^ 256)
    (hbase : G_verylow ≤ g)
    (hcopy : G_copy_word * Evm.Functions.memory_word_count z
      ≤ g - G_verylow)
    (hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
        (max x y + z)
      ≤ g - G_verylow - G_copy_word * Evm.Functions.memory_word_count z)
    (hreq : max x y + z ≤ 2 ^ 32 - 32)
    (hgrow : len < max x y + z) :
    runS (Evm.Functions.execute (.MCOPY ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1
            - BitVec.ofNat 64 1,
          (⟨off, max x y + z, {}⟩ : EvmMemorySlice),
          g - G_verylow - G_copy_word * Evm.Functions.memory_word_count z
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                (max x y + z)),
        mcopyHost (mcopyExpanded hs off len (max x y + z) mfrest) off x y z)
        ss := by
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
    show Evm.Functions.opcode_stack_effect (.MCOPY ()) = pure (3, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 3 0 hs ss (by omega)
      (by have h : top.toNat - 3 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, mcopy_dispatch]
  have hbody : runS (Evm.Functions.execute_mcopy top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, max x y + z, {}⟩ : EvmMemorySlice),
          g - G_verylow - G_copy_word * Evm.Functions.memory_word_count z
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                (max x y + z)),
        mcopyHost (mcopyExpanded hs off len (max x y + z) mfrest)
          off x y z) ss := by
    simp only [Evm.Functions.execute_mcopy]
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
    rw [mcopy_required_size_pos x z hz, mcopy_required_size_pos y z hz,
      blt_if_max, show max (x + z) (y + z) = max x y + z from by omega]
    refine runS_bind_ok (runS_charge_ok _ _ hs ss hexp) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_memory_access_ok x z hs ss hz
        (show x ≤ 2 ^ 32 - 1 by omega)
        (show z ≤ 2 ^ 32 - 1 - x by omega)) ?_
    refine runS_bind_ok
      (runS_memory_access_ok y z hs ss hz
        (show y ≤ 2 ^ 32 - 1 by omega)
        (show z ≤ 2 ^ 32 - 1 - y by omega)) ?_
    rw [blt_if_max]
    simp only [Evm.Defs.MemoryAccessFields.required_size,
      Evm.Defs.MemoryRangeFields.off, Evm.Defs.MemoryRangeFields.len]
    rw [show max (x + z) (y + z) = max x y + z from by omega]
    refine runS_bind_ok
      (runS_expand_memory_grow off len (max x y + z) msf hs ss len mfrest
        hmframe rfl hgrow) ?_
    refine runS_bind_ok
      (runS_mem_mcopy x y z _ ss
        ({ base := off, established := max x y + z } : Evm.MemoryFrame)
        mfrest rfl (by simpa using hz) (by simp; omega)) ?_
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
/-- Success inside the established window: no expansion. -/
theorem runS_execute_mcopy_ok_nogrow (pc_in : Nat) (top : StackTop)
    (off len g : Nat) (msf : EvmMemorySliceFields off len)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y z : Nat)
    (rest : List word) (mfrest : List Evm.MemoryFrame)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: z :: rest).reverse)
    (htop : top.toNat = (x :: y :: z :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hmframe : hs.memoryFrames
      = ({ base := off, established := len } : Evm.MemoryFrame) :: mfrest)
    (hz : (z == 0) = false)
    (hzw : z < 2 ^ 256)
    (hbase : G_verylow ≤ g)
    (hcopy : G_copy_word * Evm.Functions.memory_word_count z
      ≤ g - G_verylow)
    (hexp : Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
        (max x y + z)
      ≤ g - G_verylow - G_copy_word * Evm.Functions.memory_word_count z)
    (hreq : max x y + z ≤ 2 ^ 32 - 32)
    (hgrow : max x y + z ≤ len) :
    runS (Evm.Functions.execute (.MCOPY ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1
            - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice),
          g - G_verylow - G_copy_word * Evm.Functions.memory_word_count z
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                (max x y + z)),
        mcopyHost hs off x y z) ss := by
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
    show Evm.Functions.opcode_stack_effect (.MCOPY ()) = pure (3, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 3 0 hs ss (by omega)
      (by have h : top.toNat - 3 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, mcopy_dispatch]
  have hbody : runS (Evm.Functions.execute_mcopy top ⟨off, len, msf⟩ g)
      hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1 - BitVec.ofNat 64 1,
          (⟨off, len, msf⟩ : EvmMemorySlice),
          g - G_verylow - G_copy_word * Evm.Functions.memory_word_count z
            - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                (max x y + z)),
        mcopyHost hs off x y z) ss := by
    simp only [Evm.Functions.execute_mcopy]
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
    rw [mcopy_required_size_pos x z hz, mcopy_required_size_pos y z hz,
      blt_if_max, show max (x + z) (y + z) = max x y + z from by omega]
    refine runS_bind_ok (runS_charge_ok _ _ hs ss hexp) ?_
    rw [dif_neg (by simp)]
    refine runS_bind_ok
      (runS_memory_access_ok x z hs ss hz
        (show x ≤ 2 ^ 32 - 1 by omega)
        (show z ≤ 2 ^ 32 - 1 - x by omega)) ?_
    refine runS_bind_ok
      (runS_memory_access_ok y z hs ss hz
        (show y ≤ 2 ^ 32 - 1 by omega)
        (show z ≤ 2 ^ 32 - 1 - y by omega)) ?_
    rw [blt_if_max]
    simp only [Evm.Defs.MemoryAccessFields.required_size,
      Evm.Defs.MemoryRangeFields.off, Evm.Defs.MemoryRangeFields.len]
    rw [show max (x + z) (y + z) = max x y + z from by omega]
    refine runS_bind_ok
      (runS_expand_memory_le off len (max x y + z) msf hs ss hgrow) ?_
    refine runS_bind_ok
      (runS_mem_mcopy x y z hs ss
        ({ base := off, established := len } : Evm.MemoryFrame)
        mfrest hmframe (by simpa using hz) (by simp; omega)) ?_
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
/-- **The copy agrees**, source and destination both in the established
window: SpecRef's `memory_write M x (memory_read_bytes M y z)` is the
host's read-then-write memmove. Overlap is fine because both snapshot the
source before writing. -/
theorem memoryRel_mcopy (M : Bytes) (hs : Evm.HostState)
    (off len x y z : Nat)
    (hrel : MemoryRel M hs off len)
    (hy : y + z ≤ len) (hx : x + z ≤ len) :
    MemoryRel (memory_write M x (memory_read_bytes M y z))
      (mcopyHost hs off x y z) off len := by
  have hlenM : len ≤ M.length := by
    have := le_32_wc len
    have := hrel.aligned
    omega
  have hread : readArrayBytes hs.memoryBytes (off + y) z
      = memory_read_bytes M y z :=
    memoryRel_read M hs off len y z hrel hy
  have hvlen : (memory_read_bytes M y z).length = z :=
    memory_read_bytes_length M y z (by omega)
  have hw := memoryRel_write M hs off len x (memory_read_bytes M y z) hrel
    (by rw [hvlen]; exact hx)
  simp only [mcopyHost, hread]
  exact hw

/-! ## The step equivalence -/

open Evm.Functions in
/-- **MCOPY, all reachable outcomes** (success splits on zero length and
on whether the window grows). Requires the memory relation and the MM-6
gas budget; no source/destination disjointness, because both sides
snapshot the source first. -/
theorem mcopy_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (off len : Nat)
    (msf : EvmMemorySliceFields off len) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hmem : MemoryRel sRef.evm.memory hs off len)
    (hsafe : MemGasSafe sRef.evm.memory sRef.evm.gasLeft)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel MemPost (runR iMcopy sRef)
      (runS (Evm.Functions.execute (.MCOPY ()) pc_in top ⟨off, len, msf⟩ g)
        hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_iMcopy_underflow_nil sRef hS,
      runS_execute_mcopy_underflow pc_in top off len g msf hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | [x] =>
    rw [hS] at hpfx htop
    rw [runR_iMcopy_underflow_one sRef x hS,
      runS_execute_mcopy_underflow pc_in top off len g msf hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | [x, y] =>
    rw [hS] at hpfx htop
    rw [runR_iMcopy_underflow_two sRef x y hS,
      runS_execute_mcopy_underflow pc_in top off len g msf hs ss prof
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
        [(max x y, z)]).cost
        = Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
            (Evm.Functions.memory_required_size (max x y) z) :=
      extend_cost_eq sRef.evm.memory off len (max x y) z msf haligned
    have hTsplit : mcopyCost sRef.evm.memory.length x y z
        = 3 + 3 * Evm.Functions.memory_word_count z
          + Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
              (Evm.Functions.memory_required_size (max x y) z) := by
      rw [mcopyCost, hwcz, ← hcost]
      rfl
    by_cases hg : sRef.evm.gasLeft < mcopyCost sRef.evm.memory.length x y z
    · rw [runR_iMcopy_oog sRef x y z rest hS hg]
      rw [hTsplit, ← hlive] at hg
      have hgN : g < 3 + 3 * Evm.Functions.memory_word_count z
          + Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
              (Evm.Functions.memory_required_size (max x y) z) := hg
      by_cases hb : g < G_verylow
      · rw [runS_execute_mcopy_oog_base pc_in top off len g msf hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hin3 hlim' hb]
        exact StepResultRel.halted ErrorRel.outOfGas
          (haltRegs_frame_status ss msg .OutOfGas)
      · push Not at hb
        have hbN : (3 : Nat) ≤ g := hb
        by_cases hc : g - G_verylow
            < G_copy_word * Evm.Functions.memory_word_count z
        · rw [runS_execute_mcopy_oog_copy pc_in top off len g msf hs ss l
            frest x y z rest hframe hpfx htop hlim' prof
            sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hzw hb hc]
          exact StepResultRel.halted ErrorRel.outOfGas
            (haltRegs_frame_status ss msg .OutOfGas)
        · push Not at hc
          have hcN : (3 : Nat) * Evm.Functions.memory_word_count z
              ≤ g - 3 := hc
          by_cases hz0 : z = 0
          · -- zero length: the expansion charge is zero, so the only
            -- reachable OOG is the base charge, already handled
            subst hz0
            exfalso
            have hzero : Evm.Functions.memory_expansion_cost
                ⟨off, len, msf⟩
                (Evm.Functions.memory_required_size (max x y) 0) = 0 := by
              simp [Evm.Functions.memory_required_size,
                Evm.Functions.memory_expansion_cost, memory_high_water_eq,
                memory_word_count_eq]
            rw [hzero,
              show Evm.Functions.memory_word_count 0 = 0 from by
                simp [memory_word_count_eq]] at hgN
            omega
          · have hz : (z == 0) = false := by simpa using hz0
            rw [mcopy_required_size_pos (max x y) z hz] at hgN
            rw [runS_execute_mcopy_oog_exp pc_in top off len g msf hs ss l
              frest x y z rest hframe hpfx htop hlim' prof
              sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hz hzw hb hc
              (by
                show g - 3 - 3 * Evm.Functions.memory_word_count z < _
                omega)]
            exact StepResultRel.halted ErrorRel.outOfGas
              (haltRegs_frame_status ss msg .OutOfGas)
    · push Not at hg
      have hgT : 3 + 3 * Evm.Functions.memory_word_count z
          + Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
              (Evm.Functions.memory_required_size (max x y) z) ≤ g := by
        rw [← hTsplit]
        show mcopyCost sRef.evm.memory.length x y z ≤ g
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
          (Evm.Functions.memory_required_size (max x y) z)
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
                (Evm.Functions.memory_required_size (max x y) z)
          = (sRef.evm.gasLeft : Nat)
            - mcopyCost sRef.evm.memory.length x y z := by
        rw [hTsplit, ← hlive]
        omega
      rw [runR_iMcopy_success sRef x y z rest hS hg]
      by_cases hz0 : z = 0
      · subst hz0
        have hzero : (calculate_gas_extend_memory sRef.evm.memory.length
            [(max x y, 0)]) = { cost := 0, expandBy := 0 } := by
          rw [calc_extend_single]
          rfl
        rw [runS_execute_mcopy_ok_zero pc_in top off len g msf hs ss l frest
          x y rest hframe hpfx htop hlim' hbase]
        rw [hzero, show
          (({ cost := 0, expandBy := 0 } :
            EvmAsm.Stateless.SpecRef.ExtendMemory).expandBy : Nat) = 0
          from rfl]
        rw [show List.replicate 0 (0x00 : EvmAsm.EL.RLP.Byte) = [] from rfl,
          List.append_nil,
          show memory_read_bytes sRef.evm.memory y 0 = [] from by
            simp [memory_read_bytes],
          memory_write_nil]
        have hcost0 : mcopyCost sRef.evm.memory.length x y 0 = 3 := by
          rw [mcopyCost, hzero]
          rfl
        refine StepResultRel.success ?_
        refine ⟨⟨hpost hs hframe, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
          ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, by simp [hpc], ?_⟩
        · refine ⟨?_, hres, hsp⟩
          show g - 3 = sRef.evm.gasLeft - mcopyCost sRef.evm.memory.length x y 0
          rw [hcost0, hlive]
        · refine ⟨off, len, msf, rfl, ?_, ?_⟩
          · exact ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩
          · exact memGasSafe_mono_gas sRef.evm.memory (Nat.sub_le _ _) hsafe
      · have hz : (z == 0) = false := by simpa using hz0
        rw [mcopy_required_size_pos (max x y) z hz] at hcost
        rw [mcopy_required_size_pos (max x y) z hz] at hTsplit
        rw [mcopy_required_size_pos (max x y) z hz] at hexp
        rw [mcopy_required_size_pos (max x y) z hz] at hgas'
        have hreq : max x y + z ≤ 2 ^ 32 - 32 :=
          safe_required_bound sRef.evm.memory off len (max x y + z)
            (g - G_verylow - G_copy_word
              * Evm.Functions.memory_word_count z)
            sRef.evm.gasLeft msf haligned hsafe
            (le_trans (Nat.sub_le _ _) (le_trans (Nat.sub_le _ _)
              (le_of_eq hlive))) hexp
        have hexpandBy : ((calculate_gas_extend_memory
            sRef.evm.memory.length [(max x y, z)]).expandBy : Nat)
            = 32 * Evm.Functions.memory_word_count (max x y + z)
              - sRef.evm.memory.length := by
          have hiff0 : ∀ a b : Nat, (32 * a ≤ 32 * b) ↔ (a ≤ b) :=
            fun a b => by omega
          have hwcM : Evm.Functions.memory_word_count
              sRef.evm.memory.length
              = Evm.Functions.memory_word_count len := by
            rw [haligned, memory_word_count_eq, memory_word_count_eq]
            omega
          have hiff : ((ceil32 (max x y + z) : Nat)
              ≤ ceil32 sRef.evm.memory.length)
              ↔ (Evm.Functions.memory_word_count (max x y + z)
                  ≤ Evm.Functions.memory_word_count len) := by
            rw [ceil32_eq, ceil32_eq, hwcM]
            exact hiff0 _ _
          rw [calc_extend_single]
          rw [if_neg (by simpa using hz0)]
          by_cases hle : Evm.Functions.memory_word_count (max x y + z)
              ≤ Evm.Functions.memory_word_count len
          · rw [if_pos (hiff.mpr hle)]
            show (0 : Nat) = _
            have h1 : 32 * Evm.Functions.memory_word_count (max x y + z)
                ≤ sRef.evm.memory.length := by
              rw [haligned]
              omega
            omega
          · rw [if_neg (fun hc => hle (hiff.mp hc))]
            show ((ceil32 (max x y + z) : Nat)
              - ceil32 sRef.evm.memory.length) = _
            rw [ceil32_eq, ceil32_eq, hwcM, ← haligned]
        by_cases hgrow : len < max x y + z
        · rw [runS_execute_mcopy_ok_grow pc_in top off len g msf hs ss l
            frest x y z rest mfrest hframe hpfx htop hlim' hmframe hz hzw
            hbase hcopy hexp hreq hgrow]
          have hrel' := memoryRel_expand sRef.evm.memory hs off len
            (max x y + z) mfrest
            ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩ hgrow
          have hrelStored := memoryRel_mcopy _
            (mcopyExpanded hs off len (max x y + z) mfrest) off
            (max x y + z) x y z hrel' (by omega) (by omega)
          rw [hexpandBy]
          refine StepResultRel.success ?_
          refine ⟨⟨hpost _ hframe, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
            ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, by simp [hpc], ?_⟩
          · refine ⟨?_, hres, hsp⟩
            show g - 3 - 3 * Evm.Functions.memory_word_count z
                - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                    (max x y + z)
              = sRef.evm.gasLeft - mcopyCost sRef.evm.memory.length x y z
            exact hgas'
          · refine ⟨off, max x y + z, {}, rfl, ?_, ?_⟩
            · exact ⟨hrelStored.frame, hrelStored.aligned,
                hrelStored.bytes, hrelStored.tail⟩
            · show MemGasSafe _ (sRef.evm.gasLeft - mcopyCost
                sRef.evm.memory.length x y z)
              have hvlen : (memory_read_bytes
                  (sRef.evm.memory ++ List.replicate
                    (32 * Evm.Functions.memory_word_count (max x y + z)
                      - sRef.evm.memory.length) 0x00) y z).length = z := by
                refine memory_read_bytes_length _ y z ?_
                simp only [List.length_append, List.length_replicate]
                have h32 := le_32_wc (max x y + z)
                have hwc := wc_mono (Nat.le_of_lt hgrow)
                have hal := haligned
                omega
              have hsafe2 := memGasSafe_after_expand sRef.evm.memory off
                len (max x y + z) sRef.evm.gasLeft
                (mcopyCost sRef.evm.memory.length x y z) msf haligned hsafe
                (by rw [hTsplit]; omega) hg
              unfold MemGasSafe at hsafe2 ⊢
              rw [memory_write_length _ _ _ (by
                rw [hvlen]
                simp only [List.length_append, List.length_replicate]
                have h32 := le_32_wc (max x y + z)
                have hwc := wc_mono (Nat.le_of_lt hgrow)
                have hal := haligned
                omega)]
              exact hsafe2
        · push Not at hgrow
          rw [runS_execute_mcopy_ok_nogrow pc_in top off len g msf hs ss l
            frest x y z rest mfrest hframe hpfx htop hlim' hmframe hz hzw
            hbase hcopy hexp hreq hgrow]
          have hrelStored := memoryRel_mcopy sRef.evm.memory hs off len
            x y z ⟨⟨mfrest, hmframe⟩, haligned, hbytes, htail⟩
            (by omega) (by omega)
          have hzero : (0 : Nat) = (calculate_gas_extend_memory
              sRef.evm.memory.length [(max x y, z)]).expandBy := by
            rw [hexpandBy]
            have hwc := wc_mono hgrow
            have hal := haligned
            rw [memory_word_count_eq] at hwc hal ⊢
            omega
          rw [← hzero]
          rw [show List.replicate 0 (0x00 : EvmAsm.EL.RLP.Byte) = []
              from rfl,
            List.append_nil]
          have hvlen : (memory_read_bytes sRef.evm.memory y z).length = z := by
            refine memory_read_bytes_length _ y z ?_
            have h32 := le_32_wc len
            have hal := haligned
            omega
          refine StepResultRel.success ?_
          refine ⟨⟨hpost _ hframe, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
            ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, by simp [hpc], ?_⟩
          · refine ⟨?_, hres, hsp⟩
            show g - 3 - 3 * Evm.Functions.memory_word_count z
                - Evm.Functions.memory_expansion_cost ⟨off, len, msf⟩
                    (max x y + z)
              = sRef.evm.gasLeft - mcopyCost sRef.evm.memory.length x y z
            exact hgas'
          · refine ⟨off, len, msf, rfl, ?_, ?_⟩
            · exact ⟨hrelStored.frame, hrelStored.aligned,
                hrelStored.bytes, hrelStored.tail⟩
            · show MemGasSafe _ (sRef.evm.gasLeft - mcopyCost
                sRef.evm.memory.length x y z)
              have hsafe2 := memGasSafe_mono_gas sRef.evm.memory
                (g' := sRef.evm.gasLeft
                  - mcopyCost sRef.evm.memory.length x y z)
                (Nat.sub_le _ _) hsafe
              unfold MemGasSafe at hsafe2 ⊢
              rw [memory_write_length _ _ _ (by
                rw [hvlen]
                have h32 := le_32_wc len
                have hal := haligned
                omega)]
              exact hsafe2

end EvmSpecsVerify
