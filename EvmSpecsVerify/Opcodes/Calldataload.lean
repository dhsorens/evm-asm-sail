import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Relations.Calldata
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack

/-!
# CALLDATALOAD

The first calldata reader: pop the offset, charge
`G_verylow`/`OPCODE_CALLDATALOAD` (= 3, both sides), push the zero-padded
32-byte read. The value agreement is
[`calldataRel_load_word`](../Relations/Calldata.lean) — both sides
zero-pad past the end, so it holds for every popped offset with no range
hypothesis. The `calldata` register is not part of `StateRel`, so the
read (`hcdreg`) and the relation (`hcdrel` — covering both the top
frame's input-arena window and a nested frame's parent-memory window)
are hypotheses of the step theorem.

Operation order is the classic MM-1: SpecRef pops before charging, the
extraction's body charges before popping — behind `validate_stack`, so
the halt kinds still align case by case (underflow states never reach the
charge on either side's fault report). Reachable outcomes: success /
stack underflow / OOG (overflow unreachable for 1-in/1-out).
-/

open private pcNext from EvmAsm.Stateless.SpecRef.InstructionsEnv
open private writeListAt from Evm.HostAxioms

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- The pushed word (named so structure-update literals stay
single-line). -/
def cdWord (D : Bytes) (x : Nat) : word :=
  bytesBEtoNat (buffer_read D x 32)

/-! ## SpecRef run shapes -/

theorem runR_iCalldataload_underflow (s : Machine)
    (hstack : s.evm.stack = []) :
    runR iCalldataload s = .ok (.error .stackUnderflow, s) := by
  simp only [iCalldataload]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_iCalldataload_oog (s : Machine) (x : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: rest)
    (hgas : s.evm.gasLeft < GasCosts.OPCODE_CALLDATALOAD) :
    runR iCalldataload s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [iCalldataload]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _ hgas)

theorem runR_iCalldataload_success (s : Machine) (x : U256)
    (rest : List U256)
    (hstack : s.evm.stack = x :: rest)
    (hgas : GasCosts.OPCODE_CALLDATALOAD ≤ s.evm.gasLeft)
    (hlim : s.evm.stack.length ≤ 1024) :
    runR iCalldataload s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := bytesBEtoNat (buffer_read s.evm.message.data x 32)
              :: rest
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_CALLDATALOAD
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_CALLDATALOAD
            pc := s.evm.pc + 1 } }) := by
  have hlen : rest.length ≠ 1024 := by
    rw [hstack] at hlim; simp at hlim; omega
  simp only [iCalldataload, pcNext]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_stackPush _ _ (by simpa using hlen)) ?_
  exact runR_modifyEvm _ _

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for CALLDATALOAD. -/
theorem calldataload_dispatch (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_opcode (.CALLDATALOAD ()) pc_in top mem g =
      Evm.Functions.execute_calldataload top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
theorem runS_calldataload_body_ok (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (D : Bytes) (cd : CalldataSlice)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hcdreg : ss.regs.get? Register.calldata = some cd)
    (hcdrel : CalldataRel D hs cd)
    (hgas : (GasCosts.OPCODE_CALLDATALOAD : Nat) ≤ g) :
    runS (Evm.Functions.execute_calldataload top g) hs ss =
      .ok ((top, g - GasCosts.OPCODE_CALLDATALOAD),
        { hs with stackFrames := writeListAt l (top.toNat - 1) (cdWord D x) :: frest })
        ss := by
  have hn : top.toNat = rest.length + 1 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  simp only [Evm.Functions.execute_calldataload]
  refine runS_bind_ok (runS_charge_ok g G_verylow hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_pop top hs ss l frest x rest hframe hpfx htop) ?_
  refine runS_bind_ok (runS_readReg _ _ _ _ hcdreg) ?_
  refine runS_bind_ok (calldataRel_load_word D hs ss cd x hcdrel) ?_
  refine runS_bind_ok
    (runS_push_word (top - BitVec.ofNat 64 1) (cdWord D x) hs ss l frest
      hframe (by rw [hret1]; omega)) ?_
  rw [BitVec.sub_add_cancel, hret1]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_calldataload_body_oog (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < (GasCosts.OPCODE_CALLDATALOAD : Nat)) :
    runS (Evm.Functions.execute_calldataload top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_calldataload]
  refine runS_bind_ok
    (runS_charge_oog g G_verylow hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_calldataload_ok (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (D : Bytes) (cd : CalldataSlice)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hcdreg : ss.regs.get? Register.calldata = some cd)
    (hcdrel : CalldataRel D hs cd)
    (hgas : (GasCosts.OPCODE_CALLDATALOAD : Nat) ≤ g) :
    runS (Evm.Functions.execute (.CALLDATALOAD ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, g - GasCosts.OPCODE_CALLDATALOAD),
        { hs with stackFrames := writeListAt l (top.toNat - 1) (cdWord D x) :: frest })
        ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.CALLDATALOAD ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 1 hs ss (by simp at htop; omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, calldataload_dispatch]
  refine runS_bind_ok
    (runS_calldataload_body_ok top g hs ss l frest x rest D cd hframe hpfx
      htop hcdreg hcdrel hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_calldataload_oog (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (hpos : 1 ≤ top.toNat)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < (GasCosts.OPCODE_CALLDATALOAD : Nat)) :
    runS (Evm.Functions.execute (.CALLDATALOAD ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.CALLDATALOAD ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 1 hs ss (by omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, calldataload_dispatch]
  refine runS_bind_ok
    (runS_calldataload_body_oog top g hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_calldataload_underflow (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 1) :
    runS (Evm.Functions.execute (.CALLDATALOAD ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.CALLDATALOAD ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 1 1 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **CALLDATALOAD, all reachable outcomes.** `hcdreg`/`hcdrel` supply the
`calldata` register read and the calldata relation (either window
constructor). -/
theorem calldataload_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat) (cd : CalldataSlice)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (hcdreg : ss.regs.get? Register.calldata = some cd)
    (hcdrel : CalldataRel sRef.evm.message.data hs cd) :
    StepResultRel (AluPost mem) (runR iCalldataload sRef)
      (runS (Evm.Functions.execute (.CALLDATALOAD ()) pc_in top mem g)
        hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_iCalldataload_underflow sRef hS,
      runS_execute_calldataload_underflow pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | x :: rest =>
    rw [hS] at hpfx htop hlim hwfS
    have hlim' : top.toNat ≤ 1024 := by simp at htop hlim; omega
    by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_CALLDATALOAD
    · rw [runR_iCalldataload_oog sRef x rest hS hg,
        runS_execute_calldataload_oog pc_in top g mem hs ss
          (by simp at htop; omega) hlim' prof sRef.evm.stateGasSpilled msg
          hprof hsp hmsg hfork (by rw [hlive]; exact hg)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
    · push Not at hg
      rw [runR_iCalldataload_success sRef x rest hS hg
          (by rw [hS]; exact hlim),
        runS_execute_calldataload_ok pc_in top g mem hs ss l frest x rest
          sRef.evm.message.data cd hframe hpfx htop hlim' hcdreg hcdrel
          (by rw [hlive]; exact hg)]
      refine StepResultRel.success ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
        ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, hpc, rfl⟩
      · exact pop_push_post_stack top _ l frest x rest
          (cdWord sRef.evm.message.data x)
          (hostState_set_stackFrames_frames _ _) hpfx htop hlim hlen hwfS
          (by
            unfold cdWord
            exact pushVal_wf sRef.evm.message.data x 32 (Nat.le_refl 32))
      · exact ⟨by rw [hlive], hres, hsp⟩

end EvmSpecsVerify
