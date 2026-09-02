import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Relations.Jumpdest
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# JUMPI

First control-flow opcode. `iJumpi` pops destination and condition, charges,
then either falls through (`pc+1`), jumps (`pc := dest` after checking
`validJumpDestinations`), or throws `.invalidJumpDest`. The extraction's
`execute_jumpi` charges first, pops, and validates through `do_jump`
(`frame_jumpdest_valid`: range check + per-code jump-table lookup). The two
validation representations are tied by [`JumpdestRel`](../Relations/Jumpdest.lean);
the success `Post` (`ControlPost`, shared with [`JUMP`](Jump.lean)) preserves it alongside `BasePost` — the fall
and jump cases both leave code, tables, and the valid set untouched.

MM-4 note: on fall-through the returned pc is `pc_in = pc + 1` as for ALU;
on a taken jump both sides land on `dest` exactly, so the same `BasePost`
pc equation covers both. Pops precede the SpecRef charge, so — unlike
PUSH/DUP (MM-5) — all halt kinds align: success ×2 / underflow ×2 / OOG /
invalid jump.
-/

open private pcAdd from EvmAsm.Stateless.SpecRef.InstructionsCore
open private assocGet from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- Success post for the control-flow family (JUMP/JUMPI): `BasePost` plus
jumpdest preservation — every taken or untaken branch leaves the code, the
jump tables, and SpecRef's valid-destination set untouched. -/
def ControlPost (mem : EvmMemorySlice) (sR' : Machine) (step : EvmStep)
    (hs' : Evm.HostState) (ss' : SeqState) : Prop :=
  BasePost mem sR' step hs' ss' ∧ JumpdestRel sR' hs' ss'

theorem word_is_zero_eq (w : Nat) :
    Evm.Functions.word_is_zero w = (w == 0) := by
  have h0 : (Evm.Functions.WORD_ZERO : Nat) = 0 := by decide
  simp only [Evm.Functions.word_is_zero, h0]

/-! ## SpecRef run shapes -/

theorem runR_iJumpi_underflow_nil (s : Machine) (hstack : s.evm.stack = []) :
    runR iJumpi s = .ok (.error .stackUnderflow, s) := by
  simp only [iJumpi]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_iJumpi_underflow_one (s : Machine) (x : U256)
    (hstack : s.evm.stack = [x]) :
    runR iJumpi s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with stack := [] } }) := by
  simp only [iJumpi]
  refine runR_bind_ok (runR_stackPop_cons s x [] hstack) ?_
  exact runR_bind_err (runR_stackPop_nil _ (by simp))

theorem runR_iJumpi_oog (s : Machine) (x y : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: y :: rest)
    (hgas : s.evm.gasLeft < GasCosts.OPCODE_JUMPI) :
    runR iJumpi s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [iJumpi]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y rest (by simp)) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _ (by simpa using hgas))

theorem runR_iJumpi_fall (s : Machine) (x y : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: y :: rest)
    (hy : (y == 0) = true)
    (hgas : GasCosts.OPCODE_JUMPI ≤ s.evm.gasLeft) :
    runR iJumpi s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := rest
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_JUMPI
            regularGasUsed := s.evm.regularGasUsed + GasCosts.OPCODE_JUMPI
            pc := s.evm.pc + 1 } }) := by
  simp only [iJumpi, pcAdd]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y rest (by simp)) ?_
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  rw [if_pos hy]
  exact runR_modifyEvm _ _

theorem runR_iJumpi_jump (s : Machine) (x y : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: y :: rest)
    (hy : (y == 0) = false)
    (hj : s.evm.validJumpDestinations.contains x = true)
    (hgas : GasCosts.OPCODE_JUMPI ≤ s.evm.gasLeft) :
    runR iJumpi s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := rest
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_JUMPI
            regularGasUsed := s.evm.regularGasUsed + GasCosts.OPCODE_JUMPI
            pc := x } }) := by
  simp only [iJumpi]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y rest (by simp)) ?_
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  rw [if_neg (by simp [hy])]
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_neg (by simpa using hj)]
  exact runR_modifyEvm _ _

theorem runR_iJumpi_invalid (s : Machine) (x y : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: y :: rest)
    (hy : (y == 0) = false)
    (hj : s.evm.validJumpDestinations.contains x = false)
    (hgas : GasCosts.OPCODE_JUMPI ≤ s.evm.gasLeft) :
    runR iJumpi s =
      .ok (.error .invalidJumpDest,
        { s with evm := { s.evm with
            stack := rest
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_JUMPI
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_JUMPI } }) := by
  simp only [iJumpi]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y rest (by simp)) ?_
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  rw [if_neg (by simp [hy])]
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_pos (by simpa using hj)]
  exact runR_throw _ _

/-! ## `Evm` run shapes: the jumpdest read and `do_jump` -/

open Evm.Functions in
theorem runS_frame_jumpdest_valid (dest off len : Nat)
    (cf : CodeFields off len) (positions : List code_pointer)
    (hs : Evm.HostState) (ss : SeqState)
    (hcode : ss.regs.get? Register.frame_code = some ⟨off, len, cf⟩)
    (hpos : assocGet hs.jumpdestTables cf.jumpdests = some positions) :
    runS (Evm.Functions.frame_jumpdest_valid dest) hs ss =
      .ok ((decide (dest < len) && positions.contains dest), hs) ss := by
  simp only [Evm.Functions.frame_jumpdest_valid]
  refine runS_bind_ok (runS_readReg _ _ _ _ hcode) ?_
  simp only [Evm.Functions.jumpdest_ref_contains]
  refine runS_bind_ok (runS_get hs ss) ?_
  rw [hpos]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_do_jump_ok (pc_in g dest off len : Nat)
    (cf : CodeFields off len) (positions : List code_pointer)
    (hs : Evm.HostState) (ss : SeqState)
    (hcode : ss.regs.get? Register.frame_code = some ⟨off, len, cf⟩)
    (hpos : assocGet hs.jumpdestTables cf.jumpdests = some positions)
    (hlt : dest < len)
    (hmem : positions.contains dest = true) :
    runS (Evm.Functions.do_jump pc_in g dest) hs ss =
      .ok ((dest, g), hs) ss := by
  simp only [Evm.Functions.do_jump, Evm.Functions.frame_code_len]
  refine runS_bind_ok (runS_bind_ok (runS_readReg _ _ _ _ hcode)
    (runS_pure _ _ _)) ?_
  rw [if_pos (by simpa using hlt)]
  refine runS_bind_ok
    (runS_frame_jumpdest_valid dest off len cf positions hs ss hcode hpos) ?_
  rw [if_pos (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hlt, hmem⟩)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_do_jump_invalid (pc_in g dest off len : Nat)
    (cf : CodeFields off len) (positions : List code_pointer)
    (hs : Evm.HostState) (ss : SeqState)
    (hcode : ss.regs.get? Register.frame_code = some ⟨off, len, cf⟩)
    (hpos : assocGet hs.jumpdestTables cf.jumpdests = some positions)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hinv : (decide (dest < len) && positions.contains dest) = false) :
    runS (Evm.Functions.do_jump pc_in g dest) hs ss =
      .ok ((pc_in, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .InvalidJump } := by
  simp only [Evm.Functions.do_jump, Evm.Functions.frame_code_len]
  refine runS_bind_ok (runS_bind_ok (runS_readReg _ _ _ _ hcode)
    (runS_pure _ _ _)) ?_
  by_cases hlt : dest < len
  · rw [if_pos (by simpa using hlt)]
    refine runS_bind_ok
      (runS_frame_jumpdest_valid dest off len cf positions hs ss hcode
        hpos) ?_
    rw [if_neg (by simp only [hinv]; decide)]
    refine runS_bind_ok
      (runS_exc_halt g .InvalidJump hs ss prof sp msg hprof hsp hmsg
        hfork) ?_
    exact runS_pure _ _ _
  · rw [if_neg (by simpa using hlt)]
    refine runS_bind_ok
      (runS_exc_halt g .InvalidJump hs ss prof sp msg hprof hsp hmsg
        hfork) ?_
    exact runS_pure _ _ _

/-! ## `Evm` run shapes: `execute_jumpi` -/

open Evm.Functions in
/-- The dispatch equation for JUMPI (returns its own pc). -/
theorem jumpi_dispatch (pc_in : Nat) (top : StackTop) (mem : EvmMemorySlice)
    (g : Nat) :
    Evm.Functions.execute_opcode (.JUMPI ()) pc_in top mem g =
      Evm.Functions.execute_jumpi pc_in top g >>= fun p =>
        pure (p.1, p.2.1, mem, p.2.2) := rfl

open Evm.Functions in
theorem runS_jumpi_body_oog (pc_in : Nat) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < G_high) :
    runS (Evm.Functions.execute_jumpi pc_in top g) hs ss =
      .ok ((pc_in, top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_jumpi]
  refine runS_bind_ok
    (runS_charge_oog g G_high hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_jumpi_body_fall (pc_in : Nat) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: rest).reverse)
    (htop : top.toNat = (x :: y :: rest).length)
    (hy : (y == 0) = true)
    (hgas : G_high ≤ g) :
    runS (Evm.Functions.execute_jumpi pc_in top g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1, g - G_high),
        hs) ss := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  have hbound := top.isLt
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hpfx' : l.take ((top.toNat - 1) + 1) = (x :: y :: rest).reverse := by
    rw [show top.toNat - 1 + 1 = top.toNat from by omega]; exact hpfx
  have hpfx1 : l.take (top.toNat - 1) = (y :: rest).reverse :=
    take_shrink l _ x _ hpfx' (by simp; omega)
  simp only [Evm.Functions.execute_jumpi]
  refine runS_bind_ok (runS_charge_ok g G_high hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok
    (runS_pop top hs ss l frest x (y :: rest) hframe hpfx htop) ?_
  refine runS_bind_ok
    (runS_pop _ hs ss l frest y rest hframe
      (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
  rw [if_pos (by rw [word_is_zero_eq]; exact hy)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_jumpi_body_jump (pc_in : Nat) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: rest).reverse)
    (htop : top.toNat = (x :: y :: rest).length)
    (hy : (y == 0) = false)
    (off len : Nat) (cf : CodeFields off len) (positions : List code_pointer)
    (hcode : ss.regs.get? Register.frame_code = some ⟨off, len, cf⟩)
    (hpos : assocGet hs.jumpdestTables cf.jumpdests = some positions)
    (hlt : x < len)
    (hmem : positions.contains x = true)
    (hgas : G_high ≤ g) :
    runS (Evm.Functions.execute_jumpi pc_in top g) hs ss =
      .ok ((x, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1, g - G_high),
        hs) ss := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  have hbound := top.isLt
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hpfx' : l.take ((top.toNat - 1) + 1) = (x :: y :: rest).reverse := by
    rw [show top.toNat - 1 + 1 = top.toNat from by omega]; exact hpfx
  have hpfx1 : l.take (top.toNat - 1) = (y :: rest).reverse :=
    take_shrink l _ x _ hpfx' (by simp; omega)
  simp only [Evm.Functions.execute_jumpi]
  refine runS_bind_ok (runS_charge_ok g G_high hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok
    (runS_pop top hs ss l frest x (y :: rest) hframe hpfx htop) ?_
  refine runS_bind_ok
    (runS_pop _ hs ss l frest y rest hframe
      (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
  rw [if_neg (by rw [word_is_zero_eq]; simp [hy])]
  refine runS_bind_ok
    (runS_do_jump_ok pc_in (g - G_high) x off len cf positions hs ss hcode
      hpos hlt hmem) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_jumpi_body_invalid (pc_in : Nat) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: rest).reverse)
    (htop : top.toNat = (x :: y :: rest).length)
    (hy : (y == 0) = false)
    (off len : Nat) (cf : CodeFields off len) (positions : List code_pointer)
    (hcode : ss.regs.get? Register.frame_code = some ⟨off, len, cf⟩)
    (hpos : assocGet hs.jumpdestTables cf.jumpdests = some positions)
    (hinv : (decide (x < len) && positions.contains x) = false)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : G_high ≤ g) :
    runS (Evm.Functions.execute_jumpi pc_in top g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1, GAS_ZERO),
          hs)
        { ss with regs := haltRegs ss msg .InvalidJump } := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  have hbound := top.isLt
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  have hpfx' : l.take ((top.toNat - 1) + 1) = (x :: y :: rest).reverse := by
    rw [show top.toNat - 1 + 1 = top.toNat from by omega]; exact hpfx
  have hpfx1 : l.take (top.toNat - 1) = (y :: rest).reverse :=
    take_shrink l _ x _ hpfx' (by simp; omega)
  simp only [Evm.Functions.execute_jumpi]
  refine runS_bind_ok (runS_charge_ok g G_high hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok
    (runS_pop top hs ss l frest x (y :: rest) hframe hpfx htop) ?_
  refine runS_bind_ok
    (runS_pop _ hs ss l frest y rest hframe
      (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
  rw [if_neg (by rw [word_is_zero_eq]; simp [hy])]
  refine runS_bind_ok
    (runS_do_jump_invalid pc_in (g - G_high) x off len cf positions hs ss
      hcode hpos prof sp msg hprof hsp hmsg hfork hinv) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_jumpi_underflow (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 2) :
    runS (Evm.Functions.execute (.JUMPI ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.JUMPI ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 2 0 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_jumpi_oog (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hin : 2 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (hgas : g < G_high) :
    runS (Evm.Functions.execute (.JUMPI ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.JUMPI ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss hin
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, jumpi_dispatch]
  refine runS_bind_ok
    (runS_jumpi_body_oog pc_in top g hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_jumpi_fall (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: rest).reverse)
    (htop : top.toNat = (x :: y :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hy : (y == 0) = true)
    (hgas : G_high ≤ g) :
    runS (Evm.Functions.execute (.JUMPI ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1, mem,
          g - G_high), hs) ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.JUMPI ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by simp at htop; omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, jumpi_dispatch]
  refine runS_bind_ok
    (runS_jumpi_body_fall pc_in top g hs ss l frest x y rest hframe hpfx htop
      hy hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_jumpi_jump (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: rest).reverse)
    (htop : top.toNat = (x :: y :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hy : (y == 0) = false)
    (off len : Nat) (cf : CodeFields off len) (positions : List code_pointer)
    (hcode : ss.regs.get? Register.frame_code = some ⟨off, len, cf⟩)
    (hpos : assocGet hs.jumpdestTables cf.jumpdests = some positions)
    (hlt : x < len)
    (hmem : positions.contains x = true)
    (hgas : G_high ≤ g) :
    runS (Evm.Functions.execute (.JUMPI ()) pc_in top mem g) hs ss =
      .ok ((x, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1, mem,
          g - G_high), hs) ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.JUMPI ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by simp at htop; omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, jumpi_dispatch]
  refine runS_bind_ok
    (runS_jumpi_body_jump pc_in top g hs ss l frest x y rest hframe hpfx htop
      hy off len cf positions hcode hpos hlt hmem hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_jumpi_invalid (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x y : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: rest).reverse)
    (htop : top.toNat = (x :: y :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hy : (y == 0) = false)
    (off len : Nat) (cf : CodeFields off len) (positions : List code_pointer)
    (hcode : ss.regs.get? Register.frame_code = some ⟨off, len, cf⟩)
    (hpos : assocGet hs.jumpdestTables cf.jumpdests = some positions)
    (hinv : (decide (x < len) && positions.contains x) = false)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : G_high ≤ g) :
    runS (Evm.Functions.execute (.JUMPI ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1, mem,
          GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .InvalidJump } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.JUMPI ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by simp at htop; omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, jumpi_dispatch]
  refine runS_bind_ok
    (runS_jumpi_body_invalid pc_in top g hs ss l frest x y rest hframe hpfx
      htop hy off len cf positions hcode hpos hinv prof sp msg hprof hsp hmsg
      hfork hgas) ?_
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **JUMPI, all reachable outcomes**: fall-through / taken jump /
underflow ×2 / OOG / invalid destination. The success `Post` also carries
the jumpdest relation forward. -/
theorem jumpi_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hjd : JumpdestRel sRef hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (ControlPost mem) (runR iJumpi sRef)
      (runS (Evm.Functions.execute (.JUMPI ()) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  obtain ⟨off, len, cf, positions, hcode, hpos, hiff⟩ := hjd.rel
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_iJumpi_underflow_nil sRef hS,
      runS_execute_jumpi_underflow pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | [x] =>
    rw [hS] at hpfx htop
    rw [runR_iJumpi_underflow_one sRef x hS,
      runS_execute_jumpi_underflow pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | x :: y :: rest =>
    rw [hS] at hpfx htop hlim hwfS
    have hin2 : 2 ≤ top.toNat := by simp at htop; omega
    have hlim' : top.toNat ≤ 1024 := by simp at htop ⊢; simp at hlim; omega
    by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_JUMPI
    · rw [runR_iJumpi_oog sRef x y rest hS hg,
        runS_execute_jumpi_oog pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hin2 hlim'
          (by rw [hlive]; exact hg)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
    · push Not at hg
      have hn : top.toNat = rest.length + 2 := by simpa using htop
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
        calc ((x :: y :: rest).reverse).take (top.toNat - 2)
            = (rest.reverse ++ [y, x]).take (top.toNat - 2) := by simp
          _ = rest.reverse := by
              rw [List.take_append_of_le_length (by omega), ← hrl,
                List.take_length]
      have hpostStack : StackRel rest hs
          (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1) := by
        refine ⟨⟨l, frest, hframe, ?_, ?_⟩, ?_, ?_, ?_⟩
        · rw [hret2]; exact hpfx2
        · rw [hret2]; omega
        · rw [hret2]; simp at htop ⊢; omega
        · simp at hlim ⊢; omega
        · intro w hw
          exact hwfS w (by simp [hw])
      by_cases hy : (y == 0) = true
      · rw [runR_iJumpi_fall sRef x y rest hS hy hg,
          runS_execute_jumpi_fall pc_in top g mem hs ss l frest x y rest
            hframe hpfx htop hlim' hy (by rw [hlive]; exact hg)]
        refine StepResultRel.success ?_
        exact ⟨⟨⟨hpostStack, ⟨by simp [hlive, Evm.Functions.G_high, GasCosts.OPCODE_JUMPI], hres, hsp⟩,
          ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩,
          by simp [hpc], rfl⟩,
          ⟨off, len, cf, positions, hcode, hpos, hiff⟩⟩
      · have hy' : (y == 0) = false := by simpa using hy
        by_cases hj : sRef.evm.validJumpDestinations.contains x = true
        · have hj' : (decide (x < len) && positions.contains x) = true := by
            rw [← hiff x]; exact hj
          rw [Bool.and_eq_true, decide_eq_true_eq] at hj'
          obtain ⟨hlt, hmem⟩ := hj'
          rw [runR_iJumpi_jump sRef x y rest hS hy' hj hg,
            runS_execute_jumpi_jump pc_in top g mem hs ss l frest x y rest
              hframe hpfx htop hlim' hy' off len cf positions hcode hpos hlt
              hmem (by rw [hlive]; exact hg)]
          refine StepResultRel.success ?_
          exact ⟨⟨⟨hpostStack, ⟨by simp [hlive, Evm.Functions.G_high, GasCosts.OPCODE_JUMPI], hres, hsp⟩,
            ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩,
            rfl, rfl⟩,
            ⟨off, len, cf, positions, hcode, hpos, hiff⟩⟩
        · have hj' : sRef.evm.validJumpDestinations.contains x = false := by
            simpa using hj
          have hinv : (decide (x < len) && positions.contains x) = false := by
            rw [← hiff x]; exact hj'
          rw [runR_iJumpi_invalid sRef x y rest hS hy' hj' hg,
            runS_execute_jumpi_invalid pc_in top g mem hs ss l frest x y rest
              hframe hpfx htop hlim' hy' off len cf positions hcode hpos hinv
              prof sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
              (by rw [hlive]; exact hg)]
          exact StepResultRel.halted ErrorRel.invalidJumpDest
            (haltRegs_frame_status ss msg .InvalidJump)

end EvmSpecsVerify
