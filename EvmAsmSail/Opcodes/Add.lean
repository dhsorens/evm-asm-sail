import EvmAsmSail.Relations.State
import EvmAsmSail.Representation.EvmGas
import EvmAsmSail.Representation.SpecRefLemmas
import Batteries.Tactic.OpenPrivate

/-!
# ADD: the first full-outcome step equivalence

The vertical slice: SpecRef's `iAdd` vs the extraction's
`execute (.ADD ()) pc top mem g`, all reachable outcomes.

For a binop the reachable outcomes are success, stack underflow, and
out-of-gas — overflow is impossible (2 in, 1 out, height decreases), which
the `validate_stack` bound shows and the coverage registry records.

Both sides check the stack shape before gas (`validate_stack` up front vs
pops-before-charge), so the failure *kinds* align case by case (mismatch
ledger MM-1 resolves as observationally equivalent at the halt boundary).
-/

open private binOp pcAdd from EvmAsm.Stateless.SpecRef.InstructionsCore
open private writeListAt from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmAsmSail

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## SpecRef side: `iAdd` run shapes -/

theorem runR_iAdd_success (s : Machine) (x y : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: y :: rest)
    (hgas : GasCosts.OPCODE_ADD ≤ s.evm.gasLeft)
    (hlim : s.evm.stack.length ≤ 1024) :
    runR iAdd s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := wrap256 (x + y) :: rest
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_ADD
            regularGasUsed := s.evm.regularGasUsed + GasCosts.OPCODE_ADD
            pc := s.evm.pc + 1 } }) := by
  have hlen : rest.length ≠ 1024 := by
    rw [hstack] at hlim; simp at hlim; omega
  simp only [iAdd, binOp, pcAdd]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y rest (by simp)) ?_
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  refine runR_bind_ok (runR_stackPush _ _ (by simpa using hlen)) ?_
  exact runR_modifyEvm _ _

theorem runR_iAdd_underflow_nil (s : Machine) (hstack : s.evm.stack = []) :
    runR iAdd s = .ok (.error .stackUnderflow, s) := by
  simp only [iAdd, binOp]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_iAdd_underflow_one (s : Machine) (x : U256)
    (hstack : s.evm.stack = [x]) :
    runR iAdd s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with stack := [] } }) := by
  simp only [iAdd, binOp]
  refine runR_bind_ok (runR_stackPop_cons s x [] hstack) ?_
  exact runR_bind_err (runR_stackPop_nil _ (by simp))

theorem runR_iAdd_oog (s : Machine) (x y : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: y :: rest)
    (hgas : s.evm.gasLeft < GasCosts.OPCODE_ADD) :
    runR iAdd s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [iAdd, binOp]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y rest (by simp)) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _ (by simpa using hgas))

/-! ## `Evm` side: `execute_add` run shapes

Raw-hypothesis form (the final theorem unpacks `StackRel` into these). `l` is
the active host frame, `S = x :: y :: rest` the abstract stack.
-/

open Evm.Functions in
/-- `execute_add`, success path: charge 3, pop twice, push the wrapped sum.
The cursor lands at `top - 1`; the new frame's prefix represents
`alu_add x y :: rest`. -/
theorem runS_execute_add_ok (top : StackTop) (g : Nat) (hs : Evm.HostState)
    (ss : SeqState) (l : List word) (frest : List (List word))
    (x y : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: rest).reverse)
    (htop : top.toNat = (x :: y :: rest).length)
    (hlen : top.toNat ≤ l.length)
    (hgas : G_verylow ≤ g) :
    runS (Evm.Functions.execute_add top g) hs ss =
      .ok ((top - BitVec.ofNat 64 1, g - G_verylow),
        { hs with stackFrames :=
            writeListAt l (top.toNat - 2) (alu_add x y) :: frest }) ss := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  have hbound := top.isLt
  -- prefix at the once-retreated cursor: drop the top element
  have hpfx1 : l.take (top - BitVec.ofNat 64 1).toNat = (y :: rest).reverse := by
    rw [cursor_retreat_toNat top (by omega)]
    have : l.take (top.toNat - 1) = (l.take top.toNat).take (top.toNat - 1) := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [this, hpfx]
    have hrl : (y :: rest).reverse.length = top.toNat - 1 := by simp; omega
    calc ((x :: y :: rest).reverse).take (top.toNat - 1)
        = ((y :: rest).reverse ++ [x]).take (top.toNat - 1) := by simp
      _ = (y :: rest).reverse := by
          rw [List.take_append_of_le_length (by omega), ← hrl,
            List.take_length]
  have htop1 : (top - BitVec.ofNat 64 1).toNat = (y :: rest).length := by
    rw [cursor_retreat_toNat top (by omega)]; simp; omega
  have hpfx2 : l.take (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1).toNat
      = rest.reverse := by
    rw [cursor_retreat_toNat _ (by rw [htop1]; simp),
      cursor_retreat_toNat top (by omega)]
    have : l.take (top.toNat - 1 - 1) =
        (l.take top.toNat).take (top.toNat - 1 - 1) := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [this, hpfx]
    have hrl : rest.reverse.length = top.toNat - 1 - 1 := by simp; omega
    calc ((x :: y :: rest).reverse).take (top.toNat - 1 - 1)
        = (rest.reverse ++ [y, x]).take (top.toNat - 1 - 1) := by simp
      _ = rest.reverse := by
          rw [List.take_append_of_le_length (by omega), ← hrl, List.take_length]
  have hhead2 : (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1).toNat + 1 < 2 ^ 64 := by
    rw [cursor_retreat_toNat _ (by rw [htop1]; simp),
      cursor_retreat_toNat top (by omega)]
    omega
  simp only [Evm.Functions.execute_add]
  refine runS_bind_ok (runS_charge_ok g G_verylow hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_pop top hs ss l frest x (y :: rest) hframe hpfx htop) ?_
  refine runS_bind_ok
    (runS_pop _ hs ss l frest y rest hframe hpfx1 (by simpa using htop1)) ?_
  refine runS_bind_ok (runS_push_word _ (alu_add x y) hs ss l frest hframe hhead2) ?_
  -- cursor algebra: top - 1 - 1 + 1 = top - 1, and the write position is n - 2
  have hc : top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1 + BitVec.ofNat 64 1
      = top - BitVec.ofNat 64 1 := by
    rw [BitVec.sub_add_cancel]
  have hwpos : (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1).toNat
      = top.toNat - 2 := by
    rw [cursor_retreat_toNat _ (by rw [htop1]; simp),
      cursor_retreat_toNat top (by omega)]
    omega
  rw [hc, hwpos]
  exact runS_pure _ _ _

open Evm.Functions in
/-- `execute_add`, out-of-gas: `charge` fails, the halt registers are set,
the returned gas is zero, the cursor and host stack are untouched. -/
theorem runS_execute_add_oog (top : StackTop) (g : Nat) (hs : Evm.HostState)
    (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < G_verylow) :
    runS (Evm.Functions.execute_add top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_add]
  refine runS_bind_ok
    (runS_charge_oog g G_verylow hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

/-! ## `Evm` side: `execute (.ADD ())` — through the stack guard and dispatch -/

/-- ADD's pure function is SpecRef's: both wrap the `Nat` sum mod `2^256`. -/
theorem alu_add_eq_wrap256 (a b : Nat) :
    Evm.Functions.alu_add a b = wrap256 (a + b) := by
  -- lean-sail's `HPow Int Int Int` is `x ^ n.toNat` (Sail.lean:860), so the
  -- Sail modulus `2 ^i 256` is definitionally `((2 : Int) ^ (256 : Nat)).toNat`.
  have h : ((2 : Int) ^ (256 : Nat)).toNat = 2 ^ 256 := by decide
  show (a + b) % ((2 : Int) ^ (256 : Nat)).toNat = (a + b) % 2 ^ 256
  rw [h]

open Evm.Functions in
theorem runS_execute_ADD_success (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word))
    (x y : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: rest).reverse)
    (htop : top.toNat = (x :: y :: rest).length)
    (hlen : top.toNat ≤ l.length)
    (hlim : top.toNat ≤ 1024)
    (hgas : G_verylow ≤ g) :
    runS (Evm.Functions.execute (.ADD ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1, mem, g - G_verylow),
        { hs with stackFrames :=
            writeListAt l (top.toNat - 2) (alu_add x y) :: frest }) ss := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  simp only [Evm.Functions.execute, Evm.Functions.opcode_stack_effect]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 1 hs ss (by omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl]
  simp only [Evm.Functions.execute_opcode]
  refine runS_bind_ok
    (runS_execute_add_ok top g hs ss l frest x y rest hframe hpfx htop hlen
      hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_ADD_underflow (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 2) :
    runS (Evm.Functions.execute (.ADD ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute, Evm.Functions.opcode_stack_effect]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 2 1 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_ADD_oog (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hin : 2 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (hgas : g < G_verylow) :
    runS (Evm.Functions.execute (.ADD ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute, Evm.Functions.opcode_stack_effect]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 1 hs ss hin
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl]
  simp only [Evm.Functions.execute_opcode]
  refine runS_bind_ok
    (runS_execute_add_oog top g hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  exact runS_pure _ _ _

/-! ## The step equivalence -/

/-- The success post-relation for the ALU family: the state relation holds on
the returned live values, the returned pc is the SpecRef post-pc (step
boundaries re-align; mismatch ledger MM-4), and memory is a pass-through. -/
def AluPost (mem : EvmMemorySlice) (sR' : Machine) (step : EvmStep)
    (hs' : Evm.HostState) (ss' : SeqState) : Prop :=
  StateRel sR' step.2.1 step.2.2.2 hs' ss' ∧
  step.1 = sR'.evm.pc ∧ step.2.2.1 = mem

/-- **ADD, all reachable outcomes.** For related pre-states (Amsterdam
profile inside `StateRel`), SpecRef's `iAdd` and the extraction's
`execute (.ADD ())` produce corresponding outcomes: success with related
post-states, stack underflow with stack underflow, out-of-gas with
out-of-gas. (Stack overflow is unreachable for a 2-in/1-out opcode.) -/
theorem add_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iAdd sRef)
      (runS (Evm.Functions.execute (.ADD ()) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwf⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  have hADD3 : GasCosts.OPCODE_ADD = Evm.Functions.G_verylow := rfl
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_iAdd_underflow_nil sRef hS,
      runS_execute_ADD_underflow pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | [x] =>
    rw [hS] at hpfx htop
    rw [runR_iAdd_underflow_one sRef x hS,
      runS_execute_ADD_underflow pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | x :: y :: rest =>
    rw [hS] at hpfx htop hlim hwf
    have hin2 : 2 ≤ top.toNat := by simp at htop; omega
    have hlim' : top.toNat ≤ 1024 := by simp at htop ⊢; simp at hlim; omega
    by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_ADD
    · -- out of gas on both sides
      rw [runR_iAdd_oog sRef x y rest hS hg,
        runS_execute_ADD_oog pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hin2 hlim'
          (by rw [hlive]; exact hADD3 ▸ hg)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
    · -- success on both sides
      push_neg at hg
      have hn : top.toNat = rest.length + 2 := by simpa using htop
      rw [runR_iAdd_success sRef x y rest hS hg (by rw [hS]; exact hlim),
        runS_execute_ADD_success pc_in top g mem hs ss l frest x y rest hframe
          hpfx htop hlen hlim' (by rw [hlive]; exact hADD3 ▸ hg)]
      refine StepResultRel.success ?_
      refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
        ⟨msg, hmsg⟩⟩, by simp [hpc], rfl⟩
      · -- StackRel for the post-state
        have hret : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
          cursor_retreat_toNat top (by omega)
        refine ⟨⟨writeListAt l (top.toNat - 2) (Evm.Functions.alu_add x y),
          frest, rfl, ?_, ?_⟩, ?_, ?_, ?_⟩
        · -- prefix at the returned cursor
          rw [hret]
          have hstep : top.toNat - 1 = (top.toNat - 2) + 1 := by omega
          rw [hstep, take_writeListAt l (top.toNat - 2) _ (by omega)]
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
          rw [hpfx2, alu_add_eq_wrap256]
          simp
        · -- returned cursor within the new frame
          rw [hret, length_writeListAt]
          omega
        · -- height
          rw [hret]; simp; omega
        · -- limit
          simp; simp at hlim; omega
        · -- well-formed words
          intro z hz
          rcases List.mem_cons.mp hz with hz | hz
          · subst hz
            exact Nat.mod_lt _ (Nat.two_pow_pos 256)
          · exact hwf z (by simp [hz])
      · -- GasRel on the post-state
        exact ⟨by rw [hlive, hADD3], hres, hsp⟩

end EvmAsmSail
