import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.SpecRefLemmas
import Batteries.Tactic.OpenPrivate

/-!
# ALU ternop shape (3-in/1-out)

Sibling of [`Binop`](Binop.lean) / [`Unop`](Unop.lean) — do not import
those, or this file from them. Shared Post and wf lemmas:
[`Alu`](Alu.lean).

SpecRef: `iAddmod`/`iMulmod` are `pop ×3 → charge → push → pc+1` (no
upstream combinator); [`ternOp`](#ternOp) names that shape.
`Evm`: `execute_addmod`/`execute_mulmod` modulo `alu_*`.

[`ternop_step_equiv`](#ternop_step_equiv) is the full-outcome step theorem.
Reachable: success, stack underflow (×3), out-of-gas. Overflow unreachable
(height decreases).
-/

open private pcAdd from EvmAsm.Stateless.SpecRef.InstructionsCore
open private writeListAt from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- Truncating a one-longer reversed-stack prefix drops the top element:
the list-geometry step each `pop` takes on the prefix relation. -/
theorem take_shrink (l S : List word) (a : word) (k : Nat)
    (hpfx : l.take (k + 1) = (a :: S).reverse) (hS : S.length = k) :
    l.take k = S.reverse := by
  have hview : l.take k = (l.take (k + 1)).take k := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  rw [hview, hpfx]
  have hrl : S.reverse.length = k := by simp [hS]
  calc ((a :: S).reverse).take k = (S.reverse ++ [a]).take k := by simp
    _ = S.reverse := by
        rw [List.take_append_of_le_length (by omega), ← hrl, List.take_length]

/-! ## SpecRef side: the shared shape, generically -/

/-- The shape of SpecRef's ternary ALU handlers (`iAddmod`, `iMulmod` are
definitionally `ternOp GasCosts.OPCODE_* f`): pop ×3 → charge → push →
pc+1. -/
def ternOp (gas : Uint) (f : U256 → U256 → U256 → U256) : EvmM Unit := do
  let x ← stackPop
  let y ← stackPop
  let z ← stackPop
  charge_gas gas
  stackPush (f x y z)
  pcAdd 1

theorem runR_ternOp_success (cost : Uint) (f : U256 → U256 → U256 → U256)
    (s : Machine) (x y z : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: y :: z :: rest)
    (hgas : cost ≤ s.evm.gasLeft)
    (hlim : s.evm.stack.length ≤ 1024) :
    runR (ternOp cost f) s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := f x y z :: rest
            gasLeft := s.evm.gasLeft - cost
            regularGasUsed := s.evm.regularGasUsed + cost
            pc := s.evm.pc + 1 } }) := by
  have hlen : rest.length ≠ 1024 := by
    rw [hstack] at hlim; simp at hlim; omega
  simp only [ternOp, pcAdd]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: z :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y (z :: rest) (by simp)) ?_
  refine runR_bind_ok (runR_stackPop_cons _ z rest (by simp)) ?_
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  refine runR_bind_ok (runR_stackPush _ _ (by simpa using hlen)) ?_
  exact runR_modifyEvm _ _

theorem runR_ternOp_underflow_nil (cost : Uint) (f : U256 → U256 → U256 → U256)
    (s : Machine) (hstack : s.evm.stack = []) :
    runR (ternOp cost f) s = .ok (.error .stackUnderflow, s) := by
  simp only [ternOp]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_ternOp_underflow_one (cost : Uint) (f : U256 → U256 → U256 → U256)
    (s : Machine) (x : U256) (hstack : s.evm.stack = [x]) :
    runR (ternOp cost f) s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with stack := [] } }) := by
  simp only [ternOp]
  refine runR_bind_ok (runR_stackPop_cons s x [] hstack) ?_
  exact runR_bind_err (runR_stackPop_nil _ (by simp))

theorem runR_ternOp_underflow_two (cost : Uint) (f : U256 → U256 → U256 → U256)
    (s : Machine) (x y : U256) (hstack : s.evm.stack = [x, y]) :
    runR (ternOp cost f) s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with stack := [] } }) := by
  simp only [ternOp]
  refine runR_bind_ok (runR_stackPop_cons s x [y] hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y [] (by simp)) ?_
  exact runR_bind_err (runR_stackPop_nil _ (by simp))

theorem runR_ternOp_oog (cost : Uint) (f : U256 → U256 → U256 → U256)
    (s : Machine) (x y z : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: y :: z :: rest)
    (hgas : s.evm.gasLeft < cost) :
    runR (ternOp cost f) s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [ternOp]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: z :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y (z :: rest) (by simp)) ?_
  refine runR_bind_ok (runR_stackPop_cons _ z rest (by simp)) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _ (by simpa using hgas))

/-! ## `Evm` side: the handler shape, generically -/

/-- The shared body of every `Evm` ALU ternop handler. Each generated
`execute_<op>` is definitionally `ternopShape G_mid alu_<op>`. -/
def ternopShape (cost : Nat) (aluF : Nat → Nat → Nat → Nat) (top : StackTop)
    (g : Nat) : Evm.SailM (StackTop × Nat) := do
  let (gas_charged, g1) ← do (Evm.Functions.charge g cost)
  if ((! gas_charged) : Bool)
  then (pure (top, g1))
  else
    (do
      let (a, top1) ← do (Evm.Functions.pop top)
      let (b, top2) ← do (Evm.Functions.pop top1)
      let (n, top3) ← do (Evm.Functions.pop top2)
      let result := (aluF a b n)
      (pure ((← (Evm.Functions.push_word top3 result)), g1)))

open Evm.Functions in
theorem runS_ternopShape_ok (cost : Nat) (aluF : Nat → Nat → Nat → Nat)
    (top : StackTop) (g : Nat) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word))
    (x y z : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: z :: rest).reverse)
    (htop : top.toNat = (x :: y :: z :: rest).length)
    (hgas : cost ≤ g) :
    runS (ternopShape cost aluF top g) hs ss =
      .ok ((top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1, g - cost),
        { hs with stackFrames :=
            writeListAt l (top.toNat - 3) (aluF x y z) :: frest }) ss := by
  have hn : top.toNat = rest.length + 3 := by simpa using htop
  have hbound := top.isLt
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
  have hpfx' : l.take ((top.toNat - 1) + 1) = (x :: y :: z :: rest).reverse := by
    rw [show top.toNat - 1 + 1 = top.toNat from by omega]; exact hpfx
  have hpfx1 : l.take (top.toNat - 1) = (y :: z :: rest).reverse :=
    take_shrink l _ x _ hpfx' (by simp; omega)
  have hpfx1' : l.take ((top.toNat - 2) + 1) = (y :: z :: rest).reverse := by
    rw [show top.toNat - 2 + 1 = top.toNat - 1 from by omega]; exact hpfx1
  have hpfx2 : l.take (top.toNat - 2) = (z :: rest).reverse :=
    take_shrink l _ y _ hpfx1' (by simp; omega)
  simp only [ternopShape]
  refine runS_bind_ok (runS_charge_ok g cost hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok
    (runS_pop top hs ss l frest x (y :: z :: rest) hframe hpfx htop) ?_
  refine runS_bind_ok
    (runS_pop _ hs ss l frest y (z :: rest) hframe
      (by rw [hret1]; exact hpfx1) (by rw [hret1]; simp; omega)) ?_
  refine runS_bind_ok
    (runS_pop _ hs ss l frest z rest hframe
      (by rw [hret2]; exact hpfx2) (by rw [hret2]; simp; omega)) ?_
  refine runS_bind_ok
    (runS_push_word _ (aluF x y z) hs ss l frest hframe
      (by rw [hret3]; omega)) ?_
  have hc : top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1 - BitVec.ofNat 64 1
      + BitVec.ofNat 64 1
      = top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1 := by
    rw [BitVec.sub_add_cancel]
  rw [hc, hret3]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_ternopShape_oog (cost : Nat) (aluF : Nat → Nat → Nat → Nat)
    (top : StackTop) (g : Nat) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < cost) :
    runS (ternopShape cost aluF top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [ternopShape]
  refine runS_bind_ok
    (runS_charge_oog g cost hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

/-! ## `execute`-level, generic in the opcode

The two per-opcode facts are supplied as (rfl-provable) hypotheses:
the arity of `opcode_stack_effect` and the dispatch equation reducing
`execute_opcode` on this constructor to the shape.
-/

/-- The dispatch equation every ALU ternop constructor satisfies by `rfl`. -/
def TernopDispatch (op : ast) (cost : Nat) (aluF : Nat → Nat → Nat → Nat) :
    Prop :=
  Evm.Functions.opcode_stack_effect op = pure (3, 1) ∧
  ∀ (pc_in : Nat) (top : StackTop) (mem : EvmMemorySlice) (g : Nat),
    Evm.Functions.execute_opcode op pc_in top mem g =
      ternopShape cost aluF top g >>= fun p => pure (pc_in, p.1, mem, p.2)

open Evm.Functions in
theorem runS_execute_ternop_success (op : ast) (cost : Nat)
    (aluF : Nat → Nat → Nat → Nat) (hop : TernopDispatch op cost aluF)
    (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word))
    (x y z : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: z :: rest).reverse)
    (htop : top.toNat = (x :: y :: z :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hgas : cost ≤ g) :
    runS (Evm.Functions.execute op pc_in top mem g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1, mem, g - cost),
        { hs with stackFrames :=
            writeListAt l (top.toNat - 3) (aluF x y z) :: frest }) ss := by
  have hn : top.toNat = rest.length + 3 := by simpa using htop
  simp only [Evm.Functions.execute, hop.1]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 3 1 hs ss (by omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, hop.2]
  refine runS_bind_ok
    (runS_ternopShape_ok cost aluF top g hs ss l frest x y z rest hframe hpfx
      htop hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_ternop_underflow (op : ast) (cost : Nat)
    (aluF : Nat → Nat → Nat → Nat) (hop : TernopDispatch op cost aluF)
    (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 3) :
    runS (Evm.Functions.execute op pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute, hop.1]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 3 1 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_ternop_oog (op : ast) (cost : Nat)
    (aluF : Nat → Nat → Nat → Nat) (hop : TernopDispatch op cost aluF)
    (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hin : 3 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (hgas : g < cost) :
    runS (Evm.Functions.execute op pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute, hop.1]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 3 1 hs ss hin
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, hop.2]
  refine runS_bind_ok
    (runS_ternopShape_oog cost aluF top g hs ss prof sp msg hprof hsp hmsg
      hfork hgas) ?_
  exact runS_pure _ _ _

/-! ## The generic step equivalence -/

/-- **Every ALU ternop, all reachable outcomes.** Instantiated per opcode
with `rfl` shape equations (`hspec`, `hcost`, `hop`), one pure-function
lemma (`hpure`), and one wf bound (`hwf`). -/
theorem ternop_step_equiv (op : ast) (cost : Nat)
    (aluF : Nat → Nat → Nat → Nat) (iOp : EvmM Unit) (specCost : Uint)
    (fSpec : U256 → U256 → U256 → U256)
    (hspec : iOp = ternOp specCost fSpec)
    (hcost : specCost = cost)
    (hop : TernopDispatch op cost aluF)
    (hpure : ∀ x y z, WordWf x → WordWf y → WordWf z →
      aluF x y z = fSpec x y z)
    (hwf : ∀ x y z, WordWf x → WordWf y → WordWf z → WordWf (fSpec x y z))
    (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iOp sRef)
      (runS (Evm.Functions.execute op pc_in top mem g) hs ss) := by
  subst hspec hcost
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_ternOp_underflow_nil _ _ sRef hS,
      runS_execute_ternop_underflow op _ _ hop pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | [x] =>
    rw [hS] at hpfx htop
    rw [runR_ternOp_underflow_one _ _ sRef x hS,
      runS_execute_ternop_underflow op _ _ hop pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | [x, y] =>
    rw [hS] at hpfx htop
    rw [runR_ternOp_underflow_two _ _ sRef x y hS,
      runS_execute_ternop_underflow op _ _ hop pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | x :: y :: z :: rest =>
    rw [hS] at hpfx htop hlim hwfS
    have hwx : WordWf x := hwfS x (by simp)
    have hwy : WordWf y := hwfS y (by simp)
    have hwz : WordWf z := hwfS z (by simp)
    have hin3 : 3 ≤ top.toNat := by simp at htop; omega
    have hlim' : top.toNat ≤ 1024 := by simp at htop ⊢; simp at hlim; omega
    by_cases hg : sRef.evm.gasLeft < specCost
    · rw [runR_ternOp_oog _ _ sRef x y z rest hS hg,
        runS_execute_ternop_oog op _ _ hop pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hin3 hlim'
          (by rw [hlive]; exact hg)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
    · push Not at hg
      have hn : top.toNat = rest.length + 3 := by simpa using htop
      rw [runR_ternOp_success _ _ sRef x y z rest hS hg (by rw [hS]; exact hlim),
        runS_execute_ternop_success op _ _ hop pc_in top g mem hs ss l frest
          x y z rest hframe hpfx htop hlim' (by rw [hlive]; exact hg)]
      refine StepResultRel.success ?_
      refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
        ⟨msg, hmsg⟩⟩, by simp [hpc], rfl⟩
      · have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
          cursor_retreat_toNat top (by omega)
        have hret2 : (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1).toNat
            = top.toNat - 2 := by
          rw [cursor_retreat_toNat _ (by rw [hret1]; omega), hret1]
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
        refine ⟨⟨writeListAt l (top.toNat - 3) (aluF x y z),
          frest, rfl, ?_, ?_⟩, ?_, ?_, ?_⟩
        · rw [hret2]
          have hstep : top.toNat - 2 = (top.toNat - 3) + 1 := by omega
          rw [hstep, take_writeListAt l (top.toNat - 3) _ (by omega)]
          rw [hpfx3, hpure x y z hwx hwy hwz]
          simp
        · rw [hret2, length_writeListAt]
          omega
        · rw [hret2]; simp; omega
        · simp; simp at hlim; omega
        · intro w hw
          rcases List.mem_cons.mp hw with hw | hw
          · subst hw
            exact hwf x y z hwx hwy hwz
          · exact hwfS w (by simp [hw])
      · exact ⟨by rw [hlive], hres, hsp⟩

end EvmSpecsVerify
