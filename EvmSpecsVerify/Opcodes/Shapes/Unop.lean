import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.SpecRefLemmas
import Batteries.Tactic.OpenPrivate

/-!
# ALU unop shape (1-in/1-out)

Sibling of [`Binop`](Binop.lean) / [`Ternop`](Ternop.lean) — do not import
those, or this file from them. Shared Post and wf lemmas:
[`Alu`](Alu.lean).

SpecRef: `i<Op> = unOp cost fSpec` (pop → charge → push → pc+1).
`Evm`: `execute_<op>` is `execute_iszero` modulo gas constant and `alu_*`.

[`unop_step_equiv`](#unop_step_equiv) is the full-outcome step theorem.
Reachable: success, stack underflow, out-of-gas. Overflow unreachable
(height preserved, already within the limit).
-/

open private unOp pcAdd from EvmAsm.Stateless.SpecRef.InstructionsCore
open private writeListAt from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## SpecRef side: `unOp cost f`, generically -/

theorem runR_unOp_success (cost : Uint) (f : U256 → U256) (s : Machine)
    (x : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: rest)
    (hgas : cost ≤ s.evm.gasLeft)
    (hlim : s.evm.stack.length ≤ 1024) :
    runR (unOp cost f) s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := f x :: rest
            gasLeft := s.evm.gasLeft - cost
            regularGasUsed := s.evm.regularGasUsed + cost
            pc := s.evm.pc + 1 } }) := by
  have hlen : rest.length ≠ 1024 := by
    rw [hstack] at hlim; simp at hlim; omega
  simp only [unOp, pcAdd]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  refine runR_bind_ok (runR_stackPush _ _ (by simpa using hlen)) ?_
  exact runR_modifyEvm _ _

theorem runR_unOp_underflow (cost : Uint) (f : U256 → U256)
    (s : Machine) (hstack : s.evm.stack = []) :
    runR (unOp cost f) s = .ok (.error .stackUnderflow, s) := by
  simp only [unOp]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_unOp_oog (cost : Uint) (f : U256 → U256) (s : Machine)
    (x : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: rest)
    (hgas : s.evm.gasLeft < cost) :
    runR (unOp cost f) s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [unOp]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _ (by simpa using hgas))

/-! ## `Evm` side: the handler shape, generically -/

/-- The shared body of every `Evm` ALU unop handler. Each generated
`execute_<op>` is definitionally `unopShape <G_const> alu_<op>`. -/
def unopShape (cost : Nat) (aluF : Nat → Nat) (top : StackTop)
    (g : Nat) : Evm.SailM (StackTop × Nat) := do
  let (gas_charged, g1) ← do (Evm.Functions.charge g cost)
  if ((! gas_charged) : Bool)
  then (pure (top, g1))
  else
    (do
      let (a, top1) ← do (Evm.Functions.pop top)
      let result := (aluF a)
      (pure ((← (Evm.Functions.push_word top1 result)), g1)))

open Evm.Functions in
theorem runS_unopShape_ok (cost : Nat) (aluF : Nat → Nat)
    (top : StackTop) (g : Nat) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word))
    (x : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hgas : cost ≤ g) :
    runS (unopShape cost aluF top g) hs ss =
      .ok ((top, g - cost),
        { hs with stackFrames :=
            writeListAt l (top.toNat - 1) (aluF x) :: frest }) ss := by
  have hn : top.toNat = rest.length + 1 := by simpa using htop
  have hbound := top.isLt
  have hret : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  simp only [unopShape]
  refine runS_bind_ok (runS_charge_ok g cost hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_pop top hs ss l frest x rest hframe hpfx htop) ?_
  refine runS_bind_ok
    (runS_push_word _ (aluF x) hs ss l frest hframe (by rw [hret]; omega)) ?_
  have hc : top - BitVec.ofNat 64 1 + BitVec.ofNat 64 1 = top := by
    rw [BitVec.sub_add_cancel]
  rw [hc, hret]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_unopShape_oog (cost : Nat) (aluF : Nat → Nat)
    (top : StackTop) (g : Nat) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < cost) :
    runS (unopShape cost aluF top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [unopShape]
  refine runS_bind_ok
    (runS_charge_oog g cost hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

/-! ## `execute`-level, generic in the opcode

The two per-opcode facts are supplied as (rfl-provable) hypotheses:
the arity of `opcode_stack_effect` and the dispatch equation reducing
`execute_opcode` on this constructor to the shape.
-/

/-- The dispatch equation every ALU unop constructor satisfies by `rfl`. -/
def UnopDispatch (op : ast) (cost : Nat) (aluF : Nat → Nat) : Prop :=
  Evm.Functions.opcode_stack_effect op = pure (1, 1) ∧
  ∀ (pc_in : Nat) (top : StackTop) (mem : EvmMemorySlice) (g : Nat),
    Evm.Functions.execute_opcode op pc_in top mem g =
      unopShape cost aluF top g >>= fun p => pure (pc_in, p.1, mem, p.2)

open Evm.Functions in
theorem runS_execute_unop_success (op : ast) (cost : Nat)
    (aluF : Nat → Nat) (hop : UnopDispatch op cost aluF)
    (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word))
    (x : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hgas : cost ≤ g) :
    runS (Evm.Functions.execute op pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, g - cost),
        { hs with stackFrames :=
            writeListAt l (top.toNat - 1) (aluF x) :: frest }) ss := by
  have hn : top.toNat = rest.length + 1 := by simpa using htop
  simp only [Evm.Functions.execute, hop.1]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 1 hs ss (by omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, hop.2]
  refine runS_bind_ok
    (runS_unopShape_ok cost aluF top g hs ss l frest x rest hframe hpfx
      htop hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_unop_underflow (op : ast) (cost : Nat)
    (aluF : Nat → Nat) (hop : UnopDispatch op cost aluF)
    (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 1) :
    runS (Evm.Functions.execute op pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute, hop.1]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 1 1 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_unop_oog (op : ast) (cost : Nat)
    (aluF : Nat → Nat) (hop : UnopDispatch op cost aluF)
    (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hin : 1 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (hgas : g < cost) :
    runS (Evm.Functions.execute op pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute, hop.1]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 1 hs ss hin
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, hop.2]
  refine runS_bind_ok
    (runS_unopShape_oog cost aluF top g hs ss prof sp msg hprof hsp hmsg
      hfork hgas) ?_
  exact runS_pure _ _ _

/-! ## The generic step equivalence -/

/-- **Every ALU unop, all reachable outcomes.** Instantiated per opcode with
three `rfl` equations (`hspec`, `hcost`, `hop`), one pure-function lemma
(`hpure`), and one wf bound (`hwf`). -/
theorem unop_step_equiv (op : ast) (cost : Nat) (aluF : Nat → Nat)
    (iOp : EvmM Unit) (specCost : Uint) (fSpec : U256 → U256)
    (hspec : iOp = unOp specCost fSpec)
    (hcost : specCost = cost)
    (hop : UnopDispatch op cost aluF)
    (hpure : ∀ x, WordWf x → aluF x = fSpec x)
    (hwf : ∀ x, WordWf x → WordWf (fSpec x))
    (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (BasePost mem) (runR iOp sRef)
      (runS (Evm.Functions.execute op pc_in top mem g) hs ss) := by
  subst hspec hcost
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_unOp_underflow _ _ sRef hS,
      runS_execute_unop_underflow op _ _ hop pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | x :: rest =>
    rw [hS] at hpfx htop hlim hwfS
    have hwx : WordWf x := hwfS x (by simp)
    have hin1 : 1 ≤ top.toNat := by simp at htop; omega
    have hlim' : top.toNat ≤ 1024 := by simp at htop ⊢; simp at hlim; omega
    by_cases hg : sRef.evm.gasLeft < specCost
    · rw [runR_unOp_oog _ _ sRef x rest hS hg,
        runS_execute_unop_oog op _ _ hop pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hin1 hlim'
          (by rw [hlive]; exact hg)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
    · push Not at hg
      have hn : top.toNat = rest.length + 1 := by simpa using htop
      rw [runR_unOp_success _ _ sRef x rest hS hg (by rw [hS]; exact hlim),
        runS_execute_unop_success op _ _ hop pc_in top g mem hs ss l frest
          x rest hframe hpfx htop hlim' (by rw [hlive]; exact hg)]
      refine StepResultRel.success ?_
      refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
        ⟨msg, hmsg⟩⟩, by simp [hpc], rfl⟩
      · have hpfx2 : l.take (top.toNat - 1) = rest.reverse := by
          have hview : l.take (top.toNat - 1) =
              (l.take top.toNat).take (top.toNat - 1) := by
            rw [List.take_take, Nat.min_eq_left (by omega)]
          rw [hview, hpfx]
          have hrl : rest.reverse.length = top.toNat - 1 := by simp; omega
          calc ((x :: rest).reverse).take (top.toNat - 1)
              = (rest.reverse ++ [x]).take (top.toNat - 1) := by simp
            _ = rest.reverse := by
                rw [List.take_append_of_le_length (by omega), ← hrl,
                  List.take_length]
        refine ⟨⟨writeListAt l (top.toNat - 1) (aluF x),
          frest, rfl, ?_, ?_⟩, ?_, ?_, ?_⟩
        · have htake := take_writeListAt l (top.toNat - 1) (aluF x) (by omega)
          have hidx : top.toNat - 1 + 1 = top.toNat := by omega
          rw [hidx] at htake
          rw [htake, hpfx2, hpure x hwx]
          simp
        · show top.toNat ≤ _
          rw [length_writeListAt]
          omega
        · simp
          omega
        · simp; simp at hlim; omega
        · intro z hz
          rcases List.mem_cons.mp hz with hz | hz
          · subst hz
            exact hwf x hwx
          · exact hwfS z (by simp [hz])
      · exact ⟨by rw [hlive], hres, hsp⟩

end EvmSpecsVerify
