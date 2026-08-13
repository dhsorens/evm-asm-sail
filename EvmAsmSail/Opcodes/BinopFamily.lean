import EvmAsmSail.Relations.State
import EvmAsmSail.Representation.EvmGas
import EvmAsmSail.Representation.SpecRefLemmas
import Batteries.Tactic.OpenPrivate

/-!
# The ALU binop family

Every 2-in/1-out ALU opcode has the same shape on both sides:

* SpecRef: `i<Op> = binOp cost fSpec` (the shared private combinator —
  pop ×2 → charge → push → pc+1, InstructionsCore.lean:122);
* `Evm`: `execute_<op>` is byte-identical to `execute_add` modulo the gas
  constant and the `alu_*` function (`charge → pop ×2 → alu → push_word`).

This file proves the family **once**: `binopShape` names the extraction's
shape; generic run lemmas replay the ADD proofs for arbitrary
`(cost, aluF)` / `(cost, fSpec)`; `binop_step_equiv` is the full-outcome
step theorem. Each opcode then needs only `rfl` shape equations, one pure
lemma `aluF = fSpec`, and a wf bound.

Reachable outcomes for the whole family: success, stack underflow (×2
shapes), out-of-gas. Overflow is unreachable (2 in, 1 out: the height
decreases), per `validate_stack`'s bound.
-/

open private binOp pcAdd from EvmAsm.Stateless.SpecRef.InstructionsCore
open private writeListAt from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmAsmSail

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- The success post-relation for the ALU family: the state relation holds on
the returned live values, the returned pc is the SpecRef post-pc (step
boundaries re-align; mismatch ledger MM-4), and memory is a pass-through. -/
def AluPost (mem : EvmMemorySlice) (sR' : Machine) (step : EvmStep)
    (hs' : Evm.HostState) (ss' : SeqState) : Prop :=
  StateRel sR' step.2.1 step.2.2.2 hs' ss' ∧
  step.1 = sR'.evm.pc ∧ step.2.2.1 = mem

/-! ## SpecRef side: `binOp cost f`, generically -/

theorem runR_binOp_success (cost : Uint) (f : U256 → U256 → U256) (s : Machine)
    (x y : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: y :: rest)
    (hgas : cost ≤ s.evm.gasLeft)
    (hlim : s.evm.stack.length ≤ 1024) :
    runR (binOp cost f) s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := f x y :: rest
            gasLeft := s.evm.gasLeft - cost
            regularGasUsed := s.evm.regularGasUsed + cost
            pc := s.evm.pc + 1 } }) := by
  have hlen : rest.length ≠ 1024 := by
    rw [hstack] at hlim; simp at hlim; omega
  simp only [binOp, pcAdd]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y rest (by simp)) ?_
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  refine runR_bind_ok (runR_stackPush _ _ (by simpa using hlen)) ?_
  exact runR_modifyEvm _ _

theorem runR_binOp_underflow_nil (cost : Uint) (f : U256 → U256 → U256)
    (s : Machine) (hstack : s.evm.stack = []) :
    runR (binOp cost f) s = .ok (.error .stackUnderflow, s) := by
  simp only [binOp]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_binOp_underflow_one (cost : Uint) (f : U256 → U256 → U256)
    (s : Machine) (x : U256) (hstack : s.evm.stack = [x]) :
    runR (binOp cost f) s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with stack := [] } }) := by
  simp only [binOp]
  refine runR_bind_ok (runR_stackPop_cons s x [] hstack) ?_
  exact runR_bind_err (runR_stackPop_nil _ (by simp))

theorem runR_binOp_oog (cost : Uint) (f : U256 → U256 → U256) (s : Machine)
    (x y : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: y :: rest)
    (hgas : s.evm.gasLeft < cost) :
    runR (binOp cost f) s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [binOp]
  refine runR_bind_ok (runR_stackPop_cons s x (y :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ y rest (by simp)) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _ (by simpa using hgas))

/-! ## `Evm` side: the handler shape, generically -/

/-- The shared body of every `Evm` ALU binop handler. Each generated
`execute_<op>` is definitionally `binopShape <G_const> alu_<op>`. -/
def binopShape (cost : Nat) (aluF : Nat → Nat → Nat) (top : StackTop)
    (g : Nat) : Evm.SailM (StackTop × Nat) := do
  let (gas_charged, g1) ← do (Evm.Functions.charge g cost)
  if ((! gas_charged) : Bool)
  then (pure (top, g1))
  else
    (do
      let (a, top1) ← do (Evm.Functions.pop top)
      let (b, top2) ← do (Evm.Functions.pop top1)
      let result := (aluF a b)
      (pure ((← (Evm.Functions.push_word top2 result)), g1)))

open Evm.Functions in
theorem runS_binopShape_ok (cost : Nat) (aluF : Nat → Nat → Nat)
    (top : StackTop) (g : Nat) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word))
    (x y : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: rest).reverse)
    (htop : top.toNat = (x :: y :: rest).length)
    (hlen : top.toNat ≤ l.length)
    (hgas : cost ≤ g) :
    runS (binopShape cost aluF top g) hs ss =
      .ok ((top - BitVec.ofNat 64 1, g - cost),
        { hs with stackFrames :=
            writeListAt l (top.toNat - 2) (aluF x y) :: frest }) ss := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  have hbound := top.isLt
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
  have hhead2 : (top - BitVec.ofNat 64 1 - BitVec.ofNat 64 1).toNat + 1 < 2 ^ 64 := by
    rw [cursor_retreat_toNat _ (by rw [htop1]; simp),
      cursor_retreat_toNat top (by omega)]
    omega
  simp only [binopShape]
  refine runS_bind_ok (runS_charge_ok g cost hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_pop top hs ss l frest x (y :: rest) hframe hpfx htop) ?_
  refine runS_bind_ok
    (runS_pop _ hs ss l frest y rest hframe hpfx1 (by simpa using htop1)) ?_
  refine runS_bind_ok (runS_push_word _ (aluF x y) hs ss l frest hframe hhead2) ?_
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
theorem runS_binopShape_oog (cost : Nat) (aluF : Nat → Nat → Nat)
    (top : StackTop) (g : Nat) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < cost) :
    runS (binopShape cost aluF top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [binopShape]
  refine runS_bind_ok
    (runS_charge_oog g cost hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

/-! ## `execute`-level, generic in the opcode

The two per-opcode facts are supplied as (rfl-provable) hypotheses:
the arity of `opcode_stack_effect` and the dispatch equation reducing
`execute_opcode` on this constructor to the shape.
-/

/-- The dispatch equation every ALU binop constructor satisfies by `rfl`. -/
def BinopDispatch (op : ast) (cost : Nat) (aluF : Nat → Nat → Nat) : Prop :=
  Evm.Functions.opcode_stack_effect op = pure (2, 1) ∧
  ∀ (pc_in : Nat) (top : StackTop) (mem : EvmMemorySlice) (g : Nat),
    Evm.Functions.execute_opcode op pc_in top mem g =
      binopShape cost aluF top g >>= fun p => pure (pc_in, p.1, mem, p.2)

open Evm.Functions in
theorem runS_execute_binop_success (op : ast) (cost : Nat)
    (aluF : Nat → Nat → Nat) (hop : BinopDispatch op cost aluF)
    (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word))
    (x y : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: y :: rest).reverse)
    (htop : top.toNat = (x :: y :: rest).length)
    (hlen : top.toNat ≤ l.length)
    (hlim : top.toNat ≤ 1024)
    (hgas : cost ≤ g) :
    runS (Evm.Functions.execute op pc_in top mem g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1, mem, g - cost),
        { hs with stackFrames :=
            writeListAt l (top.toNat - 2) (aluF x y) :: frest }) ss := by
  have hn : top.toNat = rest.length + 2 := by simpa using htop
  simp only [Evm.Functions.execute, hop.1]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 1 hs ss (by omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, hop.2]
  refine runS_bind_ok
    (runS_binopShape_ok cost aluF top g hs ss l frest x y rest hframe hpfx
      htop hlen hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_binop_underflow (op : ast) (cost : Nat)
    (aluF : Nat → Nat → Nat) (hop : BinopDispatch op cost aluF)
    (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 2) :
    runS (Evm.Functions.execute op pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute, hop.1]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 2 1 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_binop_oog (op : ast) (cost : Nat)
    (aluF : Nat → Nat → Nat) (hop : BinopDispatch op cost aluF)
    (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hin : 2 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (hgas : g < cost) :
    runS (Evm.Functions.execute op pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute, hop.1]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 1 hs ss hin
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, hop.2]
  refine runS_bind_ok
    (runS_binopShape_oog cost aluF top g hs ss prof sp msg hprof hsp hmsg
      hfork hgas) ?_
  exact runS_pure _ _ _

/-! ## The generic step equivalence -/

/-- **Every ALU binop, all reachable outcomes.** Instantiated per opcode with
four `rfl` equations (`hspec`, `hcost`, `hop`), one pure-function lemma
(`hpure`), and one wf bound (`hwf`). -/
theorem binop_step_equiv (op : ast) (cost : Nat) (aluF : Nat → Nat → Nat)
    (iOp : EvmM Unit) (specCost : Uint) (fSpec : U256 → U256 → U256)
    (hspec : iOp = binOp specCost fSpec)
    (hcost : specCost = cost)
    (hop : BinopDispatch op cost aluF)
    (hpure : ∀ x y, WordWf x → WordWf y → aluF x y = fSpec x y)
    (hwf : ∀ x y, WordWf x → WordWf y → WordWf (fSpec x y))
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
    rw [runR_binOp_underflow_nil _ _ sRef hS,
      runS_execute_binop_underflow op _ _ hop pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | [x] =>
    rw [hS] at hpfx htop
    rw [runR_binOp_underflow_one _ _ sRef x hS,
      runS_execute_binop_underflow op _ _ hop pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | x :: y :: rest =>
    rw [hS] at hpfx htop hlim hwfS
    have hwx : WordWf x := hwfS x (by simp)
    have hwy : WordWf y := hwfS y (by simp)
    have hin2 : 2 ≤ top.toNat := by simp at htop; omega
    have hlim' : top.toNat ≤ 1024 := by simp at htop ⊢; simp at hlim; omega
    by_cases hg : sRef.evm.gasLeft < specCost
    · rw [runR_binOp_oog _ _ sRef x y rest hS hg,
        runS_execute_binop_oog op _ _ hop pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hin2 hlim'
          (by rw [hlive]; exact hg)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
    · push_neg at hg
      have hn : top.toNat = rest.length + 2 := by simpa using htop
      rw [runR_binOp_success _ _ sRef x y rest hS hg (by rw [hS]; exact hlim),
        runS_execute_binop_success op _ _ hop pc_in top g mem hs ss l frest
          x y rest hframe hpfx htop hlen hlim' (by rw [hlive]; exact hg)]
      refine StepResultRel.success ?_
      refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
        ⟨msg, hmsg⟩⟩, by simp [hpc], rfl⟩
      · have hret : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
          cursor_retreat_toNat top (by omega)
        refine ⟨⟨writeListAt l (top.toNat - 2) (aluF x y),
          frest, rfl, ?_, ?_⟩, ?_, ?_, ?_⟩
        · rw [hret]
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
          rw [hpfx2, hpure x y hwx hwy]
          simp
        · rw [hret, length_writeListAt]
          omega
        · rw [hret]; simp; omega
        · simp; simp at hlim; omega
        · intro z hz
          rcases List.mem_cons.mp hz with hz | hz
          · subst hz
            exact hwf x y hwx hwy
          · exact hwfS z (by simp [hz])
      · exact ⟨by rw [hlive], hres, hsp⟩

end EvmAsmSail
