import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Relations.Transient
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# TLOAD

Transient storage's reader (EIP-1153), and the last 1-in/1-out world read
in this tranche. Structurally the [`CALLDATALOAD`](Calldataload.lean) /
[`BLOBHASH`](Blobhash.lean) sibling — pop, charge, push — with the value
supplied by [`TloadAgree`](#TloadAgree), the transient analogue of
[`SloadAgree`](Sload.lean).

Transient storage has **no warm/cold accounting**: EIP-1153 prices both
TLOAD and TSTORE at a flat `WARM_ACCESS`, and neither side consults an
access set. So `TloadAgree` is simpler than `SloadAgree` in exactly the way
[`SelfBalanceAgree`](Selfbalance.lean) is simpler than `BalanceAgree` — no
quantification over ambient warm stamps.

Reachable outcomes: success / stack underflow / OOG; overflow is
unreachable for 1-in/1-out. MM-1 order difference as usual (SpecRef pops
before charging, the extraction's body charges before popping, both behind
`validate_stack`, so the halt kinds align case by case).

Gas (MM-2): `GasCosts.OPCODE_TLOAD = 100 = G_warm_access = WARM_ACCESS`.

TSTORE lands separately ([`Tstore.lean`](Tstore.lean)), because its
success path writes the store and `BasePost` observes only stack/gas/pc:
it needs a transient-store *relation* in the post. That relation,
`TransientRel`, also turns this slice's `TloadAgree` hypothesis into a
theorem — see `tloadAgree_of_transientRel` below.
-/

open private pcAdd from EvmAsm.Stateless.SpecRef.InstructionsCore
open private writeListAt from Evm.HostAxioms

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- The two sides' transient reads agree for the executing account and the
popped slot, and the extraction's read leaves the operand stack alone.
The `SloadAgree` sibling minus the warm machinery — transient storage is
flat-priced, so nothing is quantified over ambient stamps. -/
def TloadAgree (sRef : Machine) (hs : Evm.HostState) (ss : SeqState)
    (aV : Evm.Defs.address) (x : Nat) : Prop :=
  ∃ (v : U256) (ts' : TransactionState) (hostAfter : Evm.HostState),
    WordWf v ∧
    (getTransientStorage sRef.evm.message.currentTarget
      (toBeBytes32 x)).run sRef.txState = .ok (v, ts') ∧
    runS (Evm.Functions.k_tload aV x) hs ss = .ok (v, hostAfter) ss ∧
    hostAfter.stackFrames = hs.stackFrames

/-- **`TloadAgree` is not an axiom any more.** Once the transient store is
related pointwise ([`TransientRel`](../Relations/Transient.lean), landed
with TSTORE), the read agreement is a theorem: the two reads are the same
function of related maps, `k_tload` leaves the host state alone, and the
value's well-formedness is the relation's `wf` field. The slice keeps the
`TloadAgree` interface so its step theorem is unchanged; what changes is
that a caller can now *discharge* it instead of assuming it. -/
theorem tloadAgree_of_transientRel (sRef : Machine) (hs : Evm.HostState)
    (ss : SeqState) (aV : Evm.Defs.address) (x : Nat) (hx : WordWf x)
    (haddr : aV.toList = sRef.evm.message.currentTarget)
    (htr : TransientRel sRef.txState hs) :
    TloadAgree sRef hs ss aV x := by
  refine ⟨hostTransientRead hs aV x, sRef.txState, hs, htr.wf aV x hx, ?_,
    runS_k_tload aV x hs ss, rfl⟩
  rw [← haddr, runTx_getTransientStorage, htr.rel aV x hx]

/-! ## SpecRef run shapes -/

theorem runR_iTload_underflow (s : Machine) (hstack : s.evm.stack = []) :
    runR iTload s = .ok (.error .stackUnderflow, s) := by
  simp only [iTload]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_iTload_oog (s : Machine) (x : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: rest)
    (hgas : s.evm.gasLeft < GasCosts.OPCODE_TLOAD) :
    runR iTload s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [iTload]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _ hgas)

theorem runR_iTload_success (s : Machine) (x : U256) (rest : List U256)
    (v : U256) (ts' : TransactionState)
    (hstack : s.evm.stack = x :: rest)
    (hread : (getTransientStorage s.evm.message.currentTarget
      (toBeBytes32 x)).run s.txState = .ok (v, ts'))
    (hgas : GasCosts.OPCODE_TLOAD ≤ s.evm.gasLeft)
    (hlim : s.evm.stack.length ≤ 1024) :
    runR iTload s =
      .ok (.ok (),
        { s with
          txState := ts'
          evm := { s.evm with
            stack := v :: rest
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_TLOAD
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_TLOAD
            pc := s.evm.pc + 1 } }) := by
  have hlen : rest.length ≠ 1024 := by
    rw [hstack] at hlim; simp at hlim; omega
  simp only [iTload, pcAdd]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_liftTx_ok _ _ v ts' (by exact hread)) ?_
  refine runR_bind_ok (runR_stackPush _ _ (by simpa using hlen)) ?_
  exact runR_modifyEvm _ _

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for TLOAD. -/
theorem tload_dispatch (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_opcode (.TLOAD ()) pc_in top mem g =
      Evm.Functions.execute_tload top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
theorem runS_tload_body_ok (top : StackTop) (g : Nat)
    (hs hs' : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (msg : Evm.Defs.Message) (v : word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hval : runS (Evm.Functions.k_tload msg.address x) hs ss
      = .ok (v, hs') ss)
    (hframe' : hs'.stackFrames = l :: frest)
    (hgas : (GasCosts.OPCODE_TLOAD : Nat) ≤ g) :
    runS (Evm.Functions.execute_tload top g) hs ss =
      .ok ((top, g - GasCosts.OPCODE_TLOAD),
        { hs' with stackFrames :=
            writeListAt l (top.toNat - 1) v :: frest }) ss := by
  have hn : top.toNat = rest.length + 1 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  simp only [Evm.Functions.execute_tload]
  refine runS_bind_ok (runS_charge_ok g G_warm_access hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_pop top hs ss l frest x rest hframe hpfx htop) ?_
  refine runS_bind_ok (runS_self_addr msg hs ss hmsg) ?_
  refine runS_bind_ok hval ?_
  refine runS_bind_ok
    (runS_push_word (top - BitVec.ofNat 64 1) v hs' ss l frest hframe'
      (by rw [hret1]; omega)) ?_
  rw [BitVec.sub_add_cancel, hret1]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_tload_body_oog (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < (GasCosts.OPCODE_TLOAD : Nat)) :
    runS (Evm.Functions.execute_tload top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_tload]
  refine runS_bind_ok
    (runS_charge_oog g G_warm_access hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_tload_ok (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs hs' : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (msg : Evm.Defs.Message) (v : word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hval : runS (Evm.Functions.k_tload msg.address x) hs ss
      = .ok (v, hs') ss)
    (hframe' : hs'.stackFrames = l :: frest)
    (hgas : (GasCosts.OPCODE_TLOAD : Nat) ≤ g) :
    runS (Evm.Functions.execute (.TLOAD ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, g - GasCosts.OPCODE_TLOAD),
        { hs' with stackFrames :=
            writeListAt l (top.toNat - 1) v :: frest }) ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.TLOAD ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 1 hs ss (by simp at htop; omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, tload_dispatch]
  refine runS_bind_ok
    (runS_tload_body_ok top g hs hs' ss l frest x rest msg v hframe hpfx
      htop hmsg hval hframe' hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_tload_oog (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (hpos : 1 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < (GasCosts.OPCODE_TLOAD : Nat)) :
    runS (Evm.Functions.execute (.TLOAD ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.TLOAD ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 1 hs ss (by omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, tload_dispatch]
  refine runS_bind_ok
    (runS_tload_body_oog top g hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_tload_underflow (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 1) :
    runS (Evm.Functions.execute (.TLOAD ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.TLOAD ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 1 1 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **TLOAD, all reachable outcomes**: success / stack underflow / OOG.
Overflow is unreachable for 1-in/1-out, and there is no warm/cold split —
EIP-1153 prices transient access flat on both sides. -/
theorem tload_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (htl : ∀ (msg : Evm.Defs.Message) (x : Nat),
      ss.regs.get? Register.message = some msg →
      TloadAgree sRef hs ss msg.address x) :
    StepResultRel (BasePost mem) (runR iTload sRef)
      (runS (Evm.Functions.execute (.TLOAD ()) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_iTload_underflow sRef hS,
      runS_execute_tload_underflow pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | x :: rest =>
    rw [hS] at hpfx htop hlim hwfS
    have hlim' : top.toNat ≤ 1024 := by simp at htop hlim; omega
    by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_TLOAD
    · rw [runR_iTload_oog sRef x rest hS hg,
        runS_execute_tload_oog pc_in top g mem hs ss
          (by simp at htop; omega) hlim' prof sRef.evm.stateGasSpilled msg
          hprof hsp hmsg hfork (by rw [hlive]; exact hg)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
    · push Not at hg
      obtain ⟨v, ts', hostAfter, hwfv, hread, hval, hstk⟩ := htl msg x hmsg
      have hframe' : hostAfter.stackFrames = l :: frest := by
        rw [hstk]; exact hframe
      rw [runR_iTload_success sRef x rest v ts' hS hread hg
          (by rw [hS]; exact hlim),
        runS_execute_tload_ok pc_in top g mem hs hostAfter ss l frest x rest
          msg v hframe hpfx htop hlim' hmsg hval hframe'
          (by rw [hlive]; exact hg)]
      refine StepResultRel.success ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
        ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, hpc, rfl⟩
      · exact pop_push_post_stack top _ l frest x rest v
          (hostState_set_stackFrames_frames _ _) hpfx htop hlim hlen hwfS
          hwfv
      · exact ⟨by rw [hlive], hres, hsp⟩

end EvmSpecsVerify
