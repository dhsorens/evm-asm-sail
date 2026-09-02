import EvmSpecsVerify.Relations.Transient
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# TSTORE

Transient storage's writer (EIP-1153), and the first opcode whose entire
observable effect is a *write to world-ish state*. `BasePost` observes
stack, gas and pc only, so this slice needs
[`TransientRel`](../Relations/Transient.lean) in the post — otherwise a
green theorem would say nothing about the store.

## MM-14: the mirror of MM-11

`iTstore` tests `message.isStatic` as its **first** statement, before
either pop. The extraction's `guard_static` is likewise the first
statement of `execute_tstore` — but `execute` hoists `validate_stack`
*outside* `execute_opcode`, so on the extraction side the stack check
comes first. In a static frame with fewer than two operands the two sides
therefore report different kinds: SpecRef `.writeInStaticContext`, the
extraction `StackUnderflow`. Both are exceptional halts consuming the
frame, so this is the `StepResultRel.haltedStaticFirst` constructor —
narrower than `haltedChargeFirst`, since every opcode in this class is
`n`-in/0-out and cannot overflow.

Where LOG puts SpecRef's guard too *late* (after the charge, MM-11),
TSTORE puts it too *early* (before the stack validation). The same
crossing applies to SSTORE and SELFDESTRUCT.

## MM-13: the zero write

SpecRef's `setTransientStorage` **deletes** the row when the value is
zero; the extraction's `transient_store` stores the zero. Both readers
return zero for an absent key and nothing enumerates either map, so
`TransientRel` is stated pointwise and the divergence is invisible
through it — see `Relations/Transient.lean` and the ledger.

Reachable outcomes: success, the static halt, underflow ×2, OOG, plus the
MM-14 double fault. Overflow is unreachable (2-in/0-out).

Gas (MM-2): `GasCosts.OPCODE_TSTORE = 100 = G_warm_access`; EIP-1153
prices transient access flat, with no warm/cold component on either side.
-/

open private pcAdd from EvmAsm.Stateless.SpecRef.InstructionsCore

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## SpecRef run shapes -/

/-- MM-14: the static throw fires before either pop, so no state moves. -/
theorem runR_iTstore_static (s : Machine)
    (hstatic : s.evm.message.isStatic = true) :
    runR iTstore s = .ok (.error .writeInStaticContext, s) := by
  simp only [iTstore]
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_pos (by simpa using hstatic)]
  exact runR_bind_err (runR_throw _ _)

/-- Underflow at either height, in one lemma: the halt discards the
machine. -/
theorem runR_iTstore_underflow (s : Machine)
    (hstatic : s.evm.message.isStatic = false)
    (hlen : s.evm.stack.length < 2) :
    ∃ s', runR iTstore s = .ok (.error .stackUnderflow, s') := by
  simp only [iTstore]
  match hS : s.evm.stack with
  | [] =>
    refine ⟨s, ?_⟩
    refine runR_bind_ok (runR_getEvm _) ?_
    rw [if_neg (by simpa using hstatic)]
    refine runR_bind_ok (runR_pure _ _) ?_
    exact runR_bind_err (runR_stackPop_nil s hS)
  | [x] =>
    refine ⟨{ s with evm := { s.evm with stack := [] } }, ?_⟩
    refine runR_bind_ok (runR_getEvm _) ?_
    rw [if_neg (by simpa using hstatic)]
    refine runR_bind_ok (runR_pure _ _) ?_
    refine runR_bind_ok (runR_stackPop_cons s x [] hS) ?_
    exact runR_bind_err (runR_stackPop_nil _ rfl)
  | x :: y :: rest =>
    rw [hS] at hlen
    simp only [List.length_cons] at hlen
    omega

theorem runR_iTstore_oog (s : Machine) (x v : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: v :: rest)
    (hstatic : s.evm.message.isStatic = false)
    (hgas : s.evm.gasLeft < GasCosts.OPCODE_TSTORE) :
    runR iTstore s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [iTstore]
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_neg (by simpa using hstatic)]
  refine runR_bind_ok (runR_pure _ _) ?_
  refine runR_bind_ok (runR_stackPop_cons s x (v :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ v rest rfl) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _ hgas)

theorem runR_iTstore_success (s : Machine) (x v : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: v :: rest)
    (hstatic : s.evm.message.isStatic = false)
    (hgas : GasCosts.OPCODE_TSTORE ≤ s.evm.gasLeft) :
    runR iTstore s =
      .ok (.ok (),
        { s with
          txState :=
            transientWriteOf s.txState s.evm.message.currentTarget
              (toBeBytes32 x) v
          evm := { s.evm with
            stack := rest
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_TSTORE
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_TSTORE
            pc := s.evm.pc + 1 } }) := by
  simp only [iTstore, pcAdd]
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_neg (by simpa using hstatic)]
  refine runR_bind_ok (runR_pure _ _) ?_
  refine runR_bind_ok (runR_stackPop_cons s x (v :: rest) hstack) ?_
  refine runR_bind_ok (runR_stackPop_cons _ v rest rfl) ?_
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok
    (runR_liftTx_ok _ _ () _ (runTx_setTransientStorage _ _ _ _)) ?_
  exact runR_modifyEvm _ _

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for TSTORE. -/
theorem tstore_dispatch (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_opcode (.TSTORE ()) pc_in top mem g =
      Evm.Functions.execute_tstore top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
/-- MM-14: the hoisted stack validation runs before `guard_static`, so
underflow wins on this side whatever the frame's static flag says. -/
theorem runS_execute_tstore_underflow (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 2) :
    runS (Evm.Functions.execute (.TSTORE ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.TSTORE ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 2 0 hs ss prof sp msg hprof hsp
      hmsg hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_tstore_static (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hin : 2 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (hstatic : msg.is_static = true) :
    runS (Evm.Functions.execute (.TSTORE ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .WriteProtection } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.TSTORE ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss hin
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, tstore_dispatch]
  have hbody : runS (Evm.Functions.execute_tstore top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .WriteProtection } := by
    simp only [Evm.Functions.execute_tstore]
    refine runS_bind_ok
      (runS_guard_static_halt g hs ss prof sp msg hprof hsp hmsg hfork
        hstatic) ?_
    rw [if_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
theorem runS_execute_tstore_oog (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hin : 2 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (hstatic : msg.is_static = false)
    (hgas : g < GasCosts.OPCODE_TSTORE) :
    runS (Evm.Functions.execute (.TSTORE ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.TSTORE ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss hin
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, tstore_dispatch]
  have hbody : runS (Evm.Functions.execute_tstore top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
    simp only [Evm.Functions.execute_tstore]
    refine runS_bind_ok (runS_guard_static_ok g hs ss msg hmsg hstatic) ?_
    rw [if_neg (by simp)]
    refine runS_bind_ok
      (runS_charge_oog g G_warm_access hs ss prof sp msg hprof hsp hmsg
        hfork (by simpa [Evm.Functions.G_warm_access] using hgas)) ?_
    rw [if_pos (by simp)]
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

open Evm.Functions in
theorem runS_execute_tstore_ok (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x v : Nat)
    (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: v :: rest).reverse)
    (htop : top.toNat = (x :: v :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (msg : Evm.Defs.Message)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hstatic : msg.is_static = false)
    (hgas : (GasCosts.OPCODE_TSTORE : Nat) ≤ g) :
    runS (Evm.Functions.execute (.TSTORE ()) pc_in top mem g) hs ss =
      .ok ((pc_in, cursorDrop top 2, mem, g - GasCosts.OPCODE_TSTORE),
        hostTransientWrite hs msg.address x v) ss := by
  have hnn : top.toNat = rest.length + 2 := by simp at htop; omega
  obtain ⟨hp1, ht1⟩ := cursor_pop_step l top x (v :: rest) hpfx htop
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.TSTORE ()) = pure (2, 0)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 2 0 hs ss (by omega)
      (by have h : top.toNat - 2 + 0 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, tstore_dispatch]
  have hbody : runS (Evm.Functions.execute_tstore top g) hs ss =
      .ok ((cursorDrop top 2, g - GasCosts.OPCODE_TSTORE),
        hostTransientWrite hs msg.address x v) ss := by
    simp only [Evm.Functions.execute_tstore]
    refine runS_bind_ok (runS_guard_static_ok g hs ss msg hmsg hstatic) ?_
    rw [if_neg (by simp)]
    refine runS_bind_ok
      (runS_charge_ok g G_warm_access hs ss
        (by simpa [Evm.Functions.G_warm_access] using hgas)) ?_
    rw [if_neg (by simp)]
    refine runS_bind_ok
      (runS_pop top hs ss l frest x (v :: rest) hframe hpfx htop) ?_
    refine runS_bind_ok (runS_pop _ hs ss l frest v rest hframe hp1 ht1) ?_
    refine runS_bind_ok (runS_self_addr msg hs ss hmsg) ?_
    refine runS_bind_ok (runS_k_tstore msg.address x v hs ss) ?_
    exact runS_pure _ _ _
  exact runS_bind_ok hbody (runS_pure _ _ _)

/-! ## The step equivalence -/

open Evm.Functions in
/-- **TSTORE, all reachable outcomes**: success (the write, related by
`TransientRel`), the static halt, underflow at either height, OOG, and the
MM-14 double fault. `haddr`/`hstatic` are the usual `message`-register
ties. -/
theorem tstore_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (htr : TransientRel sRef.txState hs)
    (hpc : pc_in = sRef.evm.pc + 1)
    (haddr : ∀ m : Evm.Defs.Message,
      ss.regs.get? Register.message = some m →
      m.address.toList = sRef.evm.message.currentTarget)
    (hstatic : ∀ m : Evm.Defs.Message,
      ss.regs.get? Register.message = some m →
      m.is_static = sRef.evm.message.isStatic) :
    StepResultRel (TransientPost mem) (runR iTstore sRef)
      (runS (Evm.Functions.execute (.TSTORE ()) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ :=
    hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  have hst : msg.is_static = sRef.evm.message.isStatic := hstatic msg hmsg
  have hax : msg.address.toList = sRef.evm.message.currentTarget :=
    haddr msg hmsg
  by_cases hunder : sRef.evm.stack.length < 2
  · -- MM-14: the extraction's hoisted stack check fires first either way
    rw [runS_execute_tstore_underflow pc_in top mem g hs ss prof
      sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
      (by rw [htop]; exact hunder)]
    by_cases hstat : sRef.evm.message.isStatic = true
    · rw [runR_iTstore_static sRef hstat]
      exact StepResultRel.haltedStaticFirst
        (haltRegs_frame_status ss msg .StackUnderflow)
    · obtain ⟨s', hs'⟩ :=
        runR_iTstore_underflow sRef (by simpa using hstat) hunder
      rw [hs']
      exact StepResultRel.halted ErrorRel.stackUnderflow
        (haltRegs_frame_status ss msg .StackUnderflow)
  · push Not at hunder
    obtain ⟨x, v, rest, hS⟩ :
        ∃ x v rest, sRef.evm.stack = x :: v :: rest := by
      match hSm : sRef.evm.stack with
      | [] => rw [hSm] at hunder; simp only [List.length_nil] at hunder; omega
      | [x] =>
        rw [hSm] at hunder
        simp only [List.length_cons, List.length_nil] at hunder
        omega
      | x :: v :: rest => exact ⟨x, v, rest, rfl⟩
    rw [hS] at hpfx htop hlim hwfS
    have hnn : top.toNat = rest.length + 2 := by
      simp only [List.length_cons] at htop; omega
    have hlim' : top.toNat ≤ 1024 := by
      simp only [List.length_cons] at hlim; omega
    have hlimR : rest.length ≤ 1024 := by omega
    have hwfx : WordWf x := hwfS x (by simp)
    have hwfv : WordWf v := hwfS v (by simp)
    by_cases hstat : sRef.evm.message.isStatic = true
    · rw [runR_iTstore_static sRef hstat,
        runS_execute_tstore_static pc_in top mem g hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega) hlim'
          (by rw [hst]; exact hstat)]
      exact StepResultRel.halted ErrorRel.writeInStaticContext
        (haltRegs_frame_status ss msg .WriteProtection)
    · have hstat0 : sRef.evm.message.isStatic = false := by simpa using hstat
      have hstat' : msg.is_static = false := by rw [hst]; exact hstat0
      by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_TSTORE
      · rw [runR_iTstore_oog sRef x v rest hS hstat0 hg,
          runS_execute_tstore_oog pc_in top mem g hs ss prof
            sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)
            hlim' hstat' (by rw [hlive]; exact hg)]
        exact StepResultRel.halted ErrorRel.outOfGas
          (haltRegs_frame_status ss msg .OutOfGas)
      · push Not at hg
        have hret2 : (cursorDrop top 2).toNat = rest.length := by
          rw [cursorDrop_toNat top 2 (by omega)]
          omega
        have hpfx2 : l.take rest.length = rest.reverse := by
          obtain ⟨hp1, ht1⟩ := cursor_pop_step l top x (v :: rest) hpfx htop
          obtain ⟨hp2, ht2⟩ := cursor_pop_step l _ v rest hp1 ht1
          rw [show rest.length = (cursorDrop top 2).toNat from hret2.symm]
          exact hp2
        rw [runR_iTstore_success sRef x v rest hS hstat0 hg,
          runS_execute_tstore_ok pc_in top mem g hs ss l frest x v rest
            hframe hpfx htop hlim' msg hmsg hstat'
            (by rw [hlive]; exact hg)]
        refine StepResultRel.success ⟨⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
          ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, by simp [hpc], rfl⟩, ?_⟩
        · exact ⟨⟨l, frest, hframe, by rw [hret2]; exact hpfx2, by
              rw [hret2]; omega⟩,
            by rw [hret2],
            hlimR,
            fun w hw => hwfS w (by simp [hw])⟩
        · refine ⟨?_, hres, hsp⟩
          show g - GasCosts.OPCODE_TSTORE
            = sRef.evm.gasLeft - GasCosts.OPCODE_TSTORE
          rw [hlive]
        · rw [← hax]
          exact transientRel_write sRef.txState hs msg.address x v hwfx hwfv
            htr

end EvmSpecsVerify
