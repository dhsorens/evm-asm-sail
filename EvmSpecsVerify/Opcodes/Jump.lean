import EvmSpecsVerify.Opcodes.Jumpi

/-!
# JUMP

The unconditional branch, harvested from [`JUMPI`](Jumpi.lean): same
`do_jump` validation on the extraction side, same
[`JumpdestRel`](../Relations/Jumpdest.lean) bridge, same
[`ControlPost`](Jumpi.lean) success post. `iJump` pops the destination,
charges `OPCODE_JUMP`, throws `.invalidJumpDest` unless the destination is
in `validJumpDestinations`, and otherwise sets `pc := dest`. The
extraction's `execute_jump` charges `G_mid`, pops, and delegates to
`do_jump`.

Reachable outcomes: taken jump / underflow / OOG / invalid destination.
There is no fall-through branch (that is JUMPI's condition-zero case) and
no overflow for 1-in/0-out. SpecRef pops before charging, so all halt
kinds align kind-for-kind (mismatch ledger MM-1, not MM-5).

MM-4 note: on success both sides land on `dest` exactly, so `BasePost`'s
pc equation needs no `+1` adjustment; on the failure paths the pc is not
observable.

Gas (MM-2): `GasCosts.OPCODE_JUMP = 8 = G_mid`.
-/

open private assocGet from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## SpecRef run shapes -/

theorem runR_iJump_underflow (s : Machine) (hstack : s.evm.stack = []) :
    runR iJump s = .ok (.error .stackUnderflow, s) := by
  simp only [iJump]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_iJump_oog (s : Machine) (x : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: rest)
    (hgas : s.evm.gasLeft < GasCosts.OPCODE_JUMP) :
    runR iJump s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [iJump]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _ (by simpa using hgas))

theorem runR_iJump_jump (s : Machine) (x : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: rest)
    (hj : s.evm.validJumpDestinations.contains x = true)
    (hgas : GasCosts.OPCODE_JUMP ≤ s.evm.gasLeft) :
    runR iJump s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := rest
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_JUMP
            regularGasUsed := s.evm.regularGasUsed + GasCosts.OPCODE_JUMP
            pc := x } }) := by
  simp only [iJump]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_neg (by simpa using hj)]
  refine runR_bind_ok (runR_pure _ _) ?_
  exact runR_modifyEvm _ _

theorem runR_iJump_invalid (s : Machine) (x : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: rest)
    (hj : s.evm.validJumpDestinations.contains x = false)
    (hgas : GasCosts.OPCODE_JUMP ≤ s.evm.gasLeft) :
    runR iJump s =
      .ok (.error .invalidJumpDest,
        { s with evm := { s.evm with
            stack := rest
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_JUMP
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_JUMP } }) := by
  simp only [iJump]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_pos (by simpa using hj)]
  exact runR_bind_err (runR_throw _ _)

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for JUMP (returns its own pc). -/
theorem jump_dispatch (pc_in : Nat) (top : StackTop) (mem : EvmMemorySlice)
    (g : Nat) :
    Evm.Functions.execute_opcode (.JUMP ()) pc_in top mem g =
      Evm.Functions.execute_jump pc_in top g >>= fun p =>
        pure (p.1, p.2.1, mem, p.2.2) := rfl

open Evm.Functions in
theorem runS_jump_body_oog (pc_in : Nat) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < G_mid) :
    runS (Evm.Functions.execute_jump pc_in top g) hs ss =
      .ok ((pc_in, top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_jump]
  refine runS_bind_ok
    (runS_charge_oog g G_mid hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_jump_body_jump (pc_in : Nat) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (off len : Nat) (cf : CodeFields off len) (positions : List code_pointer)
    (hcode : ss.regs.get? Register.frame_code = some ⟨off, len, cf⟩)
    (hpos : assocGet hs.jumpdestTables cf.jumpdests = some positions)
    (hlt : x < len)
    (hmem : positions.contains x = true)
    (hgas : G_mid ≤ g) :
    runS (Evm.Functions.execute_jump pc_in top g) hs ss =
      .ok ((x, top - BitVec.ofNat 64 1, g - G_mid), hs) ss := by
  simp only [Evm.Functions.execute_jump]
  refine runS_bind_ok (runS_charge_ok g G_mid hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_pop top hs ss l frest x rest hframe hpfx htop) ?_
  refine runS_bind_ok
    (runS_do_jump_ok pc_in (g - G_mid) x off len cf positions hs ss hcode
      hpos hlt hmem) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_jump_body_invalid (pc_in : Nat) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (off len : Nat) (cf : CodeFields off len) (positions : List code_pointer)
    (hcode : ss.regs.get? Register.frame_code = some ⟨off, len, cf⟩)
    (hpos : assocGet hs.jumpdestTables cf.jumpdests = some positions)
    (hinv : (decide (x < len) && positions.contains x) = false)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : G_mid ≤ g) :
    runS (Evm.Functions.execute_jump pc_in top g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .InvalidJump } := by
  simp only [Evm.Functions.execute_jump]
  refine runS_bind_ok (runS_charge_ok g G_mid hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_pop top hs ss l frest x rest hframe hpfx htop) ?_
  refine runS_bind_ok
    (runS_do_jump_invalid pc_in (g - G_mid) x off len cf positions hs ss
      hcode hpos prof sp msg hprof hsp hmsg hfork hinv) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_jump_underflow (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 1) :
    runS (Evm.Functions.execute (.JUMP ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.JUMP ()) = pure (1, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 1 0 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_jump_oog (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hin : 1 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (hgas : g < G_mid) :
    runS (Evm.Functions.execute (.JUMP ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.JUMP ()) = pure (1, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 0 hs ss hin
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, jump_dispatch]
  refine runS_bind_ok
    (runS_jump_body_oog pc_in top g hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_jump_jump (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (off len : Nat) (cf : CodeFields off len) (positions : List code_pointer)
    (hcode : ss.regs.get? Register.frame_code = some ⟨off, len, cf⟩)
    (hpos : assocGet hs.jumpdestTables cf.jumpdests = some positions)
    (hlt : x < len)
    (hmem : positions.contains x = true)
    (hgas : G_mid ≤ g) :
    runS (Evm.Functions.execute (.JUMP ()) pc_in top mem g) hs ss =
      .ok ((x, top - BitVec.ofNat 64 1, mem, g - G_mid), hs) ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.JUMP ()) = pure (1, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 0 hs ss (by simp at htop; omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, jump_dispatch]
  refine runS_bind_ok
    (runS_jump_body_jump pc_in top g hs ss l frest x rest hframe hpfx htop
      off len cf positions hcode hpos hlt hmem hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_jump_invalid (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (off len : Nat) (cf : CodeFields off len) (positions : List code_pointer)
    (hcode : ss.regs.get? Register.frame_code = some ⟨off, len, cf⟩)
    (hpos : assocGet hs.jumpdestTables cf.jumpdests = some positions)
    (hinv : (decide (x < len) && positions.contains x) = false)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : G_mid ≤ g) :
    runS (Evm.Functions.execute (.JUMP ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .InvalidJump } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.JUMP ()) = pure (1, 0) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 0 hs ss (by simp at htop; omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, jump_dispatch]
  refine runS_bind_ok
    (runS_jump_body_invalid pc_in top g hs ss l frest x rest hframe hpfx htop
      off len cf positions hcode hpos hinv prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **JUMP, all reachable outcomes**: taken jump / underflow / OOG /
invalid destination. No fall-through (JUMPI's case) and no overflow for
1-in/0-out. -/
theorem jump_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hjd : JumpdestRel sRef hs ss) :
    StepResultRel (ControlPost mem) (runR iJump sRef)
      (runS (Evm.Functions.execute (.JUMP ()) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  obtain ⟨off, len, cf, positions, hcode, hpos, hiff⟩ := hjd.rel
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_iJump_underflow sRef hS,
      runS_execute_jump_underflow pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | x :: rest =>
    rw [hS] at hpfx htop hlim hwfS
    have hin1 : 1 ≤ top.toNat := by simp at htop; omega
    have hlim' : top.toNat ≤ 1024 := by simp at htop ⊢; simp at hlim; omega
    by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_JUMP
    · rw [runR_iJump_oog sRef x rest hS hg,
        runS_execute_jump_oog pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hin1 hlim'
          (by rw [hlive]; exact hg)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
    · push Not at hg
      by_cases hj : sRef.evm.validJumpDestinations.contains x = true
      · have hj' : (decide (x < len) && positions.contains x) = true := by
          rw [← hiff x]; exact hj
        rw [Bool.and_eq_true, decide_eq_true_eq] at hj'
        obtain ⟨hlt, hmemb⟩ := hj'
        rw [runR_iJump_jump sRef x rest hS hj hg,
          runS_execute_jump_jump pc_in top g mem hs ss l frest x rest hframe
            hpfx htop hlim' off len cf positions hcode hpos hlt hmemb
            (by rw [hlive]; exact hg)]
        have hret : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
          cursor_retreat_toNat top (by omega)
        refine StepResultRel.success ?_
        refine ⟨⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
          ⟨msg, hmsg⟩⟩, rfl, rfl⟩,
          ⟨off, len, cf, positions, hcode, hpos, hiff⟩⟩
        · refine ⟨⟨l, frest, hframe, ?_, ?_⟩, ?_, ?_, ?_⟩
          · rw [hret]
            exact take_shrink l rest x (top.toNat - 1)
              (by rw [show top.toNat - 1 + 1 = top.toNat from by
                simp at htop; omega]; exact hpfx)
              (by simp at htop; omega)
          · rw [hret]; omega
          · rw [hret]; simp at htop ⊢; omega
          · simp at hlim ⊢; omega
          · intro w hw
            exact hwfS w (by simp [hw])
        · exact ⟨by simp [hlive, Evm.Functions.G_mid, GasCosts.OPCODE_JUMP],
            hres, hsp⟩
      · have hj' : sRef.evm.validJumpDestinations.contains x = false := by
          simpa using hj
        have hinv : (decide (x < len) && positions.contains x) = false := by
          rw [← hiff x]; exact hj'
        rw [runR_iJump_invalid sRef x rest hS hj' hg,
          runS_execute_jump_invalid pc_in top g mem hs ss l frest x rest
            hframe hpfx htop hlim' off len cf positions hcode hpos hinv prof
            sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
            (by rw [hlive]; exact hg)]
        exact StepResultRel.halted ErrorRel.invalidJumpDest
          (haltRegs_frame_status ss msg .InvalidJump)

end EvmSpecsVerify
