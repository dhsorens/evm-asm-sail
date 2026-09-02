import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# BLOBHASH

The 1-in/1-out transaction-envelope reader (EIP-4844): pop the index,
charge `3`, push the indexed versioned hash — or zero past the end.
Structurally the [`CALLDATALOAD`](Calldataload.lean) sibling, with the
same MM-1 order difference (SpecRef pops before charging, the extraction's
body charges before popping, both behind `validate_stack`, so the halt
kinds align case by case).

The two sides reach the hash by different routes: SpecRef indexes
`message.txEnv.blobVersionedHashes` with an out-of-range default of
32 zero bytes; the extraction's `k_blobhash` compares the index against
`k_tx`'s `blob_hashes.count` and loads 32 bytes from the stateless input
slice, returning `ZERO_WORD` past the end. Both therefore zero-pad rather
than fault, so the agreement needs no range hypothesis — only that the
two views of the envelope's hash list coincide
([`BlobHashAgree`](#BlobHashAgree)).

Reachable outcomes: success / stack underflow / OOG; overflow is
unreachable for 1-in/1-out.

Gas (MM-2): `GasCosts.OPCODE_BLOBHASH = 3 = G_verylow`.
-/

open private pcNext from EvmAsm.Stateless.SpecRef.InstructionsEnv
open private writeListAt from Evm.HostAxioms

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- The word SpecRef pushes for index `i`: the versioned hash, or the
32-zero-byte default past the end. Named so structure-update literals stay
single-line. -/
def blobWord (sRef : Machine) (i : Nat) : word :=
  bytesBEtoNat
    (sRef.evm.message.txEnv.blobVersionedHashes.getD i
      (List.replicate 32 0x00))

/-- The two views of the transaction's blob-hash list agree, at every
index, and the extraction's read leaves the operand stack alone. Quantified
over all indices — both sides zero-pad past the end, so no range
restriction enters. The `wf` clause is the envelope invariant that each
versioned hash is 32 bytes (the `hwfv` analogue). -/
structure BlobHashAgree (sRef : Machine) (hs : Evm.HostState)
    (ss : SeqState) : Prop where
  read : ∀ i : Nat, ∃ hostAfter : Evm.HostState,
    runS (Evm.Functions.k_blobhash i) hs ss
      = .ok (blobWord sRef i, hostAfter) ss ∧
    hostAfter.stackFrames = hs.stackFrames
  wf : ∀ i : Nat, WordWf (blobWord sRef i)

/-! ## SpecRef run shapes -/

theorem runR_iBlobhash_underflow (s : Machine) (hstack : s.evm.stack = []) :
    runR iBlobhash s = .ok (.error .stackUnderflow, s) := by
  simp only [iBlobhash]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_iBlobhash_oog (s : Machine) (x : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: rest)
    (hgas : s.evm.gasLeft < GasCosts.OPCODE_BLOBHASH) :
    runR iBlobhash s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [iBlobhash]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _ hgas)

theorem runR_iBlobhash_success (s : Machine) (x : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: rest)
    (hgas : GasCosts.OPCODE_BLOBHASH ≤ s.evm.gasLeft)
    (hlim : s.evm.stack.length ≤ 1024) :
    runR iBlobhash s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := blobWord s x :: rest
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_BLOBHASH
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_BLOBHASH
            pc := s.evm.pc + 1 } }) := by
  have hlen : rest.length ≠ 1024 := by
    rw [hstack] at hlim; simp at hlim; omega
  simp only [iBlobhash, pcNext]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_stackPush _ _ (by simpa using hlen)) ?_
  exact runR_modifyEvm _ _

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for BLOBHASH. -/
theorem blobhash_dispatch (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_opcode (.BLOBHASH ()) pc_in top mem g =
      Evm.Functions.execute_blobhash top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
theorem runS_blobhash_body_ok (top : StackTop) (g : Nat)
    (hs hs' : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (v : word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hval : runS (Evm.Functions.k_blobhash x) hs ss = .ok (v, hs') ss)
    (hframe' : hs'.stackFrames = l :: frest)
    (hgas : (GasCosts.OPCODE_BLOBHASH : Nat) ≤ g) :
    runS (Evm.Functions.execute_blobhash top g) hs ss =
      .ok ((top, g - GasCosts.OPCODE_BLOBHASH),
        { hs' with stackFrames :=
            writeListAt l (top.toNat - 1) v :: frest }) ss := by
  have hn : top.toNat = rest.length + 1 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  simp only [Evm.Functions.execute_blobhash]
  refine runS_bind_ok (runS_charge_ok g G_verylow hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_pop top hs ss l frest x rest hframe hpfx htop) ?_
  refine runS_bind_ok hval ?_
  refine runS_bind_ok
    (runS_push_word (top - BitVec.ofNat 64 1) v hs' ss l frest hframe'
      (by rw [hret1]; omega)) ?_
  rw [BitVec.sub_add_cancel, hret1]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_blobhash_body_oog (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < (GasCosts.OPCODE_BLOBHASH : Nat)) :
    runS (Evm.Functions.execute_blobhash top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_blobhash]
  refine runS_bind_ok
    (runS_charge_oog g G_verylow hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_blobhash_ok (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs hs' : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (v : word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hval : runS (Evm.Functions.k_blobhash x) hs ss = .ok (v, hs') ss)
    (hframe' : hs'.stackFrames = l :: frest)
    (hgas : (GasCosts.OPCODE_BLOBHASH : Nat) ≤ g) :
    runS (Evm.Functions.execute (.BLOBHASH ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, g - GasCosts.OPCODE_BLOBHASH),
        { hs' with stackFrames :=
            writeListAt l (top.toNat - 1) v :: frest }) ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.BLOBHASH ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 1 hs ss (by simp at htop; omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, blobhash_dispatch]
  refine runS_bind_ok
    (runS_blobhash_body_ok top g hs hs' ss l frest x rest v hframe hpfx htop
      hval hframe' hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_blobhash_oog (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (hpos : 1 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < (GasCosts.OPCODE_BLOBHASH : Nat)) :
    runS (Evm.Functions.execute (.BLOBHASH ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.BLOBHASH ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 1 hs ss (by omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, blobhash_dispatch]
  refine runS_bind_ok
    (runS_blobhash_body_oog top g hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_blobhash_underflow (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 1) :
    runS (Evm.Functions.execute (.BLOBHASH ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.BLOBHASH ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 1 1 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **BLOBHASH, all reachable outcomes**: success / stack underflow / OOG.
Overflow is unreachable for 1-in/1-out. Both sides zero-pad past the end
of the versioned-hash list, so the success case covers in-range and
out-of-range indices alike with no range hypothesis. -/
theorem blobhash_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (hbh : BlobHashAgree sRef hs ss) :
    StepResultRel (BasePost mem) (runR iBlobhash sRef)
      (runS (Evm.Functions.execute (.BLOBHASH ()) pc_in top mem g)
        hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_iBlobhash_underflow sRef hS,
      runS_execute_blobhash_underflow pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | x :: rest =>
    rw [hS] at hpfx htop hlim hwfS
    have hlim' : top.toNat ≤ 1024 := by simp at htop hlim; omega
    by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_BLOBHASH
    · rw [runR_iBlobhash_oog sRef x rest hS hg,
        runS_execute_blobhash_oog pc_in top g mem hs ss
          (by simp at htop; omega) hlim' prof sRef.evm.stateGasSpilled msg
          hprof hsp hmsg hfork (by rw [hlive]; exact hg)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
    · push Not at hg
      obtain ⟨hostAfter, hval, hstk⟩ := hbh.read x
      have hframe' : hostAfter.stackFrames = l :: frest := by
        rw [hstk]; exact hframe
      rw [runR_iBlobhash_success sRef x rest hS hg (by rw [hS]; exact hlim),
        runS_execute_blobhash_ok pc_in top g mem hs hostAfter ss l frest x
          rest (blobWord sRef x) hframe hpfx htop hlim' hval hframe'
          (by rw [hlive]; exact hg)]
      refine StepResultRel.success ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
        ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, hpc, rfl⟩
      · exact pop_push_post_stack top _ l frest x rest (blobWord sRef x)
          (hostState_set_stackFrames_frames _ _) hpfx htop hlim hlen hwfS
          (hbh.wf x)
      · exact ⟨by rw [hlive], hres, hsp⟩

end EvmSpecsVerify
