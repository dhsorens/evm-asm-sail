import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Representation.AddressWord
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# BLOCKHASH

Pop the block number, charge `OPCODE_BLOCKHASH` (= 20, both sides), and
push the ancestor hash — zero outside the 256-deep window ending at the
parent. The sides index the witness differently: SpecRef holds
`blockEnv.blockHashes` oldest-first and reads `hashes[len − offset]`, the
extraction holds `ancestorHashes` parent-first and reads
`ancestorHashes[offset − 1]` — `AncestorRel` ties the two windows
(reversed indexing) together with the `k_n_headers` count. The value
codec is [`hash_to_word_eq`](../Representation/AddressWord.lean) (wf for
free, 32 bytes = the word width).

**A witness-deficient lookup aborts on both sides** — SpecRef raises the
spec-level `executionRejected` (an outer `.error`, not an EVM halt), the
extraction `fatal_error WitnessDeficient` — so the aligned rejection lies
outside the `StepResultRel` observation boundary. The theorem excludes it
with the lookup-specific hypothesis `hwit`: only an invocation that reaches
an in-window lookup must have that depth in the witness. This admits short
but sufficient witnesses and is ledgered in `Assumptions.lean`.
SpecRef also records the touched depth in the tracker
(`trackAncestorAccess`); the post-`txState` is outside `StateRel`, so the
success lemma carries it verbatim (`ancestorMark`). Operation order is
the CALLDATALOAD MM-1 layout (SpecRef pops before charging, the
extraction charges first behind `validate_stack`). Reachable outcomes:
success ×2 (in-window hash / out-of-window zero) / underflow / OOG.
-/

open private pcNext from EvmAsm.Stateless.SpecRef.InstructionsEnv
open private writeListAt from Evm.HostAxioms

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## The tracker mark and the witness relation -/

/-- `trackAncestorAccess`'s state update, named (the deepest touched
ancestor so far). -/
def ancestorMark (ts : TransactionState) (offset : Uint) :
    TransactionState :=
  { ts with parent :=
    { ts.parent with oldestAncestorOffset :=
        match ts.parent.oldestAncestorOffset with
        | none => some offset
        | some cur => some (max cur offset) } }

theorem trackAncestorAccess_run (ts : TransactionState) (offset : Uint) :
    (trackAncestorAccess offset).run ts = .ok ((), ancestorMark ts offset) :=
  rfl

/-- The extraction's ancestor-hash window represents SpecRef's
`blockEnv.blockHashes`: the `k_n_headers` register holds the witness
depth, and the parent-first store read at `d − 1` is the oldest-first
list read at `length − d`, for every in-witness depth `d`. A
`BlockEnvRel` fragment, established at frame entry (M3). -/
def AncestorRel (hashes : List Hash32) (hs : Evm.HostState)
    (ss : SeqState) : Prop :=
  ∃ nh : Nat, ss.regs.get? Register.k_n_headers = some nh ∧
    nh = hashes.length ∧
    ∀ d : Nat, 1 ≤ d → d ≤ hashes.length →
      (hs.ancestorHashes.getD (d - 1) default).toList
        = hashes.getD (hashes.length - d) (List.replicate 32 0x00)

/-- The current BLOCKHASH invocation cannot reach the witness-deficient
outer-abort path. Underflow, OOG, and out-of-window queries need no witness
coverage; an in-window query needs only its actual ancestor depth. -/
def BlockhashReady (s : Machine) : Prop :=
  ∀ x rest, s.evm.stack = x :: rest →
    GasCosts.OPCODE_BLOCKHASH ≤ s.evm.gasLeft →
    x < (s.evm.message.blockEnv.number : Nat) →
    (s.evm.message.blockEnv.number : Nat) ≤ x + 256 →
    (s.evm.message.blockEnv.number : Nat) - x
      ≤ s.evm.message.blockEnv.blockHashes.length

/-! ## SpecRef run shapes -/

theorem runR_iBlockhash_underflow (s : Machine)
    (hstack : s.evm.stack = []) :
    runR iBlockhash s = .ok (.error .stackUnderflow, s) := by
  simp only [iBlockhash]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_iBlockhash_oog (s : Machine) (x : Nat) (rest : List U256)
    (hstack : s.evm.stack = x :: rest)
    (hgas : s.evm.gasLeft < GasCosts.OPCODE_BLOCKHASH) :
    runR iBlockhash s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [iBlockhash]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _ hgas)

theorem runR_iBlockhash_zero (s : Machine) (x : Nat) (rest : List U256)
    (hstack : s.evm.stack = x :: rest)
    (hgas : GasCosts.OPCODE_BLOCKHASH ≤ s.evm.gasLeft)
    (hlim : s.evm.stack.length ≤ 1024)
    (hout : (s.evm.message.blockEnv.number : Nat) ≤ x
      ∨ x + 256 < (s.evm.message.blockEnv.number : Nat)) :
    runR iBlockhash s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := 0 :: rest
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_BLOCKHASH
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_BLOCKHASH
            pc := s.evm.pc + 1 } }) := by
  have hlen : rest.length ≠ 1024 := by
    rw [hstack] at hlim; simp at hlim; omega
  simp only [iBlockhash, pcNext]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_pos (by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact hout)]
  refine runR_bind_ok (runR_stackPush _ _ (by simpa using hlen)) ?_
  exact runR_modifyEvm _ _

/-- The pushed hash value (named so structure-update literals stay
single-line). -/
def bhWord (hashes : List Hash32) (offset : Nat) : U256 :=
  bytesBEtoNat (hashes.getD (hashes.length - offset) (List.replicate 32 0x00))

theorem runR_iBlockhash_hash (s : Machine) (x : Nat) (rest : List U256)
    (hstack : s.evm.stack = x :: rest)
    (hgas : GasCosts.OPCODE_BLOCKHASH ≤ s.evm.gasLeft)
    (hlim : s.evm.stack.length ≤ 1024)
    (hin : x < (s.evm.message.blockEnv.number : Nat))
    (hdist : (s.evm.message.blockEnv.number : Nat) ≤ x + 256)
    (hcov : (s.evm.message.blockEnv.number : Nat) - x
      ≤ s.evm.message.blockEnv.blockHashes.length) :
    runR iBlockhash s =
      .ok (.ok (),
        { s with
          evm := { s.evm with
            stack := bhWord s.evm.message.blockEnv.blockHashes
              (s.evm.message.blockEnv.number - x) :: rest
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_BLOCKHASH
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_BLOCKHASH
            pc := s.evm.pc + 1 }
          txState :=
            ancestorMark s.txState (s.evm.message.blockEnv.number - x) }) := by
  have hlen : rest.length ≠ 1024 := by
    rw [hstack] at hlim; simp at hlim; omega
  have keyNot : ∀ cur bnn : Nat, bnn < cur → cur ≤ bnn + 256 →
      ¬(cur ≤ bnn ∨ bnn + 256 < cur) := fun _ _ h1 h2 => by
    simp only [not_or]
    exact ⟨by omega, by omega⟩
  have hnot := keyNot _ _ hin hdist
  simp only [iBlockhash, pcNext]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  have keyNgt : ∀ a b c : Nat, a - b ≤ c → ¬(a - b > c) :=
    fun _ _ _ h => by omega
  have hngt := keyNgt _ _ _ hcov
  rw [if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact hnot)]
  rw [if_neg (by exact hngt)]
  refine runR_bind_ok (runR_pure _ _) ?_
  refine runR_bind_ok
    (runR_liftTx_ok _ _ _ _ (trackAncestorAccess_run s.txState _)) ?_
  refine runR_bind_ok (runR_stackPush _ _ (by simpa using hlen)) ?_
  exact runR_modifyEvm _ _

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for BLOCKHASH. -/
theorem blockhash_dispatch (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_opcode (.BLOCKHASH ()) pc_in top mem g =
      Evm.Functions.execute_blockhash top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
/-- `k_blockhash` outside the window: the zero hash. -/
theorem runS_k_blockhash_zero (bn : Nat) (hdr : BlockHeader)
    (hs : Evm.HostState) (ss : SeqState)
    (hhdr : ss.regs.get? Register.k_header = some hdr)
    (hout : (hdr.number : Nat) ≤ bn ∨ bn + 256 < (hdr.number : Nat)) :
    runS (Evm.Functions.k_blockhash bn) hs ss =
      .ok (Evm.Functions.ZERO_HASH, hs) ss := by
  simp only [Evm.Functions.k_blockhash, Evm.Functions.word_of_block_number,
    Evm.Functions.u256, Evm.Functions.blockhash_word_distance, runS_bind,
    runS_readReg _ _ _ _ hhdr, runS_pure]
  by_cases hlt : bn < (hdr.number : Nat)
  · have keyNd : ∀ a b : Nat, (a ≤ b ∨ b + 256 < a) → b < a →
        ¬(a - b ≤ 256) := fun _ _ h1 h2 => by
      rcases h1 with h | h <;> omega
    have hnd := keyNd _ _ hout hlt
    rw [if_pos (by simp only [decide_eq_true_eq]; exact hlt)]
    rw [if_neg (by simp only [decide_eq_true_eq]; exact hnd)]
    simp [runS_pure]
  · rw [if_neg (by simp only [decide_eq_true_eq]; exact hlt)]
    simp [runS_pure]

open Evm.Functions in
/-- `k_blockhash` in the window, witness sufficient: the parent-first
store read. -/
theorem runS_k_blockhash_hash (bn : Nat) (hdr : BlockHeader) (nh : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (hhdr : ss.regs.get? Register.k_header = some hdr)
    (hnh : ss.regs.get? Register.k_n_headers = some nh)
    (hin : bn < (hdr.number : Nat))
    (hdist : (hdr.number : Nat) - bn ≤ 256)
    (hcov : (hdr.number : Nat) - bn ≤ nh) :
    runS (Evm.Functions.k_blockhash bn) hs ss =
      .ok (hs.ancestorHashes.getD ((hdr.number : Nat) - bn - 1) default,
        hs) ss := by
  simp only [Evm.Functions.k_blockhash, Evm.Functions.word_of_block_number,
    Evm.Functions.u256, Evm.Functions.blockhash_word_distance, runS_bind,
    runS_readReg _ _ _ _ hhdr, runS_pure]
  rw [if_pos (by simp only [decide_eq_true_eq]; exact hin)]
  rw [if_pos (by simp only [decide_eq_true_eq]; exact hdist)]
  simp only [runS_bind, runS_readReg _ _ _ _ hnh]
  have keyNcov : ∀ a b c : Nat, a - b ≤ c → ¬(c < a - b) :=
    fun _ _ _ h => by omega
  have hncov := keyNcov _ _ _ hcov
  rw [if_neg (by simp only [decide_eq_true_eq]; exact hncov)]
  simp only [Evm.Functions.ancestor_hash_read, runS_bind, runS_get,
    runS_pure]

open Evm.Functions in
theorem runS_blockhash_body_ok (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : Nat) (rest : List word)
    (v : Evm.Defs.hash)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hval : runS (Evm.Functions.k_blockhash x) hs ss = .ok (v, hs) ss)
    (hgas : (GasCosts.OPCODE_BLOCKHASH : Nat) ≤ g) :
    runS (Evm.Functions.execute_blockhash top g) hs ss =
      .ok ((top, g - GasCosts.OPCODE_BLOCKHASH),
        { hs with stackFrames :=
            writeListAt l (top.toNat - 1) (hash_to_word v) :: frest })
        ss := by
  have hn : top.toNat = rest.length + 1 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  simp only [Evm.Functions.execute_blockhash]
  refine runS_bind_ok (runS_charge_ok g 20 hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_pop top hs ss l frest x rest hframe hpfx htop) ?_
  refine runS_bind_ok hval ?_
  refine runS_bind_ok
    (runS_push_word (top - BitVec.ofNat 64 1) (hash_to_word v) hs ss l frest
      hframe (by rw [hret1]; omega)) ?_
  rw [BitVec.sub_add_cancel, hret1]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_blockhash_body_oog (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < (GasCosts.OPCODE_BLOCKHASH : Nat)) :
    runS (Evm.Functions.execute_blockhash top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_blockhash]
  refine runS_bind_ok
    (runS_charge_oog g 20 hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_blockhash_ok (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : Nat) (rest : List word)
    (v : Evm.Defs.hash)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (hval : runS (Evm.Functions.k_blockhash x) hs ss = .ok (v, hs) ss)
    (hgas : (GasCosts.OPCODE_BLOCKHASH : Nat) ≤ g) :
    runS (Evm.Functions.execute (.BLOCKHASH ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, g - GasCosts.OPCODE_BLOCKHASH),
        { hs with stackFrames :=
            writeListAt l (top.toNat - 1) (hash_to_word v) :: frest })
        ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.BLOCKHASH ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 1 hs ss (by simp at htop; omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, blockhash_dispatch]
  refine runS_bind_ok
    (runS_blockhash_body_ok top g hs ss l frest x rest v hframe hpfx htop
      hval hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_blockhash_oog (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (hpos : 1 ≤ top.toNat)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < (GasCosts.OPCODE_BLOCKHASH : Nat)) :
    runS (Evm.Functions.execute (.BLOCKHASH ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.BLOCKHASH ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 1 hs ss (by omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, blockhash_dispatch]
  refine runS_bind_ok
    (runS_blockhash_body_oog top g hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_blockhash_underflow (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 1) :
    runS (Evm.Functions.execute (.BLOCKHASH ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.BLOCKHASH ()) = pure (1, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 1 1 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **BLOCKHASH, all reachable outcomes** (success splits on the 256-deep
window). `hhdr`/`hnum` tie the header number, `hanc` the ancestor-hash
witness (reversed indexing + count), and `hwit` excludes only an actual
witness-deficient lookup, whose aligned outer abort is beyond
`StepResultRel` — see `Assumptions.lean`. -/
theorem blockhash_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat) (hdr : BlockHeader)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (hhdr : ss.regs.get? Register.k_header = some hdr)
    (hnum : (hdr.number : Nat) = sRef.evm.message.blockEnv.number)
    (hanc : AncestorRel sRef.evm.message.blockEnv.blockHashes hs ss)
    (hwit : BlockhashReady sRef) :
    StepResultRel (BasePost mem) (runR iBlockhash sRef)
      (runS (Evm.Functions.execute (.BLOCKHASH ()) pc_in top mem g)
        hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  obtain ⟨nh, hnh, hnhlen, hbytes⟩ := hanc
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_iBlockhash_underflow sRef hS,
      runS_execute_blockhash_underflow pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | x :: rest =>
    rw [hS] at hpfx htop hlim hwfS
    have hlim' : top.toNat ≤ 1024 := by simp at htop hlim ⊢; omega
    by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_BLOCKHASH
    · rw [runR_iBlockhash_oog sRef x rest hS hg,
        runS_execute_blockhash_oog pc_in top g mem hs ss
          (by simp at htop; omega) hlim' prof sRef.evm.stateGasSpilled msg
          hprof hsp hmsg hfork (by rw [hlive]; exact hg)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
    · push Not at hg
      by_cases hout : (sRef.evm.message.blockEnv.number : Nat) ≤ x
          ∨ x + 256 < (sRef.evm.message.blockEnv.number : Nat)
      · -- out of window: both push zero
        rw [runR_iBlockhash_zero sRef x rest hS hg (by rw [hS]; exact hlim)
            hout,
          runS_execute_blockhash_ok pc_in top g mem hs ss l frest x rest
            Evm.Functions.ZERO_HASH hframe hpfx htop hlim'
            (runS_k_blockhash_zero x hdr hs ss hhdr
              (by rw [hnum]; exact hout))
            (by rw [hlive]; exact hg),
          hash_to_word_zero]
        refine StepResultRel.success ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
          ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, hpc, rfl⟩
        · exact pop_push_post_stack top _ l frest x rest 0
            (hostState_set_stackFrames_frames _ _) hpfx htop hlim hlen hwfS
            (by unfold WordWf; omega)
        · exact ⟨by rw [hlive], hres, hsp⟩
      · push Not at hout
        obtain ⟨hin, hdist⟩ := hout
        have hcov := hwit x rest hS hg hin hdist
        have keyPair : ∀ cur bnn len : Nat, bnn < cur → cur ≤ bnn + 256 →
            cur - bnn ≤ len →
            1 ≤ cur - bnn ∧ cur - bnn ≤ len ∧ cur - bnn ≤ 256 :=
          fun _ _ _ h1 h2 h3 => by omega
        have hpair := keyPair _ _ _ hin hdist hcov
        have hvaleq : (hs.ancestorHashes.getD
              ((hdr.number : Nat) - x - 1) default).toList
            = sRef.evm.message.blockEnv.blockHashes.getD
                (sRef.evm.message.blockEnv.blockHashes.length
                  - (sRef.evm.message.blockEnv.number - x))
                (List.replicate 32 0x00) := by
          rw [hnum]
          exact hbytes (sRef.evm.message.blockEnv.number - x)
            hpair.1 hpair.2.1
        rw [runR_iBlockhash_hash sRef x rest hS hg (by rw [hS]; exact hlim)
            hin hdist hpair.2.1,
          runS_execute_blockhash_ok pc_in top g mem hs ss l frest x rest
            _ hframe hpfx htop hlim'
            (runS_k_blockhash_hash x hdr nh hs ss hhdr hnh
              (by rw [hnum]; exact hin) (by rw [hnum]; exact hpair.2.2)
              (by rw [hnum, hnhlen]; exact hpair.2.1))
            (by rw [hlive]; exact hg)]
        have hval : hash_to_word (hs.ancestorHashes.getD
              ((hdr.number : Nat) - x - 1) default)
            = bhWord sRef.evm.message.blockEnv.blockHashes
                (sRef.evm.message.blockEnv.number - x) := by
          rw [hash_to_word_eq, hvaleq, bhWord]
        rw [hval]
        refine StepResultRel.success ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
          ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, hpc, rfl⟩
        · exact pop_push_post_stack top _ l frest x rest _
            (hostState_set_stackFrames_frames _ _) hpfx htop hlim hlen hwfS
            (by rw [← hval]; exact hash_to_word_wf _)
        · exact ⟨by rw [hlive], hres, hsp⟩

end EvmSpecsVerify
