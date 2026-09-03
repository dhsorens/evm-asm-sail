import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# BLOBBASEFEE

The blob base fee, and the only opcode whose two implementations run a
**loop**. SpecRef's `taylor_exponential` (a fuelled recursion,
`taylorAux`) and the extraction's `fake_exponential_word` (a
`whileFuelM` loop over the triple `(accumulator, output, term_index)`)
compute the same recurrence

    out += acc;  acc := acc * numerator / (denominator * i);  i += 1

from `acc = factor * denominator` with `BLOB_MIN_GASPRICE = 1`,
terminating at `acc = 0` and dividing by the denominator at the end.
Amsterdam selects the bpo2 schedule on both sides, so the denominator is
`11684671` either way.

## The regime, and MM-15

The two sides' *guards* do not agree. `fake_exponential_word` carries
`scaled_limit = denominator * 2^256` and `fatal_error
NumericOverflow`s once the accumulator or the running sum reaches it;
SpecRef has no such guard and pushes whatever it computes, unreduced.
Mismatch ledger **MM-15** records that this band —
`excess_blob_gas ∈ [2 073 394 371, 2 992 193 280]` for Amsterdam — lies
*inside* what the extraction's own `excess_blob_gas_limit` admits, and is
reachable in principle.

So the step theorem carries `hword : price < 2 ^ 256`: the agreement
regime, stated in the observable term (the blob base fee fits a word).
Under it neither guard can fire, and the argument needs nothing about the
exponential: the running sum bounds the accumulator (it is one of the
summands), the iteration count (each iteration adds at least one), and
therefore the term index too. `scripts/blob-fee-band.py` computes where
the regime ends.

`hspec` is the other side of the same coin: SpecRef aborts with a
`SpecError` if its fuel runs out, which is an outer abort outside
`StepResultRel`'s boundary, so the theorem is stated on runs where it
does not.

Reachable outcomes: success / stack overflow / OOG / MM-5 double fault;
underflow is impossible for 0-in.

Gas (MM-2): `GasCosts.OPCODE_BLOBBASEFEE = 2 = G_base`.
-/

open private pcNext from EvmAsm.Stateless.SpecRef.InstructionsEnv
open private taylorAux from EvmAsm.Stateless.SpecRef.Gas
open private writeListAt from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## The shared recurrence -/


theorem taylorAux_le (num den : Nat) :
    ∀ (f i acc out final : Nat),
      taylorAux num den f i acc out = .ok final → out + acc ≤ final := by
  intro f
  induction f with
  | zero =>
    intro i acc out final h
    match acc with
    | 0 =>
      have : out = final := by
        have h' : (Except.ok out : Except SpecError Nat) = Except.ok final := by
          simpa only [taylorAux] using h
        exact Except.ok.inj h'
      omega
    | k + 1 => simp [taylorAux] at h
  | succ f ih =>
    intro i acc out final h
    match acc with
    | 0 =>
      have : out = final := by
        have h' : (Except.ok out : Except SpecError Nat) = Except.ok final := by
          simpa only [taylorAux] using h
        exact Except.ok.inj h'
      omega
    | k + 1 =>
      simp only [taylorAux] at h
      have hstep := ih (i + 1) ((k + 1) * num / (den * i)) (out + (k + 1)) final h
      have hnn : 0 ≤ (k + 1) * num / (den * i) := Nat.zero_le _
      omega


theorem runS_blob_loop (num den : Nat)
    (cond : (Nat × Nat × Nat) → Evm.SailM Bool)
    (body : (Nat × Nat × Nat) → Evm.SailM (Nat × Nat × Nat))
    (hcond : ∀ (x : Nat × Nat × Nat) (hs : Evm.HostState) (ss : SeqState),
      runS (cond x) hs ss = .ok (decide (0 < x.1), hs) ss)
    (hbody : ∀ (acc out i : Nat) (hs : Evm.HostState) (ss : SeqState),
      out + acc < den * 2 ^ 256 → i < den * 2 ^ 256 →
      runS (body (acc, out, i)) hs ss
        = .ok ((acc * num / (den * i), out + acc, i + 1), hs) ss) :
    ∀ (f i acc out final ef : Nat) (hs : Evm.HostState) (ss : SeqState),
      taylorAux num den f i acc out = .ok final →
      final < den * 2 ^ 256 →
      i ≤ out + 1 →
      final < out + ef →
      ∃ j, runS (whileFuelM.go cond body (acc, out, i) ef) hs ss
        = .ok ((0, final, j), hs) ss := by
  have hstop : ∀ (out i ef : Nat) (hs : Evm.HostState) (ss : SeqState),
      runS (whileFuelM.go cond body (0, out, i) ef) hs ss
        = .ok ((0, out, i), hs) ss := by
    intro out i ef hs ss
    match ef with
    | 0 => exact runS_pure _ _ _
    | e + 1 =>
      refine runS_bind_ok (hcond (0, out, i) hs ss) ?_
      rw [if_neg (by simp)]
      exact runS_pure _ _ _
  intro f
  induction f with
  | zero =>
    intro i acc out final ef hs ss hspec hfin hi hef
    match acc with
    | 0 =>
      have hout : out = final := by
        have h' : (Except.ok out : Except SpecError Nat) = Except.ok final := by
          simpa only [taylorAux] using hspec
        exact Except.ok.inj h'
      subst hout
      exact ⟨i, hstop out i ef hs ss⟩
    | k + 1 => simp [taylorAux] at hspec
  | succ f ih =>
    intro i acc out final ef hs ss hspec hfin hi hef
    match acc with
    | 0 =>
      have hout : out = final := by
        have h' : (Except.ok out : Except SpecError Nat) = Except.ok final := by
          simpa only [taylorAux] using hspec
        exact Except.ok.inj h'
      subst hout
      exact ⟨i, hstop out i ef hs ss⟩
    | k + 1 =>
      simp only [taylorAux] at hspec
      have hle := taylorAux_le num den (f + 1) i (k + 1) out final (by
        simp only [taylorAux]; exact hspec)
      match ef with
      | 0 => omega
      | e + 1 =>
        obtain ⟨j, hj⟩ := ih (i + 1) ((k + 1) * num / (den * i))
          (out + (k + 1)) final e hs ss hspec hfin (by omega) (by omega)
        refine ⟨j, ?_⟩
        refine runS_bind_ok (hcond (k + 1, out, i) hs ss) ?_
        rw [if_pos (by simp)]
        refine runS_bind_ok (hbody (k + 1) out i hs ss (by omega) (by omega)) ?_
        exact hj


/-- The loop, followed by any function of its running sum: the final
`term_index` is not observed, so this form has no existential. -/
theorem runS_blob_loop_price (num den : Nat)
    (cond : (Nat × Nat × Nat) → Evm.SailM Bool)
    (body : (Nat × Nat × Nat) → Evm.SailM (Nat × Nat × Nat))
    (hcond : ∀ (x : Nat × Nat × Nat) (hs : Evm.HostState) (ss : SeqState),
      runS (cond x) hs ss = .ok (decide (0 < x.1), hs) ss)
    (hbody : ∀ (acc out i : Nat) (hs : Evm.HostState) (ss : SeqState),
      out + acc < den * 2 ^ 256 → i < den * 2 ^ 256 →
      runS (body (acc, out, i)) hs ss
        = .ok ((acc * num / (den * i), out + acc, i + 1), hs) ss)
    (f i acc out final ef : Nat) (hs : Evm.HostState) (ss : SeqState)
    (hspec : taylorAux num den f i acc out = .ok final)
    (hfin : final < den * 2 ^ 256)
    (hi : i ≤ out + 1)
    (hef : final < out + ef) :
    runS (do
        let d ← (do
          let lv ← whileFuelM.go cond body (acc, out, i) ef
          pure lv)
        pure (Evm.Functions.protocol_word (d.2.1 / den))) hs ss
      = .ok (Evm.Functions.protocol_word (final / den), hs) ss := by
  obtain ⟨j, hj⟩ := runS_blob_loop num den cond body hcond hbody f i acc out
    final ef hs ss hspec hfin hi hef
  exact runS_bind_ok (runS_bind_ok hj (runS_pure _ _ _)) (runS_pure _ _ _)


theorem runS_assert_true (msg : String) (hs : Evm.HostState) (ss : SeqState) :
    runS (Evm.assert true msg) hs ss = .ok ((), hs) ss := by
  simp only [Evm.assert, PreSail.assert, if_pos]
  rfl

theorem runS_fake_exponential_word {kt km den : Nat}
    (sched : BlobScheduleFields kt km den) (num f final : Nat)
    (hs : Evm.HostState) (ss : SeqState) (hden : 0 < den)
    (hspec : taylorAux num den f 1 den 0 = .ok final)
    (hfin : final < den * 2 ^ 256) :
    runS (Evm.Functions.fake_exponential_word sched num) hs ss
      = .ok (final / den, hs) ss := by
  have hscaled : ((den : Int) * 2 ^ 256).toNat = den * 2 ^ 256 := by
    have hc : ((den : Int) * 2 ^ 256) = ((den * 2 ^ 256 : Nat) : Int) := by
      push_cast
      ring
    rw [hc, Int.toNat_natCast]
  unfold Evm.Functions.fake_exponential_word
  simp only [whileFuelM]
  refine Eq.trans (runS_blob_loop_price num den _ _ ?hc ?hb f 1 den 0 final
    (((den : Int) * 2 ^ 256).toNat - 0) hs ss hspec hfin (by omega)
    (by rw [hscaled]; omega)) ?price
  case hc =>
    intro x hs' ss'
    exact runS_pure _ _ _
  case hb =>
    intro acc out i hs' ss' hout hi
    have hdiv : ((acc : Int) * (num : Int)).toNat / ((den : Int) * (i : Int)).toNat
        = acc * num / (den * i) := by
      rw [show ((acc : Int) * (num : Int)) = ((acc * num : Nat) : Int) from by
          push_cast; ring,
        show ((den : Int) * (i : Int)) = ((den * i : Nat) : Int) from by
          push_cast; ring,
        Int.toNat_natCast, Int.toNat_natCast]
    refine runS_bind_ok (runS_assert_true _ hs' ss') ?_
    rw [if_neg (by simp only [decide_eq_true_eq]; omega),
      if_neg (by simp only [decide_eq_true_eq]; omega),
      if_pos (by simp only [decide_eq_true_eq]; omega),
      ← hdiv]
    exact runS_bind_ok
      (runS_bind_ok (runS_bind_ok (runS_pure _ _ _) (runS_pure _ _ _))
        (runS_pure _ _ _)) (runS_pure _ _ _)
  case price =>
    rfl

/-- The extraction's own precondition on `blob_base_fee`: the fork has
blobs, and the header's excess is inside the profile's ceiling. MM-15 is
about states that satisfy this and still overflow. -/
def BlobConfigOk {kf kt km kd kc ki kt1 kr1 kb krd : Nat}
    (pp : ProtocolProfileFields kf kt km kd kc ki kt1 kr1 kb krd)
    (excess : Nat) : Prop :=
  Evm.Functions.Cancun ≤ kf ∧ excess ≤ (pp.excess_blob_gas_limit).toNat

theorem runS_blob_base_fee {kf kt km kd kc ki kt1 kr1 kb krd : Nat}
    (pp : ProtocolProfileFields kf kt km kd kc ki kt1 kr1 kb krd)
    (excess f final : Nat) (hs : Evm.HostState) (ss : SeqState)
    (hden : 0 < kd)
    (hcfg : BlobConfigOk pp excess)
    (hspec : taylorAux excess kd f 1 kd 0 = .ok final)
    (hfin : final < kd * 2 ^ 256) :
    runS (Evm.Functions.blob_base_fee
        ⟨kf, kt, km, kd, kc, ki, kt1, kr1, kb, krd, pp⟩ excess) hs ss
      = .ok (final / kd, hs) ss := by
  obtain ⟨hfork, hlim⟩ := hcfg
  simp only [Evm.Functions.blob_base_fee]
  rw [if_pos (by
    simp only [Bool.and_eq_true, decide_eq_true_eq,
      ProtocolProfileFields.fork]
    exact ⟨hfork, hlim⟩)]
  exact runS_fake_exponential_word pp.blob_schedule excess f final hs ss hden
    hspec hfin

/-! ## SpecRef: the price computation -/

/-- The fuel `taylor_exponential` gives the recursion (Gas.lean:126). -/
def blobFuel (excess : Nat) : Nat :=
  4 * (excess / GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION)
    + Nat.log2
        (GasCosts.BLOB_MIN_GASPRICE * GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION
          + 2)
    + 8

/-- A successful `calculate_blob_gas_price` is a terminating run of the
shared recurrence, divided by the denominator. SpecRef's other outcome —
`SpecError` on fuel exhaustion — is an outer abort, outside
`StepResultRel`'s boundary. -/
theorem calculate_blob_gas_price_ok (excess price : Nat)
    (h : calculate_blob_gas_price excess = .ok price) :
    ∃ final,
      taylorAux excess GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION
          (blobFuel excess) 1
          (GasCosts.BLOB_MIN_GASPRICE
            * GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION) 0
        = .ok final
      ∧ price = final / GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION := by
  rw [calculate_blob_gas_price, taylor_exponential] at h
  match hx : taylorAux excess GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION
      (blobFuel excess) 1
      (GasCosts.BLOB_MIN_GASPRICE * GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION)
      0 with
  | .ok final =>
    refine ⟨final, rfl, ?_⟩
    rw [blobFuel] at hx
    rw [hx] at h
    exact (Except.ok.inj h).symm
  | .error e =>
    rw [blobFuel] at hx
    rw [hx] at h
    simp at h

/-! ## SpecRef run shapes -/

theorem runR_iBlobbasefee_success (s : Machine) (price : U256)
    (hprice : calculate_blob_gas_price s.evm.message.blockEnv.excessBlobGas
      = .ok price)
    (hgas : GasCosts.OPCODE_BLOBBASEFEE ≤ s.evm.gasLeft)
    (hlen : s.evm.stack.length ≠ 1024) :
    runR iBlobbasefee s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := price :: s.evm.stack
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_BLOBBASEFEE
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_BLOBBASEFEE
            pc := s.evm.pc + 1 } }) := by
  simp only [iBlobbasefee, pcNext]
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_liftSpec_ok _ _ price hprice) ?_
  refine runR_bind_ok (runR_stackPush _ _ (by simpa using hlen)) ?_
  exact runR_modifyEvm _ _

theorem runR_iBlobbasefee_overflow (s : Machine) (price : U256)
    (hprice : calculate_blob_gas_price s.evm.message.blockEnv.excessBlobGas
      = .ok price)
    (hgas : GasCosts.OPCODE_BLOBBASEFEE ≤ s.evm.gasLeft)
    (hlen : s.evm.stack.length = 1024) :
    runR iBlobbasefee s =
      .ok (.error .stackOverflow,
        { s with evm := { s.evm with
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_BLOBBASEFEE
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_BLOBBASEFEE } }) := by
  simp only [iBlobbasefee]
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_liftSpec_ok _ _ price hprice) ?_
  exact runR_bind_err (runR_stackPush_overflow _ _
    (by show s.evm.stack.length = 1024; exact hlen))

/-- OOG fires at the leading charge, before the price is computed
(MM-5). -/
theorem runR_iBlobbasefee_oog (s : Machine)
    (hgas : s.evm.gasLeft < GasCosts.OPCODE_BLOBBASEFEE) :
    runR iBlobbasefee s = .ok (.error .outOfGas, s) := by
  simp only [iBlobbasefee]
  exact runR_bind_err (runR_charge_gas_oog _ _ hgas)

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for BLOBBASEFEE. -/
theorem blobbasefee_dispatch (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_opcode (.BLOBBASEFEE ()) pc_in top mem g =
      Evm.Functions.execute_blobbasefee top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
theorem runS_blobbasefee_body_ok (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Nat)
    (pf : ExecutionProfileFields a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12)
    (hdr : BlockHeader) (v : Nat)
    (l : List word) (frest : List (List word))
    (hprof : ss.regs.get? Register.k_execution_profile
      = some ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, pf⟩)
    (hhdr : ss.regs.get? Register.k_header = some hdr)
    (hval : runS (Evm.Functions.blob_base_fee
        ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, pf.protocol⟩
        hdr.excess_blob_gas) hs ss = .ok (v, hs) ss)
    (hframe : hs.stackFrames = l :: frest)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hgas : (G_base : Nat) ≤ g) :
    runS (Evm.Functions.execute_blobbasefee top g) hs ss =
      .ok ((top + BitVec.ofNat 64 1, g - G_base),
        { hs with stackFrames :=
            writeListAt l top.toNat v :: frest }) ss := by
  simp only [Evm.Functions.execute_blobbasefee]
  refine runS_bind_ok (runS_charge_ok g G_base hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_readReg _ _ hs ss hprof) ?_
  refine runS_bind_ok (runS_readReg _ _ hs ss hhdr) ?_
  refine runS_bind_ok hval ?_
  refine runS_bind_ok (runS_push_word top v hs ss l frest hframe hbound) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_blobbasefee_body_oog (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < (G_base : Nat)) :
    runS (Evm.Functions.execute_blobbasefee top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_blobbasefee]
  refine runS_bind_ok
    (runS_charge_oog g G_base hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_blobbasefee_success (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Nat)
    (pf : ExecutionProfileFields a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12)
    (hdr : BlockHeader) (v : Nat)
    (l : List word) (frest : List (List word))
    (hprof : ss.regs.get? Register.k_execution_profile
      = some ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, pf⟩)
    (hhdr : ss.regs.get? Register.k_header = some hdr)
    (hval : runS (Evm.Functions.blob_base_fee
        ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, pf.protocol⟩
        hdr.excess_blob_gas) hs ss = .ok (v, hs) ss)
    (hframe : hs.stackFrames = l :: frest)
    (hlim : top.toNat + 1 ≤ 1024)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hgas : (G_base : Nat) ≤ g) :
    runS (Evm.Functions.execute (.BLOBBASEFEE ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top + BitVec.ofNat 64 1, mem, g - G_base),
        { hs with stackFrames :=
            writeListAt l top.toNat v :: frest }) ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.BLOBBASEFEE ()) = pure (0, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 1 hs ss (by omega)
      (by have h : top.toNat - 0 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, blobbasefee_dispatch]
  refine runS_bind_ok
    (runS_blobbasefee_body_ok top g hs ss a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
      a11 a12 pf hdr v l frest hprof hhdr hval hframe hbound hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_blobbasefee_overflow (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hover : 1024 < top.toNat + 1) :
    runS (Evm.Functions.execute (.BLOBBASEFEE ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackOverflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.BLOBBASEFEE ()) = pure (0, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_overflow g top 0 1 hs ss prof sp msg hprof hsp hmsg
      hfork (by omega)
      (by simpa [Evm.Functions.STACK_LIMIT] using hover)) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_blobbasefee_oog (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hlim : top.toNat + 1 ≤ 1024)
    (hgas : g < (G_base : Nat)) :
    runS (Evm.Functions.execute (.BLOBBASEFEE ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.BLOBBASEFEE ()) = pure (0, 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 1 hs ss (by omega)
      (by have h : top.toNat - 0 + 1 ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, blobbasefee_dispatch]
  refine runS_bind_ok
    (runS_blobbasefee_body_oog top g hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **BLOBBASEFEE, all reachable outcomes** in the agreement regime:
success / stack overflow / OOG / the MM-5 double fault. Underflow is
impossible for 0-in.

`hden` ties the profile's blob-schedule denominator index — the Sail type
system fixes it per fork, the Lean extraction erases it — and `hcfg` is
the extraction's own `blob_base_fee` precondition. `hprice` says SpecRef's
recursion terminates within its fuel (its other outcome is a `SpecError`,
an outer abort), and `hword` is the MM-15 regime: the price fits a word,
which is exactly where the extraction's overflow guards stay silent. -/
theorem blobbasefee_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Nat)
    (pf : ExecutionProfileFields a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12)
    (hdr : BlockHeader) (price : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (hprof : ss.regs.get? Register.k_execution_profile
      = some ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, pf⟩)
    (hhdr : ss.regs.get? Register.k_header = some hdr)
    (hden : a3 = GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION)
    (hcfg : BlobConfigOk pf.protocol hdr.excess_blob_gas)
    (hexcess : hdr.excess_blob_gas
      = sRef.evm.message.blockEnv.excessBlobGas)
    (hprice : calculate_blob_gas_price sRef.evm.message.blockEnv.excessBlobGas
      = .ok price)
    (hword : price < 2 ^ 256) :
    StepResultRel (BasePost mem) (runR iBlobbasefee sRef)
      (runS (Evm.Functions.execute (.BLOBBASEFEE ()) pc_in top mem g)
        hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof', hprof', hfork'⟩,
    ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  have hprofeq : prof'
      = ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, pf⟩ := by
    rw [hprof'] at hprof
    exact Option.some.inj hprof
  subst hprofeq
  have hgb : (G_base : Nat) = GasCosts.OPCODE_BLOBBASEFEE := rfl
  obtain ⟨final, hfinal, hpf⟩ :=
    calculate_blob_gas_price_ok _ price hprice
  have hpos : 0 < GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION := by
    simp [GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION]
  have hden0 : 0 < a3 := by rw [hden]; exact hpos
  have hfinlt : final < a3 * 2 ^ 256 := by
    rw [hden]
    have hd : final / GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION < 2 ^ 256 := by
      rw [← hpf]; exact hword
    have hlt := (Nat.div_lt_iff_lt_mul hpos).mp hd
    rw [Nat.mul_comm]
    exact hlt
  have hspec : taylorAux hdr.excess_blob_gas a3 (blobFuel hdr.excess_blob_gas)
      1 a3 0 = .ok final := by
    rw [hexcess, hden]
    exact hfinal
  have hval : runS (Evm.Functions.blob_base_fee
      ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, pf.protocol⟩
      hdr.excess_blob_gas) hs ss = .ok (price, hs) ss := by
    rw [show price = final / a3 from by rw [hden]; exact hpf]
    exact runS_blob_base_fee pf.protocol hdr.excess_blob_gas
      (blobFuel hdr.excess_blob_gas) final hs ss hden0 hcfg hspec hfinlt
  by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_BLOBBASEFEE
  · rw [runR_iBlobbasefee_oog sRef hg]
    by_cases hov : sRef.evm.stack.length = 1024
    · rw [runS_execute_blobbasefee_overflow pc_in top g mem hs ss _
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork' (by omega)]
      exact StepResultRel.haltedChargeFirst (Or.inr (Or.inl rfl))
        (haltRegs_frame_status ss msg .StackOverflow)
    · rw [runS_execute_blobbasefee_oog pc_in top g mem hs ss _
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork' (by omega)
        (by rw [hgb, hlive]; exact hg)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
  · push Not at hg
    by_cases hov : sRef.evm.stack.length = 1024
    · rw [runR_iBlobbasefee_overflow sRef price hprice hg hov,
        runS_execute_blobbasefee_overflow pc_in top g mem hs ss _
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork' (by omega)]
      exact StepResultRel.halted ErrorRel.stackOverflow
        (haltRegs_frame_status ss msg .StackOverflow)
    · have hbound : top.toNat + 1 < 2 ^ 64 := by
        have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
        omega
      rw [runR_iBlobbasefee_success sRef price hprice hg hov,
        runS_execute_blobbasefee_success pc_in top g mem hs ss a0 a1 a2 a3 a4
          a5 a6 a7 a8 a9 a10 a11 a12 pf hdr price l frest hprof hhdr hval
          hframe (by omega) hbound (by rw [hgb, hlive]; exact hg)]
      have hadv : (top + BitVec.ofNat 64 1).toNat = top.toNat + 1 :=
        cursor_advance_toNat top hbound
      refine StepResultRel.success ?_
      refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
        ⟨_, hprof, hfork'⟩, ⟨msg, hmsg⟩⟩, by simp [hpc], rfl⟩
      · refine ⟨⟨writeListAt l top.toNat price, frest, rfl, ?_, ?_⟩,
          ?_, ?_, ?_⟩
        · rw [hadv, take_writeListAt l top.toNat _ (by omega), hpfx]
          simp
        · rw [hadv, length_writeListAt]
          omega
        · rw [hadv]
          simp
          omega
        · simp
          omega
        · intro w hw
          rcases List.mem_cons.mp hw with hw | hw
          · subst hw
            exact hword
          · exact hwfS w hw
      · exact ⟨by rw [hlive, hgb], hres, hsp⟩

end EvmSpecsVerify
