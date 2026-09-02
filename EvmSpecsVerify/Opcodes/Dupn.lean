import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# DUPN

The first EIP-663 deep-stack opcode: like [`DUP`](Dup.lean) but with the
depth carried as a one-byte **immediate** rather than encoded in the
opcode. That makes it the first opcode with an *immediate-validity*
outcome, and it is where two order differences stack up.

## The immediate

SpecRef reads the byte itself (`buffer_read e.code (e.pc + 1) 1`) and
decodes with `decode_single`; the extraction receives the byte as the
`.DUPN immediate` constructor argument (decode happens upstream of
`execute`) and decodes with `decode_single_stack_index`. The decode-fidelity
hypothesis `himm` bridges the two exactly as PUSH's `hv` does (MM-3 scope).

The two decoders agree — [`decode_single_agree`](#decode_single_agree):
SpecRef's `(x + 145) % 256` over the valid range is the extraction's
two-branch `x + 145` / `x - 111`, because `x ≤ 90` keeps the sum below
`256` and `128 ≤ x ≤ 255` puts it exactly one modulus above. The validity
predicates coincide too, `x` being a byte.

## Two order differences (MM-5, MM-10)

* **MM-10 (new)**: SpecRef reports an invalid immediate as
  `.invalidParameter "DUPN/SWAPN immediate out of range"`, the extraction
  as `InvalidOpcode`. Paired by the new `ErrorRel.invalidParameter`.
* **MM-10, double fault**: SpecRef **charges before decoding**, the
  extraction **checks the immediate before charging**. A state that is
  both out of gas and carries an invalid immediate reports `outOfGas` on
  the SpecRef side and `InvalidOpcode` on the extraction's — the third
  admitted kind of `StepResultRel.haltedChargeFirst`.
* **MM-5** as for DUP: with a *valid* immediate, an out-of-gas state that
  is also stack-invalid reports `outOfGas` against the extraction's hoisted
  `validate_stack` fault.

Note the extraction's `opcode_stack_effect (.DUPN imm)` returns `(0, 0)`
for an invalid immediate, so `validate_stack` waves it through and
`execute_dupn`'s own check is what halts.

Reachable outcomes: success / invalid immediate / underflow / overflow /
OOG, plus the MM-5 and MM-10 double faults.

Gas (MM-2): `GasCosts.OPCODE_DUPN = 3 = G_verylow`.
-/

open private pcAdd from EvmAsm.Stateless.SpecRef.InstructionsCore
open private writeListAt from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## The immediate decoders agree -/

/-- The decoded 1-indexed depth, in the extraction's two-branch form. -/
def dupnIndex (b : BitVec 8) : Nat :=
  if b.toNat ≤ 90 then b.toNat + 145 else b.toNat - 111

/-- The extraction's `Nat`-ascribed `toNatInt` read of a byte is its
`toNat`. -/
theorem toNatInt_nat (b : BitVec 8) :
    ((Sail.BitVec.toNatInt b).toNat : Nat) = b.toNat := by
  simp [Sail.BitVec.toNatInt]

theorem deep_stack_immediate_valid_eq (b : BitVec 8) :
    Evm.Functions.deep_stack_immediate_valid b
      = (decide (b.toNat ≤ 90) || decide (128 ≤ b.toNat)) := by
  simp only [Evm.Functions.deep_stack_immediate_valid]
  rw [show ((Sail.BitVec.toNatInt b).toNat : Nat) = b.toNat from
    toNatInt_nat b]

/-- SpecRef's modular decode and the extraction's two-branch decode
coincide on every valid immediate. -/
theorem decode_single_agree (b : BitVec 8)
    (hv : Evm.Functions.deep_stack_immediate_valid b = true) :
    decode_single b.toNat = .ok (dupnIndex b) := by
  have hb : b.toNat < 256 := b.isLt
  rw [deep_stack_immediate_valid_eq] at hv
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hv
  simp only [decode_single, dupnIndex]
  rcases hv with h | h
  · rw [if_pos (by simp [h]), if_pos h]
    congr 1
    omega
  · rw [if_pos (by simp; omega), if_neg (by omega)]
    congr 1
    omega

/-- An invalid immediate is an `.invalidParameter` throw on the SpecRef
side (the message is the diagnostic MM-10 records). -/
theorem decode_single_invalid (b : BitVec 8)
    (hv : Evm.Functions.deep_stack_immediate_valid b = false) :
    decode_single b.toNat
      = .error (.invalidParameter "DUPN/SWAPN immediate out of range") := by
  have hb : b.toNat < 256 := b.isLt
  rw [deep_stack_immediate_valid_eq] at hv
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hv
  simp only [decode_single]
  rw [if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq,
    Bool.and_eq_true]; omega)]
  rfl

open Evm.Functions in
theorem runS_decode_single_stack_index (b : BitVec 8) (hs : Evm.HostState)
    (ss : SeqState)
    (hv : Evm.Functions.deep_stack_immediate_valid b = true) :
    runS (Evm.Functions.decode_single_stack_index b) hs ss =
      .ok (dupnIndex b, hs) ss := by
  have hb : b.toNat < 256 := b.isLt
  have hv' := hv
  rw [deep_stack_immediate_valid_eq] at hv'
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hv'
  simp only [Evm.Functions.decode_single_stack_index, hv]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  rw [show ((Sail.BitVec.toNatInt b).toNat : Nat) = b.toNat from
    toNatInt_nat b]
  simp only [dupnIndex]
  rcases hv' with h | h
  · rw [if_pos (by simpa using h), if_pos h]
    exact runS_pure _ _ _
  · rw [if_neg (by simp; omega), if_neg (by omega)]
    rw [show ((128 : Nat) ≤b b.toNat) = true from by simpa using h]
    refine runS_bind_ok (runS_pure _ _ _) ?_
    exact runS_pure _ _ _

/-! ## SpecRef run shapes (`b` is the immediate byte) -/

/-- The immediate byte SpecRef reads from its own code buffer. -/
def immByte (s : Machine) : Nat :=
  ((buffer_read s.evm.code (s.evm.pc + 1) 1).headD 0).toNat

theorem runR_iDupn_oog (s : Machine)
    (hgas : s.evm.gasLeft < GasCosts.OPCODE_DUPN) :
    runR iDupn s = .ok (.error .outOfGas, s) := by
  simp only [iDupn]
  exact runR_bind_err (runR_charge_gas_oog _ _ (by simpa using hgas))

/-- MM-10: the invalid-immediate throw fires **after** the charge. -/
theorem runR_iDupn_invalid (s : Machine) (why : String)
    (hdec : decode_single (immByte s) = .error (.invalidParameter why))
    (hgas : GasCosts.OPCODE_DUPN ≤ s.evm.gasLeft) :
    runR iDupn s =
      .ok (.error (.invalidParameter why),
        { s with evm := { s.evm with
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_DUPN
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_DUPN } }) := by
  simp only [immByte] at hdec
  simp only [iDupn]
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [hdec]
  exact runR_bind_err (runR_throw _ _)

theorem runR_iDupn_underflow (s : Machine) (n : Nat)
    (hdec : decode_single (immByte s) = .ok n)
    (hn : s.evm.stack.length < n)
    (hgas : GasCosts.OPCODE_DUPN ≤ s.evm.gasLeft) :
    runR iDupn s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_DUPN
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_DUPN } }) := by
  simp only [immByte] at hdec
  simp only [iDupn]
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [hdec]
  refine runR_bind_ok (runR_pure _ _) ?_
  rw [if_pos (by show n > s.evm.stack.length; omega)]
  exact runR_bind_err (runR_throw _ _)

theorem runR_iDupn_overflow (s : Machine) (n : Nat)
    (hdec : decode_single (immByte s) = .ok n)
    (hn : n ≤ s.evm.stack.length)
    (hlen : s.evm.stack.length = 1024)
    (hgas : GasCosts.OPCODE_DUPN ≤ s.evm.gasLeft) :
    runR iDupn s =
      .ok (.error .stackOverflow,
        { s with evm := { s.evm with
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_DUPN
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_DUPN } }) := by
  simp only [immByte] at hdec
  simp only [iDupn]
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [hdec]
  refine runR_bind_ok (runR_pure _ _) ?_
  rw [if_neg (by show ¬(n > s.evm.stack.length); omega)]
  refine runR_bind_ok (runR_pure _ _) ?_
  exact runR_bind_err (runR_stackPush_overflow _ _
    (by show s.evm.stack.length = 1024; exact hlen))

theorem runR_iDupn_success (s : Machine) (n : Nat)
    (hdec : decode_single (immByte s) = .ok n)
    (hn : n ≤ s.evm.stack.length)
    (hlen : s.evm.stack.length ≠ 1024)
    (hgas : GasCosts.OPCODE_DUPN ≤ s.evm.gasLeft) :
    runR iDupn s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := s.evm.stack.getD (n - 1) 0 :: s.evm.stack
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_DUPN
            regularGasUsed := s.evm.regularGasUsed + GasCosts.OPCODE_DUPN
            pc := s.evm.pc + 2 } }) := by
  simp only [immByte] at hdec
  simp only [iDupn, pcAdd]
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [hdec]
  refine runR_bind_ok (runR_pure _ _) ?_
  rw [if_neg (by show ¬(n > s.evm.stack.length); omega)]
  refine runR_bind_ok (runR_pure _ _) ?_
  refine runR_bind_ok (runR_stackPush _ _
    (by show s.evm.stack.length ≠ 1024; exact hlen)) ?_
  exact runR_modifyEvm _ _

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for DUPN. -/
theorem dupn_dispatch (b : BitVec 8) (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_opcode (.DUPN b) pc_in top mem g =
      Evm.Functions.execute_dupn b top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
/-- `opcode_stack_effect` decodes the immediate itself for a valid byte. -/
theorem runS_stack_effect_dupn_valid (b : BitVec 8) (hs : Evm.HostState)
    (ss : SeqState)
    (hv : Evm.Functions.deep_stack_immediate_valid b = true) :
    runS (Evm.Functions.opcode_stack_effect (.DUPN b)) hs ss =
      .ok ((dupnIndex b, dupnIndex b + 1), hs) ss := by
  simp only [Evm.Functions.opcode_stack_effect, hv]
  refine runS_bind_ok (runS_decode_single_stack_index b hs ss hv) ?_
  exact runS_pure _ _ _

open Evm.Functions in
/-- For an invalid immediate the effect is `(0, 0)`, so `validate_stack`
waves the step through and `execute_dupn`'s own check is what halts. -/
theorem runS_stack_effect_dupn_invalid (b : BitVec 8) (hs : Evm.HostState)
    (ss : SeqState)
    (hv : Evm.Functions.deep_stack_immediate_valid b = false) :
    runS (Evm.Functions.opcode_stack_effect (.DUPN b)) hs ss =
      .ok ((0, 0), hs) ss := by
  simp only [Evm.Functions.opcode_stack_effect, hv]
  exact runS_pure _ _ _

/-- The host state after DUPN's push (named so the run shapes carry no
multi-line structure-update literal). -/
def dupnHost (hs : Evm.HostState) (l : List word)
    (frest : List (List word)) (top : StackTop) (w : word) :
    Evm.HostState :=
  { hs with stackFrames := writeListAt l top.toNat w :: frest }

open Evm.Functions in
/-- MM-10: the immediate check runs **before** the charge, so the halt
carries the frame's full gas into `exc_halt`. -/
theorem runS_dupn_body_invalid (b : BitVec 8) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hv : Evm.Functions.deep_stack_immediate_valid b = false) :
    runS (Evm.Functions.execute_dupn b top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .InvalidOpcode } := by
  simp only [Evm.Functions.execute_dupn, hv]
  rw [if_pos (by simp)]
  refine runS_bind_ok
    (runS_exc_halt g .InvalidOpcode hs ss prof sp msg hprof hsp hmsg
      hfork) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_dupn_body_oog (b : BitVec 8) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hv : Evm.Functions.deep_stack_immediate_valid b = true)
    (hgas : g < G_verylow) :
    runS (Evm.Functions.execute_dupn b top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_dupn, hv]
  rw [if_neg (by simp)]
  refine runS_bind_ok
    (runS_charge_oog g G_verylow hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_dupn_body_ok (b : BitVec 8) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (S : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = S.reverse)
    (htop : top.toNat = S.length)
    (hv : Evm.Functions.deep_stack_immediate_valid b = true)
    (hi : dupnIndex b - 1 < S.length)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hgas : G_verylow ≤ g) :
    runS (Evm.Functions.execute_dupn b top g) hs ss =
      .ok ((top + BitVec.ofNat 64 1, g - G_verylow),
        dupnHost hs l frest top (S.getD (dupnIndex b - 1) default)) ss := by
  simp only [Evm.Functions.execute_dupn, hv]
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_charge_ok g G_verylow hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_decode_single_stack_index b hs ss hv) ?_
  refine runS_bind_ok
    (runS_peek top (dupnIndex b - 1) hs ss l frest S hframe hpfx htop
      hi) ?_
  refine runS_bind_ok
    (runS_push_word top _ hs ss l frest hframe hbound) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_dupn_invalid (b : BitVec 8) (pc_in : Nat)
    (top : StackTop) (g : Nat) (mem : EvmMemorySlice)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hlim : top.toNat ≤ 1024)
    (hv : Evm.Functions.deep_stack_immediate_valid b = false) :
    runS (Evm.Functions.execute (.DUPN b) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .InvalidOpcode } := by
  simp only [Evm.Functions.execute]
  refine runS_bind_ok (runS_stack_effect_dupn_invalid b hs ss hv) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 0 hs ss (by omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, dupn_dispatch]
  refine runS_bind_ok
    (runS_dupn_body_invalid b top g hs ss prof sp msg hprof hsp hmsg hfork
      hv) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_dupn_underflow (b : BitVec 8) (pc_in : Nat)
    (top : StackTop) (g : Nat) (mem : EvmMemorySlice)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hv : Evm.Functions.deep_stack_immediate_valid b = true)
    (hunder : top.toNat < dupnIndex b) :
    runS (Evm.Functions.execute (.DUPN b) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute]
  refine runS_bind_ok (runS_stack_effect_dupn_valid b hs ss hv) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top (dupnIndex b) (dupnIndex b + 1)
      hs ss prof sp msg hprof hsp hmsg hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_dupn_overflow (b : BitVec 8) (pc_in : Nat)
    (top : StackTop) (g : Nat) (mem : EvmMemorySlice)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hv : Evm.Functions.deep_stack_immediate_valid b = true)
    (hin : dupnIndex b ≤ top.toNat)
    (hover : 1024 < top.toNat + 1) :
    runS (Evm.Functions.execute (.DUPN b) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackOverflow } := by
  simp only [Evm.Functions.execute]
  refine runS_bind_ok (runS_stack_effect_dupn_valid b hs ss hv) ?_
  refine runS_bind_ok
    (runS_validate_stack_overflow g top (dupnIndex b) (dupnIndex b + 1)
      hs ss prof sp msg hprof hsp hmsg hfork hin
      (by have h : (1024 : Nat) < top.toNat - dupnIndex b + (dupnIndex b + 1)
            := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_dupn_oog (b : BitVec 8) (pc_in : Nat)
    (top : StackTop) (g : Nat) (mem : EvmMemorySlice)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hv : Evm.Functions.deep_stack_immediate_valid b = true)
    (hin : dupnIndex b ≤ top.toNat)
    (hlim : top.toNat + 1 ≤ 1024)
    (hgas : g < G_verylow) :
    runS (Evm.Functions.execute (.DUPN b) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute]
  refine runS_bind_ok (runS_stack_effect_dupn_valid b hs ss hv) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top (dupnIndex b) (dupnIndex b + 1) hs ss hin
      (by have h : top.toNat - dupnIndex b + (dupnIndex b + 1) ≤ 1024 := by
            omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, dupn_dispatch]
  refine runS_bind_ok
    (runS_dupn_body_oog b top g hs ss prof sp msg hprof hsp hmsg hfork hv
      hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_dupn_success (b : BitVec 8) (pc_in : Nat)
    (top : StackTop) (g : Nat) (mem : EvmMemorySlice)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (S : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = S.reverse)
    (htop : top.toNat = S.length)
    (hv : Evm.Functions.deep_stack_immediate_valid b = true)
    (hin : dupnIndex b ≤ top.toNat) (hn1 : 1 ≤ dupnIndex b)
    (hlim : top.toNat + 1 ≤ 1024)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hgas : G_verylow ≤ g) :
    runS (Evm.Functions.execute (.DUPN b) pc_in top mem g) hs ss =
      .ok ((pc_in, top + BitVec.ofNat 64 1, mem, g - G_verylow),
        dupnHost hs l frest top (S.getD (dupnIndex b - 1) default)) ss := by
  simp only [Evm.Functions.execute]
  refine runS_bind_ok (runS_stack_effect_dupn_valid b hs ss hv) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top (dupnIndex b) (dupnIndex b + 1) hs ss hin
      (by have h : top.toNat - dupnIndex b + (dupnIndex b + 1) ≤ 1024 := by
            omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, dupn_dispatch]
  refine runS_bind_ok
    (runS_dupn_body_ok b top g hs ss l frest S hframe hpfx htop hv
      (by omega) hbound hgas) ?_
  exact runS_pure _ _ _

/-! ## The step equivalence -/

/-- Every valid immediate decodes to a positive depth (`≥ 145` on the low
branch, `≥ 17` on the high one), so `n - 1` is a genuine index. -/
theorem dupnIndex_pos (b : BitVec 8)
    (hv : Evm.Functions.deep_stack_immediate_valid b = true) :
    1 ≤ dupnIndex b := by
  rw [deep_stack_immediate_valid_eq] at hv
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hv
  simp only [dupnIndex]
  rcases hv with h | h
  · rw [if_pos h]; omega
  · rw [if_neg (by omega)]; omega

open Evm.Functions in
/-- **DUPN, all reachable outcomes**: success / invalid immediate /
underflow / overflow / OOG, plus the MM-5 and MM-10 double faults.
`himm` is the decode-fidelity hypothesis (the constructor's immediate is
the byte SpecRef reads from its own code buffer, MM-3 scope) and `hpc`
the immediate-extended MM-4 pc convention. -/
theorem dupn_step_equiv (b : BitVec 8)
    (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 2)
    (himm : immByte sRef = b.toNat) :
    StepResultRel (BasePost mem) (runR iDupn sRef)
      (runS (Evm.Functions.execute (.DUPN b) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  by_cases hv : Evm.Functions.deep_stack_immediate_valid b = true
  · -- valid immediate: DUP's outcome set, with the decoded depth
    have hdec : decode_single (immByte sRef) = .ok (dupnIndex b) := by
      rw [himm]; exact decode_single_agree b hv
    have hn1 : 1 ≤ dupnIndex b := dupnIndex_pos b hv
    by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_DUPN
    · rw [runR_iDupn_oog sRef hg]
      by_cases hu : sRef.evm.stack.length < dupnIndex b
      · rw [runS_execute_dupn_underflow b pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hv (by omega)]
        exact StepResultRel.haltedChargeFirst (Or.inl rfl)
          (haltRegs_frame_status ss msg .StackUnderflow)
      · by_cases hov : sRef.evm.stack.length = 1024
        · rw [runS_execute_dupn_overflow b pc_in top g mem hs ss prof
            sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hv (by omega)
            (by omega)]
          exact StepResultRel.haltedChargeFirst (Or.inr (Or.inl rfl))
            (haltRegs_frame_status ss msg .StackOverflow)
        · rw [runS_execute_dupn_oog b pc_in top g mem hs ss prof
            sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hv (by omega)
            (by omega) (by rw [hlive]; exact hg)]
          exact StepResultRel.halted ErrorRel.outOfGas
            (haltRegs_frame_status ss msg .OutOfGas)
    · push Not at hg
      by_cases hu : sRef.evm.stack.length < dupnIndex b
      · rw [runR_iDupn_underflow sRef (dupnIndex b) hdec hu hg,
          runS_execute_dupn_underflow b pc_in top g mem hs ss prof
            sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hv
            (by omega)]
        exact StepResultRel.halted ErrorRel.stackUnderflow
          (haltRegs_frame_status ss msg .StackUnderflow)
      · by_cases hov : sRef.evm.stack.length = 1024
        · rw [runR_iDupn_overflow sRef (dupnIndex b) hdec (by omega) hov hg,
            runS_execute_dupn_overflow b pc_in top g mem hs ss prof
              sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hv
              (by omega) (by omega)]
          exact StepResultRel.halted ErrorRel.stackOverflow
            (haltRegs_frame_status ss msg .StackOverflow)
        · have hbound : top.toNat + 1 < 2 ^ 64 := by
            have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
            omega
          rw [runR_iDupn_success sRef (dupnIndex b) hdec (by omega) hov hg,
            runS_execute_dupn_success b pc_in top g mem hs ss l frest
              sRef.evm.stack hframe hpfx htop hv (by omega) hn1 (by omega)
              hbound (by rw [hlive]; exact hg)]
          have hadv : (top + BitVec.ofNat 64 1).toNat = top.toNat + 1 :=
            cursor_advance_toNat top hbound
          refine StepResultRel.success ?_
          refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
            ⟨msg, hmsg⟩⟩, by simp [hpc], rfl⟩
          · have hv0 : sRef.evm.stack.getD (dupnIndex b - 1) (default : word)
                = sRef.evm.stack.getD (dupnIndex b - 1) 0 := rfl
            refine ⟨⟨writeListAt l top.toNat
                (sRef.evm.stack.getD (dupnIndex b - 1) default), frest,
              rfl, ?_, ?_⟩, ?_, ?_, ?_⟩
            · rw [hadv, take_writeListAt l top.toNat _ (by omega), hpfx,
                hv0]
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
                have hget : sRef.evm.stack.getD (dupnIndex b - 1) 0
                    = sRef.evm.stack[dupnIndex b - 1]'(by omega) := by
                  show (sRef.evm.stack[dupnIndex b - 1]?).getD 0 = _
                  rw [List.getElem?_eq_getElem (by omega)]
                  rfl
                rw [hget]
                exact hwfS _ (List.getElem_mem _)
              · exact hwfS w hw
          · exact ⟨by
              simp [hlive, Evm.Functions.G_verylow, GasCosts.OPCODE_DUPN],
              hres, hsp⟩
  · -- invalid immediate (MM-10)
    have hv' : Evm.Functions.deep_stack_immediate_valid b = false := by
      simpa using hv
    have hdec : decode_single (immByte sRef)
        = .error (.invalidParameter
            "DUPN/SWAPN immediate out of range") := by
      rw [himm]; exact decode_single_invalid b hv'
    have hlim' : top.toNat ≤ 1024 := by omega
    by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_DUPN
    · rw [runR_iDupn_oog sRef hg,
        runS_execute_dupn_invalid b pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hlim' hv']
      exact StepResultRel.haltedChargeFirst (Or.inr (Or.inr (Or.inl rfl)))
        (haltRegs_frame_status ss msg .InvalidOpcode)
    · push Not at hg
      rw [runR_iDupn_invalid sRef _ hdec hg,
        runS_execute_dupn_invalid b pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hlim' hv']
      exact StepResultRel.halted (ErrorRel.invalidParameter _)
        (haltRegs_frame_status ss msg .InvalidOpcode)

end EvmSpecsVerify
