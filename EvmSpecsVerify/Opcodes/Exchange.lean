import EvmSpecsVerify.Opcodes.Swapn

/-!
# EXCHANGE

The last of the three deep-stack opcodes (EIP-663 in SpecRef's
docstrings, EIP-8024 in the Sail model's), and the one that
needs real decoder work: where [`DUPN`](Dupn.lean)/[`SWAPN`](Swapn.lean)
share `decode_single`, EXCHANGE uses `decode_pair`, which packs *two*
stack indices into one byte.

## The pair decoder

Both sides compute `k = imm ^^^ 143`, split it into nibbles, and branch:
`(q + 1, r + 1)` when `q < r`, else `(r + 1, 29 - q)`. They differ only in
how the nibbles are taken — SpecRef divides and mods a `Nat` by 16, the
extraction slices bits `[7:4]` and `[3:0]` off the `BitVec 8` — so the
bridge is two byte-exhaustive `decide`s (`extractLsb_hi`/`_lo`) plus the
xor's `toNat` (`xor_143_toNat`). Everything else is `rfl`-level.

`exchangePair` names the common result. For every valid immediate it
satisfies `1 ≤ n < m ≤ 29` (`exchangePair_lt`, `exchangePair_pos`,
byte-exhaustive), which is what makes the two sides' *underflow*
predicates agree: SpecRef guards on `max n m + 1`, the extraction's
`opcode_stack_effect` on `higher + 1` where `higher` is the decoder's
second component. Those coincide exactly because the second component is
the larger — not by construction, so it is proven.

## The permutation

`execute_exchange` writes at two arbitrary stack indices rather than
SWAP's `(0, n)`, which is what motivated generalizing
[`take_swap_writes_gen`](Swap.lean) / `listSwap_getElem?_gen` /
`listSwap_mem_gen` from `(0, n)` to `(i, j)`; SWAP and SWAPN now go
through the `(0, n)` instance of the same lemmas.

## Mismatches

MM-10 recurs unchanged (invalid immediates: SpecRef
`.invalidParameter "EXCHANGE immediate in forbidden range"` — a different
message, same constructor — against the extraction's `InvalidOpcode`;
and SpecRef charges before decoding while the extraction validates
first), as does MM-5 on the valid-immediate double fault.

Overflow is unreachable: `opcode_stack_effect (.EXCHANGE imm)` is
`(higher + 1, higher + 1)`, height-preserving.

Reachable outcomes: success / invalid immediate / underflow / OOG, plus
the MM-5 and MM-10 double faults.

Gas (MM-2): `GasCosts.OPCODE_EXCHANGE = 3 = G_verylow`.
-/

open private pcAdd listSwap from EvmAsm.Stateless.SpecRef.InstructionsCore
open private writeListAt from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## The pair decoders agree -/

/-- The decoded index pair, in the shape both sides compute. -/
def exchangePair (b : BitVec 8) : Nat × Nat :=
  let k := b.toNat ^^^ 143
  if k / 16 < k % 16 then (k / 16 + 1, k % 16 + 1)
  else (k % 16 + 1, 29 - k / 16)

theorem xor_143_toNat : ∀ b : BitVec 8,
    ((b ^^^ 143#8).toNat) = b.toNat ^^^ 143 := by decide

/-- The extraction's high-nibble slice is SpecRef's `k / 16`. -/
theorem extractLsb_hi : ∀ s : BitVec 8,
    ((Sail.BitVec.toNatInt (Sail.BitVec.extractLsb s 7 4)).toNat)
      = s.toNat / 16 := by decide

/-- The extraction's low-nibble slice is SpecRef's `k % 16`. -/
theorem extractLsb_lo : ∀ s : BitVec 8,
    ((Sail.BitVec.toNatInt (Sail.BitVec.extractLsb s 3 0)).toNat)
      = s.toNat % 16 := by decide

theorem exchange_immediate_valid_eq (b : BitVec 8) :
    Evm.Functions.exchange_immediate_valid b
      = (decide (b.toNat ≤ 81) || decide (128 ≤ b.toNat)) := by
  simp only [Evm.Functions.exchange_immediate_valid]
  rw [show ((Sail.BitVec.toNatInt b).toNat : Nat) = b.toNat from
    toNatInt_nat b]

/-- Both components are genuine 1-indexed depths. -/
theorem exchangePair_pos : ∀ b : BitVec 8, 1 ≤ (exchangePair b).1 := by
  decide

/-- The decoder's second component is the larger one — so SpecRef's
`max n m` guard and the extraction's `higher` guard coincide. Byte
exhaustive over the *valid* immediates only: `q = r = 15` would give
`n = m`, but its immediate lies in the forbidden `82 … 127` band. -/
theorem exchangePair_lt : ∀ b : BitVec 8,
    Evm.Functions.exchange_immediate_valid b = true →
      (exchangePair b).1 < (exchangePair b).2 := by decide

/-- Every valid immediate stays inside the frame's 1024-slot window. -/
theorem exchangePair_le_29 : ∀ b : BitVec 8,
    Evm.Functions.exchange_immediate_valid b = true →
      (exchangePair b).2 ≤ 29 := by decide

theorem decode_pair_agree (b : BitVec 8)
    (hv : Evm.Functions.exchange_immediate_valid b = true) :
    decode_pair b.toNat = .ok (exchangePair b) := by
  rw [exchange_immediate_valid_eq] at hv
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hv
  have hb : b.toNat ≤ 255 := by
    have := b.isLt
    omega
  simp only [decode_pair, exchangePair]
  rw [if_pos (by rcases hv with h | h
                 · simp [h]
                 · simp [h, hb])]
  by_cases hqr : (b.toNat ^^^ 143) / 16 < (b.toNat ^^^ 143) % 16
  · rw [if_pos hqr, if_pos hqr]
    rfl
  · rw [if_neg hqr, if_neg hqr]
    rfl

theorem decode_pair_invalid (b : BitVec 8)
    (hv : Evm.Functions.exchange_immediate_valid b = false) :
    decode_pair b.toNat
      = .error (.invalidParameter "EXCHANGE immediate in forbidden range") := by
  rw [exchange_immediate_valid_eq] at hv
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hv
  simp only [decode_pair]
  rw [if_neg (by simp; omega)]
  rfl

open Evm.Functions in
theorem runS_decode_exchange_stack_indices (b : BitVec 8)
    (hs : Evm.HostState) (ss : SeqState)
    (hv : Evm.Functions.exchange_immediate_valid b = true) :
    runS (Evm.Functions.decode_exchange_stack_indices b) hs ss =
      .ok (exchangePair b, hs) ss := by
  simp only [Evm.Functions.decode_exchange_stack_indices, hv]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  rw [extractLsb_hi, extractLsb_lo, xor_143_toNat]
  simp only [exchangePair]
  by_cases hqr : (b.toNat ^^^ 143) / 16 < (b.toNat ^^^ 143) % 16
  · rw [if_pos (by simpa using hqr), if_pos hqr]
    exact runS_pure _ _ _
  · rw [if_neg (by simpa using hqr), if_neg hqr]
    exact runS_pure _ _ _

/-! ## SpecRef run shapes (`b` is the immediate byte) -/

theorem runR_iExchange_oog (s : Machine)
    (hgas : s.evm.gasLeft < GasCosts.OPCODE_EXCHANGE) :
    runR iExchange s = .ok (.error .outOfGas, s) := by
  simp only [iExchange]
  exact runR_bind_err (runR_charge_gas_oog _ _ (by simpa using hgas))

/-- MM-10: the invalid-immediate throw fires **after** the charge. -/
theorem runR_iExchange_invalid (s : Machine) (why : String)
    (hdec : decode_pair (immByte s) = .error (.invalidParameter why))
    (hgas : GasCosts.OPCODE_EXCHANGE ≤ s.evm.gasLeft) :
    runR iExchange s =
      .ok (.error (.invalidParameter why),
        { s with evm := { s.evm with
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_EXCHANGE
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_EXCHANGE } }) := by
  simp only [immByte] at hdec
  simp only [iExchange]
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [hdec]
  exact runR_bind_err (runR_throw _ _)

theorem runR_iExchange_underflow (s : Machine) (n m : Nat)
    (hdec : decode_pair (immByte s) = .ok (n, m))
    (hnm : n < m)
    (hn : s.evm.stack.length < m + 1)
    (hgas : GasCosts.OPCODE_EXCHANGE ≤ s.evm.gasLeft) :
    runR iExchange s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_EXCHANGE
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_EXCHANGE } }) := by
  simp only [immByte] at hdec
  simp only [iExchange]
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [hdec]
  refine runR_bind_ok (runR_pure _ _) ?_
  rw [if_pos (by show max n m + 1 > s.evm.stack.length
                 rw [Nat.max_eq_right (by omega)]; omega)]
  exact runR_bind_err (runR_throw _ _)

theorem runR_iExchange_success (s : Machine) (n m : Nat)
    (hdec : decode_pair (immByte s) = .ok (n, m))
    (hnm : n < m)
    (hn : m + 1 ≤ s.evm.stack.length)
    (hgas : GasCosts.OPCODE_EXCHANGE ≤ s.evm.gasLeft) :
    runR iExchange s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := listSwap s.evm.stack n m
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_EXCHANGE
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_EXCHANGE
            pc := s.evm.pc + 2 } }) := by
  simp only [immByte] at hdec
  simp only [iExchange, pcAdd]
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [hdec]
  refine runR_bind_ok (runR_pure _ _) ?_
  rw [if_neg (by show ¬(max n m + 1 > s.evm.stack.length)
                 rw [Nat.max_eq_right (by omega)]; omega)]
  refine runR_bind_ok (runR_pure _ _) ?_
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  exact runR_modifyEvm _ _

/-! ## `Evm` run shapes -/

open Evm.Functions in
theorem exchange_dispatch (b : BitVec 8) (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_opcode (.EXCHANGE b) pc_in top mem g =
      Evm.Functions.execute_exchange b top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
/-- The effect is keyed on the *higher* index, and height-preserving. -/
theorem runS_stack_effect_exchange_valid (b : BitVec 8) (hs : Evm.HostState)
    (ss : SeqState)
    (hv : Evm.Functions.exchange_immediate_valid b = true) :
    runS (Evm.Functions.opcode_stack_effect (.EXCHANGE b)) hs ss =
      .ok (((exchangePair b).2 + 1, (exchangePair b).2 + 1), hs) ss := by
  simp only [Evm.Functions.opcode_stack_effect, hv]
  refine runS_bind_ok (runS_decode_exchange_stack_indices b hs ss hv) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_stack_effect_exchange_invalid (b : BitVec 8)
    (hs : Evm.HostState) (ss : SeqState)
    (hv : Evm.Functions.exchange_immediate_valid b = false) :
    runS (Evm.Functions.opcode_stack_effect (.EXCHANGE b)) hs ss =
      .ok ((0, 0), hs) ss := by
  simp only [Evm.Functions.opcode_stack_effect, hv]
  exact runS_pure _ _ _

open Evm.Functions in
/-- MM-10: the immediate check runs **before** the charge. -/
theorem runS_exchange_body_invalid (b : BitVec 8) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hv : Evm.Functions.exchange_immediate_valid b = false) :
    runS (Evm.Functions.execute_exchange b top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .InvalidOpcode } := by
  simp only [Evm.Functions.execute_exchange, hv]
  rw [if_pos (by simp)]
  refine runS_bind_ok
    (runS_exc_halt g .InvalidOpcode hs ss prof sp msg hprof hsp hmsg
      hfork) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_exchange_body_oog (b : BitVec 8) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hv : Evm.Functions.exchange_immediate_valid b = true)
    (hgas : g < G_verylow) :
    runS (Evm.Functions.execute_exchange b top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_exchange, hv]
  rw [if_neg (by simp)]
  refine runS_bind_ok
    (runS_charge_oog g G_verylow hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_exchange_body_ok (b : BitVec 8) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (S : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = S.reverse)
    (htop : top.toNat = S.length)
    (hv : Evm.Functions.exchange_immediate_valid b = true)
    (hmt : (exchangePair b).2 < S.length)
    (hlen : top.toNat ≤ l.length)
    (hgas : G_verylow ≤ g) :
    runS (Evm.Functions.execute_exchange b top g) hs ss =
      .ok ((top, g - G_verylow),
        swapHostAt hs l frest top.toNat (exchangePair b).1 (exchangePair b).2
          (S.getD (exchangePair b).2 default)
          (S.getD (exchangePair b).1 default)) ss := by
  have hlt : (exchangePair b).1 < (exchangePair b).2 := exchangePair_lt b hv
  have hset1 : writeListAt l (top.toNat - 1 - (exchangePair b).1)
        (S.getD (exchangePair b).2 default)
      = l.set (top.toNat - 1 - (exchangePair b).1)
          (S.getD (exchangePair b).2 default) :=
    writeListAt_eq_set l _ _ (by omega)
  have hset2 : writeListAt
        (l.set (top.toNat - 1 - (exchangePair b).1)
          (S.getD (exchangePair b).2 default))
        (top.toNat - 1 - (exchangePair b).2)
        (S.getD (exchangePair b).1 default)
      = (l.set (top.toNat - 1 - (exchangePair b).1)
            (S.getD (exchangePair b).2 default)).set
          (top.toNat - 1 - (exchangePair b).2)
          (S.getD (exchangePair b).1 default) :=
    writeListAt_eq_set _ _ _ (by simp; omega)
  simp only [Evm.Functions.execute_exchange, hv]
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_charge_ok g G_verylow hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_decode_exchange_stack_indices b hs ss hv) ?_
  refine runS_bind_ok
    (runS_peek top (exchangePair b).1 hs ss l frest S hframe hpfx htop
      (by omega)) ?_
  refine runS_bind_ok
    (runS_peek top (exchangePair b).2 hs ss l frest S hframe hpfx htop
      hmt) ?_
  refine runS_bind_ok
    (runS_stack_set top (exchangePair b).1
      (S.getD (exchangePair b).2 default) hs ss l frest hframe) ?_
  refine runS_bind_ok
    (runS_stack_set top (exchangePair b).2
      (S.getD (exchangePair b).1 default) _ ss
      (writeListAt l (top.toNat - 1 - (exchangePair b).1)
        (S.getD (exchangePair b).2 default)) frest rfl) ?_
  rw [hset1, hset2]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_exchange_invalid (b : BitVec 8) (pc_in : Nat)
    (top : StackTop) (g : Nat) (mem : EvmMemorySlice)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hlim : top.toNat ≤ 1024)
    (hv : Evm.Functions.exchange_immediate_valid b = false) :
    runS (Evm.Functions.execute (.EXCHANGE b) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .InvalidOpcode } := by
  simp only [Evm.Functions.execute]
  refine runS_bind_ok (runS_stack_effect_exchange_invalid b hs ss hv) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 0 0 hs ss (by omega)
      (by simpa [Evm.Functions.STACK_LIMIT] using hlim)) ?_
  rw [dif_pos rfl, exchange_dispatch]
  refine runS_bind_ok
    (runS_exchange_body_invalid b top g hs ss prof sp msg hprof hsp hmsg
      hfork hv) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_exchange_underflow (b : BitVec 8) (pc_in : Nat)
    (top : StackTop) (g : Nat) (mem : EvmMemorySlice)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hv : Evm.Functions.exchange_immediate_valid b = true)
    (hunder : top.toNat < (exchangePair b).2 + 1) :
    runS (Evm.Functions.execute (.EXCHANGE b) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute]
  refine runS_bind_ok (runS_stack_effect_exchange_valid b hs ss hv) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top ((exchangePair b).2 + 1)
      ((exchangePair b).2 + 1) hs ss prof sp msg hprof hsp hmsg hfork
      hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_exchange_oog (b : BitVec 8) (pc_in : Nat)
    (top : StackTop) (g : Nat) (mem : EvmMemorySlice)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hv : Evm.Functions.exchange_immediate_valid b = true)
    (hin : (exchangePair b).2 + 1 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (hgas : g < G_verylow) :
    runS (Evm.Functions.execute (.EXCHANGE b) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute]
  refine runS_bind_ok (runS_stack_effect_exchange_valid b hs ss hv) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top ((exchangePair b).2 + 1)
      ((exchangePair b).2 + 1) hs ss hin
      (by have h : top.toNat - ((exchangePair b).2 + 1)
              + ((exchangePair b).2 + 1) ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, exchange_dispatch]
  refine runS_bind_ok
    (runS_exchange_body_oog b top g hs ss prof sp msg hprof hsp hmsg hfork
      hv hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_exchange_success (b : BitVec 8) (pc_in : Nat)
    (top : StackTop) (g : Nat) (mem : EvmMemorySlice)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (S : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = S.reverse)
    (htop : top.toNat = S.length)
    (hv : Evm.Functions.exchange_immediate_valid b = true)
    (hmt : (exchangePair b).2 < S.length)
    (hlen : top.toNat ≤ l.length)
    (hlim : top.toNat ≤ 1024)
    (hgas : G_verylow ≤ g) :
    runS (Evm.Functions.execute (.EXCHANGE b) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, g - G_verylow),
        swapHostAt hs l frest top.toNat (exchangePair b).1 (exchangePair b).2
          (S.getD (exchangePair b).2 default)
          (S.getD (exchangePair b).1 default)) ss := by
  simp only [Evm.Functions.execute]
  refine runS_bind_ok (runS_stack_effect_exchange_valid b hs ss hv) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top ((exchangePair b).2 + 1)
      ((exchangePair b).2 + 1) hs ss (by omega)
      (by have h : top.toNat - ((exchangePair b).2 + 1)
              + ((exchangePair b).2 + 1) ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, exchange_dispatch]
  refine runS_bind_ok
    (runS_exchange_body_ok b top g hs ss l frest S hframe hpfx htop hv hmt
      hlen hgas) ?_
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **EXCHANGE, all reachable outcomes**: success / invalid immediate /
underflow / OOG, plus the MM-5 and MM-10 double faults. Overflow is
unreachable (height-preserving). `himm` and `hpc` are DUPN's hypotheses
unchanged. -/
theorem exchange_step_equiv (b : BitVec 8)
    (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 2)
    (himm : immByte sRef = b.toNat) :
    StepResultRel (BasePost mem) (runR iExchange sRef)
      (runS (Evm.Functions.execute (.EXCHANGE b) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  by_cases hv : Evm.Functions.exchange_immediate_valid b = true
  · have hdec : decode_pair (immByte sRef) = .ok (exchangePair b) := by
      rw [himm]; exact decode_pair_agree b hv
    have hlt : (exchangePair b).1 < (exchangePair b).2 := exchangePair_lt b hv
    have hpos : 1 ≤ (exchangePair b).1 := exchangePair_pos b
    have hdec' : decode_pair (immByte sRef)
        = .ok ((exchangePair b).1, (exchangePair b).2) := hdec
    by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_EXCHANGE
    · rw [runR_iExchange_oog sRef hg]
      by_cases hu : sRef.evm.stack.length < (exchangePair b).2 + 1
      · rw [runS_execute_exchange_underflow b pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hv (by omega)]
        exact StepResultRel.haltedChargeFirst (Or.inl rfl)
          (haltRegs_frame_status ss msg .StackUnderflow)
      · rw [runS_execute_exchange_oog b pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hv (by omega)
          (by omega) (by rw [hlive]; exact hg)]
        exact StepResultRel.halted ErrorRel.outOfGas
          (haltRegs_frame_status ss msg .OutOfGas)
    · push Not at hg
      by_cases hu : sRef.evm.stack.length < (exchangePair b).2 + 1
      · rw [runR_iExchange_underflow sRef _ _ hdec' hlt hu hg,
          runS_execute_exchange_underflow b pc_in top g mem hs ss prof
            sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hv
            (by omega)]
        exact StepResultRel.halted ErrorRel.stackUnderflow
          (haltRegs_frame_status ss msg .StackUnderflow)
      · rw [runR_iExchange_success sRef _ _ hdec' hlt (by omega) hg,
          runS_execute_exchange_success b pc_in top g mem hs ss l frest
            sRef.evm.stack hframe hpfx htop hv (by omega) hlen (by omega)
            (by rw [hlive]; exact hg)]
        refine StepResultRel.success ?_
        refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
          ⟨msg, hmsg⟩⟩, by simp [hpc], rfl⟩
        · refine ⟨⟨(l.set (top.toNat - 1 - (exchangePair b).1)
                (sRef.evm.stack.getD (exchangePair b).2 default)).set
                (top.toNat - 1 - (exchangePair b).2)
                (sRef.evm.stack.getD (exchangePair b).1 default),
              frest, rfl, ?_, ?_⟩, ?_, ?_, ?_⟩
          · exact take_swap_writes_gen l sRef.evm.stack top.toNat
              (exchangePair b).1 (exchangePair b).2 hpfx htop (by omega)
              (by omega) (by omega) hlen
          · simp
            omega
          · rw [listSwap_length]
            exact htop
          · rw [listSwap_length]
            exact hlim
          · intro w hw
            exact hwfS w
              (listSwap_mem_gen sRef.evm.stack top.toNat (exchangePair b).1
                (exchangePair b).2 htop (by omega) (by omega) (by omega) hw)
        · exact ⟨by
            simp [hlive, Evm.Functions.G_verylow, GasCosts.OPCODE_EXCHANGE],
            hres, hsp⟩
  · have hv' : Evm.Functions.exchange_immediate_valid b = false := by
      simpa using hv
    have hdec : decode_pair (immByte sRef)
        = .error (.invalidParameter
            "EXCHANGE immediate in forbidden range") := by
      rw [himm]; exact decode_pair_invalid b hv'
    have hlim' : top.toNat ≤ 1024 := by omega
    by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_EXCHANGE
    · rw [runR_iExchange_oog sRef hg,
        runS_execute_exchange_invalid b pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hlim' hv']
      exact StepResultRel.haltedChargeFirst (Or.inr (Or.inr (Or.inl rfl)))
        (haltRegs_frame_status ss msg .InvalidOpcode)
    · push Not at hg
      rw [runR_iExchange_invalid sRef _ hdec hg,
        runS_execute_exchange_invalid b pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork hlim' hv']
      exact StepResultRel.halted (ErrorRel.invalidParameter _)
        (haltRegs_frame_status ss msg .InvalidOpcode)

end EvmSpecsVerify
