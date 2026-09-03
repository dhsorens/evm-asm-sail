import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# SWAP1–SWAP16

`iSwapN n` (dispatched as `iSwapN (op - 0x8F)`, so 1-indexed) vs
`execute (.SWAP n)` with the same `n` and stack effect `(n + 1, n + 1)`.
Unlike [`DUP`](Dup.lean) the index conventions already agree, and the
height never changes — so **overflow is unreachable** here even though DUP
has it: `validate_stack` checks `top - (n+1) + (n+1) = top`, which the 1024
invariant already bounds. Reachable outcomes: success / underflow / OOG /
MM-5 double fault (`iSwapN` is charge-first, like `iDupN`).

The content of the slice is that the two sides describe the same exchange
in opposite coordinates:

* SpecRef rewrites the head-first list with
  `listSwap S 0 n = (S.set 0 S[n]).set n S[0]`;
* the extraction issues two in-place `stack_set` writes into the
  bottom-indexed frame list, at slots `0` and `n` below the cursor — i.e.
  positions `top - 1` and `top - 1 - n`.

[`take_swap_writes`](#take_swap_writes) is the bridge: reversing the
prefix maps index `j` to `top - 1 - j`, so the two writes land exactly on
`listSwap`'s two changed indices. Note both extraction writes read the
*pre-swap* values (`peek` twice before either `stack_set`), so the order of
the writes does not matter — and the same is true of `listSwap`, whose two
`set`s both take their values from the original `S`.

Gas (MM-2): `GasCosts.OPCODE_SWAP = 3 = G_verylow`.
-/

open private pcAdd listSwap from EvmAsm.Stateless.SpecRef.InstructionsCore
open private writeListAt from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## `listSwap`, as two `List.set`s -/

theorem listSwap_eq (S : List U256) (i j : Nat) :
    listSwap S i j = (S.set i (S.getD j 0)).set j (S.getD i 0) := rfl

theorem listSwap_length (S : List U256) (i j : Nat) :
    (listSwap S i j).length = S.length := by
  rw [listSwap_eq]; simp

/-- `listSwap S 0 n` agrees with `S` away from the two swapped indices. -/
theorem listSwap_getElem? (S : List U256) (t n j : Nat) (ht : t = S.length)
    (hn : 0 < n) (hnt : n < t) (hj : j < t) :
    (listSwap S 0 n)[j]? =
      if j = 0 then S[n]? else if j = n then S[0]? else S[j]? := by
  rw [listSwap_eq]
  simp only [List.getElem?_set, List.length_set]
  by_cases h0 : j = 0
  · subst h0
    rw [if_neg (by omega), if_pos rfl, if_pos (by omega)]
    rw [List.getElem?_eq_getElem (by omega)]
    simp [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show n < S.length by omega)]
  · by_cases hjn : j = n
    · subst hjn
      rw [if_pos rfl, if_pos (by omega)]
      rw [List.getElem?_eq_getElem (show 0 < S.length by omega)]
      simp only [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show 0 < S.length by omega)]
      simp [h0]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]

/-- A swap is a permutation, so it introduces no new entries — the stack
well-formedness invariant survives. -/
theorem listSwap_mem (S : List U256) (t n : Nat) (ht : t = S.length)
    (hn : 0 < n) (hnt : n < t) {x : U256} (hx : x ∈ listSwap S 0 n) :
    x ∈ S := by
  rw [List.mem_iff_getElem?] at hx
  obtain ⟨j, hj⟩ := hx
  have hjlt : j < t := by
    have h : j < (listSwap S 0 n).length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at hj
      exact absurd hj (by simp)
    rw [listSwap_length] at h
    omega
  rw [listSwap_getElem? S t n j ht hn hnt hjlt] at hj
  split at hj
  · exact List.mem_iff_getElem?.mpr ⟨n, hj⟩
  · split at hj
    · exact List.mem_iff_getElem?.mpr ⟨0, hj⟩
    · exact List.mem_iff_getElem?.mpr ⟨j, hj⟩

/-- **The coordinate bridge.** Two in-place writes at frame positions
`t - 1` and `t - 1 - n` turn the reversed-prefix representation of `S` into
that of `listSwap S 0 n`. -/
theorem take_swap_writes (l : List word) (S : List U256) (t n : Nat)
    (hpfx : l.take t = S.reverse) (ht : t = S.length)
    (hn : 0 < n) (hnt : n < t) (hlen : t ≤ l.length) :
    ((l.set (t - 1) (S.getD n 0)).set (t - 1 - n) (S.getD 0 0)).take t
      = (listSwap S 0 n).reverse := by
  have hlS : (listSwap S 0 n).length = t := by rw [listSwap_length]; omega
  have hli : ∀ i, i < t → l[i]? = S[t - 1 - i]? := by
    intro i hi
    have h1 : (l.take t)[i]? = l[i]? := List.getElem?_take_of_lt hi
    rw [← h1, hpfx, List.getElem?_reverse (by omega)]
    congr 1
    omega
  apply List.ext_getElem?
  intro i
  by_cases hi : i < t
  · rw [List.getElem?_take_of_lt hi, List.getElem?_reverse (by omega), hlS,
      listSwap_getElem? S t n (t - 1 - i) ht hn hnt (by omega)]
    simp only [List.getElem?_set, List.length_set]
    by_cases hitop : i = t - 1
    · subst hitop
      rw [if_neg (by omega), if_pos rfl, if_pos (by omega), if_pos (by omega)]
      simp [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show n < S.length by omega)]
    · by_cases hin : i = t - 1 - n
      · subst hin
        rw [if_pos rfl, if_pos (by omega), if_neg (by omega),
          if_pos (by omega)]
        simp [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show 0 < S.length by omega)]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega)]
        exact hli i hi
  · rw [List.getElem?_eq_none (by simp; omega),
      List.getElem?_eq_none (by simp [hlS]; omega)]

/-- The host state after SWAP's two in-place writes, named so the run
shapes below carry no multi-line structure-update literal. Stated with
`List.set` (the in-range form of `writeListAt`) so `take_swap_writes`
applies directly. -/
def swapHost (hs : Evm.HostState) (l : List word)
    (frest : List (List word)) (t n : Nat) (a b : word) : Evm.HostState :=
  { hs with stackFrames := (l.set (t - 1) a).set (t - 1 - n) b :: frest }

/-! ## SpecRef run shapes -/

theorem runR_iSwapN_success (s : Machine) (n : Nat)
    (hn : n < s.evm.stack.length)
    (hgas : GasCosts.OPCODE_SWAP ≤ s.evm.gasLeft) :
    runR (iSwapN n) s =
      .ok (.ok (),
        { s with evm := { s.evm with
            stack := listSwap s.evm.stack 0 n
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_SWAP
            regularGasUsed := s.evm.regularGasUsed + GasCosts.OPCODE_SWAP
            pc := s.evm.pc + 1 } }) := by
  simp only [iSwapN, pcAdd]
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_neg (by show ¬(n ≥ s.evm.stack.length); omega)]
  refine runR_bind_ok (runR_pure _ _) ?_
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  exact runR_modifyEvm _ _

theorem runR_iSwapN_underflow (s : Machine) (n : Nat)
    (hn : s.evm.stack.length ≤ n)
    (hgas : GasCosts.OPCODE_SWAP ≤ s.evm.gasLeft) :
    runR (iSwapN n) s =
      .ok (.error .stackUnderflow,
        { s with evm := { s.evm with
            gasLeft := s.evm.gasLeft - GasCosts.OPCODE_SWAP
            regularGasUsed :=
              s.evm.regularGasUsed + GasCosts.OPCODE_SWAP } }) := by
  simp only [iSwapN]
  refine runR_bind_ok (runR_charge_gas _ _ (by simpa using hgas)) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  rw [if_pos (by show n ≥ s.evm.stack.length; omega)]
  exact runR_bind_err (runR_throw _ _)

/-- OOG fires at the leading charge, before any stack inspection (MM-5). -/
theorem runR_iSwapN_oog (s : Machine) (n : Nat)
    (hgas : s.evm.gasLeft < GasCosts.OPCODE_SWAP) :
    runR (iSwapN n) s = .ok (.error .outOfGas, s) := by
  simp only [iSwapN]
  exact runR_bind_err (runR_charge_gas_oog _ _ (by simpa using hgas))

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The dispatch equation for the SWAP family. -/
theorem swap_dispatch (n : Nat) (pc_in : Nat) (top : StackTop)
    (mem : EvmMemorySlice) (g : Nat) :
    Evm.Functions.execute_opcode (.SWAP n) pc_in top mem g =
      Evm.Functions.execute_swap n top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
theorem runS_swap_body_ok (n : Nat) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (S : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = S.reverse)
    (htop : top.toNat = S.length)
    (hnt : n < S.length) (hn : 0 < n)
    (hlen : top.toNat ≤ l.length)
    (hgas : G_verylow ≤ g) :
    runS (Evm.Functions.execute_swap n top g) hs ss =
      .ok ((top, g - G_verylow),
        swapHost hs l frest top.toNat n (S.getD n default)
          (S.getD 0 default)) ss := by
  have hset1 : writeListAt l (top.toNat - 1) (S.getD n default)
      = l.set (top.toNat - 1) (S.getD n default) :=
    writeListAt_eq_set l _ _ (by omega)
  have hset2 : writeListAt (l.set (top.toNat - 1) (S.getD n default))
        (top.toNat - 1 - n) (S.getD 0 default)
      = (l.set (top.toNat - 1) (S.getD n default)).set
          (top.toNat - 1 - n) (S.getD 0 default) :=
    writeListAt_eq_set _ _ _ (by simp; omega)
  simp only [Evm.Functions.execute_swap]
  refine runS_bind_ok (runS_charge_ok g G_verylow hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok
    (runS_peek top 0 hs ss l frest S hframe hpfx htop (by omega)) ?_
  refine runS_bind_ok
    (runS_peek top n hs ss l frest S hframe hpfx htop hnt) ?_
  refine runS_bind_ok
    (runS_stack_set top 0 (S.getD n default) hs ss l frest hframe) ?_
  refine runS_bind_ok
    (runS_stack_set top n (S.getD 0 default) _ ss
      (writeListAt l (top.toNat - 1) (S.getD n default)) frest rfl) ?_
  rw [hset1, hset2]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_swap_body_oog (n : Nat) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < G_verylow) :
    runS (Evm.Functions.execute_swap n top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_swap]
  refine runS_bind_ok
    (runS_charge_oog g G_verylow hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_swap_success (n : Nat) (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (S : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = S.reverse)
    (htop : top.toNat = S.length)
    (hnt : n < S.length) (hn : 0 < n)
    (hlen : top.toNat ≤ l.length)
    (hlim : top.toNat ≤ 1024)
    (hgas : G_verylow ≤ g) :
    runS (Evm.Functions.execute (.SWAP n) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, g - G_verylow),
        swapHost hs l frest top.toNat n (S.getD n default)
          (S.getD 0 default)) ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.SWAP n) = pure (n + 1, n + 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top (n + 1) (n + 1) hs ss (by omega)
      (by have h : top.toNat - (n + 1) + (n + 1) ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, swap_dispatch]
  refine runS_bind_ok
    (runS_swap_body_ok n top g hs ss l frest S hframe hpfx htop hnt hn hlen
      hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_swap_underflow (n : Nat) (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < n + 1) :
    runS (Evm.Functions.execute (.SWAP n) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.SWAP n) = pure (n + 1, n + 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top (n + 1) (n + 1) hs ss prof sp msg
      hprof hsp hmsg hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_swap_oog (n : Nat) (pc_in : Nat) (top : StackTop)
    (g : Nat) (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hin : n + 1 ≤ top.toNat) (hlim : top.toNat ≤ 1024)
    (hgas : g < G_verylow) :
    runS (Evm.Functions.execute (.SWAP n) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.SWAP n) = pure (n + 1, n + 1)
      from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top (n + 1) (n + 1) hs ss hin
      (by have h : top.toNat - (n + 1) + (n + 1) ≤ 1024 := by omega
          simpa [Evm.Functions.STACK_LIMIT] using h)) ?_
  rw [dif_pos rfl, swap_dispatch]
  refine runS_bind_ok
    (runS_swap_body_oog n top g hs ss prof sp msg hprof hsp hmsg hfork
      hgas) ?_
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **SWAPn, all reachable outcomes**: success / underflow / OOG / MM-5
double fault. Overflow is unreachable — the height is unchanged, so
`validate_stack`'s post-height is the pre-height, already bounded by the
1024 invariant. -/
theorem swap_step_equiv (n : Nat) (hn1 : 1 ≤ n)
    (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (BasePost mem) (runR (iSwapN n) sRef)
      (runS (Evm.Functions.execute (.SWAP n) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  by_cases hg : sRef.evm.gasLeft < GasCosts.OPCODE_SWAP
  · rw [runR_iSwapN_oog sRef n hg]
    by_cases hu : sRef.evm.stack.length < n + 1
    · rw [runS_execute_swap_underflow n pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.haltedChargeFirst (Or.inl rfl)
        (haltRegs_frame_status ss msg .StackUnderflow)
    · rw [runS_execute_swap_oog n pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)
        (by omega) (by rw [hlive]; exact hg)]
      exact StepResultRel.halted ErrorRel.outOfGas
        (haltRegs_frame_status ss msg .OutOfGas)
  · push Not at hg
    by_cases hu : sRef.evm.stack.length < n + 1
    · rw [runR_iSwapN_underflow sRef n (by omega) hg,
        runS_execute_swap_underflow n pc_in top g mem hs ss prof
          sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork (by omega)]
      exact StepResultRel.halted ErrorRel.stackUnderflow
        (haltRegs_frame_status ss msg .StackUnderflow)
    · rw [runR_iSwapN_success sRef n (by omega) hg,
        runS_execute_swap_success n pc_in top g mem hs ss l frest
          sRef.evm.stack hframe hpfx htop (by omega) hn1 hlen (by omega)
          (by rw [hlive]; exact hg)]
      refine StepResultRel.success ?_
      refine ⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE, ⟨prof, hprof, hfork⟩,
        ⟨msg, hmsg⟩⟩, by simp [hpc], rfl⟩
      · refine ⟨⟨(l.set (top.toNat - 1) (sRef.evm.stack.getD n default)).set
              (top.toNat - 1 - n) (sRef.evm.stack.getD 0 default),
            frest, rfl, ?_, ?_⟩, ?_, ?_, ?_⟩
        · exact take_swap_writes l sRef.evm.stack top.toNat n hpfx htop
            hn1 (by omega) hlen
        · simp
          omega
        · rw [listSwap_length]
          exact htop
        · rw [listSwap_length]
          exact hlim
        · intro w hw
          exact hwfS w
            (listSwap_mem sRef.evm.stack top.toNat n htop hn1 (by omega) hw)
      · exact ⟨by simp [hlive, Evm.Functions.G_verylow, GasCosts.OPCODE_SWAP],
          hres, hsp⟩

end EvmSpecsVerify
