import EvmSpecsVerify.Opcodes.Shapes.LivePusher

/-!
# PC

The first 0-in/1-out pusher whose value is *not* a `k_env` block field but
the live step state, so it goes through the
[`live-state pusher shape`](Shapes/LivePusher.lean) rather than the
[`env pusher shape`](Shapes/EnvPusher.lean).

SpecRef's `iPc` charges `OPCODE_PC`, pushes `evm.pc` — the opcode's own
position — and advances the pc. The extraction receives the *already
advanced* `pc_in` (mismatch ledger MM-4) and recovers the opcode position
by subtracting one: `word_of_source_byte_count pc_in` embeds the counter as
a word, then `alu_sub … WORD_ONE`. Under `pc_in = sRef.evm.pc + 1` the two
values coincide, and the subtraction never wraps because `pc_in ≥ 1`.

Charge-first on both sides, so the double-fault states (full stack ∧ out of
gas) land on MM-5: SpecRef reports `outOfGas`, the extraction's hoisted
`validate_stack` reports `StackOverflow`. Reachable outcomes: success /
stack overflow / OOG / MM-5 double fault. Underflow is impossible for
0-in.

Gas (MM-2): `GasCosts.OPCODE_PC = 2 = G_base`.
-/

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- `iPc` is the live-state pusher for the program counter. -/
theorem iPc_eq : iPc = livePushOf GasCosts.OPCODE_PC (fun e => e.pc) := rfl

/-- The extraction recovers the opcode's own position from the advanced
counter. No wrap: `pc_in ≥ 1` on every reachable state. -/
theorem alu_sub_one (n : Nat) (hn : 1 ≤ n) :
    Evm.Functions.alu_sub n Evm.Functions.WORD_ONE = n - 1 := by
  have h1 : (Evm.Functions.WORD_ONE : Nat) = 1 := by decide
  show Evm.Functions.word_sub_word n Evm.Functions.WORD_ONE = n - 1
  rw [Evm.Functions.word_sub_word, h1]
  simp [hn]

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- PC's dispatch: the incoming pc is returned unchanged (the handler only
reads it to compute the pushed word) and the memory passes through. -/
theorem pc_dispatch :
    LivePushDispatch (.PC ())
      (fun pc_in top g => Evm.Functions.execute_pc pc_in top g) :=
  ⟨rfl, fun _ _ _ _ => rfl⟩

open Evm.Functions in
theorem runS_pc_body_ok (pc_in : Nat) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word))
    (hframe : hs.stackFrames = l :: frest)
    (hwfpc : pc_in < 2 ^ 256) (hpos : 1 ≤ pc_in)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hgas : (G_base : Nat) ≤ g) :
    runS (Evm.Functions.execute_pc pc_in top g) hs ss =
      .ok ((top + BitVec.ofNat 64 1, g - G_base),
        livePushHost hs l frest top (pc_in - 1)) ss := by
  simp only [Evm.Functions.execute_pc]
  refine runS_bind_ok (runS_charge_ok g G_base hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_word_of_source_byte_count pc_in hs ss hwfpc) ?_
  rw [alu_sub_one pc_in hpos]
  refine runS_bind_ok (runS_push_word top _ hs ss l frest hframe hbound) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_pc_body_oog (pc_in : Nat) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < (G_base : Nat)) :
    runS (Evm.Functions.execute_pc pc_in top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_pc]
  refine runS_bind_ok
    (runS_charge_oog g G_base hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **PC, all reachable outcomes**: success / stack overflow / OOG / MM-5
double fault. Underflow is impossible for 0-in. `hwfpc` is the
program-counter word bound both sides need to agree on the pushed value —
see `Assumptions.lean`. -/
theorem pc_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (hwfpc : WordWf pc_in) :
    StepResultRel (BasePost mem) (runR iPc sRef)
      (runS (Evm.Functions.execute (.PC ()) pc_in top mem g) hs ss) := by
  have hval : livePushWord GasCosts.OPCODE_PC (fun e => e.pc) sRef.evm
      = pc_in - 1 := by
    subst hpc
    simp [livePushWord, chargedEvm]
  refine livePush_step_equiv (.PC ()) _ pc_dispatch iPc GasCosts.OPCODE_PC
    (fun e => e.pc) iPc_eq rfl sRef top g hs ss mem pc_in hrel hpc
    (fun l frest hframe hbound hgas => ?_)
    (fun prof sp msg hprof hsp hmsg hfork hgas =>
      runS_pc_body_oog pc_in top g hs ss prof sp msg hprof hsp hmsg hfork
        hgas) ?_
  · rw [hval]
    exact runS_pc_body_ok pc_in top g hs ss l frest hframe hwfpc (by omega)
      hbound hgas
  · rw [hval]
    unfold WordWf at hwfpc ⊢
    omega

end EvmSpecsVerify
