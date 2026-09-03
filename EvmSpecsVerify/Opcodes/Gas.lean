import EvmSpecsVerify.Opcodes.Shapes.LivePusher

/-!
# GAS

The second [`live-state pusher`](Shapes/LivePusher.lean), and the one that
makes the shape's "read the machine *after* the charge" convention matter:
SpecRef's `iGas` charges `OPCODE_GAS` and *then* pushes `evm.gasLeft`, so
the pushed value is `gasLeft - 2`. The extraction's `execute_gas` charges
`G_base` and pushes the post-charge carried gas `g1`, so the two agree.

Only the execution-gas dimension is pushed. Amsterdam's state-gas
reservoir (`stateGasLeft` / `state_gas_remaining`) is untouched by both
sides, so there is nothing to relate beyond the live gas.

Reachable outcomes: success / stack overflow / OOG / MM-5 double fault
(charge-first on both sides); underflow is impossible for 0-in.

Gas (MM-2): `GasCosts.OPCODE_GAS = 2 = G_base`.

Mismatch ledger MM-8: the extraction's `push_gas` reduces the pushed
quantity modulo `2^256` where SpecRef pushes the raw `Nat`, so the two
sides disagree — silently, not by aborting — above the word modulus. The
theorem is domain-restricted by `hwfg` and the restriction is ledgered
rather than hidden.
-/

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- `iGas` is the live-state pusher for the remaining execution gas. -/
theorem iGas_eq :
    iGas = livePushOf GasCosts.OPCODE_GAS (fun e => e.gasLeft) := rfl

/-! ## `Evm` run shapes -/

/-- The extraction's `2 ^i 256` is an *Int*-exponent power, so
[`two_pow_toNat`](Shapes/Alu.lean) (Nat exponent) does not apply to it. -/
theorem two_zpow_toNat : (((2 : Int) ^ (256 : Int)).toNat) = 2 ^ 256 := by
  decide

open Evm.Functions in
/-- `push_gas` is `push_word` of the modularly reduced quantity; below the
word modulus the reduction is the identity (MM-8 lives exactly at the
hypothesis `hwf`). -/
theorem runS_push_gas (top : StackTop) (v : Nat) (hs : Evm.HostState)
    (ss : SeqState) (l : List word) (frest : List (List word))
    (hframe : hs.stackFrames = l :: frest)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hwf : v < 2 ^ 256) :
    runS (Evm.Functions.push_gas top v) hs ss =
      .ok (top + BitVec.ofNat 64 1, livePushHost hs l frest top v) ss := by
  have hmod : Nat.mod v (((2 : Int) ^ (256 : Int)).toNat) = v := by
    rw [two_zpow_toNat]
    exact Nat.mod_eq_of_lt hwf
  simp only [Evm.Functions.push_gas, Evm.Functions.u256]
  show runS (Evm.Functions.push_word top
    (Nat.mod v (((2 : Int) ^ (256 : Int)).toNat))) hs ss = _
  rw [hmod]
  exact runS_push_word top v hs ss l frest hframe hbound

open Evm.Functions in
/-- GAS's dispatch: the pc and memory pass through. -/
theorem gas_dispatch :
    LivePushDispatch (.GAS ())
      (fun _ top g => Evm.Functions.execute_gas top g) :=
  ⟨rfl, fun _ _ _ _ => rfl⟩

open Evm.Functions in
theorem runS_gas_body_ok (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word))
    (hframe : hs.stackFrames = l :: frest)
    (hbound : top.toNat + 1 < 2 ^ 64)
    (hgas : (G_base : Nat) ≤ g)
    (hwf : g - (G_base : Nat) < 2 ^ 256) :
    runS (Evm.Functions.execute_gas top g) hs ss =
      .ok ((top + BitVec.ofNat 64 1, g - G_base),
        livePushHost hs l frest top (g - G_base)) ss := by
  simp only [Evm.Functions.execute_gas]
  refine runS_bind_ok (runS_charge_ok g G_base hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok
    (runS_push_gas top (g - G_base) hs ss l frest hframe hbound hwf) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_gas_body_oog (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hgas : g < (G_base : Nat)) :
    runS (Evm.Functions.execute_gas top g) hs ss =
      .ok ((top, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_gas]
  refine runS_bind_ok
    (runS_charge_oog g G_base hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

/-! ## The step equivalence -/

open Evm.Functions in
/-- **GAS, all reachable outcomes**: success / stack overflow / OOG / MM-5
double fault. Underflow is impossible for 0-in. `hwfg` is the MM-8 domain
restriction: above the word modulus the extraction's `push_gas` wraps and
SpecRef does not. -/
theorem gas_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (hwfg : WordWf sRef.evm.gasLeft) :
    StepResultRel (BasePost mem) (runR iGas sRef)
      (runS (Evm.Functions.execute (.GAS ()) pc_in top mem g) hs ss) := by
  have hlive : g = sRef.evm.gasLeft := hrel.gas.live
  have hval : livePushWord GasCosts.OPCODE_GAS (fun e => e.gasLeft) sRef.evm
      = g - (G_base : Nat) := by
    rw [hlive]
    simp [livePushWord, chargedEvm, Evm.Functions.G_base,
      GasCosts.OPCODE_GAS]
  have hwf' : g - (G_base : Nat) < 2 ^ 256 := by
    unfold WordWf at hwfg
    omega
  refine livePush_step_equiv (.GAS ()) _ gas_dispatch iGas
    GasCosts.OPCODE_GAS (fun e => e.gasLeft) iGas_eq rfl sRef top g hs ss mem
    pc_in hrel hpc (fun l frest hframe hbound hgas => ?_)
    (fun prof sp msg hprof hsp hmsg hfork hgas =>
      runS_gas_body_oog top g hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  · rw [hval]
    exact runS_gas_body_ok top g hs ss l frest hframe hbound hgas hwf'
  · rw [hval]
    exact hwf'

end EvmSpecsVerify
