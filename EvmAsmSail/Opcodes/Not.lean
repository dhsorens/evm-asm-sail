import EvmAsmSail.Opcodes.UnopFamily
import EvmAsmSail.Representation.BitwiseWord

/-!
# NOT

Derived through `unop_step_equiv` (`Opcodes/UnopFamily.lean`); per-opcode
content is the pure-function lemma (the extraction complements through
`BitVec 256`, SpecRef subtracts from `U256_MAX` — `word_not_eq` collapses
the round trip) and the wf bound. Reachable outcomes: success / stack
underflow / out-of-gas (overflow unreachable for 1-in/1-out).
-/

set_option maxHeartbeats 1000000

namespace EvmAsmSail

open EvmAsm.Stateless.SpecRef
open Evm.Defs

theorem alu_not_eq (a : Nat) (ha : WordWf a) :
    Evm.Functions.alu_not a = U256_MAX - a := by
  show Evm.Functions.word_not a = U256_MAX - a
  rw [word_not_eq a ha]
  rfl

theorem sub_from_max_wf (a : Nat) : WordWf (U256_MAX - a) := by
  unfold WordWf U256_MAX
  omega

open Evm.Functions in
/-- **NOT, all reachable outcomes.** -/
theorem not_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iNot sRef)
      (runS (Evm.Functions.execute (.NOT ()) pc_in top mem g) hs ss) :=
  unop_step_equiv (.NOT ()) G_verylow alu_not iNot
    GasCosts.OPCODE_NOT (fun x => U256_MAX - x) rfl rfl
    ⟨rfl, fun _ _ _ _ => rfl⟩ alu_not_eq
    (fun x _ => sub_from_max_wf x) sRef top g hs ss mem pc_in hrel hpc

end EvmAsmSail
