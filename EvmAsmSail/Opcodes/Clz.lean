import EvmAsmSail.Opcodes.UnopFamily
import EvmAsmSail.Representation.BitwiseWord

/-!
# CLZ

Derived through `unop_step_equiv` (`Opcodes/UnopFamily.lean`); per-opcode
content is the pure-function lemma (the extraction counts leading zeros
limb-wise via `BitVec.clz`, SpecRef via `Nat.log2` — `word_bit_length_eq`
identifies the two) and the wf bound. Reachable outcomes: success / stack
underflow / out-of-gas (overflow unreachable for 1-in/1-out).

The Osaka fork gate on CLZ lives in instruction decode, upstream of the
`execute` step boundary these theorems compare at; the handlers themselves
are fork-free.
-/

set_option maxHeartbeats 1000000

namespace EvmAsmSail

open EvmAsm.Stateless.SpecRef
open Evm.Defs

theorem alu_clz_eq (x : Nat) (hx : WordWf x) :
    Evm.Functions.alu_clz x
      = 256 - (if x == 0 then 0 else Nat.log2 x + 1) := by
  simp only [Evm.Functions.alu_clz, Evm.Functions.u256]
  rw [word_bit_length_eq x hx]
  by_cases h : x = 0 <;> simp [h]

theorem clz_wf (x : Nat) :
    WordWf (256 - (if x == 0 then 0 else Nat.log2 x + 1)) := by
  unfold WordWf
  have h := Nat.sub_le 256 (if x == 0 then 0 else Nat.log2 x + 1)
  omega

open Evm.Functions in
/-- **CLZ, all reachable outcomes.** -/
theorem clz_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1) :
    StepResultRel (AluPost mem) (runR iClz sRef)
      (runS (Evm.Functions.execute (.CLZ ()) pc_in top mem g) hs ss) :=
  unop_step_equiv (.CLZ ()) G_low alu_clz iClz GasCosts.OPCODE_CLZ
    (fun x =>
      let bit_length := if x == 0 then 0 else Nat.log2 x + 1
      256 - bit_length)
    rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩ alu_clz_eq
    (fun x _ => clz_wf x) sRef top g hs ss mem pc_in hrel hpc

end EvmAsmSail
