import EvmSpecsVerify.Relations.Memory

/-!
# External-code relation

`EXTCODECOPY` resolves code for an arbitrary account rather than the current
frame. SpecRef reaches it through the journalled account/code trackers; the
extraction reaches it through `k_code_key` and the witness-backed code store.

`ExternalCodeRel` isolates that world-state seam. It requires the two lookups
to select the same bytes and specifies `k_code_copy` byte-for-byte for every
warm-stamp and active-memory variant created by the opcode before the lookup.
The continuation host may contain lookup-cache updates, but the stack, memory
frame, warmth, and epoch fields are preserved explicitly.
-/

open private writeArrayBytes from Evm.HostAxioms

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-- Exact agreement for resolving and copying one masked account's code.
The quantified host variants are precisely the fields EXTCODECOPY changes
before calling `k_code_copy`: warm stamps and active memory storage. -/
def ExternalCodeRel (sRef : Machine) (hs : Evm.HostState) (ss : SeqState)
    (addressWord : Nat) : Prop :=
  ∃ (acct : EvmAsm.Stateless.SpecRef.Account) (code : Bytes)
    (ts1 ts2 : TransactionState)
    (hostAfter : List (Evm.Defs.address × Nat) → Array byte →
      List Evm.MemoryFrame → Evm.HostState),
    (getAccount (to_address_masked addressWord)).run sRef.txState
        = .ok (acct, ts1) ∧
    (getCode acct.codeHash (to_address_masked addressWord)).run ts1
        = .ok (code, ts2) ∧
    (∀ ws memoryBytes fr mfrest dst src size,
      dst + size ≤ fr.established →
      runS (Evm.Functions.k_code_copy
          (Evm.Functions.word_to_address addressWord) dst src size)
        { hs with
          warmAddresses := ws
          memoryBytes := memoryBytes
          memoryFrames := fr :: mfrest } ss =
        .ok ((),
          { hostAfter ws memoryBytes (fr :: mfrest) with
            memoryBytes := writeArrayBytes memoryBytes (fr.base + dst)
              (buffer_read code src size) }) ss) ∧
    (∀ ws memoryBytes memoryFrames,
      (hostAfter ws memoryBytes memoryFrames).stackFrames = hs.stackFrames) ∧
    (∀ ws memoryBytes memoryFrames,
      (hostAfter ws memoryBytes memoryFrames).memoryFrames = memoryFrames) ∧
    (∀ ws memoryBytes memoryFrames,
      (hostAfter ws memoryBytes memoryFrames).warmAddresses = ws) ∧
    (∀ ws memoryBytes memoryFrames,
      (hostAfter ws memoryBytes memoryFrames).warmEpoch = hs.warmEpoch)

/-- `MemoryRel` observes only the active frame list and memory byte array. -/
theorem memoryRel_host_congr (M : Bytes) (hs₁ hs₂ : Evm.HostState)
    (off len : Nat) (hrel : MemoryRel M hs₁ off len)
    (hbytes : hs₂.memoryBytes = hs₁.memoryBytes)
    (hframes : hs₂.memoryFrames = hs₁.memoryFrames) :
    MemoryRel M hs₂ off len := by
  obtain ⟨⟨frest, hframe⟩, haligned, hmem, htail⟩ := hrel
  refine ⟨⟨frest, by rw [hframes, hframe]⟩, haligned, ?_, htail⟩
  intro i hi
  rw [hbytes]
  exact hmem i hi

end EvmSpecsVerify
