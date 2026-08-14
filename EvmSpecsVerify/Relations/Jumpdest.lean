import EvmSpecsVerify.Relations.State
import Batteries.Tactic.OpenPrivate

/-!
# Jumpdest relation

SpecRef precomputes `Evm.validJumpDestinations : List Uint` (Vm.lean:194).
The extraction stores per-code jump tables in
`HostState.jumpdestTables : List (jump_table_index × List code_pointer)`,
addressed through the `frame_code` register's `jumpdests` index;
`frame_jumpdest_valid dest` (Machine.lean:112) computes
`dest < code.len && positions.contains dest` via `jumpdest_ref_contains`.

The relation ties the two as sets: the frame's table row exists and
SpecRef's membership test coincides with the extraction's range-guarded
lookup, for every destination. The `Code` sigma is kept destructured
(`off` / `len` / `cf`) so downstream goals never carry `.2.2` projection
atoms. Preserved trivially by any step that leaves `validJumpDestinations`,
the `frame_code` register, and the jumpdest tables untouched (all of the
current tranche).
-/

open private assocGet from Evm.HostAxioms

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef (Machine)
open Evm (HostState)
open Evm.Defs

/-- The frame's jumpdest table represents SpecRef's valid-destination set. -/
structure JumpdestRel (sRef : Machine) (hs : HostState) (ss : SeqState) :
    Prop where
  rel : ∃ (off len : Nat) (cf : CodeFields off len)
      (positions : List code_pointer),
    ss.regs.get? Register.frame_code = some ⟨off, len, cf⟩ ∧
    assocGet hs.jumpdestTables cf.jumpdests = some positions ∧
    ∀ d : Nat, sRef.evm.validJumpDestinations.contains d
      = (decide (d < len) && positions.contains d)

end EvmSpecsVerify
