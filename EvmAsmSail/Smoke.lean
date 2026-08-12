import EvmAsm.Stateless.SpecRef
import Evm

/-!
# Smoke test

Both sides of the intended equivalence import into one environment:

- `EvmAsm.Stateless.SpecRef` — evm-asm's internal Lean port of the execution-specs
  (the semantic anchor its README wants validated externally), and
- `Evm` — the Lean extraction of evm-sail (generated model + executable host contract).

The `#check`s pin the entry points the equivalence proofs will connect, so a drift
in either upstream surfaces here first.
-/

open EvmAsm.Stateless

#check @SpecRef.run_stateless_guest
#check @Evm.Functions.process_transaction
#check @Evm.Functions.interpret
#check @Evm.initialHostState
