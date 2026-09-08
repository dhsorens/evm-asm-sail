/-
# Audit: the `!a = b` precedence trap

Lean's `!` (`Bool.not`) binds **looser** than `=`, so a statement written

    theorem foo : !someBool = otherBool

elaborates as `!(someBool = otherBool)` and then coerces through
`decide`, giving `(!decide (someBool = otherBool)) = true` — that is,
`someBool ≠ otherBool`. For `Bool`s that is *equivalent* to the intended
`(!someBool) = otherBool`, so the mis-parsed statement is still true and
usually still provable. It compiles, it proves, and it is useless as a
`rw`/`simp` lemma — which is how one of these survived review in
`beneficiaryDead_eq` (`Relations/Selfdestruct.lean`).

This scans every `EvmSpecsVerify` declaration's type for `Bool.not`
applied to a `Decidable.decide`, which is the fingerprint. Run it after
adding any `Bool`-valued equation:

    lake env lean scripts/audit-bool-not-precedence.lean

Exit output is either `clean: …` or `HITS (n): [names]`. A hit is not
automatically wrong — a statement may legitimately mention
`!decide (…)` — but each one should be read to confirm the parentheses
say what the author meant.
-/
import EvmSpecsVerify
open Lean Elab Meta

run_cmd do
  let env ← getEnv
  let mut hits : Array Name := #[]
  for (n, ci) in env.constants.toList do
    unless n.isInternal do
    if (`EvmSpecsVerify).isPrefixOf n then
      let found := ci.type.find? fun e =>
        match e with
        | .app (.const ``Bool.not _) arg =>
            match arg.getAppFn with
            | .const ``Decidable.decide _ => true
            | _ => false
        | _ => false
      if found.isSome then hits := hits.push n
  if hits.isEmpty then
    logInfo "clean: no `!a = b` precedence traps"
  else
    logInfo m!"HITS ({hits.size}): {hits.toList}"
