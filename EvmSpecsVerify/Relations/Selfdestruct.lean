import EvmSpecsVerify.Relations.Transfer

/-!
# The `SELFDESTRUCT` lifecycle

What `SELFDESTRUCT` needs beyond the account overlay and the value
transfer: the Amsterdam gas schedule, the "creates an account" predicate,
and the EIP-6780 lifecycle flags.

## The two representations of "created" and "deleted"

Both specifications defer the deletion itself to transaction end, and both
apply the EIP-6780 same-transaction test at the *opcode*:

| | SpecRef | `Evm` |
| --- | --- | --- |
| created this tx | `txState.createdAccounts : List Address` | the row's `created : Bool` |
| marked for deletion | `evm.accountsToDelete : List Address` | the row's `selfdestructed : Bool` |
| the test at the opcode | `createdAccounts.contains originator` | `k_was_created address` |
| the mark | `accountsToDelete := setAdd …` | `k_selfdestruct` sets `selfdestructed` |
| tx end | `clearAccountPreservingBalance` per address (Fork.lean:457) | `account_clear_preserving_balance` + `storage_tx_clear` per deleted row (`k_tx_merge`, Kernel/Lifecycle.lean:119) |

So the shapes differ (a frame-local address list against a per-row flag)
but the semantics line up, EIP-8246's balance preservation included.

`LifecycleRel` relates them, and it is **one-directional in the `created`
component** for a reason that is upstream and deliberate:
`restoreTxState` (StateTracker.lean:332) restores the write maps and
transient storage but *not* `createdAccounts` — its own comment says
"reads and `created_accounts` keep accumulating" — while the extraction's
`state_journal_revert` (HostAxioms.lean:2041) restores the whole
`accountTx` list, so a reverted frame's `created` flag goes back to
`false`. A reverted `CREATE` therefore leaves SpecRef thinking the target
was created this transaction and the extraction thinking it was not.

That asymmetry is **not** observable through `SELFDESTRUCT`, and the
argument is worth writing down: to reach the divergent branch the
originator must be executing code at `SELFDESTRUCT` time, and the only
creation of that address in this transaction reverted — which rolled its
code back too, so there is no code to execute. A *later* creation at the
same address marks `created` on both sides. `generic_create`
(Interpreter.lean:561) also settles the neighbouring worry: the
collision test `accountDeployable` runs *before* `process_create_message`,
so `markAccountCreated` never fires on an occupied target.

`selfdestructed` needs no such caveat: SpecRef drops a failed child's
whole `evm` (so `accountsToDelete` is discarded) and the extraction's
journal restores the flag, so both roll back together.

## The frame parameter

`accountsToDelete` is frame-local and merged into the parent by
`incorporate_child_on_success` (Interpreter.lean:110), while the row flag
is set once and seen by every frame. `LifecycleRel` therefore carries an
`outer` list — the addresses ancestors already marked — exactly as
[`LogRel`](Log.lean) carries a `base`. It is not a weakening: no
frame-local statement can pin a global flag to one frame's list.
-/

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## The Amsterdam `SELFDESTRUCT` schedule

Five constants, five identities. Together they close the account-write
subset of mismatch ledger MM-2 for this opcode: the two vocabularies name
the same numbers. -/

theorem selfdestructBase_eq :
    Evm.Functions.G_selfdestruct = GasCosts.OPCODE_SELFDESTRUCT_BASE := rfl

theorem coldAccountAccess_eq :
    Evm.Functions.G_amsterdam_cold_account_access
      = GasCosts.COLD_ACCOUNT_ACCESS := rfl

theorem warmAccessZero_eq : Evm.Functions.G_zero = 0 := rfl

theorem accountWrite_eq :
    Evm.Functions.G_amsterdam_account_write = GasCosts.ACCOUNT_WRITE := rfl

/-- The state-gas constant is a *product* on SpecRef's side
(`STATE_BYTES_PER_NEW_ACCOUNT * COST_PER_STATE_BYTE` = `120 * 1530`) and a
literal on the extraction's. -/
theorem newAccount_eq :
    Evm.Functions.G_amsterdam_state_new_account
      = StateGasCosts.NEW_ACCOUNT := rfl

/-- The regular-gas cost of one `SELFDESTRUCT`, as a closed form both
sides reduce to: the base, the cold-access surcharge, and the
account-write surcharge when the transfer brings a dead beneficiary to
life. -/
def selfdestructCost (cold creates : Bool) : Nat :=
  GasCosts.OPCODE_SELFDESTRUCT_BASE
    + (if cold then GasCosts.COLD_ACCOUNT_ACCESS else 0)
    + (if creates then GasCosts.ACCOUNT_WRITE else 0)

/-- The sentry amount both sides check before doing any work: the cost
without the account-write surcharge, which is decided only after the
beneficiary has been read. -/
def selfdestructAccessCost (cold : Bool) : Nat :=
  GasCosts.OPCODE_SELFDESTRUCT_BASE
    + (if cold then GasCosts.COLD_ACCOUNT_ACCESS else 0)

theorem selfdestructCost_eq_access (cold : Bool) :
    selfdestructCost cold false = selfdestructAccessCost cold := by
  unfold selfdestructCost selfdestructAccessCost
  simp

/-- The extraction's `access_cost` is `selfdestructAccessCost` on the
warmth flag SpecRef's `is_cold` negates. -/
theorem extractionAccessCost_eq (warm : Bool) :
    (0 + Evm.Functions.G_selfdestruct
        + (if warm then Evm.Functions.G_zero
            else Evm.Functions.G_amsterdam_cold_account_access))
      = selfdestructAccessCost (!warm) := by
  unfold selfdestructAccessCost
  cases warm with
  | false => rw [if_neg (by decide), if_pos (by decide)]; rfl
  | true => rw [if_pos (by decide), if_neg (by decide)]; rfl

/-- The extraction's `execution_cost` is `selfdestructCost`. -/
theorem extractionExecutionCost_eq (warm creates : Bool) :
    (if creates then
        selfdestructAccessCost (!warm) + Evm.Functions.G_amsterdam_account_write
      else selfdestructAccessCost (!warm))
      = selfdestructCost (!warm) creates := by
  unfold selfdestructCost selfdestructAccessCost
  cases creates <;> simp [accountWrite_eq]

/-! ## The "creates an account" predicate

SpecRef: `beneficiary_dead && originator_has_balance`, where
`beneficiary_dead = !isAccountAlive beneficiary` and the balance is read
with `getAccount originator`. The extraction: `nonzero_balance &&
beneficiary_empty`, where `beneficiary_empty = k_account_is_empty` and the
balance comes from `k_get_balance`. Same conjunction, opposite operand
order; the two lemmas below identify the operands, leaving the assembly to
the step theorem (which is where the `Bool`/`Prop` coercion SpecRef's `&&`
performs becomes concrete). -/

theorem word_nonzero_eq (w : Nat) :
    Evm.Functions.word_nonzero w = !(w == 0) := by
  unfold Evm.Functions.word_nonzero Evm.Functions.word_is_zero
  rw [show Evm.Functions.WORD_ZERO = 0 from rfl]

/-- **SpecRef's `beneficiary_dead` is the extraction's
`beneficiary_empty`.** SpecRef tests `EMPTY_ACCOUNT` equality on the tuple
it stores; the extraction tests EIP-161 emptiness on the row's `info`.
`AccountRel`'s discipline fields make those the same predicate. -/
theorem beneficiaryDead_eq {ts : TransactionState} {hs : Evm.HostState}
    (hrel : AccountRel ts hs) (bV : Evm.Defs.address)
    (bv : Evm.Defs.AcctValue) (hbrow : hostAcctRow hs bV = some bv) :
    !((hostAcctView bv.curr).getD EMPTY_ACCOUNT != EMPTY_ACCOUNT)
      = Evm.Functions.account_info_empty bv.curr.info := by
  rw [accountRel_alive hrel bV bv hbrow,
    accountRel_empty_iff_absent hrel bV bv hbrow]
  simp

/-- **SpecRef's `originator_has_balance` is the extraction's
`nonzero_balance`.** -/
theorem originatorHasBalance_eq {ts : TransactionState} {hs : Evm.HostState}
    (hrel : AccountRel ts hs) (oV : Evm.Defs.address)
    (ov : Evm.Defs.AcctValue) (horow : hostAcctRow hs oV = some ov) :
    (((hostAcctView ov.curr).getD EMPTY_ACCOUNT).balance != 0)
      = Evm.Functions.word_nonzero ov.curr.info.balance := by
  rw [accountRel_balance hrel oV ov horow, word_nonzero_eq]
  rfl

/-! ## The lifecycle flags

`k_selfdestruct` installs a whole row that differs from the old one only in
`selfdestructed`, so it is *not* one of `store_account_info`'s shapes —
`hostAcctView` and both `AccountRel` discipline fields ignore the lifecycle
flags entirely, which is what `accountRel_flagWrite` says. -/

/-- The row `k_selfdestruct` installs. Named for the record-literal parse
constraint. -/
def acctRowDeleted (c : Evm.Defs.Account) : Evm.Defs.Account :=
  { c with selfdestructed := true }

@[simp] theorem acctRowDeleted_info (c : Evm.Defs.Account) :
    (acctRowDeleted c).info = c.info := rfl

@[simp] theorem acctRowDeleted_present (c : Evm.Defs.Account) :
    (acctRowDeleted c).present = c.present := rfl

@[simp] theorem acctRowDeleted_flag (c : Evm.Defs.Account) :
    (acctRowDeleted c).selfdestructed = true := rfl

@[simp] theorem acctRowDeleted_created (c : Evm.Defs.Account) :
    (acctRowDeleted c).created = c.created := rfl

/-- Setting a flag that is already set changes nothing — the
`k_selfdestruct` no-op branch. -/
theorem acctRowDeleted_idem (c : Evm.Defs.Account)
    (h : c.selfdestructed = true) : acctRowDeleted c = c := by
  unfold acctRowDeleted
  rw [← h]

/-- **A lifecycle-flag write cannot break `AccountRel`.** All four fields
read `info` and `present`, which the write leaves alone, and the relation
lives over an *unchanged* SpecRef state: SpecRef records the deletion in
`evm.accountsToDelete`, not in `accountWrites`. -/
theorem accountRel_flagWrite {ts : TransactionState} {hs hs' : Evm.HostState}
    (hrel : AccountRel ts hs) (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue)
    (hw : HostAcctWritten hs hs' aV { v with curr := acctRowDeleted v.curr })
    (hrow : hostAcctRow hs aV = some v) :
    AccountRel ts hs' := by
  have hframe : ∀ bV : Evm.Defs.address, bV ≠ aV →
      hostAcctRow hs' bV = hostAcctRow hs bV := hw.2.1
  have hview : hostAcctView (acctRowDeleted v.curr) = hostAcctView v.curr := by
    unfold hostAcctView
    rw [acctRowDeleted_present, acctRowDeleted_info]
  constructor
  case curr =>
    intro bV v' hv'
    by_cases hkey : bV = aV
    · rw [hkey] at hv' ⊢
      rw [hw.1] at hv'
      rw [← Option.some.inj hv']
      show specAcctRow ts aV.toList = some (hostAcctView (acctRowDeleted v.curr))
      rw [hview]
      exact hrel.curr aV v hrow
    · exact hrel.curr bV v' (by rw [← hframe bV hkey]; exact hv')
  case absentEmpty =>
    intro bV v' hv' habs
    by_cases hkey : bV = aV
    · rw [hkey] at hv'
      rw [hw.1] at hv'
      rw [← Option.some.inj hv'] at habs ⊢
      rw [acctRowDeleted_info]
      exact hrel.absentEmpty aV v hrow (by rwa [acctRowDeleted_present] at habs)
    · exact hrel.absentEmpty bV v' (by rw [← hframe bV hkey]; exact hv') habs
  case presentNonEmpty =>
    intro bV v' hv' hpres
    by_cases hkey : bV = aV
    · rw [hkey] at hv'
      rw [hw.1] at hv'
      rw [← Option.some.inj hv'] at hpres ⊢
      rw [acctRowDeleted_info]
      exact hrel.presentNonEmpty aV v hrow (by rwa [acctRowDeleted_present] at hpres)
    · exact hrel.presentNonEmpty bV v' (by rw [← hframe bV hkey]; exact hv') hpres
  case wf =>
    intro bV v' hv'
    by_cases hkey : bV = aV
    · rw [hkey] at hv'
      rw [hw.1] at hv'
      rw [← Option.some.inj hv']
      show WordWf (acctRowDeleted v.curr).info.balance
      rw [acctRowDeleted_info]
      exact hrel.wf aV v hrow
    · exact hrel.wf bV v' (by rw [← hframe bV hkey]; exact hv')

/-! ### Run shapes -/

theorem runS_k_was_created_hit (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (hs : Evm.HostState) (ss : SeqState)
    (h : hostAcctRow hs aV = some v) :
    runS (Evm.Functions.k_was_created aV) hs ss
      = .ok (v.curr.created, hs) ss := by
  refine runS_bind_ok (runS_k_aload_hit aV v hs ss h) ?_
  exact runS_pure _ _ _

theorem runS_k_is_selfdestructed_hit (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (hs : Evm.HostState) (ss : SeqState)
    (h : hostAcctRow hs aV = some v) :
    runS (Evm.Functions.k_is_selfdestructed aV) hs ss
      = .ok (v.curr.selfdestructed, hs) ss := by
  refine runS_bind_ok (runS_k_aload_hit aV v hs ss h) ?_
  exact runS_pure _ _ _

/-- **`k_selfdestruct` marks the row.** Both branches leave the same row:
the guard only avoids a redundant `assocPut`. -/
theorem runS_k_selfdestruct_hit (aV : Evm.Defs.address)
    (v : Evm.Defs.AcctValue) (hs : Evm.HostState) (ss : SeqState)
    (h : hostAcctRow hs aV = some v) :
    ∃ hs', runS (Evm.Functions.k_selfdestruct aV) hs ss = .ok ((), hs') ss
      ∧ HostAcctWritten hs hs' aV { v with curr := acctRowDeleted v.curr } := by
  by_cases hd : v.curr.selfdestructed = true
  · refine ⟨hs, ?_, ?_⟩
    · unfold Evm.Functions.k_selfdestruct
      refine runS_bind_ok (runS_k_aload_hit aV v hs ss h) ?_
      show runS (if (!v.curr.selfdestructed) = true then
          Evm.Functions.store_account aV (acctRowDeleted v.curr)
        else pure ()) hs ss = _
      rw [if_neg (by rw [hd]; decide)]
      exact runS_pure _ _ _
    · rw [acctRowDeleted_idem v.curr hd]
      simpa using hostAcctWritten_refl hs aV v h
  · refine ⟨hostAcctWrite hs aV v (acctRowDeleted v.curr), ?_,
      hostAcctWritten_write hs aV v (acctRowDeleted v.curr)⟩
    unfold Evm.Functions.k_selfdestruct
    refine runS_bind_ok (runS_k_aload_hit aV v hs ss h) ?_
    show runS (if (!v.curr.selfdestructed) = true then
        Evm.Functions.store_account aV (acctRowDeleted v.curr)
      else pure ()) hs ss = _
    rw [if_pos (by
      rw [show v.curr.selfdestructed = false from by simpa using hd]
      decide)]
    exact runS_store_account_hit aV v _ hs ss h

/-! ### The relation -/

/-- SpecRef's two address lists against the extraction's two row flags.
`outer` carries the deletions ancestor frames already marked, exactly as
[`LogRel`](Log.lean)'s `base` carries their logs: `accountsToDelete` is
frame-local and merged upward on success, while the row flag is global
within the transaction.

The `created` component is **one-directional** — every row the extraction
marks created, SpecRef's set contains — because `restoreTxState` keeps
`createdAccounts` across a revert and the extraction's journal does not
keep the flag. See the header for why that is not observable through
`SELFDESTRUCT`, and `CreatedAgree` for the converse where a step needs
it. -/
structure LifecycleRel (sRef : Machine) (hs : Evm.HostState)
    (outer : List Address) : Prop where
  created : ∀ (aV : Evm.Defs.address) (v : Evm.Defs.AcctValue),
    hostAcctRow hs aV = some v → v.curr.created = true →
      sRef.txState.createdAccounts.contains aV.toList = true
  deleted : ∀ (aV : Evm.Defs.address) (v : Evm.Defs.AcctValue),
    hostAcctRow hs aV = some v →
      v.curr.selfdestructed
        = (sRef.evm.accountsToDelete.contains aV.toList
            || outer.contains aV.toList)

/-- The converse of `LifecycleRel.created`, at one address. A step that
*branches* on "was this created in this transaction?" needs both
directions there, and the relation cannot supply this one — the states
where it fails are the reverted-`CREATE` states, which cannot reach
`SELFDESTRUCT` (header). Ledgered in `Assumptions.lean`. -/
def CreatedAgree (sRef : Machine) (hs : Evm.HostState)
    (aV : Evm.Defs.address) : Prop :=
  ∀ v : Evm.Defs.AcctValue, hostAcctRow hs aV = some v →
    v.curr.created = sRef.txState.createdAccounts.contains aV.toList

/-- SpecRef's mark: one `evm` field. -/
def specMarkDeleted (e : Evm) (a : Address) : Evm :=
  { e with accountsToDelete := setAdd e.accountsToDelete a }

/-- **The mark preserves the relation.** SpecRef appends the address to
`accountsToDelete`; the extraction sets the row's `selfdestructed`. -/
theorem lifecycleRel_mark {sRef : Machine} {hs hs' : Evm.HostState}
    {outer : List Address} (hrel : LifecycleRel sRef hs outer)
    (aV : Evm.Defs.address) (v : Evm.Defs.AcctValue)
    (hrow : hostAcctRow hs aV = some v)
    (hw : HostAcctWritten hs hs' aV { v with curr := acctRowDeleted v.curr }) :
    LifecycleRel { sRef with evm := specMarkDeleted sRef.evm aV.toList } hs'
      outer := by
  have hframe : ∀ bV : Evm.Defs.address, bV ≠ aV →
      hostAcctRow hs' bV = hostAcctRow hs bV := hw.2.1
  have hne' : ∀ bV : Evm.Defs.address, bV ≠ aV → bV.toList ≠ aV.toList :=
    fun bV hbV hc => hbV (Vector.toList_inj.mp hc)
  constructor
  case created =>
    intro bV v' hv' hc
    by_cases hkey : bV = aV
    · rw [hkey] at hv' ⊢
      rw [hw.1] at hv'
      exact hrel.created aV v hrow (by
        rw [← acctRowDeleted_created v.curr,
          show acctRowDeleted v.curr = v'.curr from by
            rw [← Option.some.inj hv']]
        exact hc)
    · exact hrel.created bV v' (by rw [← hframe bV hkey]; exact hv') hc
  case deleted =>
    intro bV v' hv'
    by_cases hkey : bV = aV
    · rw [hkey] at hv' ⊢
      rw [hw.1] at hv'
      rw [← Option.some.inj hv']
      show (acctRowDeleted v.curr).selfdestructed = _
      rw [acctRowDeleted_flag]
      show true = ((setAdd sRef.evm.accountsToDelete aV.toList).contains aV.toList
        || outer.contains aV.toList)
      rw [setAdd_contains_self]
      rfl
    · rw [hrel.deleted bV v' (by rw [← hframe bV hkey]; exact hv')]
      simp only [specMarkDeleted]
      rw [setAdd_contains_ne _ _ _ (hne' bV hkey)]

end EvmSpecsVerify
