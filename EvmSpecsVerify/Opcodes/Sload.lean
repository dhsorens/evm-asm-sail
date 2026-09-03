import EvmSpecsVerify.Opcodes.Shapes.Alu
import EvmSpecsVerify.Relations.Storage
import EvmSpecsVerify.Representation.EvmGas
import EvmSpecsVerify.Representation.EvmStack
import EvmSpecsVerify.Representation.SpecRefLemmas

/-!
# SLOAD

Warm/cold accounting (EIP-2929) and gas are proven outright: SpecRef's
`accessedStorageKeys` set tracks the extraction's epoch-stamped `warmSlots`
via [`WarmRel`](../Relations/Warm.lean), and the Amsterdam constants agree
on both sides (warm `100`, cold `3000` — `WARM_ACCESS`/`G_warm_access` and
`COLD_STORAGE_ACCESS`/`G_amsterdam_cold_storage_access`).

The **value read** is behind the ledgered [`SloadAgree`](#) hypothesis:
SpecRef reads through the transaction-state journals (`getStorage`), while
the extraction's `k_sload` misses through its tx/block caches into a
keccak-hashed witness-trie walk (`stateless_storage_by_key`) — opaque
crypto plus world-state machinery that is out of scope until the world
tranche relates the two storage representations. `SloadAgree` states
exactly that the two reads return the same word (and that `k_sload` leaves
the stack frames, warm stamps, and epoch alone); the world tranche
discharges it.

Both sides pop before charging, so there is no MM-5 divergence. Order does
differ *within* a step: the extraction stamps the slot warm before its
kernel read, SpecRef marks (cold only) before charging — hence `SloadAgree`
quantifies the kernel read over the ambient `warmSlots`.

Reachable outcomes: success (warm/cold) / stack underflow / out-of-gas
(warm/cold; overflow unreachable for 1-in/1-out).
-/

open private pcAdd warmStorageKey from
  EvmAsm.Stateless.SpecRef.InstructionsCore
open private writeListAt assocGet assocPut from Evm.HostAxioms

set_option maxHeartbeats 1000000

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## The ledgered read-agreement hypothesis -/

/-- **Ledgered hypothesis** (see `Assumptions.lean`): the two sides' storage
reads agree for the popped slot `x` of the owning account (host address
vector `aV`). Covers SpecRef's `getStorage` (journalled tracker) and the
extraction's `k_sload` (tx/block caches over the witness trie); the world
tranche discharges it by relating the storage representations. -/
def SloadAgree (sRef : Machine) (hs : Evm.HostState) (ss : SeqState)
    (aV : Evm.Defs.address) (x : Nat) : Prop :=
  ∃ (v : U256) (ts' : TransactionState) (entry : Evm.Defs.StorageValue)
    (hostAfter : List (Evm.Defs.StorageKey × Nat) → Evm.HostState),
    WordWf v ∧
    entry.curr = v ∧
    (getStorage sRef.evm.message.currentTarget (toBeBytes32 x)).run
      sRef.txState = .ok (v, ts') ∧
    (∀ ws, runS (Evm.Functions.k_sload aV x) { hs with warmSlots := ws } ss =
      .ok (entry, hostAfter ws) ss) ∧
    (∀ ws, (hostAfter ws).stackFrames = hs.stackFrames) ∧
    (∀ ws, (hostAfter ws).warmSlots = ws) ∧
    (∀ ws, (hostAfter ws).warmEpoch = hs.warmEpoch)

/-- **`SloadAgree` on the transaction-overlay regime.** A slot the
transaction has already written is a `storage_tx_get` hit, so `k_sload`
returns the stored row without touching any state, and SpecRef's
`getStorage` finds the same value in its first probe. Both misses (block
overlay, witness trie) stay in the world tranche —
see [`StorageRel`](../Relations/Storage.lean). -/
theorem sloadAgree_of_storageRel (sRef : Machine) (hs : Evm.HostState)
    (ss : SeqState) (aV : Evm.Defs.address) (x : Nat) (hx : WordWf x)
    (e : Evm.Defs.StorageValue) (hrow : hostStorageSlot hs aV x = some e)
    (haddr : aV.toList = sRef.evm.message.currentTarget)
    (hsr : StorageRel sRef.txState hs) :
    SloadAgree sRef hs ss aV x := by
  refine ⟨e.curr, specStorageReadOf sRef.txState aV.toList (toBeBytes32 x), e,
    fun ws => { hs with warmSlots := ws }, hsr.wf aV x hx e hrow, rfl, ?_,
    fun ws => runS_k_sload_hit aV x e _ ss hrow, fun _ => rfl, fun _ => rfl,
    fun _ => rfl⟩
  rw [← haddr]
  exact runTx_getStorage_tx_hit _ _ _ _ (hsr.curr aV x hx e hrow)

/-! ## Small warm-set helpers -/

/-- Record-update projections (`show`-free to avoid whnf blowups). -/
private theorem hostState_set_stackFrames_warmSlots (h : Evm.HostState)
    (f : List (List word)) :
    ({ h with stackFrames := f } : Evm.HostState).warmSlots = h.warmSlots :=
  rfl

private theorem hostState_set_stackFrames_warmEpoch (h : Evm.HostState)
    (f : List (List word)) :
    ({ h with stackFrames := f } : Evm.HostState).warmEpoch = h.warmEpoch :=
  rfl

/-! ## SpecRef run shapes -/

theorem runR_iSload_underflow (s : Machine) (hstack : s.evm.stack = []) :
    runR iSload s = .ok (.error .stackUnderflow, s) := by
  simp only [iSload]
  exact runR_bind_err (runR_stackPop_nil s hstack)

theorem runR_iSload_warm_success (s : Machine) (x v : U256)
    (rest : List U256) (ts' : TransactionState)
    (hstack : s.evm.stack = x :: rest)
    (hwarm : s.evm.accessedStorageKeys.contains
      (s.evm.message.currentTarget, toBeBytes32 x) = true)
    (hgas : GasCosts.WARM_ACCESS ≤ s.evm.gasLeft)
    (hread : (getStorage s.evm.message.currentTarget (toBeBytes32 x)).run
      s.txState = .ok (v, ts'))
    (hlim : s.evm.stack.length ≤ 1024) :
    runR iSload s =
      .ok (.ok (), { s with
        evm := { s.evm with
          stack := v :: rest
          gasLeft := s.evm.gasLeft - GasCosts.WARM_ACCESS
          regularGasUsed := s.evm.regularGasUsed + GasCosts.WARM_ACCESS
          pc := s.evm.pc + 1 }
        txState := ts' }) := by
  have hlen : rest.length ≠ 1024 := by
    rw [hstack] at hlim; simp at hlim; omega
  simp only [iSload, pcAdd]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_isWarmStorageKey _ _) ?_
  rw [if_pos hwarm]
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_liftTx_ok _ _ v ts' hread) ?_
  refine runR_bind_ok (runR_stackPush _ v (by simpa using hlen)) ?_
  exact runR_modifyEvm _ _

theorem runR_iSload_cold_success (s : Machine) (x v : U256)
    (rest : List U256) (ts' : TransactionState)
    (hstack : s.evm.stack = x :: rest)
    (hcold : s.evm.accessedStorageKeys.contains
      (s.evm.message.currentTarget, toBeBytes32 x) = false)
    (hgas : GasCosts.COLD_STORAGE_ACCESS ≤ s.evm.gasLeft)
    (hread : (getStorage s.evm.message.currentTarget (toBeBytes32 x)).run
      s.txState = .ok (v, ts'))
    (hlim : s.evm.stack.length ≤ 1024) :
    runR iSload s =
      .ok (.ok (), { s with
        evm := { s.evm with
          stack := v :: rest
          gasLeft := s.evm.gasLeft - GasCosts.COLD_STORAGE_ACCESS
          regularGasUsed :=
            s.evm.regularGasUsed + GasCosts.COLD_STORAGE_ACCESS
          pc := s.evm.pc + 1
          accessedStorageKeys := setAdd s.evm.accessedStorageKeys
            (s.evm.message.currentTarget, toBeBytes32 x) }
        txState := ts' }) := by
  have hlen : rest.length ≠ 1024 := by
    rw [hstack] at hlim; simp at hlim; omega
  simp only [iSload, pcAdd, warmStorageKey]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_isWarmStorageKey _ _) ?_
  rw [if_neg (by simpa using hcold)]
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  refine runR_bind_ok (runR_charge_gas _ _ hgas) ?_
  refine runR_bind_ok (runR_liftTx_ok _ _ v ts' hread) ?_
  refine runR_bind_ok (runR_stackPush _ v (by simpa using hlen)) ?_
  exact runR_modifyEvm _ _

theorem runR_iSload_warm_oog (s : Machine) (x : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: rest)
    (hwarm : s.evm.accessedStorageKeys.contains
      (s.evm.message.currentTarget, toBeBytes32 x) = true)
    (hgas : s.evm.gasLeft < GasCosts.WARM_ACCESS) :
    runR iSload s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with stack := rest } }) := by
  simp only [iSload]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_isWarmStorageKey _ _) ?_
  rw [if_pos hwarm]
  exact runR_bind_err (runR_charge_gas_oog _ _ hgas)

theorem runR_iSload_cold_oog (s : Machine) (x : U256) (rest : List U256)
    (hstack : s.evm.stack = x :: rest)
    (hcold : s.evm.accessedStorageKeys.contains
      (s.evm.message.currentTarget, toBeBytes32 x) = false)
    (hgas : s.evm.gasLeft < GasCosts.COLD_STORAGE_ACCESS) :
    runR iSload s =
      .ok (.error .outOfGas,
        { s with evm := { s.evm with
            stack := rest
            accessedStorageKeys := setAdd s.evm.accessedStorageKeys
              (s.evm.message.currentTarget, toBeBytes32 x) } }) := by
  simp only [iSload, warmStorageKey]
  refine runR_bind_ok (runR_stackPop_cons s x rest hstack) ?_
  refine runR_bind_ok (runR_getEvm _) ?_
  refine runR_bind_ok (runR_isWarmStorageKey _ _) ?_
  rw [if_neg (by simpa using hcold)]
  refine runR_bind_ok (runR_modifyEvm _ _) ?_
  exact runR_bind_err (runR_charge_gas_oog _ _ hgas)

/-! ## `Evm` run shapes -/

open Evm.Functions in
/-- The Amsterdam SLOAD charge, warm or cold. -/
theorem runS_sload_cost (warmb : Bool) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hfork : Amsterdam ≤ prof.1) :
    runS (Evm.Functions.sload_cost warmb) hs ss =
      .ok ((if warmb then G_warm_access
        else G_amsterdam_cold_storage_access : Nat), hs) ss := by
  obtain ⟨fork, t, mx, dn, cl, il, ptl, prl, tbl, rd, bl, ttl, trl, epf⟩ := prof
  simp only at hfork
  simp only [Evm.Functions.sload_cost, runS_bind, runS_readReg _ _ _ _ hprof]
  cases warmb
  · simp only [Bool.false_eq_true, if_false]
    simp only [ProtocolProfileFields.fork, decide_eq_true_eq]
    rw [if_pos (by simpa using hfork)]
    exact runS_pure _ _ _
  · simp only [if_true]
    exact runS_pure _ _ _

open Evm.Functions in
/-- The dispatch equation for SLOAD. -/
theorem sload_dispatch (pc_in : Nat) (top : StackTop) (mem : EvmMemorySlice)
    (g : Nat) :
    Evm.Functions.execute_opcode (.SLOAD ()) pc_in top mem g =
      Evm.Functions.execute_sload top g >>= fun p =>
        pure (pc_in, p.1, mem, p.2) := rfl

open Evm.Functions in
theorem runS_sload_body_ok (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hfork : Amsterdam ≤ prof.1)
    (hmsg : ss.regs.get? Register.message = some msg)
    (warmb : Bool)
    (hwarmb : decide (hs.warmEpoch ≤ (assocGet hs.warmSlots
      ({ addr := msg.address, slot := x } : Evm.Defs.StorageKey)).getD 0)
      = warmb)
    (hgas : (if warmb then G_warm_access
      else G_amsterdam_cold_storage_access : Nat) ≤ g)
    (entry : Evm.Defs.StorageValue)
    (hostAfter : List (Evm.Defs.StorageKey × Nat) → Evm.HostState)
    (hrun : ∀ ws, runS (k_sload msg.address x) { hs with warmSlots := ws } ss
      = .ok (entry, hostAfter ws) ss)
    (hframes : ∀ ws, (hostAfter ws).stackFrames = hs.stackFrames) :
    runS (Evm.Functions.execute_sload top g) hs ss =
      .ok ((top, g - (if warmb then G_warm_access
          else G_amsterdam_cold_storage_access : Nat)),
        { hostAfter (assocPut hs.warmSlots
            ({ addr := msg.address, slot := x } : Evm.Defs.StorageKey)
            hs.warmEpoch) with
          stackFrames := writeListAt l (top.toNat - 1) entry.curr :: frest })
        ss := by
  have hn : top.toNat = rest.length + 1 := by simpa using htop
  have hret1 : (top - BitVec.ofNat 64 1).toNat = top.toNat - 1 :=
    cursor_retreat_toNat top (by omega)
  simp only [Evm.Functions.execute_sload]
  refine runS_bind_ok (runS_pop top hs ss l frest x rest hframe hpfx htop) ?_
  refine runS_bind_ok (runS_self_addr msg hs ss hmsg) ?_
  refine runS_bind_ok
    (show runS (k_slot_is_warm msg.address x) hs ss = .ok (warmb, hs) ss from by
      rw [show Evm.Functions.k_slot_is_warm msg.address x
        = Evm.Functions.storage_is_warm msg.address x from rfl,
        runS_storage_is_warm, hwarmb]) ?_
  refine runS_bind_ok (runS_sload_cost warmb hs ss prof hprof hfork) ?_
  refine runS_bind_ok (runS_charge_ok g _ hs ss hgas) ?_
  rw [if_neg (by simp)]
  refine runS_bind_ok (runS_storage_mark_warm msg.address x hs ss) ?_
  refine runS_bind_ok (hrun _) ?_
  refine runS_bind_ok
    (runS_push_word (top - BitVec.ofNat 64 1) entry.curr _ ss l frest
      (by rw [hframes]; exact hframe) (by rw [hret1]; omega)) ?_
  rw [BitVec.sub_add_cancel, hret1]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_sload_body_oog (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (warmb : Bool)
    (hwarmb : decide (hs.warmEpoch ≤ (assocGet hs.warmSlots
      ({ addr := msg.address, slot := x } : Evm.Defs.StorageKey)).getD 0)
      = warmb)
    (hgas : g < (if warmb then G_warm_access
      else G_amsterdam_cold_storage_access : Nat)) :
    runS (Evm.Functions.execute_sload top g) hs ss =
      .ok ((top - BitVec.ofNat 64 1, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute_sload]
  refine runS_bind_ok (runS_pop top hs ss l frest x rest hframe hpfx htop) ?_
  refine runS_bind_ok (runS_self_addr msg hs ss hmsg) ?_
  refine runS_bind_ok
    (show runS (k_slot_is_warm msg.address x) hs ss = .ok (warmb, hs) ss from by
      rw [show Evm.Functions.k_slot_is_warm msg.address x
        = Evm.Functions.storage_is_warm msg.address x from rfl,
        runS_storage_is_warm, hwarmb]) ?_
  refine runS_bind_ok (runS_sload_cost warmb hs ss prof hprof hfork) ?_
  refine runS_bind_ok
    (runS_charge_oog g _ hs ss prof sp msg hprof hsp hmsg hfork hgas) ?_
  rw [if_pos (by simp)]
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_sload_ok (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hfork : Amsterdam ≤ prof.1)
    (hmsg : ss.regs.get? Register.message = some msg)
    (warmb : Bool)
    (hwarmb : decide (hs.warmEpoch ≤ (assocGet hs.warmSlots
      ({ addr := msg.address, slot := x } : Evm.Defs.StorageKey)).getD 0)
      = warmb)
    (hgas : (if warmb then G_warm_access
      else G_amsterdam_cold_storage_access : Nat) ≤ g)
    (entry : Evm.Defs.StorageValue)
    (hostAfter : List (Evm.Defs.StorageKey × Nat) → Evm.HostState)
    (hrun : ∀ ws, runS (k_sload msg.address x) { hs with warmSlots := ws } ss
      = .ok (entry, hostAfter ws) ss)
    (hframes : ∀ ws, (hostAfter ws).stackFrames = hs.stackFrames) :
    runS (Evm.Functions.execute (.SLOAD ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, g - (if warmb then G_warm_access
          else G_amsterdam_cold_storage_access : Nat)),
        { hostAfter (assocPut hs.warmSlots
            ({ addr := msg.address, slot := x } : Evm.Defs.StorageKey)
            hs.warmEpoch) with
          stackFrames := writeListAt l (top.toNat - 1) entry.curr :: frest })
        ss := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.SLOAD ()) = pure (1, 1) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 1 hs ss (by simp at htop; omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, sload_dispatch]
  refine runS_bind_ok
    (runS_sload_body_ok top g hs ss l frest x rest hframe hpfx htop hlim
      prof msg hprof hfork hmsg warmb hwarmb hgas entry hostAfter hrun
      hframes) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_sload_oog (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (l : List word) (frest : List (List word)) (x : word) (rest : List word)
    (hframe : hs.stackFrames = l :: frest)
    (hpfx : l.take top.toNat = (x :: rest).reverse)
    (htop : top.toNat = (x :: rest).length)
    (hlim : top.toNat ≤ 1024)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (warmb : Bool)
    (hwarmb : decide (hs.warmEpoch ≤ (assocGet hs.warmSlots
      ({ addr := msg.address, slot := x } : Evm.Defs.StorageKey)).getD 0)
      = warmb)
    (hgas : g < (if warmb then G_warm_access
      else G_amsterdam_cold_storage_access : Nat)) :
    runS (Evm.Functions.execute (.SLOAD ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top - BitVec.ofNat 64 1, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .OutOfGas } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.SLOAD ()) = pure (1, 1) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_ok g top 1 1 hs ss (by simp at htop; omega)
      (by simp [Evm.Functions.STACK_LIMIT]; omega)) ?_
  rw [dif_pos rfl, sload_dispatch]
  refine runS_bind_ok
    (runS_sload_body_oog top g hs ss l frest x rest hframe hpfx htop prof sp
      msg hprof hsp hmsg hfork warmb hwarmb hgas) ?_
  exact runS_pure _ _ _

open Evm.Functions in
theorem runS_execute_sload_underflow (pc_in : Nat) (top : StackTop) (g : Nat)
    (mem : EvmMemorySlice) (hs : Evm.HostState) (ss : SeqState)
    (prof : ExecutionProfile) (sp : state_gas_spill) (msg : Evm.Defs.Message)
    (hprof : ss.regs.get? Register.k_execution_profile = some prof)
    (hsp : ss.regs.get? Register.state_gas_spilled = some sp)
    (hmsg : ss.regs.get? Register.message = some msg)
    (hfork : Amsterdam ≤ prof.1)
    (hunder : top.toNat < 1) :
    runS (Evm.Functions.execute (.SLOAD ()) pc_in top mem g) hs ss =
      .ok ((pc_in, top, mem, GAS_ZERO), hs)
        { ss with regs := haltRegs ss msg .StackUnderflow } := by
  simp only [Evm.Functions.execute,
    show Evm.Functions.opcode_stack_effect (.SLOAD ()) = pure (1, 1) from rfl]
  refine runS_bind_ok (runS_pure _ _ _) ?_
  refine runS_bind_ok
    (runS_validate_stack_underflow g top 1 1 hs ss prof sp msg hprof hsp hmsg
      hfork hunder) ?_
  rw [dif_neg (by simp)]
  exact runS_pure _ _ _

/-! ## The step equivalence -/

/-- Success post-relation for SLOAD: the ALU-slice relation plus the warm
storage-key relation on the post-states. -/
def SloadPost (mem : EvmMemorySlice) (sR' : Machine) (step : EvmStep)
    (hs' : Evm.HostState) (ss' : SeqState) : Prop :=
  BasePost mem sR' step hs' ss' ∧ WarmRel sR' hs'

open Evm.Functions in
/-- **SLOAD, all reachable outcomes.** Warm/cold accounting and gas are
unconditional; the value read is supplied by the ledgered [`SloadAgree`]
hypothesis (see the module docstring), and `haddr` ties the extraction's
message register to SpecRef's storage owner. -/
theorem sload_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice) (pc_in : Nat)
    (hrel : StateRel sRef top g hs ss)
    (hwrel : WarmRel sRef hs)
    (hpc : pc_in = sRef.evm.pc + 1)
    (haddr : ∀ msg : Evm.Defs.Message,
      ss.regs.get? Register.message = some msg →
      msg.address.toList = sRef.evm.message.currentTarget)
    (hagree : ∀ (msg : Evm.Defs.Message) (x : U256) (rest : List U256),
      ss.regs.get? Register.message = some msg →
      sRef.evm.stack = x :: rest →
      SloadAgree sRef hs ss msg.address x) :
    StepResultRel (SloadPost mem) (runR iSload sRef)
      (runS (Evm.Functions.execute (.SLOAD ()) pc_in top mem g) hs ss) := by
  obtain ⟨hstackR, hgasR, hrunR, hrunE, ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩ := hrel
  obtain ⟨⟨l, frest, hframe, hpfx, hlen⟩, htop, hlim, hwfS⟩ := hstackR
  obtain ⟨hlive, hres, hsp⟩ := hgasR
  match hS : sRef.evm.stack with
  | [] =>
    rw [hS] at hpfx htop
    rw [runR_iSload_underflow sRef hS,
      runS_execute_sload_underflow pc_in top g mem hs ss prof
        sRef.evm.stateGasSpilled msg hprof hsp hmsg hfork
        (by simp at htop; omega)]
    exact StepResultRel.halted ErrorRel.stackUnderflow
      (haltRegs_frame_status ss msg .StackUnderflow)
  | x :: rest =>
    rw [hS] at hpfx htop hlim hwfS
    have hwx : WordWf x := hwfS x (by simp)
    have hax : msg.address.toList = sRef.evm.message.currentTarget :=
      haddr msg hmsg
    obtain ⟨v, ts', entry, hostAfter, hwfv, hcurr, hspec, hrun, hframes,
      hslots, hepoch⟩ := hagree msg x rest hmsg hS
    have hiff := hwrel.rel msg.address x hwx
    rw [hax] at hiff
    have hlim' : top.toNat ≤ 1024 := by simp at htop hlim; omega
    cases hwc : sRef.evm.accessedStorageKeys.contains
        (sRef.evm.message.currentTarget, toBeBytes32 x) with
    | true =>
      have hle := hiff.mp hwc
      have hwb : decide (hs.warmEpoch ≤ (assocGet hs.warmSlots
          ({ addr := msg.address, slot := x } :
            Evm.Defs.StorageKey)).getD 0) = true := decide_eq_true hle
      by_cases hg : sRef.evm.gasLeft < GasCosts.WARM_ACCESS
      · rw [runR_iSload_warm_oog sRef x rest hS hwc hg,
          runS_execute_sload_oog pc_in top g mem hs ss l frest x rest hframe
            hpfx htop hlim' prof sRef.evm.stateGasSpilled msg hprof hsp hmsg
            hfork true hwb (by rw [if_pos rfl, hlive]; exact hg)]
        exact StepResultRel.halted ErrorRel.outOfGas
          (haltRegs_frame_status ss msg .OutOfGas)
      · push Not at hg
        rw [runR_iSload_warm_success sRef x v rest ts' hS hwc hg
            hspec (by rw [hS]; exact hlim),
          runS_execute_sload_ok pc_in top g mem hs ss l frest x rest hframe
            hpfx htop hlim' prof msg hprof hfork hmsg true hwb
            (by rw [if_pos rfl, hlive]; exact hg) entry hostAfter
            hrun hframes]
        rw [if_pos rfl, hcurr]
        refine StepResultRel.success ⟨⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
          ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, hpc, rfl⟩, ?_⟩
        · exact pop_push_post_stack top _ l frest x rest v
            (hostState_set_stackFrames_frames _ _) hpfx htop hlim hlen hwfS
            hwfv
        · exact ⟨by rw [hlive]; rfl, hres, hsp⟩
        · refine ⟨fun bV w hw => ?_⟩
          rw [hostState_set_stackFrames_warmSlots,
            hostState_set_stackFrames_warmEpoch, hslots, hepoch]
          have hmark := warm_after_mark sRef.evm.accessedStorageKeys
            hs.warmSlots hs.warmEpoch msg.address x hwx hwrel.rel bV w hw
          rw [hax, setAdd_eq_of_contains _ _ hwc] at hmark
          exact hmark
    | false =>
      have hnle : ¬ hs.warmEpoch ≤ (assocGet hs.warmSlots
          ({ addr := msg.address, slot := x } :
            Evm.Defs.StorageKey)).getD 0 := fun hle => by
        rw [hiff.mpr hle] at hwc
        cases hwc
      have hwb : decide (hs.warmEpoch ≤ (assocGet hs.warmSlots
          ({ addr := msg.address, slot := x } :
            Evm.Defs.StorageKey)).getD 0) = false := decide_eq_false hnle
      by_cases hg : sRef.evm.gasLeft < GasCosts.COLD_STORAGE_ACCESS
      · rw [runR_iSload_cold_oog sRef x rest hS hwc hg,
          runS_execute_sload_oog pc_in top g mem hs ss l frest x rest hframe
            hpfx htop hlim' prof sRef.evm.stateGasSpilled msg hprof hsp hmsg
            hfork false hwb (by rw [if_neg (by simp), hlive]; exact hg)]
        exact StepResultRel.halted ErrorRel.outOfGas
          (haltRegs_frame_status ss msg .OutOfGas)
      · push Not at hg
        rw [runR_iSload_cold_success sRef x v rest ts' hS hwc hg
            hspec (by rw [hS]; exact hlim),
          runS_execute_sload_ok pc_in top g mem hs ss l frest x rest hframe
            hpfx htop hlim' prof msg hprof hfork hmsg false hwb
            (by rw [if_neg (by simp), hlive]; exact hg) entry
            hostAfter hrun hframes]
        rw [if_neg (by simp), hcurr]
        refine StepResultRel.success ⟨⟨⟨?_, ?_, ⟨hrunR.1, hrunR.2⟩, hrunE,
          ⟨prof, hprof, hfork⟩, ⟨msg, hmsg⟩⟩, hpc, rfl⟩, ?_⟩
        · exact pop_push_post_stack top _ l frest x rest v
            (hostState_set_stackFrames_frames _ _) hpfx htop hlim hlen hwfS
            hwfv
        · exact ⟨by rw [hlive]; rfl, hres, hsp⟩
        · refine ⟨fun bV w hw => ?_⟩
          rw [hostState_set_stackFrames_warmSlots,
            hostState_set_stackFrames_warmEpoch, hslots, hepoch]
          have hmark := warm_after_mark sRef.evm.accessedStorageKeys
            hs.warmSlots hs.warmEpoch msg.address x hwx hwrel.rel bV w hw
          rw [hax] at hmark
          exact hmark

end EvmSpecsVerify
