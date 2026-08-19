import EvmSpecsVerify.Opcodes.Shapes.EnvPusher
import EvmSpecsVerify.Representation.AddressWord

/-!
# The block-environment pushers

COINBASE, TIMESTAMP, NUMBER, PREVRANDAO, GASLIMIT, CHAINID, BASEFEE,
SLOTNUM — all derived through `envPush_step_equiv`
([`Shapes/EnvPusher.lean`](Shapes/EnvPusher.lean)). Per-opcode content:
the `k_env` field read (`runS_k_env_*`, off the `k_header` /
`k_chain_id` registers; `k_env` reads `k_tx` first regardless of field,
so `htx` is threaded everywhere) and the header-field tie to SpecRef's
`blockEnv` — fragments of the future `BlockEnvRel`, established at frame
entry in M3. COINBASE goes through the `address_to_word` codec (wf for
free); the numeric fields are codec-free and their word bounds are
hypothesized like `hwfv` (SSZ-bounded u64s / words on the extraction
side; SpecRef never states them). MM-5 applies to the double-fault
states of the whole family. Reachable outcomes, each opcode: success /
stack overflow / OOG / MM-5 double fault.
-/

namespace EvmSpecsVerify

open EvmAsm.Stateless.SpecRef
open Evm.Defs

/-! ## `k_env` field reads -/

open Evm.Functions in
theorem runS_k_env_coinbase (txp : TxEnv) (hdr : BlockHeader)
    (hs : Evm.HostState) (ss : SeqState)
    (htx : ss.regs.get? Register.k_tx = some txp)
    (hhdr : ss.regs.get? Register.k_header = some hdr) :
    runS (Evm.Functions.k_env EnvField.F_Coinbase) hs ss =
      .ok (address_to_word hdr.fee_recipient, hs) ss := by
  obtain ⟨lim, tx⟩ := txp
  simp only [Evm.Functions.k_env, runS_bind, runS_readReg _ _ _ _ htx,
    runS_readReg _ _ _ _ hhdr, runS_pure]

open Evm.Functions in
theorem runS_k_env_timestamp (txp : TxEnv) (hdr : BlockHeader)
    (hs : Evm.HostState) (ss : SeqState)
    (htx : ss.regs.get? Register.k_tx = some txp)
    (hhdr : ss.regs.get? Register.k_header = some hdr) :
    runS (Evm.Functions.k_env EnvField.F_Timestamp) hs ss =
      .ok (hdr.timestamp, hs) ss := by
  obtain ⟨lim, tx⟩ := txp
  simp only [Evm.Functions.k_env, Evm.Functions.word_of_block_timestamp,
    Evm.Functions.u256, runS_bind, runS_readReg _ _ _ _ htx,
    runS_readReg _ _ _ _ hhdr, runS_pure]

open Evm.Functions in
theorem runS_k_env_number (txp : TxEnv) (hdr : BlockHeader)
    (hs : Evm.HostState) (ss : SeqState)
    (htx : ss.regs.get? Register.k_tx = some txp)
    (hhdr : ss.regs.get? Register.k_header = some hdr) :
    runS (Evm.Functions.k_env EnvField.F_Number) hs ss =
      .ok (hdr.number, hs) ss := by
  obtain ⟨lim, tx⟩ := txp
  simp only [Evm.Functions.k_env, Evm.Functions.word_of_block_number,
    Evm.Functions.u256, runS_bind, runS_readReg _ _ _ _ htx,
    runS_readReg _ _ _ _ hhdr, runS_pure]

open Evm.Functions in
theorem runS_k_env_prevrandao (txp : TxEnv) (hdr : BlockHeader)
    (hs : Evm.HostState) (ss : SeqState)
    (htx : ss.regs.get? Register.k_tx = some txp)
    (hhdr : ss.regs.get? Register.k_header = some hdr) :
    runS (Evm.Functions.k_env EnvField.F_PrevRandao) hs ss =
      .ok (hdr.prev_randao, hs) ss := by
  obtain ⟨lim, tx⟩ := txp
  simp only [Evm.Functions.k_env, runS_bind, runS_readReg _ _ _ _ htx,
    runS_readReg _ _ _ _ hhdr, runS_pure]

open Evm.Functions in
theorem runS_k_env_gaslimit (txp : TxEnv) (hdr : BlockHeader)
    (hs : Evm.HostState) (ss : SeqState)
    (htx : ss.regs.get? Register.k_tx = some txp)
    (hhdr : ss.regs.get? Register.k_header = some hdr) :
    runS (Evm.Functions.k_env EnvField.F_GasLimit) hs ss =
      .ok (hdr.gas_limit, hs) ss := by
  obtain ⟨lim, tx⟩ := txp
  simp only [Evm.Functions.k_env, Evm.Functions.u256, runS_bind,
    runS_readReg _ _ _ _ htx, runS_readReg _ _ _ _ hhdr, runS_pure]

open Evm.Functions in
theorem runS_k_env_chainid (txp : TxEnv) (cid : chain_identifier)
    (hs : Evm.HostState) (ss : SeqState)
    (htx : ss.regs.get? Register.k_tx = some txp)
    (hcid : ss.regs.get? Register.k_chain_id = some cid) :
    runS (Evm.Functions.k_env EnvField.F_ChainId) hs ss =
      .ok (cid, hs) ss := by
  obtain ⟨lim, tx⟩ := txp
  simp only [Evm.Functions.k_env, Evm.Functions.word_of_chain_identifier,
    Evm.Functions.u256, runS_bind, runS_readReg _ _ _ _ htx,
    runS_readReg _ _ _ _ hcid, runS_pure]

open Evm.Functions in
theorem runS_k_env_basefee (txp : TxEnv) (hdr : BlockHeader)
    (hs : Evm.HostState) (ss : SeqState)
    (htx : ss.regs.get? Register.k_tx = some txp)
    (hhdr : ss.regs.get? Register.k_header = some hdr) :
    runS (Evm.Functions.k_env EnvField.F_BaseFee) hs ss =
      .ok (hdr.base_fee, hs) ss := by
  obtain ⟨lim, tx⟩ := txp
  simp only [Evm.Functions.k_env, runS_bind, runS_readReg _ _ _ _ htx,
    runS_readReg _ _ _ _ hhdr, runS_pure]

open Evm.Functions in
theorem runS_k_env_slotnum (txp : TxEnv) (hdr : BlockHeader)
    (hs : Evm.HostState) (ss : SeqState)
    (htx : ss.regs.get? Register.k_tx = some txp)
    (hhdr : ss.regs.get? Register.k_header = some hdr) :
    runS (Evm.Functions.k_env EnvField.F_SlotNumber) hs ss =
      .ok (hdr.slot_number, hs) ss := by
  obtain ⟨lim, tx⟩ := txp
  simp only [Evm.Functions.k_env, Evm.Functions.word_of_slot_number,
    Evm.Functions.u256, runS_bind, runS_readReg _ _ _ _ htx,
    runS_readReg _ _ _ _ hhdr, runS_pure]

/-! ## The step equivalences -/

open Evm.Functions in
/-- **COINBASE, all reachable outcomes.** `hcb` ties the header's fee
recipient to SpecRef's coinbase; the pushed word's bound is the
`address_to_word` range (free). -/
theorem coinbase_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat) (txp : TxEnv) (hdr : BlockHeader)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (htx : ss.regs.get? Register.k_tx = some txp)
    (hhdr : ss.regs.get? Register.k_header = some hdr)
    (hcb : hdr.fee_recipient.toList = sRef.evm.message.blockEnv.coinbase) :
    StepResultRel (BasePost mem) (runR iCoinbase sRef)
      (runS (Evm.Functions.execute (.COINBASE ()) pc_in top mem g)
        hs ss) :=
  envPush_step_equiv (.COINBASE ()) EnvField.F_Coinbase iCoinbase
    GasCosts.OPCODE_COINBASE
    (fun e => bytesBEtoNat e.message.blockEnv.coinbase)
    rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩
    sRef top g hs ss mem pc_in hrel hpc
    (by rw [runS_k_env_coinbase txp hdr hs ss htx hhdr,
      address_to_word_eq, hcb])
    (by show WordWf (bytesBEtoNat sRef.evm.message.blockEnv.coinbase)
        rw [← hcb, ← address_to_word_eq]
        exact address_to_word_wf hdr.fee_recipient)

open Evm.Functions in
/-- **TIMESTAMP, all reachable outcomes.** `htime` ties the header
timestamp; `hwf` is the SSZ u64 bound, hypothesized. -/
theorem timestamp_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat) (txp : TxEnv) (hdr : BlockHeader)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (htx : ss.regs.get? Register.k_tx = some txp)
    (hhdr : ss.regs.get? Register.k_header = some hdr)
    (htime : hdr.timestamp = sRef.evm.message.blockEnv.time)
    (hwf : WordWf sRef.evm.message.blockEnv.time) :
    StepResultRel (BasePost mem) (runR iTimestamp sRef)
      (runS (Evm.Functions.execute (.TIMESTAMP ()) pc_in top mem g)
        hs ss) :=
  envPush_step_equiv (.TIMESTAMP ()) EnvField.F_Timestamp iTimestamp
    GasCosts.OPCODE_TIMESTAMP (fun e => e.message.blockEnv.time)
    rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩
    sRef top g hs ss mem pc_in hrel hpc
    (by rw [runS_k_env_timestamp txp hdr hs ss htx hhdr, htime]) hwf

open Evm.Functions in
/-- **NUMBER, all reachable outcomes.** `hnum` ties the header number;
`hwf` is the SSZ u64 bound, hypothesized. -/
theorem number_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat) (txp : TxEnv) (hdr : BlockHeader)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (htx : ss.regs.get? Register.k_tx = some txp)
    (hhdr : ss.regs.get? Register.k_header = some hdr)
    (hnum : hdr.number = sRef.evm.message.blockEnv.number)
    (hwf : WordWf sRef.evm.message.blockEnv.number) :
    StepResultRel (BasePost mem) (runR iNumber sRef)
      (runS (Evm.Functions.execute (.NUMBER ()) pc_in top mem g) hs ss) :=
  envPush_step_equiv (.NUMBER ()) EnvField.F_Number iNumber
    GasCosts.OPCODE_NUMBER (fun e => e.message.blockEnv.number)
    rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩
    sRef top g hs ss mem pc_in hrel hpc
    (by rw [runS_k_env_number txp hdr hs ss htx hhdr, hnum]) hwf

open Evm.Functions in
/-- **PREVRANDAO, all reachable outcomes.** `hpr` ties the header's
randao word to SpecRef's 32-byte decode; `hwf` is the word bound,
hypothesized (the extraction's field is a word by construction). -/
theorem prevrandao_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat) (txp : TxEnv) (hdr : BlockHeader)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (htx : ss.regs.get? Register.k_tx = some txp)
    (hhdr : ss.regs.get? Register.k_header = some hdr)
    (hpr : hdr.prev_randao
      = bytesBEtoNat sRef.evm.message.blockEnv.prevRandao)
    (hwf : WordWf (bytesBEtoNat sRef.evm.message.blockEnv.prevRandao)) :
    StepResultRel (BasePost mem) (runR iPrevrandao sRef)
      (runS (Evm.Functions.execute (.PREVRANDAO ()) pc_in top mem g)
        hs ss) :=
  envPush_step_equiv (.PREVRANDAO ()) EnvField.F_PrevRandao iPrevrandao
    GasCosts.OPCODE_PREVRANDAO
    (fun e => bytesBEtoNat e.message.blockEnv.prevRandao)
    rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩
    sRef top g hs ss mem pc_in hrel hpc
    (by rw [runS_k_env_prevrandao txp hdr hs ss htx hhdr, hpr]) hwf

open Evm.Functions in
/-- **GASLIMIT, all reachable outcomes.** `hgl` ties the header gas
limit; `hwf` is the SSZ bound, hypothesized. -/
theorem gaslimit_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat) (txp : TxEnv) (hdr : BlockHeader)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (htx : ss.regs.get? Register.k_tx = some txp)
    (hhdr : ss.regs.get? Register.k_header = some hdr)
    (hgl : hdr.gas_limit = sRef.evm.message.blockEnv.blockGasLimit)
    (hwf : WordWf sRef.evm.message.blockEnv.blockGasLimit) :
    StepResultRel (BasePost mem) (runR iGaslimit sRef)
      (runS (Evm.Functions.execute (.GASLIMIT ()) pc_in top mem g)
        hs ss) :=
  envPush_step_equiv (.GASLIMIT ()) EnvField.F_GasLimit iGaslimit
    GasCosts.OPCODE_GASLIMIT (fun e => e.message.blockEnv.blockGasLimit)
    rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩
    sRef top g hs ss mem pc_in hrel hpc
    (by rw [runS_k_env_gaslimit txp hdr hs ss htx hhdr, hgl]) hwf

open Evm.Functions in
/-- **CHAINID, all reachable outcomes.** `hci` ties the `k_chain_id`
register; `hwf` is the u64 bound, hypothesized. -/
theorem chainid_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat) (txp : TxEnv) (cid : chain_identifier)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (htx : ss.regs.get? Register.k_tx = some txp)
    (hcid : ss.regs.get? Register.k_chain_id = some cid)
    (hci : cid = sRef.evm.message.blockEnv.chainId)
    (hwf : WordWf sRef.evm.message.blockEnv.chainId) :
    StepResultRel (BasePost mem) (runR iChainid sRef)
      (runS (Evm.Functions.execute (.CHAINID ()) pc_in top mem g) hs ss) :=
  envPush_step_equiv (.CHAINID ()) EnvField.F_ChainId iChainid
    GasCosts.OPCODE_CHAINID (fun e => e.message.blockEnv.chainId)
    rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩
    sRef top g hs ss mem pc_in hrel hpc
    (by rw [runS_k_env_chainid txp cid hs ss htx hcid, hci]) hwf

open Evm.Functions in
/-- **BASEFEE, all reachable outcomes.** `hbf` ties the header base fee;
`hwf` is the word bound, hypothesized. -/
theorem basefee_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat) (txp : TxEnv) (hdr : BlockHeader)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (htx : ss.regs.get? Register.k_tx = some txp)
    (hhdr : ss.regs.get? Register.k_header = some hdr)
    (hbf : hdr.base_fee = sRef.evm.message.blockEnv.baseFeePerGas)
    (hwf : WordWf sRef.evm.message.blockEnv.baseFeePerGas) :
    StepResultRel (BasePost mem) (runR iBasefee sRef)
      (runS (Evm.Functions.execute (.BASEFEE ()) pc_in top mem g) hs ss) :=
  envPush_step_equiv (.BASEFEE ()) EnvField.F_BaseFee iBasefee
    GasCosts.OPCODE_BASEFEE (fun e => e.message.blockEnv.baseFeePerGas)
    rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩
    sRef top g hs ss mem pc_in hrel hpc
    (by rw [runS_k_env_basefee txp hdr hs ss htx hhdr, hbf]) hwf

open Evm.Functions in
/-- **SLOTNUM, all reachable outcomes.** `hsn` ties the header slot
number; `hwf` is the u64 bound, hypothesized. -/
theorem slotnum_step_equiv (sRef : Machine) (top : StackTop) (g : Nat)
    (hs : Evm.HostState) (ss : SeqState) (mem : EvmMemorySlice)
    (pc_in : Nat) (txp : TxEnv) (hdr : BlockHeader)
    (hrel : StateRel sRef top g hs ss)
    (hpc : pc_in = sRef.evm.pc + 1)
    (htx : ss.regs.get? Register.k_tx = some txp)
    (hhdr : ss.regs.get? Register.k_header = some hdr)
    (hsn : hdr.slot_number = sRef.evm.message.blockEnv.slotNumber)
    (hwf : WordWf sRef.evm.message.blockEnv.slotNumber) :
    StepResultRel (BasePost mem) (runR iSlotnum sRef)
      (runS (Evm.Functions.execute (.SLOTNUM ()) pc_in top mem g) hs ss) :=
  envPush_step_equiv (.SLOTNUM ()) EnvField.F_SlotNumber iSlotnum
    GasCosts.OPCODE_SLOTNUM (fun e => e.message.blockEnv.slotNumber)
    rfl rfl ⟨rfl, fun _ _ _ _ => rfl⟩
    sRef top g hs ss mem pc_in hrel hpc
    (by rw [runS_k_env_slotnum txp hdr hs ss htx hhdr, hsn]) hwf

end EvmSpecsVerify
