# evm-asm-sail

Connecting [`evm-asm`](https://github.com/Verified-zkEVM/evm-asm) and
[`evm-sail`](https://github.com/frisitano/evm-sail): one Lean 4 project holding both
evm-asm and the Lean extraction of the evm-sail EVM specification, and (the point of it
all) the equivalence proofs between them.

## Proof coverage dashboard

**[Live coverage report](https://derekhsorensen.com/evm-asm-sail/)** — SpecRef ↔ `Evm`
proof progress (opcode statuses, expandable theorem links, comparison-matrix components).

Regenerate after matrix edits (updates `docs/index.html` + the Cursor canvas from the same
snapshot; push `docs/index.html` on `main` to publish the site):

```sh
python3 scripts/refresh-proof-coverage-canvas.py
```

## Why

- **evm-asm** is a verified macro assembler in Lean 4 building a zkEVM stateless block
  validator on RV64. Its theorems are proven against an *internal, untrusted* Lean port of
  the execution-specs ("SpecRef") — and its README explicitly asks for an external Lean
  specification to break that circularity.
- **evm-sail** is a formal, executable EVM specification in Sail, written as a complement
  to evm-asm. It ships a committed Lean extraction (`extractions/lean/`) with an executable
  host contract, validated byte-exact against the EELS reference over the tests-zkevm
  fixture corpus.

Proving evm-asm's SpecRef equivalent to the evm-sail extraction gives evm-asm the external
spec it asks for, and puts evm-sail's theorem-prover backend to work.

## Layout

| path | what |
|---|---|
| `EvmAsmSail/` | the proofs connecting SpecRef ↔ `Evm` (the extraction) |
| `docs/index.html` | generated site root ([live](https://derekhsorensen.com/evm-asm-sail/); sync with canvas) |
| `docs/comparison-matrix.md` | living SpecRef ↔ `Evm` semantic coverage matrix |
| `docs/opcode-coverage.md` | living per-opcode proof coverage matrix |
| `scripts/refresh-proof-coverage-canvas.py` | refresh HTML report + Cursor canvas from the two docs |
| `extraction/evm-sail` | pinned submodule; its `extractions/lean/src` is required by path |
| `scripts/setup.sh` | post-clone provisioning (submodule + Sail Lean support library) |
| `PROGRESS.md` | live plan and status |

Dependencies (no vendoring): `EvmAsm` is a Lake git dependency pinned by revision;
the `evm` package is upstream's committed generated model, consumed in place from the
submodule. Everything is built on evm-asm's toolchain (`v4.30.0-rc1`); the extraction
pins `v4.29.0` upstream but builds unchanged on the newer toolchain.

## Building

```sh
./scripts/setup.sh   # once after cloning
lake build
```

Regenerating the extraction itself is upstream's business (`make extract-lean` in
evm-sail, which requires their custom Sail compiler); this repo consumes the committed
generated sources at the submodule pin.

## Status

Early bootstrap — see [PROGRESS.md](PROGRESS.md). Coverage: [derekhsorensen.com/evm-asm-sail](https://derekhsorensen.com/evm-asm-sail/).
