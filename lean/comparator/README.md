# Comparator

[Comparator](https://github.com/leanprover/comparator) checks that a proof proves exactly the statement
of a challenge, using no axioms beyond a permitted list. It builds the proof inside a sandbox, exports
the statements of the challenge and the proof, compares them, and has the proof checked by the Lean
kernel. It can also have the proof checked by [nanoda](https://github.com/ammkrn/nanoda_lib), an
independent kernel written in Rust.

## The challenges

| Config | Challenge (only `import Mathlib`) | Solution | Theorems |
|---|---|---|---|
| `B4ClassNumber.json` | `Challenge/B4ClassNumber.lean` | `B4ClassNumber.lean` | `B4.ClassNumber.classNumber_gt_{100,200,500,1000,2000}` |
| `B4ZeroGap.json` | `Challenge/B4ZeroGap.lean` | `B4Chi8.lean` | `B4.Chi8.re_LFunction_pos`, `zero_gap_all`, `zero_gap_large` |

The `*_nanoda.json` configs are the same, with the nanoda check enabled. The permitted axioms are
`propext`, `Classical.choice` and `Quot.sound`.

## Running

Comparator needs three tools, and a fourth for the nanoda check. Versions we used:

| Tool | Version |
|---|---|
| [comparator](https://github.com/leanprover/comparator) | commit `d03acab` |
| [lean4export](https://github.com/leanprover/lean4export) | commit `076e8e5` |
| [landrun](https://github.com/Zouuup/landrun) | v0.1.18 |
| [nanoda_lib](https://github.com/ammkrn/nanoda_lib) | commit `3a24072` |

Build comparator and lean4export with `lake build`, nanoda with `cargo build --release`, and landrun with
Go. Then, from `lean/`:

```
export COMPARATOR=/path/to/comparator/.lake/build/bin/comparator
export COMPARATOR_LEAN4EXPORT=/path/to/lean4export/.lake/build/bin/lean4export
export COMPARATOR_LANDRUN=/path/to/landrun/landrun
export COMPARATOR_NANODA=/path/to/nanoda_lib/target/release/nanoda_bin
bash comparator/run.sh B4ClassNumber_nanoda
bash comparator/run.sh B4ZeroGap_nanoda
```

`run.sh` runs Comparator under `systemd-run --user`, with Unix sockets forbidden, as Comparator's README
recommends. A successful run ends with "Your solution is okay!".

As a negative test, change a constant in a challenge, for example `5811/10000000` to `5812/10000000` in
`Challenge/B4ZeroGap.lean`. Comparator then rejects the proof, because the statements do not match.
