# Lean formalization

This directory is the Lean formalization for the paper *Imaginary quadratic fields of class number at most
2000* (Iwao Kimura). It proves Theorem 1 (the explicit zero gap) and Theorem 10 (the class number bounds)
of the paper. `PAPER-MAP.md` lists, for each statement of the paper, the Lean declaration that formalizes
it, with its file and line.

## What to read

The final theorems, which use only Mathlib definitions:

- `B4.ClassNumber.classNumber_gt_100`, …, `classNumber_gt_2000` in `B4ClassNumber.lean`
- `B4.Chi8.zero_gap_all`, `B4.Chi8.zero_gap_large`, `B4.Chi8.re_LFunction_pos` in `B4Chi8.lean`

The same statements, importing only Mathlib and proved by `sorry`, are in `Challenge/`. Comparator
checks that the proofs prove exactly these statements (`comparator/README.md`). Everything else is
checked by the Lean kernel.

## Building

You need [elan](https://github.com/leanprover/elan). `lean-toolchain` fixes the Lean version to 4.34.1.
The build needs about 10 GB of disk space.

```
lake exe cache get    # Mathlib's compiled files
lake build
```

On a 12-core machine the full build takes about 20 minutes. The build prints the axioms of each main
theorem; they are `propext`, `Classical.choice` and `Quot.sound`. Our files contain no `sorry`, no
`axiom` and no `native_decide`.

Some Linux systems need a larger `vm.max_map_count` for Mathlib. If the build fails with memory
mapping errors, raise it, for example with `sudo sysctl vm.max_map_count=1048576`.

## Layout

| Path | Contents |
|---|---|
| `B4*.lean` | our proof, 20 files |
| `vendor/` | upstream files the proof imports, copied from pinned commits (`vendor/README.md`, checked by `vendor/check.sh`) |
| `Challenge/`, `comparator/` | the Comparator challenges and how to run them |
| `B4Replay.lean` | kernel replay of the proof from an empty environment |
| `PAPER-MAP.md` | paper ↔ Lean |

The prefix `B4` and the labels "B-4 (i)", "B-4 (ii)", "B-4 (iii)" in the file headers name the stages
of the development; `PAPER-MAP.md` gives the paper's numbering.

The dependencies are Mathlib, LeanCert and LeanArchitect. `lakefile.lean` pins them to the same commits
as [openai/math](https://github.com/openai/math) at commit `301488868`.

The core of the argument comes from the Lean formalization of the preprint *Uniform exclusion of
Landau–Siegel zeros* in openai/math (`vendor/openai-math/`). We use its lemmas unchanged, not its final
theorem; see the paper, Section 7, and `PAPER-MAP.md`.

## Kernel replay

```
lake env lean --run B4Replay.lean
```

This collects the dependency closure of the final theorems, about 123,000 constants including the
parts of Lean's core library and Mathlib they use. It checks all of them again with the Lean kernel,
starting from an empty environment, and prints the axioms in the closure. It takes about 8 minutes.

## License

Our files are under the Apache License 2.0 (`../LICENSE`). The files in `vendor/` keep their upstream
licenses, which are all Apache 2.0 (`vendor/licenses/`).
