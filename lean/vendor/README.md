# Vendored upstream files

This directory holds copies of the upstream Lean files that the proof imports, and nothing else: the
import closure of `B4*.lean` outside Mathlib, LeanCert and LeanArchitect. Those three are ordinary Lake
dependencies (`lakefile.lean`), pinned to the same commits as openai/math.

The copies replace dependencies on openai/math, PrimeNumberTheoremAnd, TauCeti and AINTLIB. Built as
Lake packages, these would pull in many unrelated packages, and they need patches applied in place.

| Directory | Upstream | Commit | Changes |
|---|---|---|---|
| `openai-math/` | [openai/math](https://github.com/openai/math), `lean/OAI/NumberTheory/SiegelZeros` (254 files) | `301488868beec11bfd897168433b0a64f5258559` | none |
| `PrimeNumberTheoremAnd/` | [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (22 files) | `c39a751132c88b6e8080b74c74023fd95b3d8be0` | the compatibility patch of openai/math, `lean/patches/PrimeNumberTheoremAnd-lean4341.patch` at the commit above |
| `TauCeti/` | [TauCeti](https://github.com/TauCetiProject/TauCeti) (51 files) | `3bed7e37f3c504a99e8c07e9f309540812a7aa90` | `patches/TauCeti-pinned-mathlib.patch` (ours) |
| `AINTLIB/` | [AINTLIB](https://github.com/CBirkbeck/AINTLIB), `projects/FltRegularBernoulli` (2 files) | `160e446617a2168c34c95bbe7a76c4105b392434` | none (the openai/math patch for AINTLIB does not touch these files) |

Notes on the changes:

- **PrimeNumberTheoremAnd.** openai/math applies the compatibility patch when it fetches its
  dependencies. The patch also adds the files under `PrimeNumberTheoremAnd/SiegelZeros/`, with their copyright notices
  (`NOTICE.md` there).
- **TauCeti.** At the pinned commit, TauCeti does not build against the pinned Mathlib. Our patch
  changes three lemma calls: two lemmas were renamed in Mathlib, and one call now passes its arguments by
  name. No statement changes.

All four packages are under the Apache License 2.0; their license texts are in `licenses/`.

## Checking the copies

`SHA256SUMS` lists the checksums of all 329 files. To re-create every file from the upstream
repositories and compare it byte for byte, run:

```
bash vendor/check.sh
```

It needs git and network access. It clones the four repositories at the commits above, applies the
patches listed above, and compares each file.
