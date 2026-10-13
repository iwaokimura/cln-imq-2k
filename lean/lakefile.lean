import Lake

open Lake DSL

/-!
Lean formalization for "Imaginary quadratic fields of class number at most 2000" (I. Kimura).

The files `B4*.lean` are ours. The directory `vendor/` holds the upstream files they import, copied
from pinned commits (Apache License 2.0); see `vendor/README.md` for the commits, the patches applied,
and `vendor/check.sh`, which re-creates `vendor/` from the upstream repositories and compares.
The Lean options of each library are those of its upstream package, so that the build is the same.
-/

package B4 where
  version := v!"1.0.0"

-- The same pins as openai/math, `lean/lakefile.lean` at commit 301488868.
-- Declare shared dependencies last: Lake resolves later requirements first.
require LeanArchitect from git
  "https://github.com/hanwenzhu/LeanArchitect.git" @ "468e8f58fb4ad6e6ad672a08da6d0d0531e95a97"
require leancert from git
  "https://github.com/alerad/leancert.git" @ "7f91b6eb3567437f6cfac03ed279706603ee22f4"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

/-- openai/math, `lean/OAI/NumberTheory/SiegelZeros` (commit 301488868), unchanged. -/
lean_lib OAI where
  srcDir := "vendor/openai-math"
  globs := #[.andSubmodules `OAI.NumberTheory.SiegelZeros]
  leanOptions := #[⟨`autoImplicit, false⟩]

/-- PrimeNumberTheoremAnd (commit c39a751) with the compatibility patch of openai/math. -/
lean_lib PrimeNumberTheoremAnd where
  srcDir := "vendor/PrimeNumberTheoremAnd"
  globs := #[.andSubmodules `PrimeNumberTheoremAnd]
  leanOptions := #[⟨`autoImplicit, false⟩]

/-- TauCeti (commit 3bed7e3) with `vendor/patches/TauCeti-pinned-mathlib.patch` (three lemma calls adapted). -/
lean_lib TauCeti where
  srcDir := "vendor/TauCeti"
  globs := #[.andSubmodules `TauCeti]
  leanOptions := #[⟨`weak.linter.mathlibStandardSet, true⟩, ⟨`weak.linter.style.longFile, (1500 : Nat)⟩,
    ⟨`weak.linter.style.longFileDefValue, (1500 : Nat)⟩, ⟨`weak.linter.style.header, true⟩,
    ⟨`warningAsError, true⟩]

/-- AINTLIB (commit 160e446), `projects/FltRegularBernoulli`, unchanged. -/
lean_lib BernoulliRegular where
  srcDir := "vendor/AINTLIB"
  globs := #[.andSubmodules `BernoulliRegular]
  leanOptions := #[⟨`pp.unicode.fun, true⟩, ⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩]

/-- Our files. The final theorems are in `B4ClassNumber` and `B4Chi8`. -/
@[default_target] lean_lib B4 where
  roots := #[`B4ExplicitBias, `B4MasterAlgebra, `B4ZeroGap, `B4PrimeMass, `B4Analytic,
    `B4ElementaryGap, `B4Interval, `B4Chain, `B4Certificates, `B4LSeriesCont, `B4ZetaEM, `B4Sign,
    `B4Hyperbola, `B4L1, `B4ClassBound, `B4ClassCert, `B4QuadSplit, `B4QuadZeta, `B4ClassNumber,
    `B4Chi8]

/-- The Comparator challenges: the statements of the final theorems with `sorry`, importing only Mathlib.
Not a default target; Comparator builds them (`comparator/README.md`). -/
lean_lib Challenge where
  globs := #[.submodules `Challenge]
