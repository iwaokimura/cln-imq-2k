# Imaginary quadratic fields of class number at most 2000

Code, formal proofs and data for the paper *Imaginary quadratic fields of class number at most 2000* by
Iwao Kimura, [arXiv:2610.21511](https://arxiv.org/abs/2610.21511) [math.NT].

The paper determines all imaginary quadratic fields with class number h ≤ 2000, without assuming any
Riemann hypothesis. There are 16,453,493 of them, and the largest |d| is 1,062,350,083.

| Directory | Contents |
|---|---|
| `lean/` | Lean 4 proof of the explicit zero gap (Theorem 1) and of the class number bounds (Theorem 10): `lean/README.md`. The map from the paper to the Lean declarations is `lean/PAPER-MAP.md`. |
| `qsieve/` | the sieve that excludes the discriminants above the class group tables (Section 5), with its tests (`qsieve/TESTING.md`) and the logs of the runs |
| `computations/` | the PARI/GP and Python scripts cited in the paper, with their outputs (`.txt`): `computations/README.md` |
| `lists/` | the lists of all fields with h ≤ 1000 and h ≤ 2000, with checksums: `lists/README.md` |

The proof has three parts:

1. **Theorem 10, proved in Lean.** Every imaginary quadratic field with log |d_K| ≥ T_N has class number
   greater than N.
2. **The sieve.** It excludes the fields with 6·2^28 ≤ |d_K| < e^(T_2000).
3. **The class group tables of Mosunov and Jacobson.** They cover the fields below 6·2^28. The tables
   are distributed by the [LMFDB](https://www.lmfdb.org) and are not included here;
   `computations/mj_data.sha256` gives the checksums of the files we used.

## AI contributions

Parts of this work were done with AI systems: the Lean code, the sieve program and the scripts were
written with Claude (Anthropic). The
preprint *Uniform exclusion of Landau–Siegel zeros* and its Lean formalization (`lean/vendor/openai-math/`)
were produced by an OpenAI model. Section 8 of the paper says which parts, and what was checked
independently and how.

## License

Copyright 2026 Iwao Kimura.

- The lists in `lists/` and the tables derived from them (`computations/h1000_table.txt`,
  `computations/h2000_table.txt`, `computations/mj_h200_list.txt`): CC0 1.0 (`lists/LICENSE`).
- The files in `lean/vendor/`: their upstream licenses, all Apache 2.0 (`lean/vendor/licenses/`).
- Everything else: Apache License 2.0 (`LICENSE`).
