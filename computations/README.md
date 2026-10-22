# Computations

The scripts cited in the paper, with their outputs (`.txt`), and the scripts and data they read. GP
scripts run with `gp -q script.gp < /dev/null > script.txt` from this directory (the first lines of each
file give the command). The scripts need PARI/GP and Python 3.

## Explicit constants (Sections 2 and 3)

| File | Contents | Cited in |
|---|---|---|
| `effective_c2.gp` | functions for the explicit bound of (1-β) log q; read by the next three scripts | |
| `certify_c2.gp`, `.txt` | certified constants with the bounds of Rosser and Schoenfeld | Remark after Proposition 6 |
| `certify_c2_lean.gp`, `.txt` | the same for exactly the statement proved in Lean | |
| `lean_grid.gp`, `.txt` | the 314 intervals of the proof of Theorem 1, their parameters and constants; writes `../lean/B4Certificates.lean` | proof of Theorem 1, Remark after Proposition 6, Section 7 |
| `lean_h_cert.gp`, `.txt` | the numerical step of Proposition 9 for each N; writes `../lean/B4ClassCert.lean` | Section 3, Section 7 |
| `qrh_cert.gp`, `.txt` | Proposition 9 under a zero-free half-plane Re s > 31/32 (h > 2000 for log d ≥ 27.2, h > 10^5 for log d ≥ 35.4) | Remark after Theorem 10 |

`lean_grid.gp` and `lean_h_cert.gp` generate Lean files. The Lean kernel checks those files, so the
generators play no role in their correctness. `lean_grid.gp` also writes `lean_grid_c.gp` (grid data, not
used here).

## The tables of Mosunov and Jacobson (Section 4)

The tables are not included; they are available from the
[LMFDB](https://www.lmfdb.org/NumberField/QuadraticImaginaryClassGroups). `mj_data.sha256` gives the
SHA-256 checksums of the 24 files we used.

| File | Contents |
|---|---|
| `mj_extract.py` | extracts the fields with h ≤ N; the output lists are in `../lists/` |
| `mj_extract_h2000.txt`, `mj_extract_h1000.txt`, `mj_extract_h200.txt` | its per-file statistics for N = 2000, 1000, 200 |
| `mj_completeness.py`, `.txt` | checks that the files list every fundamental discriminant of their range |
| `mj_h200_list.txt` | the fields with h ≤ 200 (read by `../qsieve/postproc_test.gp`) |
| `h_table.sh` | the per-h table of a list: h, the number of fields, the largest \|d\| |
| `h1000_table.txt`, `h2000_table.txt` | its output for the two lists |
| `watkins_table4.gp`, `.txt` | recomputes Watkins' Table 4 (h ≤ 100) and compares; writes `watkins_table4_computed.txt` and `watkins_h100_list.txt` |
| `random_check_h2000_sample.py` | draws 2000 random entries with 1000 < h ≤ 2000 from `../lists/imq_h2000.txt.xz` (fixed seed): `python3 -I random_check_h2000_sample.py ../lists/imq_h2000.txt.xz random_check_h2000_sample.txt` |
| `random_check_h2000.gp`, `.txt` | checks them with `isfundamental` and `qfbclassno` (check (b) of Section 4) |

## The sieve and the Lean thresholds (Section 5)

| File | Contents |
|---|---|
| `lean_threshold_match.gp`, `.txt` | the ranges of the tables and the sieve runs meet the thresholds T_N of Theorem 10 |

## Comparisons (Section 6)

These scripts download the external data or read a local copy, and print its checksum. The external
data are not included.

| File | Compared with |
|---|---|
| `external_compare_h1000.sh`, `.txt` | Holmin–Jones–Kurlberg–McLeman–Petersen (odd h ≤ 999) and OEIS A046125, A038552 |
| `lmfdb_check.py`, `.txt` | the LMFDB (h ≤ 100) |
| `compare_cs1000.py`, `.txt` | Cremona–Sutherland (h ≤ 1000) |
| `compare_hk2000.sh`, `.txt` | Holmin–Jones–Kurlberg–McLeman–Petersen (odd h ≤ 1999) |
| `compare_gglm2000.py`, `.txt` | Garcia–Grenié–Lee–Molteni (h ≤ 2000): `python3 -I compare_gglm2000.py classes-list-2000.txt ../lists/imq_h2000.txt.xz`, the first file from https://sites.unimi.it/molteni/research/class_numbers/ |
