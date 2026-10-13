# The lists

| File | Fields | Largest d |
|---|---|---|
| `imq_h1000.txt.xz` | all 4,115,897 imaginary quadratic fields with class number h ≤ 1000 | 227,932,027 |
| `imq_h2000.txt.xz` | all 16,453,493 imaginary quadratic fields with class number h ≤ 2000 | 1,062,350,083 |

Each line is `d h(-d)`: here d = |D| for the fundamental discriminant D < 0 of the field Q(√D), and
h(-d) is its class number. The lines are in increasing order of d. The files are compressed with xz.

`SHA256SUMS` gives the checksums of the uncompressed files; they are also printed in the paper. To
check them:

```
xz -dk imq_h1000.txt.xz imq_h2000.txt.xz && sha256sum -c SHA256SUMS
```

The completeness of the lists is the main result of the paper, *Imaginary quadratic fields of class
number at most 2000*.

The class numbers come from the class group tables of Mosunov and Jacobson (Math. Comp. 85 (2016)), as
distributed by the LMFDB. The fields beyond these tables are excluded by the sieve in `../qsieve/`. The
scripts that extract the lists and check them are in `../computations/`. The tables themselves are not
redistributed here.

The lists are dedicated to the public domain under CC0 1.0 (`LICENSE`).
