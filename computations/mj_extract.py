"""Extract imaginary quadratic fields with h <= N from the Mosunov--Jacobson class-group files.

Data: LMFDB, https://www.lmfdb.org/NumberField/QuadraticImaginaryClassGroups (Mosunov--Jacobson,
Math. Comp. 85 (2016)); files cl{r}mod{m}.{k}.gz, kept outside the repository.
Format, determined by us and checked against PARI (see Section 4 of the paper): file k covers
k*2^28 <= |d| < (k+1)*2^28 for the fundamental |d| = r mod m; each line is
"gap  h  invariants", and |d| advances by m*gap from the residue-r start of the file.

Usage: python3 -I mj_extract.py DATADIR N KMAX OUT
Writes the sorted pairs "|d| h" with h <= N over files k = 0..KMAX, and per-file statistics
to stdout.
"""
import gzip
import sys

CLASSES = [(3, 8), (7, 8), (4, 16), (8, 16)]


def scan(path, r, m, k, N, out):
    start = k * 2**28
    d = start + ((r - start) % m)
    n = 0
    found = 0
    first = None
    with gzip.open(path, "rt") as fh:
        for line in fh:
            a, b = line.split(None, 2)[:2]
            d += m * int(a)
            if first is None:
                first = d
            h = int(b)
            n += 1
            if h <= N:
                out.append((d, h))
                found += 1
    if not (start <= first and d < start + 2**28):
        raise SystemExit(f"range check failed for {path}: first {first}, last {d}")
    return n, found, first, d


def main():
    datadir, N, kmax, outpath = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    out = []
    for k in range(kmax + 1):
        for r, m in CLASSES:
            path = f"{datadir}/cl{r}mod{m}.{k}.gz"
            n, found, first, last = scan(path, r, m, k, N, out)
            print(f"cl{r}mod{m}.{k}: entries {n}, first {first}, last {last}, h<={N}: {found}", flush=True)
    out.sort()
    with open(outpath, "w") as fh:
        for d, h in out:
            fh.write(f"{d} {h}\n")
    print(f"total h<={N}: {len(out)}, largest |d|: {out[-1][0] if out else None}")


if __name__ == "__main__":
    main()
