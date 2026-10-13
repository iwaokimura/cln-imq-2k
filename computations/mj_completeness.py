"""Completeness of the Mosunov--Jacobson files used (k = 0..KMAX): every fundamental discriminant occurs.

For each file cl{r}mod{m}.{k}.gz (format as in mj_extract.py) check that
  * every gap is >= 1, so the decoded |d| are strictly increasing,
  * every decoded |d| lies in [k*2^28, (k+1)*2^28) and -|d| is a fundamental discriminant,
  * the number of entries equals the number of fundamental -d with |d| = r mod m in that range
    (counted with an independent squarefree sieve).
Together these say that the file lists exactly the fundamental discriminants of its range.

Usage: python3 -I mj_completeness.py DATADIR KMAX > mj_completeness.txt
"""
import gzip
import math
import sys
from multiprocessing import Pool

CLASSES = [(3, 8), (7, 8), (4, 16), (8, 16)]
SF = None


def squarefree_table(bound):
    sf = bytearray([1]) * bound
    sf[0] = 0
    lim = math.isqrt(bound) + 1
    isp = bytearray([1]) * (lim + 1)
    for p in range(2, lim + 1):
        if isp[p]:
            isp[p * p :: p] = bytes(len(range(p * p, lim + 1, p)))
            sf[0 :: p * p] = bytes(len(range(0, bound, p * p)))
    return sf


def fundamental(d):
    if d % 4 == 3:
        return SF[d] == 1
    if d % 16 in (4, 8):
        return SF[d // 4] == 1
    return False


def expected(r, m, lo, hi):
    start = lo + ((r - lo) % m)
    if m == 8:
        return SF[start:hi:m].count(1)
    n = len(range(start, hi, m))
    return SF[start // 4 :: m // 4][:n].count(1)


def check(args):
    datadir, r, m, k = args
    lo, hi = k * 2**28, (k + 1) * 2**28
    d = lo + ((r - lo) % m)
    n = bad = 0
    first = True
    with gzip.open(f"{datadir}/cl{r}mod{m}.{k}.gz", "rt") as fh:
        for line in fh:
            g = int(line.split(None, 1)[0])
            if g < 1 and not (first and g == 0):
                bad += 1
            first = False
            d += m * g
            n += 1
            if not (lo <= d < hi and fundamental(d)):
                bad += 1
    e = expected(r, m, lo, hi)
    ok = bad == 0 and n == e
    return f"cl{r}mod{m}.{k}: entries {n}, fundamental in range {e}, bad {bad}: {'OK' if ok else 'FAIL'}", ok


def main():
    global SF
    datadir, kmax = sys.argv[1], int(sys.argv[2])
    SF = squarefree_table((kmax + 1) * 2**28)
    jobs = [(datadir, r, m, k) for k in range(kmax + 1) for r, m in CLASSES]
    with Pool(min(12, len(jobs))) as pool:
        res = pool.map(check, jobs)
    for line, _ in res:
        print(line)
    print("ALL FILES COMPLETE" if all(ok for _, ok in res) else "SOME FILES FAILED")


if __name__ == "__main__":
    main()
