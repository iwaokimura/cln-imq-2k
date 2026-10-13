#!/usr/bin/env python3
"""Compare our list of fundamental discriminants with h <= 1000 (imq_h1000.txt.xz, lines "|D0| h")
with Cremona--Sutherland's cmdiscs1000.txt (line "h:[|D|, ...]" for ALL discriminants D < 0, orders
included, with h(D) = h; complete under GRH by their Prop. 19).

From our fundamental list we generate every D = f^2 D0 with h(D) <= 1000 by the class number formula
for orders (Cox, Thm 7.24; their (2.1)):
    h(f^2 D0) = h(D0) * f / [O_K^x : O^x] * prod_{p | f} (1 - (D0/p)/p),
with [O_K^x : O^x] = 3 (D0 = -3), 2 (D0 = -4), 1 otherwise (f >= 2), and compare the set of pairs
(|D|, h) with theirs. Equality means: their list is exactly the set of discriminants of orders in the
fields of our list with h <= 1000.

Usage: python3 -I compare_cs1000.py OUR_LIST.txt.xz cmdiscs1000.txt
"""
import lzma
import sys
from fractions import Fraction

HMAX = 1000


def kronecker(D0, p):
    """(D0/p) for a fundamental discriminant D0 < 0 and a prime p."""
    if p == 2:
        if D0 % 2 == 0:
            return 0
        return 1 if D0 % 8 == 1 else -1
    r = D0 % p
    if r == 0:
        return 0
    return 1 if pow(r, (p - 1) // 2, p) == 1 else -1


def prime_factors_table(n):
    spf = list(range(n + 1))
    for i in range(2, int(n ** 0.5) + 1):
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
    pf = [[] for _ in range(n + 1)]
    for m in range(2, n + 1):
        x, ps = m, []
        while x > 1:
            p = spf[x]
            ps.append(p)
            while x % p == 0:
                x //= p
        pf[m] = ps
    return pf


def phi(m, ps):
    r = m
    for p in ps:
        r = r // p * (p - 1)
    return r


def read_ours(path):
    fund = {}
    with lzma.open(path, "rt") as fh:
        for line in fh:
            d, h = line.split()
            fund[int(d)] = int(h)
    return fund


def read_cs(path):
    pairs = {}
    with open(path) as fh:
        for n, line in enumerate(fh, start=1):
            head, body = line.strip().split(":", 1)  # "h:[|D|, ...]"
            h = int(head)
            assert h == n, ("line order", n, h)
            for x in body.strip("[]").split(","):
                if x:
                    d = int(x)
                    if d in pairs:
                        raise SystemExit(f"duplicate |D| = {d} in cmdiscs1000.txt")
                    pairs[d] = h
    return pairs


def run():
    ours_path, cs_path = sys.argv[1], sys.argv[2]
    fund = read_ours(ours_path)
    cs = read_cs(cs_path)
    print(f"ours: {len(fund)} fundamental |D0| with h <= {HMAX}, max {max(fund)}")
    print(f"Cremona-Sutherland: {len(cs)} |D| with h <= {HMAX}, max {max(cs)} (h = {cs[max(cs)]})")

    # h(f^2 D0) >= h(D0) * phi(f) / w, so phi(f) <= 3 HMAX = 3000. Rosser-Schoenfeld (3.42):
    # phi(n) > n / (e^gamma llog n + 2.50637 / llog n) for n >= 3, which is > 3000 for all n > 40000
    # (the denominator is < 6.6 there and grows only like llog n); the assert re-checks (FMAX/2, FMAX].
    FMAX = 40000
    pf = prime_factors_table(FMAX)
    fs = sorted((phi(f, pf[f]), f) for f in range(2, FMAX + 1))
    assert min(ph for ph, f in fs if f > FMAX // 2) > 3 * HMAX, "FMAX too small"

    gen = {}
    for d0, h0 in fund.items():
        D0 = -d0
        gen[d0] = h0
        w = 3 if d0 == 3 else (2 if d0 == 4 else 1)
        bound = HMAX * w / h0  # need phi(f) <= bound
        for ph, f in fs:
            if ph > bound:
                break
            hh = Fraction(h0 * f, w)
            for p in pf[f]:
                hh *= 1 - Fraction(kronecker(D0, p), p)
            assert hh.denominator == 1, (d0, f, hh)
            if hh <= HMAX:
                d = f * f * d0
                assert d not in gen, ("collision", d)
                gen[d] = int(hh)
    print(f"generated from ours: {len(gen)} |D| with h <= {HMAX}, of which {len(fund)} fundamental")

    only_ours = sorted(set(gen) - set(cs))
    only_cs = sorted(set(cs) - set(gen))
    hdiff = sorted(d for d in set(gen) & set(cs) if gen[d] != cs[d])
    print(f"only in ours: {len(only_ours)} {only_ours[:10]}")
    print(f"only in Cremona-Sutherland: {len(only_cs)} {only_cs[:10]}")
    print(f"class number differs: {len(hdiff)} {hdiff[:10]}")
    cs_fund = sum(1 for d in cs if d in fund)
    print(f"fundamental entries of Cremona-Sutherland (= our list): {cs_fund}")
    for h in (1, 2, 100, 400, 425, 450, 475, 500, 1000):
        print(f"#S_{h} = {sum(1 for d in cs if cs[d] == h)} (C-S), {sum(1 for d in gen if gen[d] == h)} (ours)")
    ok = not only_ours and not only_cs and not hdiff
    print("CS1000 COMPARE PASS" if ok else "CS1000 COMPARE FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(run())
