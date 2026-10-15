#!/usr/bin/env python3
"""Draw a reproducible random sample of 2000 entries with 1000 < h <= 2000 from the list of
imaginary quadratic fields with h <= 2000 (paper, Section "Small discriminants", check (b)).

Usage: python3 -I random_check_h2000_sample.py LIST.txt.xz OUT.txt

LIST is lists/imq_h2000.txt.xz of the code repository (one line "d h" per field, increasing d).
The sample is drawn by reservoir sampling with a fixed seed, so it depends only on the list;
OUT gets the sampled lines in increasing order of d. random_check_h2000.gp checks them with PARI/GP.
"""
import lzma
import random
import sys

SEED = 20261015
SIZE = 2000


def run(path, out):
    rng = random.Random(SEED)
    sample = []
    seen = 0
    with lzma.open(path, "rt") as f:
        for line in f:
            d, h = map(int, line.split())
            if not 1000 < h <= 2000:
                continue
            seen += 1
            if len(sample) < SIZE:
                sample.append((d, h))
            else:
                j = rng.randrange(seen)
                if j < SIZE:
                    sample[j] = (d, h)
    sample.sort()
    with open(out, "w") as g:
        for d, h in sample:
            g.write(f"{d} {h}\n")
    print(f"entries with 1000 < h <= 2000: {seen}; sampled: {len(sample)}; seed {SEED}")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    run(sys.argv[1], sys.argv[2])
