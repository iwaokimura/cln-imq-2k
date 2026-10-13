"""Cross-check: class numbers h(-d) <= 100 from the LMFDB Postgres mirror
(table nf_fields, imaginary quadratic fields) against our PARI/GP recomputation of Watkins' Table 4.

Run (uv venv with psycopg2-binary):
    <venv>/bin/python -I lmfdb_check.py > lmfdb_check.txt
Reads watkins_h100_list.txt (written by watkins_table4.gp) from this directory.
"""
import os
import sys

import psycopg2

DMAX = 2_250_000  # LMFDB nf_fields is complete for |D| <= 2250002 (checked 2026-10-08)


def main() -> int:
    here = os.path.dirname(os.path.abspath(__file__))
    conn = psycopg2.connect(host="devmirror.lmfdb.xyz", port=5432, dbname="lmfdb",
                            user="lmfdb", password="lmfdb", connect_timeout=20)
    cur = conn.cursor()
    cur.execute("select count(*) from nf_fields where degree=2 and r2=1 and disc_abs <= %s", (DMAX,))
    total = cur.fetchone()[0]
    cur.execute("select disc_abs, class_number from nf_fields "
                "where degree=2 and r2=1 and disc_abs <= %s and class_number <= 100", (DMAX,))
    lm = {(int(d), int(h)) for d, h in cur.fetchall()}
    print(f"LMFDB nf_fields: imaginary quadratic fields with |D| <= {DMAX}: {total}")
    ours = set()
    with open(os.path.join(here, "watkins_h100_list.txt")) as f:
        for line in f:
            d, h = map(int, line.split())
            if d <= DMAX:
                ours.add((d, h))
    only_lm, only_gp = sorted(lm - ours), sorted(ours - lm)
    bad = len(only_lm) + len(only_gp)
    print(f"pairs (d, h) with h <= 100, d <= {DMAX}: LMFDB {len(lm)}, GP {len(ours)}")
    print(f"only in LMFDB: {only_lm[:20]}  only in GP: {only_gp[:20]}")
    print("LMFDB CROSS-CHECK OK" if bad == 0 else "LMFDB CROSS-CHECK FAILED")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
