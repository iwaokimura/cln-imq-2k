#!/bin/bash
# Comparison of the number of fields with odd class number h <= 1999 (h2000_table.txt, our unconditional list)
# with Holmin--Jones--Kurlberg--McLeman--Petersen, Exp. Math. 28 (2019) 233--254 (F(h) for odd h < 10^6,
# conditional on GRH): https://people.kth.se/~kurlberg/class_group_data/class_group_orders.txt
# Run: bash compare_hk2000.sh WORKDIR > compare_hk2000.txt
# WORKDIR: an empty scratch directory for the download (not committed: third-party data).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
W=$1
T=$here/h2000_table.txt
cd "$W"
curl -sfL -o cgo.txt https://people.kth.se/~kurlberg/class_group_data/class_group_orders.txt
echo "downloaded $(date -u +%Y-%m-%dT%H:%MZ); sha256:"
sha256sum cgo.txt
echo
echo "[HK] F(h) for odd h <= 1999 against h2000_table.txt"
grep -v '^#' cgo.txt | awk -F'\t' '$1 <= 2000' > hk2000.txt
awk 'NR==FNR {F[$1] = $2; next}
     ($1 % 2 == 1) {n++; s += $2; t += F[$1]; if (F[$1] != $2) {bad++; print "  DIFF h=" $1 " ours=" $2 " HK=" F[$1]}}
     END {print "  odd h compared: " n ", differences: " bad + 0 ", total fields ours " s ", HK " t;
          print (bad + 0 == 0 && n == 1000 ? "HK2000 COMPARE PASS" : "HK2000 COMPARE FAIL")}' hk2000.txt "$T"
