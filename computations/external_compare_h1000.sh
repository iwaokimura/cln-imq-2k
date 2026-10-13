#!/bin/bash
# External comparison of the h <= 1000 list (h1000_table.txt, imq_h1000.txt.xz) with published data.
#   [HK]  Holmin--Kurlberg, F(h) for odd h < 10^6 (conditional on GRH), data of Holmin--Jones--Kurlberg--
#         McLeman--Petersen, Exp. Math. 28 (2019) 233--254:
#         https://people.kth.se/~kurlberg/class_group_data/class_group_orders.txt
#   [OEIS] A046125 (number of negative fundamental discriminants with class number n, n <= 100) and
#         A038552 (largest squarefree k with h(Q(sqrt(-k))) = n, n <= 100), b-files.
# Run: bash external_compare_h1000.sh WORKDIR > external_compare_h1000.txt
# WORKDIR: an empty scratch directory for the downloads (not committed: third-party data).
# LIST: the h <= 1000 list (default ../lists/imq_h1000.txt.xz).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
W=$1
T=$here/h1000_table.txt
LIST=${LIST:-$(dirname "$0")/../lists/imq_h1000.txt.xz}
cd "$W"
curl -sfL -o cgo.txt https://people.kth.se/~kurlberg/class_group_data/class_group_orders.txt
curl -sfL -o b046125.txt https://oeis.org/A046125/b046125.txt
curl -sfL -o b038552.txt https://oeis.org/A038552/b038552.txt
echo "downloaded $(date -u +%Y-%m-%dT%H:%MZ); sha256:"
sha256sum cgo.txt b046125.txt b038552.txt

echo
echo "[HK] F(h) for odd h <= 999 against h1000_table.txt"
grep -v '^#' cgo.txt | awk -F'\t' '$1 <= 1000' > hk1000.txt
awk 'NR==FNR {F[$1] = $2; next}
     ($1 % 2 == 1) {n++; s += $2; t += F[$1]; if (F[$1] != $2) {bad++; print "  DIFF h=" $1 " ours=" $2 " HK=" F[$1]}}
     END {print "  odd h compared: " n ", differences: " bad + 0 ", total fields ours " s ", HK " t}' hk1000.txt "$T"

echo
echo "[OEIS A046125] number of fields for h <= 100"
awk 'NR==FNR {F[$1] = $2; next}
     ($1 <= 100) {n++; if (F[$1] != $2) {bad++; print "  DIFF h=" $1}}
     END {print "  h compared: " n ", differences: " bad + 0}' b046125.txt "$T"

echo
echo "[OEIS A038552] largest squarefree k (k = |d| for odd d, |d|/4 otherwise) for h <= 100"
xz -dc "$LIST" |
  awk '($2 <= 100) {k = ($1 % 4 == 0) ? $1 / 4 : $1; if (k > m[$2]) m[$2] = k}
       END {for (h = 1; h <= 100; h++) print h, m[h]}' > ours_sqfree.txt
awk 'NR==FNR {A[$1] = $2; next}
     {n++; if (A[$1] != $2) {bad++; print "  DIFF h=" $1 " ours=" $2 " OEIS=" A[$1]}}
     END {print "  h compared: " n ", differences: " bad + 0}' b038552.txt ours_sqfree.txt
echo "EXTERNAL COMPARE DONE"
