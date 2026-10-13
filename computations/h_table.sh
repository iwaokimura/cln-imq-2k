#!/bin/bash
# Per-h table of a list: for each h = 1..N, the number of imaginary quadratic fields with class number h
# and the largest |d| among them. Lines "h count max|d|".
# Run: bash h_table.sh ../lists/imq_h1000.txt.xz 1000 > h1000_table.txt
#      bash h_table.sh ../lists/imq_h2000.txt.xz 2000 > h2000_table.txt
set -euo pipefail
LIST=$1
N=$2
xz -dc "$LIST" | awk -v N="$N" '
  { c[$2]++; if ($1 > m[$2]) m[$2] = $1 }
  END { for (h = 1; h <= N; h++) print h, c[h] + 0, m[h] + 0 }'
