#!/bin/bash
# Re-create every file of vendor/ from the upstream repositories and compare it byte for byte.
# Needs git and network access. Usage: bash vendor/check.sh   (from lean/ or from vendor/)
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

OAI_COMMIT=301488868beec11bfd897168433b0a64f5258559
PNT_COMMIT=c39a751132c88b6e8080b74c74023fd95b3d8be0
TAU_COMMIT=3bed7e37f3c504a99e8c07e9f309540812a7aa90
AINTLIB_COMMIT=160e446617a2168c34c95bbe7a76c4105b392434

fetch() {  # fetch <url> <dir> <commit>
  git clone -q --filter=blob:none --no-checkout "$1" "$tmp/$2"
  git -C "$tmp/$2" -c advice.detachedHead=false checkout -q --detach "$3"
}
fetch https://github.com/openai/math.git openai-math "$OAI_COMMIT"
fetch https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.git PrimeNumberTheoremAnd "$PNT_COMMIT"
fetch https://github.com/TauCetiProject/TauCeti.git TauCeti "$TAU_COMMIT"
fetch https://github.com/CBirkbeck/AINTLIB.git AINTLIB "$AINTLIB_COMMIT"

# The compatibility patches of openai/math (applied by its lakefile), and ours for TauCeti.
git -C "$tmp/PrimeNumberTheoremAnd" apply --whitespace=nowarn \
  "$tmp/openai-math/lean/patches/PrimeNumberTheoremAnd-lean4341.patch"
git -C "$tmp/AINTLIB" apply --whitespace=nowarn "$tmp/openai-math/lean/patches/AINTLIB-lean4341.patch"
git -C "$tmp/TauCeti" apply "$here/patches/TauCeti-pinned-mathlib.patch"

bad=0; n=0
cd "$here"
while read -r f; do
  pkg=${f%%/*}; rel=${f#*/}
  case $pkg in
    openai-math) up=$tmp/openai-math/lean/$rel ;;
    AINTLIB) up=$tmp/AINTLIB/projects/FltRegularBernoulli/$rel ;;
    *) up=$tmp/$pkg/$rel ;;
  esac
  n=$((n + 1))
  if ! cmp -s "$up" "$f"; then echo "DIFFERS: $f"; bad=$((bad + 1)); fi
done < <(find openai-math PrimeNumberTheoremAnd TauCeti AINTLIB -name '*.lean' | sort)
sha256sum --quiet -c SHA256SUMS || bad=$((bad + 1))
echo "$n files compared, $bad differences"
[ "$bad" -eq 0 ]
