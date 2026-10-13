#!/bin/bash
# Run Comparator (https://github.com/leanprover/comparator) on one of the challenges in this directory,
# with a landrun sandbox as in Comparator's README. Usage, from lean/:
#   bash comparator/run.sh [config]      config: B4ClassNumber (default), B4ZeroGap, or *_nanoda
# The tools are taken from these environment variables (see comparator/README.md):
#   COMPARATOR        the comparator binary
#   COMPARATOR_LANDRUN, COMPARATOR_LEAN4EXPORT, COMPARATOR_NANODA (the last only for *_nanoda configs)
set -uo pipefail
cfg=${1:-B4ClassNumber}
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)
: "${COMPARATOR:?set COMPARATOR}" "${COMPARATOR_LANDRUN:?set COMPARATOR_LANDRUN}"
: "${COMPARATOR_LEAN4EXPORT:?set COMPARATOR_LEAN4EXPORT}"
echo "# $(date -u)  config $cfg  landrun $("$COMPARATOR_LANDRUN" --version)  kernel $(uname -r)"
# systemd-run with --pipe --wait (non-interactive); RestrictAddressFamilies as in Comparator's README.
systemd-run --user --pipe --wait --collect --property=RestrictAddressFamilies=~AF_UNIX \
  -E PATH="$PATH" -E HOME="$HOME" -E COMPARATOR_LANDRUN="$COMPARATOR_LANDRUN" \
  -E COMPARATOR_LEAN4EXPORT="$COMPARATOR_LEAN4EXPORT" -E COMPARATOR_NANODA="${COMPARATOR_NANODA:-}" \
  --working-directory "$root" -- \
  bash -c "lake env \"$COMPARATOR\" comparator/$cfg.json"
rc=$?
echo "comparator exit: $rc"
exit $rc
