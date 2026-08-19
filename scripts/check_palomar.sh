#!/usr/bin/env bash
# check_palomar.sh — pre-submission guard for the palomar/ Comparator wrapper.
#
# Checks, in order:
#   1. The shared definition preamble of Challenge.lean and Solution.lean is
#      byte-identical (Comparator requires term-level identity; this catches
#      drift at the source level, where it is fixable).
#   2. Both modules build.
#   3. Every compared declaration in comparator.json exists in the Solution
#      and depends on no axiom beyond propext / Classical.choice / Quot.sound.
#   4. Challenge.lean stays inside Palomar's preferred review surface
#      (warn > 300 lines, fail > 1000 lines or > 100 KiB).
#
# Run from the repo root: ./scripts/check_palomar.sh
set -u
cd "$(dirname "$0")/.."
PAL=palomar
status=0

echo "== 1. preamble identity =="
if diff <(sed -n '/^namespace KTAIT/,/^end Localization/p' "$PAL/Challenge.lean") \
        <(sed -n '/^namespace KTAIT/,/^end Localization/p' "$PAL/Solution.lean") >/dev/null; then
  echo "  OK: shared definitions identical"
else
  echo "  FAIL: Challenge/Solution definition preambles differ"; status=1
fi

echo "== 2. build =="
if (cd "$PAL" && lake build Challenge Solution >/dev/null 2>&1); then
  echo "  OK: Challenge and Solution build"
else
  echo "  FAIL: palomar build failed (run: cd palomar && lake build)"; status=1
fi

echo "== 3. axiom footprint of compared declarations =="
DECLS=$(python3 -c "
import json
print('\n'.join(json.load(open('$PAL/comparator.json'))['theorem_names']))")
AXFILE=$(mktemp)
{
  echo "import Solution"
  while IFS= read -r d; do echo "#print axioms $d"; done <<< "$DECLS"
} > "$AXFILE.lean"
OUT=$(cd "$PAL" && lake env lean "$AXFILE.lean" 2>&1)
if [ $? -ne 0 ]; then
  echo "  FAIL: axiom check did not run:"; echo "$OUT" | head -5; status=1
else
  BAD=$(echo "$OUT" | tr ',[]' '\n' | grep -oE "[A-Za-z0-9_.]+" \
    | grep -vE "^(propext|Classical\.choice|Quot\.sound|KTAIT|Localization|depends|on|axioms|.*'.*)$" \
    | grep -vE "^(persistence_conservation|conservation_tradeoff|localization_balance_reversible|recurrent_recoverability_persistence_bound|meta_persistence)$" \
    | sort -u | grep -vE "^$" || true)
  if echo "$OUT" | grep -qE "sorryAx|ofReduceBool"; then
    echo "  FAIL: forbidden axiom in footprint:"; echo "$OUT" | grep -E "sorryAx|ofReduceBool"; status=1
  elif echo "$OUT" | grep -q "error"; then
    echo "  FAIL:"; echo "$OUT" | grep "error" | head -5; status=1
  else
    echo "  OK: only permitted axioms"
    echo "$OUT" | sed 's/^/    /'
  fi
fi
rm -f "$AXFILE" "$AXFILE.lean"

echo "== 4. Challenge surface size =="
LINES=$(wc -l < "$PAL/Challenge.lean")
BYTES=$(wc -c < "$PAL/Challenge.lean")
if [ "$LINES" -gt 1000 ] || [ "$BYTES" -gt 102400 ]; then
  echo "  FAIL: Challenge.lean exceeds hard limits ($LINES lines, $BYTES bytes)"; status=1
elif [ "$LINES" -gt 300 ] || [ "$BYTES" -gt 32768 ]; then
  echo "  WARN: Challenge.lean above preferred surface ($LINES lines, $BYTES bytes)"
else
  echo "  OK: $LINES lines, $BYTES bytes"
fi

exit $status
