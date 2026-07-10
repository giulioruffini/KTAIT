#!/usr/bin/env bash
# Fail if the Lean development has drifted from its status paper (docs/WP0195.tex).
#
# WP0195 is the human-readable record of what KTAIT proves. It is easy to add a
# module or a theorem and forget the paper; this catches that. Run it before you
# push, or wire it into a pre-commit hook.
#
# Helper lemmas are exempt via HELPER_RE below -- keep that list tight, and prefer
# documenting a result over exempting it.
set -uo pipefail
cd "$(dirname "$0")/.."

WP=docs/WP0195.tex
[ -f "$WP" ] || { echo "FAIL: $WP not found"; exit 1; }

# WP0195 escapes underscores for LaTeX: foo\_bar -> foo_bar
NORM=$(mktemp); trap 'rm -f "$NORM"' EXIT
sed 's/\\_/_/g' "$WP" > "$NORM"

# Helper lemmas / witnesses that need no prose entry of their own.
HELPER_RE='^(coflow_|rel_|toy[A-Za-z]*_|cweight_|contrast_Z_|mem_|exists_map_without_decoder$|null_selection_transmits_nothing$)'

status=0

echo "== modules =="
for f in KTAIT/*.lean; do
  m=$(basename "$f" .lean)
  if ! grep -qF "\\lean{${m}.lean}" "$WP"; then
    echo "  MISSING from WP0195 module table: ${m}.lean"; status=1
  fi
done

echo "== theorems =="
while read -r t; do
  [[ "$t" =~ $HELPER_RE ]] && continue
  grep -qF "$t" "$NORM" || { echo "  MISSING from WP0195: $t"; status=1; }
done < <(grep -hoE "^(theorem|lemma) [A-Za-z_0-9]+" KTAIT/*.lean | awk '{print $2}' | sort -u)

if [ "$status" -eq 0 ]; then
  echo "OK: docs/WP0195.tex covers every module and every non-helper theorem."
else
  echo
  echo "WP0195 is out of date. Update docs/WP0195.tex (module table, proved list,"
  echo "inventory), rebuild it, and commit BOTH the Lean and the paper."
fi
exit $status
