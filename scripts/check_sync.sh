#!/usr/bin/env bash
# Guard against the three ways KTAIT, its status paper, and the papers that cite it
# drift apart. Each check exists because the corresponding failure actually happened.
#
#   1. SORRY-FREE   — a proof gap must never sit behind a "machine-checked" claim.
#   2. WP0195       — the status paper must list every module and non-helper theorem.
#   3. CITING PAPERS — every \lean{...} name a paper cites must resolve to a real
#                     declaration. (2026-07: WP0058's Prop. 2 was rewritten and its
#                     Appendix B cited two new lemmas; nothing checked that link.)
#   4. --released   — before a paper goes public: the tree is clean AND HEAD is pushed.
#                     (2026-07: the Prop. 2 fix sat uncommitted while the paper claimed
#                     it was machine-checked; GitHub still served the false hypothesis.)
#
# Usage:  scripts/check_sync.sh [--released]
# Exit 0 = in sync. Non-zero = drift; the message says what to do.
set -uo pipefail
cd "$(dirname "$0")/.."

RELEASED=0
[ "${1:-}" = "--released" ] && RELEASED=1

WP=docs/WP0195.tex
REGISTRY=docs/citing-papers.txt
status=0

# Helper lemmas / witnesses that need no prose entry of their own in WP0195.
HELPER_RE='^(coflow_|rel_|toy[A-Za-z]*_|cweight_|contrast_Z_|mem_|exists_map_without_decoder$|null_selection_transmits_nothing$)'

# ── 1. sorry-free ────────────────────────────────────────────────────────────
# BadStatements.lean documents-by-compilation that bad statements are REJECTED;
# its `#check_failure` prints `sorry` as the placeholder for the caught type error.
# That is the guard working, not a proof gap — so we look for real `sorry` tokens
# in tactic/term position only.
echo "== sorry-free =="
if grep -rnE '(:=|by|;|^)[[:space:]]*sorry\b' KTAIT/*.lean | grep -v 'BadStatements.lean'; then
  echo "  FAIL: a proof contains 'sorry'"; status=1
else
  echo "  OK: no proof gaps"
fi

# ── 2. WP0195 covers the development ─────────────────────────────────────────
echo "== WP0195 coverage =="
if [ ! -f "$WP" ]; then
  echo "  FAIL: $WP not found"; status=1
else
  NORM=$(mktemp); trap 'rm -f "$NORM"' EXIT
  sed 's/\\_/_/g' "$WP" > "$NORM"           # WP0195 escapes underscores for LaTeX

  for f in KTAIT/*.lean; do
    m=$(basename "$f" .lean)
    grep -qF "\\lean{${m}.lean}" "$WP" || { echo "  MISSING module: ${m}.lean"; status=1; }
  done

  while read -r t; do
    [[ "$t" =~ $HELPER_RE ]] && continue
    grep -qF "$t" "$NORM" || { echo "  MISSING theorem: $t"; status=1; }
  done < <(grep -hoE "^(theorem|lemma) [A-Za-z_0-9]+" KTAIT/*.lean | awk '{print $2}' | sort -u)

  [ "$status" -eq 0 ] && echo "  OK: every module and non-helper theorem is documented"
fi

# ── 3. citing papers ─────────────────────────────────────────────────────────
# Every \lean{Foo.bar} a paper cites must name a real declaration. Papers live
# outside this repo, so a missing path is SKIPPED (CI has no checkout of them),
# never a failure — the guard runs where the papers actually are.
echo "== citing papers =="
if [ ! -f "$REGISTRY" ]; then
  echo "  (no $REGISTRY — nothing registered)"
else
  # All declaration names KTAIT actually defines.
  DECLS=$(mktemp); trap 'rm -f "$NORM" "$DECLS"' EXIT
  grep -hoE '^(theorem|lemma|def|structure|abbrev|instance) [A-Za-z_0-9]+' KTAIT/*.lean \
    | awk '{print $2}' | sort -u > "$DECLS"

  while IFS= read -r line; do
    case "$line" in ''|'#'*) continue ;; esac
    tag=${line%%|*}; path=${line#*|}
    tag=$(echo "$tag" | xargs); path=$(echo "$path" | xargs)
    if [ ! -f "$path" ]; then
      echo "  SKIP $tag (not present here: $path)"
      continue
    fi
    missing=0
    # Papers also wrap \lean{} around Lean core axioms and commands. Those are not
    # KTAIT declarations and must not be reported as missing.
    CORE_RE='^(propext|Classical\.choice|Quot\.sound|sorryAx|sorry|Lean|Mathlib)$'
    # \lean{Mod.name} or \lean{name}; strip LaTeX underscore escapes; ignore paths/commands.
    while read -r name; do
      [ -z "$name" ] && continue
      case "$name" in */*|'#'*|'\#'*) continue ;; esac  # KTAIT/Foo.lean, #print axioms
      [[ "$name" =~ $CORE_RE ]] && continue             # Lean core axioms
      base=${name##*.}                                  # WriteBack.foo -> foo
      case "$base" in lean|'') continue ;; esac
      grep -qxF "$base" "$DECLS" || { echo "  $tag CITES MISSING: $name"; missing=1; status=1; }
    done < <(grep -oE '\\lean\{[^}]*\}' "$path" | sed 's/\\lean{//; s/}//; s/\\_/_/g' | sort -u)
    [ "$missing" -eq 0 ] && echo "  OK $tag: all \\lean{} references resolve"
  done < "$REGISTRY"
fi

# ── 4. released: committed and pushed ────────────────────────────────────────
if [ "$RELEASED" -eq 1 ]; then
  echo "== released (tree clean, HEAD pushed) =="
  if [ -n "$(git status --porcelain)" ]; then
    echo "  FAIL: uncommitted changes — a paper must not claim results that only exist on this disk"
    git status --short | sed 's/^/    /'
    status=1
  fi
  if git rev-parse --abbrev-ref '@{u}' >/dev/null 2>&1; then
    ahead=$(git rev-list --count '@{u}..HEAD')
    if [ "$ahead" -ne 0 ]; then
      echo "  FAIL: $ahead commit(s) not pushed — GitHub would serve the old proofs"; status=1
    fi
  else
    echo "  FAIL: no upstream branch set"; status=1
  fi
  [ "$status" -eq 0 ] && echo "  OK: everything the paper cites is on GitHub"
fi

echo
if [ "$status" -eq 0 ]; then
  echo "IN SYNC."
else
  echo "OUT OF SYNC. Fix the above, rebuild any affected paper, and commit the Lean"
  echo "AND the papers together. Never ship a 'machine-checked' claim that isn't pushed."
fi
exit $status
