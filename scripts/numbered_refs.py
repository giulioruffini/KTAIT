#!/usr/bin/env python3
"""Ratchet against references-by-number in prose that cannot track \\ref.

WP0007's conditional-form corollary was renumbered three times as results were
inserted ahead of it, and the prose here kept the old number every time: this
repo's docstrings and WP0195 entries live outside the papers' LaTeX, so no
cross-reference machinery maintains them.

The rule is to name results instead. The existing 111 numbered references
describe results in papers whose numbering has not been audited, so this is a
ratchet rather than a wall: no NEW ones, and any line touched for other reasons
should be converted while you are in it.

Version-pinned references ("v0.3.0 Corollary 1") are exempt — those are
historical records, not live pointers.

Usage:
    numbered_refs.py --check        fail on references not in the baseline
    numbered_refs.py --rebaseline   record the current set as the new baseline
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / "docs" / "numbered-refs-baseline.tsv"

NUMBERED = re.compile(r"(Theorem|Corollary|Proposition|Lemma)~?\s*[0-9]")
VERSION_PINNED = re.compile(r"v[0-9]+\.[0-9]+\.[0-9]+")
PROSE_LINE = ("--", "*", "/-", "WP")

HEADER = """# Legacy references-by-number in prose that cannot track \\ref.
# This file is a RATCHET, not an approval: no NEW ones may be added, and any
# line touched for other reasons should be converted to a named reference while
# you are in there. Regenerate only after deliberately converting entries:
#     scripts/numbered_refs.py --rebaseline
# WP0007's entries are already converted and deliberately absent.
"""


def offenders() -> list[str]:
    out: set[str] = set()

    wp = ROOT / "docs" / "WP0195.tex"
    if wp.exists():
        for line in wp.read_text(encoding="utf-8", errors="replace").splitlines():
            if NUMBERED.search(line) and not VERSION_PINNED.search(line):
                out.add("WP0195\t" + " ".join(line.split()))

    for path in sorted((ROOT / "KTAIT").glob("*.lean")):
        for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
            if not line.strip().startswith(PROSE_LINE):
                continue  # code, not prose
            if NUMBERED.search(line) and not VERSION_PINNED.search(line):
                out.add(path.name + "\t" + " ".join(line.split()))

    return sorted(out)


def load_baseline() -> set[str]:
    if not BASELINE.exists():
        return set()
    return {
        ln
        for ln in BASELINE.read_text(encoding="utf-8").splitlines()
        if ln.strip() and not ln.startswith("#")
    }


def main() -> int:
    current = offenders()

    if "--rebaseline" in sys.argv:
        BASELINE.write_text(HEADER + "\n".join(current) + "\n", encoding="utf-8")
        print(f"  baseline rewritten: {len(current)} legacy references recorded")
        return 0

    base = load_baseline()
    new = [c for c in current if c not in base]
    gone = len(base) - len([c for c in current if c in base])

    if new:
        print(f"  FAIL: {len(new)} reference(s) by number that the baseline does not cover:")
        for n in new[:10]:
            src, text = n.split("\t", 1)
            print(f"    {src}: {text[:96]}")
        if len(new) > 10:
            print(f"    ... and {len(new) - 10} more")
        print("  Name the result instead. A number here goes stale the moment a result is")
        print("  inserted ahead of it in the paper, and \\ref cannot reach into this repo.")
        print("  Pin a version if the reference is deliberately historical.")
        return 1

    msg = f"  OK: no new references by number ({len(base)} legacy"
    print(msg + (f", {gone} converted since baseline)" if gone else ")"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
