#!/usr/bin/env python3
"""Fingerprint each KTAIT declaration and the prose that describes it.

The sync guard verifies that cited NAMES resolve. It cannot see when a
declaration's STATEMENT changes while the prose describing it stays put — which
is how WP0007's conditional-form corollary came to cite a declaration saying
something else, with the guard green throughout. Three separate drifts of this
kind shipped before anyone noticed.

So: hash three things per declaration.

  stmt    the statement, from `theorem NAME` to the proof separator, whitespace
          normalized. Changes when the theorem says something different.
          Deliberately excludes the proof: refactoring a proof is not a reason to
          re-read the prose.
  leandoc the `/-- ... -/` docstring immediately above it, if any.
  wp0195  the `\\item` block in docs/WP0195.tex that mentions the declaration.

The guard then enforces the co-change rule: if `stmt` moved and the prose did
not, the prose is stale until a human says otherwise.

Usage:
    fingerprint.py            emit the manifest on stdout
    fingerprint.py --check    compare against docs/declaration-manifest.tsv
"""
from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_DIR = ROOT / "KTAIT"
WP0195 = ROOT / "docs" / "WP0195.tex"
MANIFEST = ROOT / "docs" / "declaration-manifest.tsv"

# Helper lemmas that carry no prose of their own; same list the guard uses.
HELPER = re.compile(
    r"^(coflow_|rel_|toy[A-Za-z]*_|cweight_|contrast_Z_|mem_"
    r"|exists_map_without_decoder$|null_selection_transmits_nothing$)"
)

OPEN, CLOSE = "([{⟨", ")]}⟩"


def digest(text: str) -> str:
    return hashlib.sha256(" ".join(text.split()).encode()).hexdigest()[:16]


def statement_of(src: str, start: int) -> str:
    """From the declaration keyword to the proof separator, at bracket depth 0.

    The separator is `:=` or a standalone `by`. Scanning with a depth counter
    rather than a regex because both appear inside types (`fun x => ...`,
    structure instances) and a flat search picks the wrong one.
    """
    depth, i, n = 0, start, len(src)
    while i < n:
        c = src[i]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif depth == 0:
            if src.startswith(":=", i):
                return src[start:i]
            if src.startswith("by", i):
                before = src[i - 1] if i else " "
                after = src[i + 2] if i + 2 < n else " "
                if before in " \n" and after in " \n":
                    return src[start:i]
        i += 1
    return src[start:]


def docstring_before(src: str, start: int) -> str:
    """The `/-- ... -/` block immediately preceding `start`, if any."""
    head = src[:start].rstrip()
    if not head.endswith("-/"):
        return ""
    open_at = head.rfind("/--")
    return head[open_at:] if open_at != -1 else ""


def wp0195_entries() -> dict[str, str]:
    """Map declaration name -> the \\item block(s) of WP0195 mentioning it."""
    if not WP0195.exists():
        return {}
    text = WP0195.read_text(encoding="utf-8", errors="replace").replace("\\_", "_")
    items = re.split(r"\n(?=\\item\b)", text)
    out: dict[str, list[str]] = {}
    for block in items:
        for name in set(re.findall(r"\\(?:lean|ktait)\{([A-Za-z0-9_.]+)\}", block)):
            out.setdefault(name.split(".")[-1], []).append(block)
    return {k: "\n".join(sorted(v)) for k, v in out.items()}


def collect() -> list[tuple[str, str, str, str]]:
    entries = wp0195_entries()
    rows = []
    for path in sorted(LEAN_DIR.glob("*.lean")):
        if path.name == "BadStatements.lean":
            continue
        src = path.read_text(encoding="utf-8", errors="replace")
        for m in re.finditer(r"^(?:theorem|lemma) ([A-Za-z0-9_']+)", src, re.M):
            name = m.group(1)
            if HELPER.match(name):
                continue
            rows.append(
                (
                    name,
                    digest(statement_of(src, m.start())),
                    digest(docstring_before(src, m.start())),
                    digest(entries.get(name, "")),
                )
            )
    return sorted(rows)


def main() -> int:
    rows = collect()
    lines = ["\t".join(r) for r in rows]

    if "--check" not in sys.argv:
        print("# KTAIT declaration manifest — name, statement, lean docstring, WP0195 entry.")
        print("# Regenerate with scripts/fingerprint.py > docs/declaration-manifest.tsv")
        print("\n".join(lines))
        return 0

    if not MANIFEST.exists():
        print("  FAIL: docs/declaration-manifest.tsv missing — run scripts/fingerprint.py > it")
        return 1

    old = {}
    for line in MANIFEST.read_text(encoding="utf-8").splitlines():
        if line.startswith("#") or not line.strip():
            continue
        parts = line.split("\t")
        if len(parts) == 4:
            old[parts[0]] = parts[1:]

    status = 0
    for name, stmt, doc, wp in rows:
        if name not in old:
            print(f"  NEW declaration not in manifest: {name}")
            status = 1
            continue
        o_stmt, o_doc, o_wp = old[name]
        if stmt == o_stmt:
            continue
        stale = []
        if doc == o_doc and o_doc != digest(""):
            stale.append("its Lean docstring")
        if wp == o_wp and o_wp != digest(""):
            stale.append("its WP0195 entry")
        if stale:
            print(f"  DRIFT: the statement of {name} changed but {' and '.join(stale)} did not.")
            status = 1

    for name in sorted(set(old) - {r[0] for r in rows}):
        print(f"  REMOVED declaration still in manifest: {name}")
        status = 1

    if status == 0:
        print("  OK: no statement changed while its prose stood still")
    else:
        print()
        print("  Read the declaration and the prose side by side. If the prose is still")
        print("  correct, record that you checked:")
        print("      scripts/fingerprint.py > docs/declaration-manifest.tsv")
    return status


if __name__ == "__main__":
    sys.exit(main())
