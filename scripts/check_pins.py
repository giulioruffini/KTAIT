#!/usr/bin/env python3
"""Check that each registered paper's provenance pin contains every declaration it cites.

A paper that says its results are machine-checked points readers at one KTAIT commit
("source commit 8c602ff"). That pin is the paper's actual claim: not "these names resolve
on the author's laptop today" but "check out this tree and you will find these proofs".
check_sync.sh resolves cited names against HEAD, so it cannot see a pin that fell behind.

That is what happened. WP0203 v30 added ARTExactForm.lean and cited nine of its
declarations, while the provenance paragraph kept the pin from v26 (d00a991). Every
check stayed green for three releases: the names resolved at HEAD, the tree was pushed,
CI passed. A reader following the link found a tree without the module.

RULE
----
For each paper in docs/citing-papers.txt that carries a pin (a link of the form
github.com/giulioruffini/KTAIT/tree/<hash> or /commit/<hash>), the pinned commit must
exist in this repository and its KTAIT/ tree must define every name the paper cites with
\\ktait{...}. Names cited with \\lean{...} are incidental text and are not checked here.

Archived releases keep their historical pins, so the check is enforced only on the
last-registered version of each paper family (entries sharing the leading WPnnnn of their
tag; the version is the path component after the paper's folder). Earlier versions warn.

Usage:  check_pins.py [--check]      exit 1 on an enforced failure
"""

import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REGISTRY = os.path.join(ROOT, "docs", "citing-papers.txt")

PIN_RE = re.compile(r"github\.com/giulioruffini/KTAIT/(?:tree|commit)/([0-9a-f]{7,40})")
KTAIT_RE = re.compile(r"\\ktait\{([^}]*)\}")
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?"
    r"(?:theorem|lemma|def|structure|abbrev|instance|inductive|class)\s+([A-Za-z_][A-Za-z0-9_.']*)",
    re.M,
)
FAMILY_RE = re.compile(r"^(WP\d+)")


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True)


def read_registry():
    entries = []
    with open(REGISTRY, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#") or "|" not in line:
                continue
            tag, path = (s.strip() for s in line.split("|", 1))
            if not os.path.isabs(path):
                path = os.path.normpath(os.path.join(ROOT, path))
            entries.append((tag, path))
    return entries


def version_key(path):
    """The path component after the paper's working-draft folder: v31.2, current_version, ..."""
    parts = path.split(os.sep)
    for i, part in enumerate(parts):
        if re.match(r"WP\d+", part) and i + 1 < len(parts):
            return parts[i + 1]
    return os.path.basename(path)


def strip_comments(tex):
    return re.sub(r"(?<!\\)%.*", "", tex)


def declarations_at(commit):
    ls = git("ls-tree", "-r", "--name-only", commit, "--", "KTAIT/")
    if ls.returncode != 0:
        return None
    names = set()
    for fname in ls.stdout.split():
        if not fname.endswith(".lean"):
            continue
        blob = git("show", f"{commit}:{fname}")
        if blob.returncode != 0:
            continue
        for m in DECL_RE.finditer(blob.stdout):
            names.add(m.group(1).split(".")[-1])
    return names


def main():
    entries = read_registry()
    if not entries:
        print("  (no registry — nothing to check)")
        return 0

    # Enforce the last-registered version of each family; warn on the rest.
    last_version = {}
    for tag, path in entries:
        fam = FAMILY_RE.match(tag)
        if fam:
            last_version[fam.group(1)] = version_key(path)

    status = 0
    cache = {}
    for tag, path in entries:
        if not os.path.isfile(path):
            continue  # SKIPped by check_sync.sh already; papers are not checked out in CI
        with open(path, encoding="utf-8", errors="replace") as fh:
            tex = strip_comments(fh.read())
        pins = sorted(set(PIN_RE.findall(tex)))
        if not pins:
            continue
        cited = sorted({n.split(".")[-1].replace("\\_", "_") for n in KTAIT_RE.findall(tex)})
        fam = FAMILY_RE.match(tag)
        enforced = bool(fam) and version_key(path) == last_version[fam.group(1)]
        level = "FAIL" if enforced else "WARN"
        for pin in pins:
            if pin not in cache:
                cache[pin] = declarations_at(pin)
            decls = cache[pin]
            if decls is None:
                print(f"  {level} {tag}: pin {pin} is not a commit in this repository")
                status |= enforced
                continue
            missing = [n for n in cited if n not in decls]
            if missing:
                print(f"  {level} {tag}: pin {pin} lacks {len(missing)} cited declaration(s): "
                      + ", ".join(missing[:6]) + (" ..." if len(missing) > 6 else ""))
                status |= enforced
            else:
                print(f"  OK {tag}: pin {pin} defines all {len(cited)} cited declarations")
    if status:
        print("  A stale pin sends readers to a tree without the proofs the paper claims.")
        print("  Re-pin the paper to the last commit that changed KTAIT/ and rebuild it.")
    return 1 if status else 0


if __name__ == "__main__":
    sys.exit(main())
