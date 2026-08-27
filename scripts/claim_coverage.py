#!/usr/bin/env python3
"""Walk from the prose to Lean: every stated result must have a recorded formal status.

check_sync.sh checks 1-5 all walk the other way. They start from something the paper
already cites and ask whether it still resolves, still says the same thing, is still
pushed. That direction cannot see the failure that motivated this file: WP0007 v0.26.0
introduced a new corollary (the witness-based optimality barrier) with no Lean
counterpart at all. There was no citation for the guard to follow, the declaration it
did cite was untouched, and so every check stayed green while Appendix D disclaimed a
formalization that standing practice required. A human reading the diff caught it.

The check here is deliberately narrow. It does NOT decide whether a Lean statement
faithfully renders the prose -- nothing mechanical can, and the landau `formalize` lens
is where that judgment happens. It asks only that every stated result carry an explicit,
recorded answer to "is this machine-checked, and by what?" An unannotated new result is
the finding, because silence is how the WP0007 gap survived.

ANNOTATION
----------
A LaTeX comment on (or just above) the environment, contiguous with it:

    % ktait: relational_optimality_barrier
    \\begin{Corollary}[Relational optimality barrier]\\label{cor:relational-optimality}

    % ktait: none -- definitional; fixes notation, asserts nothing
    \\begin{Lemma}\\label{lem:notation}

`% ktait: <decl>[, <decl>...]` asserts the result is machine-checked, and every name is
verified against the declarations KTAIT actually defines -- so this annotation cannot rot
the way a prose appendix can. `% ktait: none` records a deliberate decision and REQUIRES a
reason; "none" with no reason reads as an oversight and is rejected as one.

A `\\ktait{...}` inside the environment body counts on its own -- the claim cites its
declaration where it stands, and no comment is needed.

KEYS, AND WHY THEY ARE NOT PER-PAPER
------------------------------------
A claim is keyed by its `\\label`, falling back to a hash of its normalized body. Keys are
global, not per-paper-version: registering v19 of a paper inherits every status already
recorded for v18, because the labels are the same. Only genuinely new or restated results
fire. Registering a new version must not produce fourteen failures, or the check will be
silenced within a week.

RATCHET, NOT A WALL
-------------------
Same posture as numbered_refs.py. 300-odd results predate this file, most in frozen
versions that will never be annotated. `--accept` records them; the check fails only on
what is new. Restatement of an already-recorded result is a WARNING (the body hash moved,
so the recorded status may no longer describe it) and an ERROR under --released, where
"we have not re-confirmed this" is not good enough to publish on.

Usage:  claim_coverage.py --check [--released] | --accept | --report
"""

import argparse
import hashlib
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REGISTRY = os.path.join(ROOT, "docs", "citing-papers.txt")
BASELINE = os.path.join(ROOT, "docs", "claim-coverage-baseline.tsv")

# Results only. `definition`, `remark`, `assumption`, `problem` are deliberately out of
# scope: they assert nothing that could be machine-checked, and sweeping them in triples
# the baseline while diluting the signal this file exists to carry. A definition with real
# computational content can still be annotated -- annotations on out-of-scope environments
# are read and validated, just never required.
RESULT_ENVS = ["theorem", "proposition", "corollary", "lemma", "claim", "conjecture"]
ANNOTATABLE = RESULT_ENVS + ["definition", "remark", "assumption", "problem"]

DECL_RE = re.compile(r"^(theorem|lemma|def|structure|abbrev|instance) ([A-Za-z_0-9]+)", re.M)


def declarations():
    """Every name KTAIT defines. Same extraction as check_sync.sh check 3."""
    names = set()
    for dirpath, _, files in os.walk(os.path.join(ROOT, "KTAIT")):
        for fn in files:
            if fn.endswith(".lean"):
                with open(os.path.join(dirpath, fn), errors="replace") as fh:
                    names.update(m.group(2) for m in DECL_RE.finditer(fh.read()))
    return names


def registered():
    """(tag, path) for each registered paper file that is present on this disk."""
    out = []
    with open(REGISTRY) as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            tag, _, path = line.partition("|")
            tag, path = tag.strip(), path.strip()
            full = path if os.path.isabs(path) else os.path.normpath(os.path.join(ROOT, path))
            if os.path.isfile(full):
                out.append((tag, full))
    return out


def normalize(body):
    """Body text stripped to what a restatement would actually change."""
    body = re.sub(r"(?m)^\s*%.*$", "", body)
    body = re.sub(r"(?<!\\)%.*", "", body)
    body = re.sub(r"\\label\{[^}]*\}", "", body)
    return re.sub(r"\s+", " ", body).strip()


def annotation_above(text, begin_pos):
    """The `% ktait:` comment on or just above the \\begin, if any.

    Walks back over contiguous comment and blank lines, capped at six -- far enough for a
    wrapped reason, near enough that an unrelated comment further up cannot be mistaken
    for this claim's status.
    """
    head = text[: text.rfind("\n", 0, begin_pos) + 1]
    for line in reversed(head.split("\n")[-7:-1]):
        stripped = line.strip()
        if not stripped:
            continue
        if not stripped.startswith("%"):
            break
        m = re.search(r"ktait\s*:\s*(.*)", stripped.lstrip("%").strip(), re.I)
        if m:
            return m.group(1).strip()
    return None


def parse_status(raw, decls):
    """(status, decls, note, error) for an annotation value."""
    if re.match(r"^none\b", raw, re.I):
        reason = raw[4:].strip().lstrip("-\u2013\u2014:,").strip()
        if not reason:
            return None, [], "", "`% ktait: none` with no reason -- say why, or it reads as an oversight"
        return "none", [], reason, None
    names = [n.strip().replace("\\_", "_").strip("`\\") for n in raw.split(",")]
    names = [n for n in names if n]
    if not names:
        return None, [], "", "empty `% ktait:` annotation"
    unknown = [n for n in names if n.split(".")[-1] not in decls]
    if unknown:
        return None, [], "", "names no such KTAIT declaration: " + ", ".join(unknown)
    return "checked", names, "", None


def collect():
    """Every in-scope claim across every registered paper, keyed and status-resolved."""
    decls = declarations()
    env_re = re.compile(r"\\begin\{(" + "|".join(ANNOTATABLE) + r")(\*?)\}", re.I)
    claims = {}
    errors = []
    for tag, path in registered():
        with open(path, errors="replace") as fh:
            text = fh.read()
        for m in env_re.finditer(text):
            env = m.group(1).lower()
            end = re.compile(r"\\end\{" + m.group(1) + r"\*?\}").search(text, m.end())
            body = text[m.end() : end.start()] if end else text[m.end() : m.end() + 4000]

            raw = annotation_above(text, m.start())
            status, names, note, err = (None, [], "", None)
            if raw is not None:
                status, names, note, err = parse_status(raw, decls)
                if err:
                    errors.append(f"  {tag}: {err}")
            if status is None:
                inline = re.findall(r"\\ktait\{([^}]*)\}", body)
                if inline:
                    status = "checked"
                    names = [n.replace("\\_", "_") for n in inline]
                    note = "cited in body"

            if env not in RESULT_ENVS:
                continue  # annotation validated above; presence not required

            label = re.search(r"\\label\{([^}]*)\}", body)
            key = (
                "label:" + label.group(1)
                if label
                else "body:" + hashlib.sha1(normalize(body).encode()).hexdigest()[:12]
            )
            digest = hashlib.sha1(normalize(body).encode()).hexdigest()[:12]
            prev = claims.get(key)
            # One key can appear in many registered versions of the same paper. Keep the
            # first sighting for reporting, but let any version that carries a status
            # supply it -- annotating the live file must satisfy the frozen ones too.
            if prev is None:
                claims[key] = {"tag": tag, "env": env, "status": status,
                               "decls": names, "note": note, "hash": digest}
            elif prev["status"] is None and status is not None:
                prev.update(status=status, decls=names, note=note)
    return claims, errors


def load_baseline():
    if not os.path.isfile(BASELINE):
        return {}
    out = {}
    with open(BASELINE) as fh:
        for line in fh:
            line = line.rstrip("\n")
            if not line.strip() or line.startswith("#"):
                continue
            parts = line.split("\t")
            if len(parts) >= 3:
                out[parts[0]] = {"status": parts[1], "hash": parts[2],
                                 "note": parts[3] if len(parts) > 3 else ""}
    return out


def write_baseline(claims):
    lines = [
        "# Formal status of every result stated in a registered paper.",
        "# Generated by scripts/claim_coverage.py --accept. Keyed by \\label (stable across",
        "# renumbering and across versions of the same paper), or by body hash where a result",
        "# carries no label. `legacy` means the result predates the coverage check and its",
        "# formal status was never recorded -- not that it was reviewed and exempted.",
        "#",
        "# key\tstatus\tbodyhash\tnote",
    ]
    for key in sorted(claims):
        c = claims[key]
        status = c["status"] or "legacy"
        note = c["note"] or (",".join(c["decls"]) if c["decls"] else c["tag"])
        lines.append(f"{key}\t{status}\t{c['hash']}\t{note}")
    with open(BASELINE, "w") as fh:
        fh.write("\n".join(lines) + "\n")
    return len(claims)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--accept", action="store_true")
    ap.add_argument("--report", action="store_true")
    ap.add_argument("--released", action="store_true")
    args = ap.parse_args()

    claims, errors = collect()

    if args.accept:
        n = write_baseline(claims)
        recorded = sum(1 for c in claims.values() if c["status"])
        print(f"  recorded {n} results ({recorded} with a formal status, "
              f"{n - recorded} legacy) -> {os.path.relpath(BASELINE, ROOT)}")
        return 0

    if args.report:
        for key in sorted(claims):
            c = claims[key]
            print(f"  {c['status'] or 'UNRECORDED':10s} {key:52s} {c['tag']} "
                  f"{','.join(c['decls'])}")
        return 0

    baseline = load_baseline()
    new, restated = [], []
    for key, c in sorted(claims.items()):
        if c["status"] is not None:
            continue  # annotated in the source; no baseline lookup needed
        b = baseline.get(key)
        if b is None:
            new.append((key, c))
        elif b["hash"] != c["hash"]:
            restated.append((key, c))

    status = 0
    for line in errors:
        print(line)
        status = 1
    for key, c in new:
        print(f"  {c['tag']}: {c['env']} {key} has no recorded formal status")
        status = 1
    for key, c in restated:
        where = "FAIL" if args.released else "warn"
        print(f"  {where} {c['tag']}: {key} was restated since its status was recorded")
        if args.released:
            status = 1

    if new:
        print("  -> annotate each with `% ktait: <decl>` or `% ktait: none -- <reason>`,")
        print("     or run scripts/claim_coverage.py --accept to record them as legacy")
    if restated and not new:
        print("  -> re-confirm the recorded status still describes it, then --accept")
    if status == 0 and not restated:
        n = len(claims)
        k = sum(1 for c in claims.values() if c["status"] == "checked")
        print(f"  OK: {n} results, every one with a recorded status ({k} machine-checked)")
    return status


if __name__ == "__main__":
    sys.exit(main())
