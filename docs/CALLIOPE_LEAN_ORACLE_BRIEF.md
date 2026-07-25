# Brief: give Calliope's Modeling Engine a well-typedness oracle

**For:** a Calliope working session.
**Status:** design brief, nothing built yet.
**Prepared:** 2026-07-26, from a session that landed `KTAIT/PatternPersist.lean`.

---

## 1. The problem

Calliope's Modeling Engine currently *retrieves*. `query_ontology` returns canonical
definitions as prose, ranked by cosine similarity — and on definitional queries those
similarities came back at **0.05–0.11**, which is weak. Retrieval tells you what the corpus
*said*. It cannot tell you whether a new claim is *sayable in KT at all*.

That second question is the one that keeps costing us. In one recent session, three separate
errors reached a draft and had to be caught by hand:

- a class treated as a rung of composition between an individual and a collective;
- an admissibility condition that *admitted* the exact projection the source paper excludes
  by name;
- `Agent` written as a type rival to `Pattern`, which makes the paper's own claim — that the
  persistent patterns strictly *contain* the agents — unstateable.

All three are **type errors**. A machine can catch all three. None of them is detectable by
similarity search over prose.

## 2. What to build

A **well-typedness oracle**: given a candidate statement, return `well-typed` /
`ill-typed` / `unproved`, and when ill-typed, return the type error verbatim as the
explanation.

This already works. Asking whether a collective can be composed of classes returns:

```
error: Type mismatch
  T.traj
has type
  Time → F.Obj
but is expected to have type
  Pattern F
```

That is a usable, quotable answer.

## 3. The architecture decision: **consume, do not fork**

Calliope should **pin and consume** the existing KTAIT repository read-only. She should not
build her own formalization of KT.

**Why not a second system.** Two formalizations diverge, and nothing guards between them.
This is not hypothetical — it is the failure mode the KTAIT repo has already suffered three
times: WP0195 drifted from the Lean for weeks; `ModelOrPay.lean`'s docstring fossilized half
an hour after its paper was retitled; and WP0058 claimed "machine-checked in Lean" in public
while the correcting fix sat uncommitted on a laptop. A second ontology guarantees a second
drift surface, with no `check_sync` between them. The value of a type system is that it is
*the* arbiter; two arbiters is none.

There is also a governance reason. KTAIT's discipline — sorry-free, every theorem documented
in WP0195, pre-push hook, CI, human guarantor — exists so that KT theorems do not land
unreviewed. An agent authoring into that repo dissolves the guarantee it provides.

**Why not naively share it either.** The traffic is the wrong shape. KTAIT is slow, curated,
durable, and always green. Oracle checks are ephemeral, high-volume, and **mostly failing** —
that is the point of them. They must never touch the repo, and Calliope must not hold push
rights to a human-guaranteed research artifact.

**So:** pin a commit SHA, keep a warm build cache, elaborate each candidate in a throwaway
file that imports KTAIT and is discarded immediately.

Three properties follow, all of which matter for a librarian specifically:

1. **One source of truth.** The GitHub repo stays the arbiter.
2. **Attributable verdicts.** "Well-typed against KTAIT @ `e27559b`" is citable and
   reproducible. A verdict without a SHA is worthless six months later.
3. **Pin moves are deliberate.** And re-running the accumulated query log against a new SHA
   is a free regression test on KT itself — it would have caught the WP0058 problem.

## 4. Two speeds — this is the important design detail

Measured on a warm cache, on the machine this brief was written on:

| Path | Imports | Cost per query | Catches |
|---|---|---|---|
| **Structural** | `KTAIT.Ontology` only (Mathlib-free) | **~0.3 s** | category errors: role confusion, part-whole, pattern vs agent vs kind |
| **Full** | `KTAIT.Basic` and up (pulls Mathlib) | **~29 s** | everything, including complexity inequalities |

**29 seconds is not interactive.** The full oracle must be asynchronous — run when a draft is
written or a claim proposed, not as live autocomplete.

**Build the structural oracle first.** All three errors in §1 are structural, and the fast
path catches them in under a second. Treat the full path as batch.

## 5. What Calliope owns

None of these are Lean theorems, so none creates a second ontology:

- **The concept→declaration map.** Each ontology concept gains a `lean_name` field pointing
  at the KTAIT declaration that formalizes it. This is librarian work, hers by right. It also
  extends `check_sync`'s guarantee to the catalog: a concept whose Lean name stops resolving
  gets flagged, so the ontology cannot drift from the formalization. The paper-side anchor
  already exists: `\ktait{decl}` (see `docs/citing-papers.txt`) marks a machine-checked claim
  and is resolved by the same guard.
- **The query log.** Candidate statements plus verdicts plus SHA. Nobody currently has this
  dataset, and it doubles as the regression suite in §3.
- **The elaboration harness.** Shell-out, timeouts, sandboxing, caching.

## 6. The boundary — hold this one

When a check reveals a claim that *should* be sayable but is not, because KTAIT lacks a
definition, that is a **feature request against KTAIT**. It goes to the human guarantor. It
is not auto-added.

The moment Calliope can extend the ontology unsupervised, the guarantee the whole apparatus
provides is gone. "The Lean and the paper ship together" is the repo's stated rule; an agent
that can land theorems breaks it.

## 7. Security

Elaborating Lean from untrusted input **executes code** — `#eval` runs, and `lake` can run
build scripts. Calliope may receive candidate statements from drafts, agents, or users.

Required: run in a container; no network; whitelist imports to `KTAIT.*` and reject arbitrary
paths; hard timeout (30 s structural, 120 s full); no write access to the pinned checkout.

## 8. First deliverable

A structural oracle with:

- a pinned KTAIT checkout at a recorded SHA, read-only;
- `check(statement) -> {verdict, error_text, sha, elapsed_ms}`;
- the concept→declaration map for the concepts that have formal counterparts;
- a query log table.

**Acceptance criteria.** All three §1 errors are rejected with a quotable type error, and at
least one known-good KT statement is accepted, in under a second each, with the SHA recorded
on every verdict.

## 9. Repository facts

| | |
|---|---|
| Remote | `https://github.com/giulioruffini/KTAIT.git` |
| Pin at time of writing | `e27559b24cab8ea5f3d9407ed9cde5bd9ba20e9a` (`e27559b`) |
| Toolchain | `leanprover/lean4:v4.31.0` + Mathlib v4.31 |
| Modules | 20 |
| Build | `lake build` (full: ~8600 jobs) |
| Guard | `./scripts/check_sync.sh` must exit clean; pre-push hook enforces it |
| Status paper | `docs/WP0195.tex` — every module and non-helper theorem is listed there |

**Mathlib-free modules** (the fast path): `Ontology.lean`. Everything else imports Mathlib
transitively via `Basic.lean`.
