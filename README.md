# KTAIT — Kolmogorov Theory, formalized in Lean 4

A [Lean 4](https://leanprover.github.io/) + [Mathlib](https://github.com/leanprover-community/mathlib4)
formalization that **machine-checks the corollaries of Kolmogorov Theory (KT)** against an
explicit, *satisfiable* axiomatic interface to algorithmic information theory (AIT) and Bayesian
inference.

> **What it certifies:** the KT results — the probabilistic Algorithmic Regulator Theorem,
> persistence and its conservation ledger, universal-prior regulator selection, the temporal
> self-model, self-model incompleteness, and the uncomputability of regulatory coarse-graining —
> follow *logically* from a clearly delimited layer of standard AIT/probability facts, with no
> `sorry`. The KT ontology is **typed** so that structural errors (e.g. comparing a pattern to
> its own part) cannot even compile.

It does **not** re-prove classical AIT. Those results (the coding theorem, symmetry of
information, Bayes' rule, Kleene/Rice/Chaitin, Vereshchagin–Vitányi) are an honest, named
**axiom layer**; the contribution is checking that the *new* KT corollaries are correctly typed
and genuinely entailed by it.

- **Toolchain:** Lean `v4.31.0`, Mathlib `v4.31.0` (both pinned).
- **Companion working paper:** BCOM **WP0195** — methodology, full theorem inventory with
  per-statement status, and roadmap.
- **Source theory:** the KT papers (Pattern Persistence WP0162, Agent Know Thyself WP0192,
  Regulatory Coarse-Graining WP0193, and *An Algorithmic-Information-Theoretic Regulator
  Theorem*, Entropy 2026 28:257).

## The one rule

> **Standard AIT and probability theorems may be *assumed* (a named axiom layer).
> KT corollaries must be *proved* from them, with no `sorry`.**

If a KT corollary needed a `sorry`, that would be a real gap in the theory. An assumed coding
theorem is honest and expected.

**Soundness note.** The AIT facts are stated as *named hypotheses* (`Prop`s about a frame),
**not** as global `axiom`s — a global "law for every frame" would be inconsistent here (one can
build a frame violating it and derive `False`). As a result, `#print axioms` on every KT
corollary shows only Lean's core axioms (`propext`, `Classical.choice`, `Quot.sound`) plus the
named hypotheses, and a *toy model* witnesses that the hypotheses are jointly satisfiable — so
the corollaries are not vacuously true.

## What is proved

All results are `sorry`-free; `#print axioms` confirms each rests only on Lean core + the named
AIT hypotheses.

| Result | Lean name | Module |
|---|---|---|
| **ART Theorem 2** — `P((W,R)\|x,E) ≤ C·2^{M(W:R)}·2^{−Δ}` | `probabilistic_regulator_theorem` | `ART` |
| ART Theorem 2, **sharp** (`·2^{−K(R)}`) + `2^{−K(R\|W)}` form | `..._sharp`, `..._conditional` | `ART`, `RegulatorSelection` |
| ART **Theorem 1** (posterior tilt) | `theorem1_posterior_tilt` | `ART` |
| ART **Theorem 3** (on/off evidence `≍ 2^{Δ}`) | `theorem3_onoff_evidence` | `ART` |
| ART **wrapper bound** Eq. (6) — *derived* from the coding theorem | `wrapper_bound` | `ART` |
| **Lemma 1** — Bayes posterior `= 2^{−\|p\|}/m(x)`, sandwiched by coding thm | `lemma1_posterior_bounds` | `Probability` |
| **Persistence** = temporal self-information | `pers_eq_nmai`, `persistent_pos` | `Persistence` |
| **Conservation ledger** (WP0162 Prop. 2) + trade-off | `persistence_conservation`, `conservation_tradeoff` | `Persistence` |
| **Regulator selection** (WP0162 Prop. 1) | `regulator_selection` | `RegulatorSelection` |
| **Temporal self-model** (WP0162 Prop. 3 / WP0192 Prop. 1) | `self_regulation_temporal_model` | `SelfModel` |
| **Self-model incompleteness** (WP0162 Prop. 4 / WP0192 Principle 1) | `quine_floor`, `self_prediction_dichotomy`, `chaitin_blocks_minimality` | `SelfModelLimits` |
| **Coarse-graining uncomputability** (WP0193 Thm B / Cor. B) | `theoremB`, `corollaryB` | `CoarseGraining` |

Plus: typed KT **ontology** with a part-whole guard (`Ontology`), **satisfiability witnesses**
(`ToyModel`), and documented **guards** — the whole-vs-part error and the `y`-vs-`y*` conditioning
error fail to compile (`BadStatements`).

## The axiom layer (what we assume)

Standard, classical results — assumed, not re-proved:

- **Complexity:** invariance theorem; coding theorem `−log m(x) = K(x) ± O(1)` (uncond. & cond.);
  Kraft–McMillan; symmetry of information `I_K(x:y) = K(x) − K(x|y*) + O(log)`; chain rule.
- **Probability:** Solomonoff–Levin universal semimeasure; Bayes' rule with the deterministic
  likelihood `P(x|p)=𝟙{U(p)=x}`.
- **Computability/logic:** Kleene's recursion theorem; Rice's theorem; Chaitin's incompleteness;
  Vereshchagin–Vitányi (structure-function uncomputability).

## Build & verify

```sh
elan default stable            # one-time: install Lean toolchain manager
lake exe cache get             # download prebuilt Mathlib (do this once; avoids ~1h compile)
lake build                     # compile the project — should be green
```

Verify a result is honest (no hidden `sorry`/axioms):

```sh
echo 'import KTAIT.ART
#print axioms KTAIT.AITProb.probabilistic_regulator_theorem' | lake env lean /dev/stdin
# → depends on axioms: [propext, Classical.choice, Quot.sound]
```

Use **VS Code / Cursor + the Lean 4 extension** for the interactive goal view.

## Repository layout

```
KTAIT/
├── Ontology.lean        — six typed KT roles + the part-whole guard
├── Basic.lean           — AITFrame; IK, NMAI, condStar; AIT laws as named Props
├── Probability.lean     — prefix machine, Bayes posterior, Lemma 1
├── ART.lean             — AITProb; ART Theorems 1–3 (+ sharp form), wrapper bound
├── Persistence.lean     — persistence + conservation ledger
├── SelfModel.lean       — temporal self-model (Prop. 3)
├── RegulatorSelection.lean — regulator selection (Prop. 1) + conditional ART form
├── SelfModelLimits.lean — self-model incompleteness (Prop. 4)
├── CoarseGraining.lean  — regulatory coarse-graining uncomputable (WP0193)
├── ToyModel.lean        — satisfiability witnesses (non-vacuity)
└── BadStatements.lean   — the guards bite (documentation-by-compilation)
LEARNING_LOG.md          — a short note per milestone
```

## Status & future work

The arithmetic/probabilistic KT corpus is complete. Documented future work:

- **Easy/medium extensions:** the contrast-fiber posterior (Eq. 26); ART low-complexity
  shrinkage; the boundary-as-sufficient-statistic; the orbit-label / generalized-energy theorem.
- **Geometry track:** the Lie-group / Noether layer of the world-models paper (needs Mathlib
  differential geometry).
- **Level 2 (grounding):** replace the abstract complexity/computability hypotheses with a
  concrete universal prefix machine, so `K` is computability-backed rather than axiomatic.

See **WP0195** for the full inventory and roadmap.

## Citing

See `CITATION.cff` (GitHub shows a "Cite this repository" button). BibTeX:

```bibtex
@software{ruffini2026ktait,
  author  = {Ruffini, Giulio},
  title   = {{KTAIT}: A {Lean}~4 Formalization of {Kolmogorov} {Theory}},
  year    = {2026}, version = {0.1.0},
  doi     = {10.5281/zenodo.20969562},
  url     = {https://github.com/giulioruffini/KTAIT},
  note    = {Companion: BCOM Working Paper WP0195 (bundled in \texttt{docs/})}
}
```

Permanent archive (DOI): **[10.5281/zenodo.20969562](https://doi.org/10.5281/zenodo.20969562)**.
The companion working paper **WP0195** is bundled in `docs/WP0195.pdf`.

## License

Apache-2.0. Built with [Claude Code](https://claude.com/claude-code).
