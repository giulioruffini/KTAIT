# KTAIT — Kolmogorov Theory, formalized in Lean 4

A [Lean 4](https://leanprover.github.io/) + [Mathlib](https://github.com/leanprover-community/mathlib4)
formalization that **machine-checks the corollaries of Kolmogorov Theory (KT)** against an
explicit, *satisfiable* axiomatic interface to algorithmic information theory (AIT) and Bayesian
inference.

> **What it certifies:** the KT results — the Algorithmic Regulator Theorem and its Good
> Algorithmic Regulator extension, persistence and its conservation ledger, universal-prior
> regulator selection, the temporal self-model, self-model incompleteness, the uncomputability of
> regulatory coarse-graining, the algorithmic-emergence barriers, and the inheritance-architecture
> bounds — follow *logically* from a clearly delimited layer of standard AIT/probability facts,
> with no `sorry`. The KT ontology is **typed** so that structural errors (e.g. comparing a
> pattern to its own part) cannot even compile.

It does **not** re-prove classical AIT. Those results (the coding theorem, symmetry of
information, Bayes' rule, Kleene/Rice/Chaitin, Vereshchagin–Vitányi) are an honest, named
**axiom layer**; the contribution is checking that the *new* KT corollaries are correctly typed
and genuinely entailed by it.

- **Toolchain:** Lean `v4.31.0`, Mathlib `v4.31.0` (both pinned).
- **Companion working paper:** BCOM **WP0195** — methodology, full theorem inventory with
  per-statement status, and roadmap. Bundled as `docs/WP0195.pdf`; canonical source
  `docs/WP0195.tex`.
- **Source theory:** the KT papers. Pattern Persistence (WP0162), Agent Know Thyself (WP0192),
  Regulatory Coarse-Graining (WP0193), *An Algorithmic-Information-Theoretic Regulator Theorem*
  (Entropy 2026 28:257), the Good Algorithmic Regulator Theorem (WP0203), Algorithmic Emergence
  (WP0007), Inheritance Architecture (WP0058), Push and Pull (WP0186), Agentoptosis (WP0207),
  Pattern, Persist! (WP0216), Algorithmic Information Conservation (WP0218), and the
  simulation, computation-core, and certified-program papers (WP0215, WP0229, WP0228).

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
AIT hypotheses. WP0195 carries the per-statement inventory; this table names the flagship
declarations by source paper.

| Source | Result | Lean name | Module |
|---|---|---|---|
| ART (Entropy 2026) | **Theorem 2** — `P((W,R)\|x,E) ≤ C·2^{M(W:R)}·2^{−Δ}` | `probabilistic_regulator_theorem` | `ART` |
| ART | Theorem 2, **sharp** (`·2^{−K(R)}`) + `2^{−K(R\|W)}` form | `..._sharp`, `..._conditional` | `ART`, `RegulatorSelection` |
| ART | **Theorem 1** (posterior tilt), **Theorem 3** (on/off evidence `≍ 2^{Δ}`) | `theorem1_posterior_tilt`, `theorem3_onoff_evidence` | `ART` |
| ART | **wrapper bound** Eq. (6) — *derived* from the coding theorem; single-episode shrinkage | `wrapper_bound`, `low_complexity_shrinkage` | `ART` |
| ART | **Lemma 1** — Bayes posterior `= 2^{−\|p\|}/m(x)`, sandwiched by the coding theorem | `lemma1_posterior_bounds` | `Probability` |
| WP0162 | **Persistence** = temporal self-information; **conservation ledger** (Prop. 2) + trade-off | `pers_eq_nmai`, `persistence_conservation`, `conservation_tradeoff` | `Persistence` |
| WP0162 | **Regulator selection** (Prop. 1); contrast-fiber posterior (Eq. 26) | `regulator_selection`, `contrast_posterior_ranks_by_complexity` | `RegulatorSelection`, `Contrast` |
| WP0162 / WP0192 | **Temporal self-model** (Prop. 3); **self-model incompleteness** (Prop. 4 / Principle 1) | `self_regulation_temporal_model`, `quine_floor`, `self_prediction_dichotomy`, `chaitin_blocks_minimality` | `SelfModel`, `SelfModelLimits` |
| WP0162 App. C | Conserved orbit labels; abstract Noether core | `genEnergy_conserved`, `trajLabel_conserved` | `OrbitLabel`, `NoetherFlow` |
| WP0193 | **Coarse-graining uncomputability** (Thm B / Cor. B) | `theoremB`, `corollaryB` | `CoarseGraining` |
| WP0203 | **GART** — the regulation balance, its deficit and cyclic forms, the finite rate core | `balance`, `deficit`, `cyclic_form`, `balance_rate_finite` | `RegulationBalance` |
| WP0203 | Grounding transfer, initial-information and residual bounds, exact counterfactual balance, self-regulation corollary | `gap_transfer`, `repaired_good_regulator`, `simple_regulator_forces_residual`, `exact_counterfactual_balance`, `self_regulation_forces_self_model` | `GroundedRegulation` |
| WP0203 | Reconstruction from complete reversible records; lossless model-based regulation | `null_from_complete_records`, `model_initial_information` | `ReversibleReconstruction`, `GenerativeRegulation` |
| WP0203 | **ART with the residual** — two-sided posterior bound, bridge identity, nonnegative excess | `art_with_residual`, `bridge_identity`, `excess_nonneg` | `ARTExactForm` |
| WP0203 | Probabilistic ART conditioned on a residual budget; the unadjusted-threshold guard | `conditional_art_tail`, `conditional_deficit_zero`, `unadjusted_threshold_counterexample` | `ResidualTransfer` |
| WP0203 | Chance regulation under independent initial sampling | `independent_regulation_threshold`, `independent_regulation_given_residual` | `IndependentRegulation` |
| WP0203 | A cheap regulator cannot model; multiplicity witnesses | `simple_regulator_cannot_model`, `perpair_does_not_lift` | `ModelOrPay` |
| WP0007 | Counting bound, construction barriers, no computable schedule | `counting_bound`, `no_compression_improver`, `no_computable_schedule` | `AlgorithmicEmergence` |
| WP0007 | **Functional-core benchmark** — a shortest task-equivalent representative exists and costs no more than an implementation plus its wrapper | `exists_functional_core`, `functional_core_le_implementation` | `FunctionalCore` |
| WP0058 | Decoder existence and its limits (Prop. 1, axiom-free); write-back channel bound (Props. 2–3); optimal retention kernel (Prop. 4) | `no_universal_decoder`, `channel_bound`, `bangbang_optimal` | `Decoder`, `WriteBack`, `Retention` |
| WP0186 | Push–pull necessity and sufficiency (Thms 1–2) | `theorem1_necessity`, `theorem2_sufficiency`, `regulation_iff` | `PushPull` |
| WP0202 App. A | Circular shifts are not a null model for algorithmic mutual information | `shift_is_not_a_null` | `ShiftInvariance` |
| WP0207 | Agentoptosis: self-targeting requires an agent and a target | `collective_self_targeting_requires_agent` | `Agentoptosis` |
| WP0216 | Pattern, Persist! ontology; **Algorithmic Persistence Balance** and the flow corollaries | `persists_iff_nmai`, `algorithmic_persistence_balance`, `bounded_persistence_forces_flow` | `PatternPersist`, `PersistenceFlow` |
| WP0218 | Localization algebra, reversible balance, recoverable-description overlap; canonical token transport | `localization_conserved_exact`, `recoverable_description_overlap`, `transport_plan_exists` | `Localization`, `TokenTransport` |
| WP0215 | Common-semantics bound; boundary vs. organization; finite-horizon unfolding | `common_semantics_bound`, `boundary_eq_of_iso`, `no_fixed_unfolding_covers_all_horizons` | `IS/CommonSemantics`, `IS/Boundary`, `IS/Unfolding` |
| WP0229 | Deterministic experiments, observability, coordinate overwrites | `observable_conjugacy`, `overwrite_rigidity` | `ComputationCores` |
| WP0228 | Certified programs: marking budget and coverage, prefix-free descriptors, finite counting, whole-function minima | `marking_step_covers`, `gamma_prefix_free`, `whole_function_minimum_exists` | `CertifiedPrograms/*` |
| WP0236 | One diagonal: Lawvere fixed point, Cantor and Kleene faces, valence self-scoring bar | `lawvere_fixed_point`, `self_prediction_bar` | `Lawvere` |

Plus: typed KT **ontology** with a part-whole guard (`Ontology`), **satisfiability witnesses**
(`ToyModel`), and documented **guards** — the whole-vs-part error and the `y`-vs-`y*` conditioning
error fail to compile (`BadStatements`).

Scope notes that the inventory keeps explicit: `FunctionalCore` minimizes description length for a
declared behavior, not predictive loss or runtime, and claims no core-extraction algorithm.
`CertifiedPrograms` proves the finite marking scan, descriptor parsing, and counting core of WP0228;
its `combine_decoder_costs` checks arithmetic from supplied scalar bounds and does not prove decoder
complexity bounds, and the whole-function AIT theorem is not yet instantiated. The WP0203 conditional
probabilities require positive finite conditioning mass, and the classical coding and Kraft facts
they rest on remain named hypotheses.

## The axiom layer (what we assume)

Standard, classical results — assumed, not re-proved:

- **Complexity:** invariance theorem; coding theorem `−log m(x) = K(x) ± O(1)` (uncond. & cond.);
  Kraft–McMillan; symmetry of information `I_K(x:y) = K(x) − K(x|y*) + O(log)`; chain rule.
- **Probability:** Solomonoff–Levin universal semimeasure; Bayes' rule with the deterministic
  likelihood `P(x|p)=𝟙{U(p)=x}`.
- **Computability/logic:** Kleene's recursion theorem; Rice's theorem; Chaitin's incompleteness;
  Vereshchagin–Vitányi (structure-function uncomputability).

Each fact enters as a named `Prop` about a frame and is consumed as an explicit hypothesis in the
theorem that needs it; `docs/axiom-audit.md` records the audit.

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

### Keep the Lean and the papers in step

The papers that cite KTAIT say their results are "machine-checked in Lean 4" and point readers
here. That claim is about *this repo*, not about anyone's laptop, so drift is a correctness bug.

```sh
git config core.hooksPath .githooks   # one-time: arms the pre-push guard
./scripts/check_sync.sh               # sorry-free? WP0195 current? citing papers resolve? pins hold?
./scripts/check_sync.sh --released    # + tree clean and HEAD pushed — run before a paper goes public
```

`check_sync.sh` fails if a proof contains `sorry`, if `docs/WP0195.tex` is missing a module or
theorem, if any `\lean{...}` or `\ktait{...}` name cited by a paper in `docs/citing-papers.txt`
no longer resolves, if a declaration's statement changed while its prose stood still, if prose
here numbers a result instead of naming it, if a paper states a result with no recorded formal
status, or if a paper's provenance pin lacks a declaration it cites. The pre-push hook and CI both
run it, so a rename cannot silently break a paper's claim. **Register a paper in
`docs/citing-papers.txt` when it starts citing `\lean{}` or `\ktait{}` names** — otherwise nothing
guards it. When you change the Lean, commit the Lean **and** the affected papers together.

Two macros carry the citations. `\lean{...}` is incidental Lean text — an identifier, a filename,
a core axiom. `\ktait{decl}` is a machine-checked-claim citation: the prose at that point asserts
a result and names the KTAIT declaration that proves it, so "which claims are machine-checked" is
a lookup, not an interpretation. `\ktait{}` admits declarations only — the guard rejects filenames,
paths, and core axioms inside it. Canonical preamble definition, beside the existing `\lean`:

```latex
\newcommand{\ktait}[1]{\texttt{\small #1}}
```

### Claim coverage: the check that runs the other way

Every check above starts from something a paper already cites and asks whether it still holds up.
None of them can see a result the paper states and never formalizes, because there is no citation
to follow. In August 2026 WP0007 gained a corollary with no Lean counterpart; the declaration it
did cite was untouched, so nothing drifted and every check stayed green while the paper disclaimed
a formalization that standing practice required.

`scripts/claim_coverage.py` closes that direction. It reads every `theorem`, `proposition`,
`corollary`, `lemma`, `claim`, and `conjecture` in the registered papers and requires each to carry
a recorded formal status — a LaTeX comment contiguous with the environment:

```latex
% ktait: relational_optimality_barrier
\begin{Corollary}[Relational optimality barrier]\label{cor:relational-optimality}

% ktait: none -- classical Kolmogorov-Solomonoff-Chaitin, proved here at paper level; it
%   enters the development as the named hypothesis KUncomputable and is not re-proved
\begin{Theorem}[Kolmogorov, Solomonoff, Chaitin]\label{thm:uncomp}
```

Declaration names are verified against what KTAIT defines, so an annotation cannot rot the way a
prose appendix can; `none` requires a reason, because bare `none` reads as an oversight and is
rejected as one. A `\ktait{}` inside the body counts on its own. Claims are keyed by `\label`, so
registering a new version of a paper inherits the statuses already recorded and only genuinely new
results fire.

What it does **not** do is judge whether a Lean statement faithfully renders the prose. Nothing
mechanical can; that is what the `formalize` lens of the `landau` skill is for. This check asks
only that the question have been asked and answered somewhere other than in someone's head.

```sh
python3 scripts/claim_coverage.py --check     # run by check_sync.sh
python3 scripts/claim_coverage.py --report    # per-claim status census
python3 scripts/claim_coverage.py --accept    # re-baseline docs/claim-coverage-baseline.tsv
```

Ratchet, not a wall: the results predating the check are recorded as `legacy` and stay quiet.
Restating one is a warning, and an error under `--released`.

### Provenance pins: the commit a paper points readers at

A paper's machine-checked claim names one commit ("source commit `8c602ff`"). The checks above
resolve cited names against HEAD, so a pin that falls behind the declarations a paper cites stays
invisible to them. In September 2026 WP0203 added `ARTExactForm.lean` and cited nine of its
declarations while keeping a pin from before the module existed; three releases passed every check.

`scripts/check_pins.py` reads each registered paper's pinned commit and verifies that the tree there
defines every `\ktait{}` name the paper cites. The last-registered version of each paper is
enforced; archived versions warn. Pin the last commit that changed `KTAIT/`
(`git log -1 --format=%H -- KTAIT/`), never a docs-only registration commit.

## Repository layout

```
KTAIT/
├── Ontology, Basic, Probability, ToyModel, BadStatements   — types, frame, witnesses, guards
├── ART, RegulatorSelection, Contrast                       — ART Theorems 1–3, selection, Eq. 26
├── Persistence, SelfModel, SelfModelLimits, Lawvere        — persistence, self-model, incompleteness
├── CoarseGraining, AlgorithmicEmergence, FunctionalCore    — WP0193, WP0007
├── RegulationBalance, GroundedRegulation, ARTExactForm,
│   ResidualTransfer, IndependentRegulation, ModelOrPay,
│   ReversibleReconstruction, GenerativeRegulation          — WP0203 (GART)
├── Decoder, WriteBack, Retention                           — WP0058
├── PushPull, ShiftInvariance, Agentoptosis                 — WP0186, WP0202, WP0207
├── PatternPersist, PersistenceFlow                         — WP0216
├── Localization, TokenTransport                            — WP0218
├── OrbitLabel, NoetherFlow, ComputationCores               — orbit labels, Noether core, WP0229
├── IS/  (CommonSemantics, Boundary, Unfolding)             — WP0215
└── CertifiedPrograms/  (Certification, Marking, Encoding, Counting) — WP0228
docs/WP0195.tex          — the status paper (canonical; symlinked from the working-drafts folder)
docs/citing-papers.txt   — registry of papers whose \lean{}/\ktait{} citations the guard checks
scripts/                 — check_sync.sh and the checks it runs
LEARNING_LOG.md          — a short note per milestone
```

## Status & future work

The original five roadmap phases (WP0162 Props. 1–4, WP0192 Principle 1, WP0193 Thm B, the full
probabilistic ART chain) are complete, and the development has since grown module by module with
the KT papers it serves. Documented future work:

- **WP0228:** partial-recursive decoder correctness, the executable source-to-finite-vertex
  correspondence, and uniform prefix-machine compilation, so the whole-function AIT theorem is
  instantiated rather than assumed.
- **Geometry track:** the Lie-group / Noether layer of the world-models paper (needs Mathlib
  differential geometry); `NoetherFlow` holds the abstract core.
- **Level 2 (grounding):** replace the abstract complexity/computability hypotheses with a
  concrete universal prefix machine, so `K` is computability-backed rather than axiomatic.

See **WP0195** for the full inventory and roadmap.

## Citing

See `CITATION.cff` (GitHub shows a "Cite this repository" button). BibTeX:

```bibtex
@software{ruffini2026ktait,
  author  = {Ruffini, Giulio},
  title   = {{KTAIT}: A {Lean}~4 Formalization of {Kolmogorov} {Theory}},
  year    = {2026},
  url     = {https://github.com/giulioruffini/KTAIT},
  note    = {Cite a specific commit; this source tree has no software DOI.
             Companion paper: BCOM WP0195, doi:10.5281/zenodo.21008868}
}
```

**This repository has no software DOI.** There is no Zenodo deposit of this
source tree. Cite it by URL plus the commit hash you built against.

The Zenodo records belong to the companion *paper*, WP0195 *A Lean 4
Formalization of Kolmogorov Theory (KT-LEAN)* — resource type Preprint,
CC-BY-4.0, not Apache-2.0, and not this code:

| DOI | What it is |
|---|---|
| [10.5281/zenodo.21008868](https://doi.org/10.5281/zenodo.21008868) | **Concept DOI** — always resolves to the latest version of the paper. Cite this one. |
| 10.5281/zenodo.21982845 | Version DOI, WP0195 v0.6.0 (2026-08-17) |
| 10.5281/zenodo.21838718 | Version DOI, WP0195 v0.5.0 (2026-08-07) |
| 10.5281/zenodo.21737260 | Version DOI, WP0195 v0.4.0 (2026-08-01) |
| 10.5281/zenodo.21008869 | Version DOI, WP0195 v0.1.0 |
| 10.5281/zenodo.20969562 | Superseded earlier deposit of the same paper. Do not cite. |

The paper is also bundled in `docs/WP0195.pdf`. If a software DOI is ever
wanted, mint it through the GitHub–Zenodo release integration so it inherits
Apache-2.0.

## License

Apache-2.0. Built with [Claude Code](https://claude.com/claude-code).
