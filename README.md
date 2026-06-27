# KTAIT — Kolmogorov Theory / AIT interface, formalized in Lean 4

A small, typed, **axiomatic** KT/AIT interface in Lean 4 + Mathlib. We machine-check
that the **KT corollaries** (Proposition 1, the persistence equation) follow logically
from a clearly stated **AIT interface** — and that the ontology is typed so structural
bugs (comparing a whole to its own part) cannot hide.

## The one rule

> **AIT theorems are allowed to be _axioms_ at this stage. KT corollaries must be
> _proved_ from those axioms with no `sorry`.**

If a KT corollary needs a `sorry`, that is a real gap in the paper. If an AIT fact is
an `axiom`, that is honest and expected at Level 1.

## Scope guardrail

> **Level 1 = axiomatic, typed KT/AIT interface.** AIT theorems are axioms; KT
> corollaries are proved from them without `sorry`; a toy model witnesses consistency.
> We are forcing the ontology — substrate, pattern, readout, regulator, self-code,
> time — not formalizing Kolmogorov complexity. Levels 2 (computability-backed `K`)
> and 3 (universal prior / ART proof) are future work.

## Paper statement (earned by this formalization)

> *This formalization checks the dependency structure of the KT corollaries relative
> to an explicit AIT interface; it does not re-prove the AIT theorems themselves.*

## Build

```sh
lake exe cache get   # download prebuilt Mathlib (do this once)
lake build           # compile the project; should be green
```

Toolchain is pinned in `lean-toolchain` (Lean v4.31.0); Mathlib is pinned in
`lakefile.toml`. Use VS Code + the Lean 4 extension for the interactive goal view.

## Milestones

- **M0** — Toolchain & hello-Lean ✅
- **M1** — Typed ontology (`KTAIT/Ontology.lean`) ✅
- **M2** — AIT interface (`KTAIT/Basic.lean`) ✅
- **M2.5** — Probabilistic ART, Level 1.5 (`KTAIT/ART.lean` Theorem 2, `KTAIT/Probability.lean` Lemma 1) ✅
- **M3** — Persistence (`KTAIT/Persistence.lean`) ✅
- **M4** — Self-model corollary, Prop. 3 (`KTAIT/SelfModel.lean`) ✅
- **M5** — Toy model + bad statements (`KTAIT/ToyModel.lean`, `KTAIT/BadStatements.lean`) ✅

See `LEARNING_LOG.md` for a running 2–3 line note per milestone.

## What is proved (Level 1 + the probabilistic ART of Level 1.5)

- **`AITProb.probabilistic_regulator_theorem`** — ART Theorem 2 (the real posterior
  bound `P((W,R)|x,E) ≤ C·2^{M(W:R)}·2^{−Δ}`).
- **`PrefixMachine.lemma1_posterior_bounds`** — Lemma 1, the Bayes↔Kolmogorov bridge.
- **`self_regulation_temporal_model`** — Prop. 3, self-regulation requires a temporal
  self-model.
- **`pers_eq_nmai`**, **`persistent_pos`** — persistence as temporal self-information.
- All KT corollaries are `sorry`-free; `#print axioms` shows only Lean core
  (`propext`, `Classical.choice`, `Quot.sound`) plus the named AIT *hypotheses*.
- Non-vacuity witnessed in `ToyModel.lean`; the typed/`y*` guards bite in
  `BadStatements.lean`.
