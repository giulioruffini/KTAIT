# Axiom audit for Palomar submission (Phase A)

Date: 2026-08-19. Baseline commit: e281f54 (`main`).

## Finding

KTAIT contains no custom `axiom` declarations. Every AIT input is a named
`Prop` about a frame (`def ... : Prop` in the library), consumed as an
explicit hypothesis in each theorem signature. This is the architecture the
Palomar implementation proposal (§2) asks for as its target pattern; the
proposal's Phases B and C (interface design, mechanical refactor) are
therefore already satisfied and require no code change. The work that
remains is the Palomar-facing interface (Phases D–F).

The two grep hits for `axiom` in the source are docstrings in
`CoarseGraining.lean` and `ShiftInvariance.lean` explaining why global
axioms are not used: a global `axiom (F : AITFrame) : P F` would assert the
law for every frame, including hand-built frames that violate it, making
the environment inconsistent. `ToyModel.lean` witnesses that the hypothesis
set is satisfiable.

## Baseline `#print axioms` on flagship candidates

All 16 candidates report only Lean-core axioms, each a subset of
`[propext, Classical.choice, Quot.sound]` — exactly Palomar's permitted
set. No `sorryAx`, no `Lean.ofReduceBool`, no custom axiom.

| Theorem | Module | Axioms |
|---|---|---|
| `persistence_conservation` | Persistence | propext |
| `conservation_tradeoff` | Persistence | propext, Quot.sound |
| `meta_persistence` | Persistence | all three |
| `meta_persistence_limit` | Persistence | all three |
| `Localization.localization_sum_exact` | Localization | propext, Quot.sound |
| `Localization.localization_conserved_exact` | Localization | propext, Quot.sound |
| `Localization.localization_balance_reversible` | Localization | all three |
| `Localization.recoverable_description_overlap` | Localization | propext, Quot.sound |
| `Localization.recurrent_recoverability_persistence_bound` | Localization | all three |
| `AITProb.wrapper_bound` | ART | all three |
| `AITProb.probabilistic_regulator_theorem` | ART | all three |
| `AITProb.theorem3_onoff_evidence` | ART | all three |
| `PersistenceFlow.algorithmic_persistence_balance` | PersistenceFlow | propext, Quot.sound |
| `PersistenceFlow.bounded_persistence_forces_flow` | PersistenceFlow | propext, Quot.sound |
| `TokenTransport.transport_plan_exists` | TokenTransport | propext, Quot.sound |
| `TokenTransport.minimum_moved_mass` | TokenTransport | propext, Quot.sound |

## Named AIT hypotheses consumed by the flagship spine

Each theorem states the smallest interface it needs; none uses a monolithic
bundle. Sources: the AIT facts are standard (Li–Vitányi; Gács; Levin) and
are cited per-fact in the module docstrings and in WP0195.

| Hypothesis `Prop` | Defined in | Standard AIT content | Consumed by (flagship) |
|---|---|---|---|
| `SymmetryOfInformation F` | Basic | `I_K(x:y) = K(x) − K(x\|y*) + O(log)` | `persistence_conservation`, `meta_persistence`(+limit) |
| `Subadd F a b` | GroundedRegulation | `K(a) ≤ K(b) + K(a\|b) + slack` | `localization_balance_reversible`, `reversible_complexity_invariance` |
| `MutualChain F y R` | RegulationBalance | chain-rule form of mutual information | `recoverable_description_overlap` and descendants |
| `CondDataProcessing F D X Y` | Localization | `I_K(D:Y) ≤ I_K(X:Y) + K(D\|X) + slack` | `recoverable_description_overlap` and descendants |
| `AITProb.CodingLB c₁` / `CodingUB c₂` | ART | coding theorem, `m(x) ≍ 2^{−K(x)}` | `wrapper_bound`, ART Theorems 1–3 |
| `ConservationLedger F OW R` | Persistence | exact ledger `K(O_W) = I_K + K(O_W\|R*)` | `conservation_tradeoff` |

`localization_sum_exact`, `localization_conserved_exact`, and the
TokenTransport theorems are hypothesis-free: exact integer algebra and
finite combinatorics, no AIT input at all.

## Implication for the Palomar candidate

The conservation → localization → persistence spine proposed as the first
entry (proposal §12) is submission-ready at the axiom level. Statement
work, not proof work, is what remains: a thin `Challenge.lean` restating
the selected declarations over Mathlib-only imports, a `Solution.lean`
mapping them to the KTAIT proofs, `comparator.json`, and
`formalization.yaml`.

Regression guard: `scripts/check_sync.sh` already enforces sorry-freedom;
an axiom-footprint check over the Palomar declarations is added with the
Palomar layer so a future edit cannot silently reintroduce a custom axiom
into the submitted chain.
