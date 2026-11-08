# Informational self-model bound — November 8, 2026

Module: `KTAIT.InformationalSelfModel`, based on WP0215 source pin `27ef89636ac59d41840eb81e26841f5ef1735fe3`.

The module reuses `WriteBack.condIK`, whose value is an integer. `ModelParts` indexes candidate descriptions by their realizations, with a supplied admissibility predicate and remainder. `HasSelfModel` defines the proposed strict information threshold with a nonnegative integer tolerance.

`candidate_information_bound` proves the bound `B + c` from a uniform conditional-complexity bound on every admissible candidate and the named `RightProjection` coding premise. `all_information_le_tolerance` applies a previously chosen tolerance covering this bound. `no_informational_self_model` excludes every witness to the criterion. The statements do not establish physical admissibility, the decomposition of a thermostat, absence of reports, or an experiential interpretation of the criterion.

All three definitions have no axiom dependencies. Each new theorem depends only on `propext` and `Quot.sound`. The combined audit of WP0215's existing 133 declarations and these six declarations passes: 139 declarations, no custom axioms, and no `sorryAx`. Standard AIT projection is an explicit theorem premise, so it is not listed by `#print axioms`.

Validation: the module build and full `lake build` passed (Lean 4.31.0, mathlib v4.31.0; 8620 build jobs). WP0195 was updated at the module table, proved-corollaries list, and inventory and rebuilt. The declaration manifest was regenerated, and `scripts/check_sync.sh` passed. In the isolated worktree, external citing-paper paths are absent and are skipped by that guard; the separate 139-declaration WP0215 audit resolves the selected declarations directly.
