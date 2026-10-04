# WP0218 completion account: axiom audit

October 4, 2026. `KTAIT/CompletionLedger.lean` states the reconstruction-and-capacity account with neutral names (grouped and ordered forms) and re-derives WP0216's five-record flow bound as the ordered instance with `k = 3`.

`#print axioms` on each of the eleven declarations reports only Lean core axioms: `[propext, Quot.sound]` for `grouped_completion_balance`, `grouped_bounded_internal_forces_external`, `grouped_internal_capacity`, `ordered_completion_balance`, `flowSplit5_iff_orderedSplit`, `orderedCost_internal_three`; `[propext]` for `orderedInfo_append`; `[propext, Classical.choice, Quot.sound]` for `orderedInfo_le_orderedCost`, `ordered_bounded_internal_forces_external`, `ordered_two_external_pigeonhole`, `apb_flow_from_ordered` (the `Classical.choice` dependence enters through `List` and `max` lemmas from Mathlib). No custom axioms and no `sorryAx`. The full library build and `scripts/check_sync.sh` pass.

Hypotheses are named frame facts: `CondSubadd`, `CondChain`, `ReconstructionBound`, `CIKCeiling`, and the ordered split `OrderedSplit`. The reconstruction allowance `δ` and the frame slack stay distinct; `(2 + k)·slack` counts hypothesis uses, with the split's slack covering the whole ordered split as one named estimate. The checks establish implications from these hypotheses, not the physical choice of a record class, a decoder, or a reversible realization.

Documentation repair in the same commit: the `PersistenceFlow` module overview now lists the initial retained state `σ_t` in `Ctx_{P,t}`, matching WP0216 draft9; the formal `Ctx` is an opaque object, so no theorem changed.
