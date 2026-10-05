# WP0218 Appendix E: singleton support layers, axiom audit

October 5, 2026. `KTAIT/StateGraph.lean` checks that a transition-support relation with exactly one allowed successor and one allowed predecessor at every state is the graph of a permutation, that exact-step layers are then singletons, and that the permutation's orbit label (`OrbitLabel.genEnergy`) is conserved along allowed transitions. The empty state space is covered; no finiteness is assumed.

`#print axioms` on the seven theorems reports Lean core axioms only: `[Classical.choice, Quot.sound]` for `permGraph_of_unique`; `[propext, Classical.choice, Quot.sound]` for `unique_of_permGraph`, `unique_iff_permGraph`, `steps_iff_pow`, `steps_unique_succ`, `steps_unique_pred`, and `orbit_label_of_unique`. This per-declaration listing was rechecked during WP0218 draft-4 integration. No `sorryAx`, no custom axioms, no AIT frame. Full library build and `scripts/check_sync.sh` pass.

Not formalized, by design: the identification of bounded recovery advice (`O(1)` bits) with the singleton condition. The former is weaker and is what WP0218's reversible invariance lemma consumes; Appendix E states the distinction in prose.
