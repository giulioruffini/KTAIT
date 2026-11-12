# Future-equivalence quotient: Lean verification

Base: 675a2249404053112340fc3f43ac24730a3686bb. Branch: wp0215-coarsest-content-20261112. No remote push is authorized.

The core future-equivalence result and both refinement laws already belong to WP0004 v0.4.0. KTAIT/OperationalAlgebra.lean is imported unchanged from its pinned commit 062f32330d3b234dbb808c8e658e45e960d29d8e; its Git blob is 6ada0af2e73fdecdfb758790c0b9806566a03c17 (provenance.json). ComputationCores and ClosureInvariance have identical blobs at the two source pins. InformationalSelfModel from the WP0215 base is retained. No WP0004 manuscript source was changed.

KTAIT/IS/MinimalRealization.lean now constructs the quotient updates/readout, specializes the existing fiber-factorization theorem, proves the quotient accessible and observable, and applies the existing observable-conjugacy theorem to its reachable part. The arbitrary-relation lemma strengthens the existing Setoid statement. Execution abbreviates ComputationCores.run; no independent equivalence, stability, content-refinement, input-refinement, or conjugacy proof remains.

- Full lake build: successful, 8,622 jobs, Lean/mathlib 4.31.0 (build.log).
- Axiom audit: 14 quotient-adapter/helper theorems plus eight reused theorems; seven use no axioms, fifteen use only subsets of propext, Classical.choice, Quot.sound (audit.lean, axioms.log).
- Library sync: passed with the canonical registry (sync.log). The isolated worktree lacks canonical external manuscript paths; draft-source and pin checks are recorded separately in the WP0215 delivery after it adopts the new commit.
- WP0195: rebuilt to 55 pages; the imported module and quotient specialization have module rows, explanatory entries, and inventory rows (wp0195-build.log). Existing long-identifier overflow warnings outside the added entries remain.

These exact set-level results assert neither an effective general quotient construction nor smoothness, physical admissibility, or experiential preservation. The source pin remains provisional until K approves publication. The release guard must fail while this branch has no published upstream.
