# Exact content-preserving reduction: Lean verification

Base: 675a2249404053112340fc3f43ac24730a3686bb. Branch: wp0215-coarsest-content-20261112. No remote push is authorized.

The module KTAIT/IS/MinimalRealization.lean proves the coarsest deterministic content quotient, onto factorization and transport, refinement by inputs or content, and the isomorphism of reachable quotients under equal initialized response functions. The unmarked theorem permits empty state types; the two-system corollary supplies marked initial states. All input maps are total. No finiteness, computability, smoothness, physical admissibility, or experiential premise is asserted.

- Full lake build: successful, 8,621 jobs, Lean/mathlib 4.31.0 (build.log).
- Axiom audit: all 19 new theorem declarations; 11 use no axioms, 8 use only subsets of propext, Classical.choice, Quot.sound (audit.lean, axioms.log).
- Sync: passed with the two WP0215 entries temporarily directed to the reviewed Part 1 manuscript worktree; canonical registry paths restored afterward (sync.log). Other external papers are absent from this isolated worktree and explicitly skipped.
- WP0195: rebuilt to 55 pages; new module row, explanatory entry, and inventory rows; extracted text contains the new entries without control characters (wp0195-build.log). Existing long-identifier overflow warnings elsewhere remain.

The source pin remains provisional until K approves publication. The release guard must fail while this branch has no published upstream.
