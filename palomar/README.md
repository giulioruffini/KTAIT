# Palomar submission package

A thin Comparator wrapper for the Palomar registry
(https://palomar-registry.org), restating five theorems of the KTAIT library
— the KT conservation–localization–persistence spine — over Mathlib alone.

- `Challenge.lean` — the audited statement surface: definitions plus the five
  compared theorems with placeholder `sorry` proofs.
- `Solution.lean` — the same definitions (byte-identical preamble) with the
  proofs of the substantive development carried over, plus Solution-only
  auxiliary lemmas.
- `comparator.json` — the compared declarations and permitted axioms.
- `formalization.yaml` — provenance, sources, automation, and fidelity notes.

The substantive development is the KTAIT library at the repository root; its
theorem inventory is tracked in BCOM WP0195 (`../docs/WP0195.tex`). This
wrapper can be deleted without loss to the library.

Verify before submitting:

```sh
../scripts/check_palomar.sh
```

which checks preamble identity, builds both modules, and confirms every
compared declaration depends only on `propext`, `Classical.choice`, and
`Quot.sound`.
