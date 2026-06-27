---
name: lean-kt
description: Work on the KTAIT Lean 4 formalization of Kolmogorov Theory (KT) / algorithmic information theory. Use when proving or extending KT theorems in Lean, adding to the KTAIT repo, or formalizing a result from the KT papers (WP0162/WP0192/WP0193, the ART paper). Covers the methodology (AIT facts as axioms, KT corollaries proved sorry-free), build workflow, proof idioms, and conventions.
---

# Lean KT — formalizing Kolmogorov Theory in Lean 4

Goal: machine-check that **KT corollaries follow from an explicit AIT interface**, with the
ontology typed so structural bugs can't compile. Repo: `KTAIT` (Lean 4.31 + Mathlib v4.31).
Status tracker: **BCOM WP0195**. Papers live in `../papers/` (read them before formalizing —
quote statements faithfully; do not paraphrase from memory).

## The one rule (non-negotiable)
- Standard **AIT and probability** theorems (invariance, coding theorem, symmetry of
  information, Kraft, Bayes, Solomonoff–Levin, Kleene/Rice/Chaitin, Vereshchagin–Vitányi) may
  be **assumed**. KT corollaries must be **proved** from them with **no `sorry`**.
- **Soundness:** state each AIT fact as a **named `Prop` hypothesis** (or a `def ... : Prop`
  consumed by a theorem) — NEVER as a global `axiom (F : Frame) : P F`. A global ∀-frame
  axiom is inconsistent here (build a frame with `slack=0` violating it → `False`). With
  hypotheses, `#print axioms` shows only Lean core; the toy model witnesses satisfiability.

## Build & verify
```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build KTAIT.<Module>     # fast single-module build (no-Mathlib modules ~0.3s; with Mathlib ~5s)
lake build                    # full project (gate after a milestone)
```
After every KT proof, check it is honest:
```sh
echo 'import KTAIT.<Module>
#print axioms KTAIT.<theorem>' > /tmp/ax.lean
lake env lean /tmp/ax.lean    # expect: [propext, Classical.choice, Quot.sound] (or fewer) — NO sorryAx, NO custom axioms
```

## Proof idioms that keep recurring
Almost every KT corollary = **rearrange an AIT identity, then close with `omega`/`gcongr`**:
- Integer exponents/gaps: cast to `ℤ`, `simp only [IK]` to unfold, then `omega`.
- Real powers: `zpow` over `ℤ` on `ℝ`. Split/combine with `zpow_add₀ (by norm_num : (2:ℝ)≠0)`,
  `zpow_sub₀`. Monotone lift `a≤b → 2^a≤2^b` via `gcongr` (it auto-discharges side goals from
  context by `assumption`/`positivity`, and often leaves only `1 ≤ 2` → finish with `norm_num`).
- Division bounds: `div_le_div_iff₀ (0<b)(0<d)`, `div_le_div₀ (0≤c)(a≤c)(0<d)(d≤b)`,
  `mul_div_mul_comm`, `mul_div_right_comm`, `mul_le_mul_of_nonneg_right`.
- `2^(neg) ≤ 1`: `zpow_le_one_of_nonpos₀ (by norm_num) (by omega)` — the `n≤0` side is `omega`, not `positivity`.
- `|·|` over `ℤ`: `Int.natAbs_neg`, or `omega` (handles `Int.natAbs`).
- Order-equivalence corollaries (regulator selection, conservation trade-off): `simp only [<identity def>]; constructor <;> intro h <;> omega`.

## Gotchas (learned the hard way)
- `F.foo` is field/namespace projection of the *value's type*; a top-level `def foo` is `foo F`.
- Numerals at a projected carrier type (`SomeFrame.Obj`) fail `OfNat` synthesis — write `(3 : Nat)`.
- `relaxedAutoImplicit = false` (our config): an undefined multi-char identifier is a hard ERROR
  (good) — import the module that defines it (e.g. `Time` lives in `Ontology`).
- `decide` refuses goals with free variables even if value-independent — `simp [defs]` to reduce them away first.
- Mathlib renames: e.g. `div_le_div_iff` → `div_le_div_iff₀`. `grep` in `.lake/packages/mathlib` to find current names; use `exact?`/`apply?`.
- Unused-variable / unused-simp-arg warnings often reveal a cleaner, stronger statement — chase them.

## Conventions (do every milestone)
1. Append a 2–3 line note to `LEARNING_LOG.md` (what we learned / what tripped us up).
2. Update **WP0195** (`../../BCOM WPs and Blogs/working_drafts/WP0195-Lean_KT_Formalization/main.tex`):
   mark the result Proved in the inventory table + proved list; recompile with `latexmk -pdf`.
3. Run `#print axioms` on the new KT theorem; record the result.
4. Commit + push (`Co-Authored-By: Claude ...`). Branch off `main` only for larger work.

## File map
`Ontology` (typed roles, part-whole guard) · `Basic` (AITFrame, IK/NMAI/condStar, named AIT
laws) · `Probability` (PrefixMachine, Bayes posterior, Lemma 1) · `ART` (AITProb, Theorems
1/2/2-sharp/3, wrapper bound) · `Persistence` (Pers, conservation) · `SelfModel` (Prop 3) ·
`RegulatorSelection` (Prop 1) · `SelfModelLimits` (Prop 4) · `CoarseGraining` (WP0193) ·
`ToyModel` (satisfiability witnesses) · `BadStatements` (guards bite).

## Roadmap status
Phases 1–5 DONE: WP0162 (Props 1–4) + WP0192 (Principle 1) + WP0193 (Thm B) + full
probabilistic ART, all sorry-free. Future: **geometry track** (entropy-27 Lie/Noether) and
**Level-2 grounding** (computability-backed `K` from a real universal machine, replacing the
abstract `Computable`/`KIsShortest`/`VV` hypotheses).
