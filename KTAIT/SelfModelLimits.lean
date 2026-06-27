/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Probability

/-!
# KTAIT.SelfModelLimits — Principle 1: self-model incompleteness (Phase 4)

WP0192 Principle 1 / WP0162 Proposition 4: an embedded agent cannot jointly secure
(i) usable exactness, (ii) lossless completeness, and (iii) verifiable minimality of an
internal self-model. The three fail for THREE INDEPENDENT reasons, formalized here:

* **Reflexive regress / quine floor** (`quine_floor`): completeness costs `≥ K(A)`.
* **Computational diagonalization** (`self_prediction_dichotomy`): no consulted,
  contravenable self-prediction is exact.
* **Algorithmic ceiling** (`chaitin_blocks_minimality`): Chaitin's bound blocks certifying
  near-minimality for complex outputs.

Per the project methodology, the standard computability theorems (Kleene's recursion
theorem, Chaitin's incompleteness) enter as named hypotheses/axioms; the content here is
the KT reading of their consequences for self-modeling.
-/

namespace KTAIT

namespace PrefixMachine

variable (M : PrefixMachine)

/-- `K` is the length of the SHORTEST program (the defining property of Kolmogorov
    complexity): any program producing `x` is at least as long as `K x`. -/
def KIsShortest : Prop := ∀ (x : M.Out) (p : M.Prog), M.U p = x → M.K x ≤ M.len p

/-- **Obstruction 1 — the quine floor.** Any *lossless* internal self-model `Â` (a program
    that regenerates `A`, i.e. `U Â = A`) has length at least `K(A)`. Lossless completeness
    survives only as a compressed self-quine bounded below by the quine floor. -/
theorem quine_floor (hK : M.KIsShortest) {A : M.Out} {selfA : M.Prog} (h : M.U selfA = A) :
    M.K A ≤ M.len selfA := hK A selfA h

/-- **Obstruction 3 — the Chaitin ceiling blocks verifiable minimality.** If certified lower
    bounds on complexity are capped at a ceiling `c` (Chaitin's incompleteness), then for any
    output `x` whose complexity exceeds `c+1` the near-minimality bound `K x > K x − 1`
    cannot be certified. So an agent cannot verify its self-model is (near-)minimal. -/
theorem chaitin_blocks_minimality
    (Cert : M.Out → ℕ → Prop)
    {c : ℕ} (chaitin : ∀ x n, Cert x n → n ≤ c)
    {x : M.Out} (hx : c + 1 < M.K x) : ¬ Cert x (M.K x - 1) := by
  intro h
  have := chaitin x (M.K x - 1) h
  omega

end PrefixMachine

/-- **Obstruction 2 — the self-prediction dichotomy (diagonalization).** An agent that
    *consults* an exact prediction `pred` of its own next action and *acts to contravene* it
    (`act = flip` with `flip` fixed-point-free) cannot have that prediction be exact:
    no consulted, contravenable self-model is exact. -/
theorem self_prediction_dichotomy {Action : Type} {flip : Action → Action}
    (hflip : ∀ a, flip a ≠ a) {pred : Action} {act : Action → Action}
    (hcontravene : act = flip) (hexact : act pred = pred) : False := by
  rw [hcontravene] at hexact
  exact hflip pred hexact

/-- The contravention map exists (non-vacuity of Obstruction 2): boolean negation has no
    fixed point, so an agent with a binary open choice can always falsify a consulted exact
    self-prediction. -/
example : ∀ a : Bool, (!a) ≠ a := by decide

end KTAIT
