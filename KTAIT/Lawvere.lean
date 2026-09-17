/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.SelfModelLimits

/-!
# KTAIT.Lawvere — one diagonal, many limits (WP0236)

Lawvere's fixed-point theorem, in the set-theoretic (cartesian closed) form KT needs,
and the three KT instances WP0236 §"Consequence for the Lean layer" says should be
corollaries of one statement rather than separate interface facts:

* `lawvere_fixed_point` — a weakly point-surjective `f : A → A → B` forces every
  `t : B → B` to have a fixed point. The one-line diagonal.
* `fixed_point_free_forbids_surjection` — the contrapositive: a fixed-point-free
  endomorphism of `B` forbids any weakly point-surjective `A → (A → B)`.
* `kleene_face` — the positive face (O1 of WP0192): under a weakly point-surjective
  evaluator on codes, every code transformation has a fixed point. This is the *shape* of
  Kleene's recursion theorem; the recursion theorem proper additionally asserts that a
  universal machine's evaluator is weakly point-surjective, which remains an assumed input
  of the axiom layer (README §Computability). What this module removes is the need for a
  second, hand-rolled diagonalization for O2.
* `self_prediction_bar` — O2 of WP0192 as the contrapositive instance: a fixed-point-free
  action flip forbids a weakly point-surjective self-predictor.
* `valence_self_scoring_bar` — the new instance, the valence self-scoring bar of WP0236: the valence
  codomain `(-1, 1)` is open, so `v ↦ (v+1)/2` is a fixed-point-free endomorphism of it,
  and no agent can weakly point-surjectively index all valence-scorings of its own models.
* `cantor_bool` — the classical sanity instance (Cantor via boolean negation).

`self_prediction_dichotomy` in `SelfModelLimits` is left in place and is now redundant with
`self_prediction_bar`; WP0192 cites it by name.
-/

namespace KTAIT

/-- `f` is *weakly point-surjective*: every map `g : A → B` is represented by some `a : A`,
    in the sense that `f a` agrees with `g` pointwise. This is the set-level reading of a
    point-surjective `A → Bᴬ` in a cartesian closed category. -/
def WeaklyPointSurjective {A B : Type*} (f : A → A → B) : Prop :=
  ∀ g : A → B, ∃ a : A, ∀ x : A, f a x = g x

/-- **Lawvere's fixed-point theorem** (set-theoretic form). If `f : A → A → B` is weakly
    point-surjective then every `t : B → B` has a fixed point. Proof: `g x := t (f x x)` is
    represented by some `a`; then `f a a = t (f a a)`. -/
theorem lawvere_fixed_point {A B : Type*} (f : A → A → B) (hf : WeaklyPointSurjective f)
    (t : B → B) : ∃ b : B, t b = b := by
  obtain ⟨a, ha⟩ := hf (fun x => t (f x x))
  exact ⟨f a a, (ha a).symm⟩

/-- **The contrapositive engine.** A fixed-point-free endomorphism of `B` forbids any weakly
    point-surjective `f : A → A → B`. -/
theorem fixed_point_free_forbids_surjection {A B : Type*} (t : B → B) (ht : ∀ b, t b ≠ b)
    (f : A → A → B) : ¬ WeaklyPointSurjective f := by
  intro hf
  obtain ⟨b, hb⟩ := lawvere_fixed_point f hf t
  exact ht b hb

/-- **Cantor** as the boolean instance: no `A → (A → Bool)` is weakly point-surjective. -/
theorem cantor_bool {A : Type*} (f : A → A → Bool) : ¬ WeaklyPointSurjective f :=
  fixed_point_free_forbids_surjection (fun b => !b) (by decide) f

/-! ## O1, the positive face -/

/-- **Kleene's recursion theorem, as a face of Lawvere.** Read `Code` as programs and
    `eval : Code → Code → Code` as a universal evaluator applied to a code and an input. If
    the evaluator is weakly point-surjective (every code transformation is realized by some
    program), every transformation `t` of codes has a fixed point `s` with `t s = s` — the
    self-quine of WP0192 Obstruction 1 is the case `t = id`; its *floor* `K(A) ≤ |Â|`
    (`quine_floor`) is an incompressibility fact layered on top of this guaranteed fixed point. -/
theorem kleene_face {Code : Type*} (eval : Code → Code → Code)
    (huniv : WeaklyPointSurjective eval) (t : Code → Code) : ∃ s : Code, t s = s :=
  lawvere_fixed_point eval huniv t


/-! ## O2, the contrapositive face -/

/-- **Obstruction 2 as an instance of Lawvere.** If the agent can *contravene* — there is a
    fixed-point-free `flip : Action → Action` — then no self-predictor
    `pred : State → State → Action` (a state's prediction of what it does in each state) can be
    weakly point-surjective. Compare `self_prediction_dichotomy`, which proves the pointwise
    contradiction directly; this is the same fact obtained from the shared lemma. -/
theorem self_prediction_bar {State Action : Type*} (flip : Action → Action)
    (hflip : ∀ a, flip a ≠ a) (pred : State → State → Action) :
    ¬ WeaklyPointSurjective pred :=
  fixed_point_free_forbids_surjection flip hflip pred

/-! ## The new instance: the open valence codomain -/

/-- The KT valence codomain, the open interval `(-1, 1)`. -/
abbrev Valence : Type := Set.Ioo (-1 : ℝ) 1

/-- The strict shift toward the excluded endpoint, `v ↦ (v+1)/2`, lands in `(-1, 1)`. -/
noncomputable def valenceShift (v : Valence) : Valence :=
  ⟨(v.1 + 1) / 2, by
    obtain ⟨h₁, h₂⟩ := v.2
    constructor <;> linarith⟩

/-- `valenceShift` has no fixed point: `(v+1)/2 = v ↔ v = 1`, and `1 ∉ (-1, 1)`. -/
theorem valenceShift_fixed_point_free : ∀ v : Valence, valenceShift v ≠ v := by
  intro v h
  have hv : ((v.1 + 1) / 2 : ℝ) = v.1 := congrArg Subtype.val h
  have : v.1 = 1 := by linarith
  exact absurd (this ▸ v.2.2) (lt_irrefl _)

/-- **Valence self-scoring bar** (the named result of WP0236). For any object `M` of
    model-descriptions, no `f : M → M → Valence` — an agent's internal indexing of
    valence-scorings of its own models — is weakly point-surjective. Forced by the openness
    of the valence scale alone, independently of `M`. -/
theorem valence_self_scoring_bar {M : Type*} (f : M → M → Valence) :
    ¬ WeaklyPointSurjective f :=
  fixed_point_free_forbids_surjection valenceShift valenceShift_fixed_point_free f

end KTAIT
