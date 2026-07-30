/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib

/-!
# KTAIT.AlgorithmicEmergence — reduction is not construction (WP0007 v0.3.0)

WP0007's two barriers between a microscopic generator and a compressive macroscopic model.

A *finite micro-experiment* `μ` carries an update rule, an initial microstate, an observation
map and a horizon; `data μ` is the finite macrodata record it produces. WP0007 Theorem 1
supplies a computable *embedding* `emb : Str → Exp` — the shift-and-read register seeded with
`y` — whose macrohistory is `y` itself (`Faithful`). Everything below is a reduction along
that embedding.

* `counting_bound` / `few_low_complexity_strings` — the counting step of WP0007 Theorem 1
  (existence barrier). Genuinely proved here: distinct strings need distinct shortest
  programs, so at most `|P|` strings have a shortest program in `P`.
* `identification_barrier` — WP0007 Theorem 2. No computable solver returns a shortest
  program for the macrodata of every experiment.
* `no_additive_approximation` — WP0007 Proposition 3. Relaxing "shortest" to "within a fixed
  additive constant `c` of shortest" does not help.

Computability is modeled abstractly, as in `KTAIT.CoarseGraining`: `CompE` / `CompN` are
predicates "this solver is computable" on the two shapes, and `ReductionClosure` states the one
closure property the reductions consume (post-composing a computable solver with the computable
embedding and the computable length function yields a computable numeric function).

The AIT inputs enter as named hypotheses, never as global `axiom`s — the discipline of
`KTAIT.Basic`. There are two, and they are different facts:

* `KUncomputable` — `K` is not computable. Berry/diagonal; WP0007 Appendix A,
  Li–Vitányi Thm 2.3.2.
* `KNotApproximable c` — no computable `f` satisfies `K ≤ f ≤ K + c` everywhere. This is
  *not* implied by `KUncomputable` without argument; it is the Berry argument run with slack
  `c`, proved in WP0007 Proposition 3. Assuming it here is the honest Level-1 reading: the
  paper proves it, the Lean development reduces to it.

What is NOT claimed: nothing here re-proves an AIT theorem, and nothing here concerns optimal
*coarse-graining selection*. WP0007 v0.3.0 withdrew that theorem (degenerate objective, moving
target, missing reduction) and restated it as an open problem; see `KTAIT.CoarseGraining` for
the regulatory case, which is WP0193's and fixes the target.
-/

namespace KTAIT
namespace AlgorithmicEmergence

/-! ## The existence barrier: the counting step -/

/-- **Counting bound (WP0007 Theorem 1).** If every string in `S` is assigned a program in the
finite set `P`, and distinct strings get distinct programs, then `|S| ≤ |P|`.

Instantiated with `p y` a shortest program for `y` given the conditioning data, and `P` the
programs of length `< m`, this bounds the number of strings of conditional complexity `< m` by
the number of short programs. -/
theorem counting_bound {Str Prog : Type} (S : Finset Str) (P : Finset Prog) (p : Str → Prog)
    (hmem : ∀ y ∈ S, p y ∈ P) (hinj : Set.InjOn p S) :
    S.card ≤ P.card :=
  Finset.card_le_card_of_injOn p hmem hinj

/-- **Few strings are compressible (WP0007 Theorem 1, eq. (2)).** Fewer than `2 ^ m` strings
have a shortest (conditional) program among the fewer-than-`2 ^ m` programs of length `< m`.

The bound does not mention the conditioning string, which is the point: no choice of microlaw
and observation map improves the fraction. -/
theorem few_low_complexity_strings {Str Prog : Type} {m : ℕ}
    (S : Finset Str) (P : Finset Prog) (p : Str → Prog)
    (hmem : ∀ y ∈ S, p y ∈ P) (hinj : Set.InjOn p S) (hP : P.card < 2 ^ m) :
    S.card < 2 ^ m :=
  lt_of_le_of_lt (counting_bound S P p hmem hinj) hP

/-! ## The identification barrier -/

section Identification

variable {Exp Str Prog : Type}
  (data : Exp → Str) (emb : Str → Exp) (K : Str → ℕ) (len : Prog → ℕ)
  (CompE : (Exp → Prog) → Prop) (CompN : (Str → ℕ) → Prop)

/-- The embedding is faithful: the macrohistory of the shift-and-read experiment seeded with
`y` is `y` itself. This is the content of WP0007 Theorem 1's construction. -/
def Faithful : Prop := ∀ y, data (emb y) = y

/-- The reduction mechanism: post-composing a computable experiment solver with the computable
embedding `emb` and the computable length function `len` yields a computable function of the
string. -/
def ReductionClosure : Prop := ∀ A, CompE A → CompN (fun y => len (A (emb y)))

/-- **AIT input 1.** `K` is not computable (Berry/diagonal; WP0007 Appendix A). -/
def KUncomputable : Prop := ¬ CompN K

/-- **AIT input 2.** No computable function brackets `K` within the fixed additive constant
`c`. Strictly stronger than `KUncomputable` as stated, and proved by the Berry argument run
with slack (WP0007 Proposition 3). -/
def KNotApproximable (c : ℕ) : Prop := ∀ f, CompN f → ¬ (∀ y, K y ≤ f y ∧ f y ≤ K y + c)

/-- A solver is *optimal* when it returns a shortest program for every experiment's macrodata. -/
def Optimal (A : Exp → Prog) : Prop := ∀ μ, len (A μ) = K (data μ)

/-- A solver is *`c`-near-optimal* when its output is never shorter than optimal and never more
than `c` bits longer. -/
def NearOptimal (c : ℕ) (A : Exp → Prog) : Prop :=
  ∀ μ, K (data μ) ≤ len (A μ) ∧ len (A μ) ≤ K (data μ) + c

/-- **WP0007 Theorem 2 (identification barrier).** No computable procedure returns, for every
finite micro-experiment, a shortest program for its macrodata. Complete knowledge of the
microscopic generator — rule, initial microstate, observation map and horizon — does not yield
the shortest macroscopic description. -/
theorem identification_barrier
    (hred : ReductionClosure emb len CompE CompN) (hfaith : Faithful data emb)
    (hK : KUncomputable K CompN) {A : Exp → Prog} (hA : Optimal data K len A) :
    ¬ CompE A := by
  intro hcomp
  have h1 : CompN (fun y => len (A (emb y))) := hred A hcomp
  have h2 : (fun y => len (A (emb y))) = K := by
    funext y; rw [hA (emb y), hfaith y]
  rw [h2] at h1
  exact hK h1

/-- **WP0007 Proposition 3.** Relaxing optimality to within a fixed additive constant does not
restore computability, for any constant. -/
theorem no_additive_approximation {c : ℕ}
    (hred : ReductionClosure emb len CompE CompN) (hfaith : Faithful data emb)
    (hApx : KNotApproximable K CompN c) {A : Exp → Prog} (hA : NearOptimal data K len c A) :
    ¬ CompE A := by
  intro hcomp
  refine hApx _ (hred A hcomp) ?_
  intro y
  have h := hA (emb y)
  rw [hfaith y] at h
  exact h

/-- **WP0007 Corollary 1 (conditional form).** Stated for a solver whose target is complexity
conditional on the fixed microlaw/observation data `z`: the same reduction applies verbatim,
because the counting and diagonal arguments are uniform in the conditioning string. -/
theorem identification_barrier_conditional (Kc : Str → ℕ)
    (hred : ReductionClosure emb len CompE CompN) (hfaith : Faithful data emb)
    (hKc : KUncomputable Kc CompN) {A : Exp → Prog} (hA : Optimal data Kc len A) :
    ¬ CompE A :=
  identification_barrier data emb Kc len CompE CompN hred hfaith hKc hA

end Identification

end AlgorithmicEmergence
end KTAIT
