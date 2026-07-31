/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib

/-!
# KTAIT.AlgorithmicEmergence — reduction is not construction (WP0007 v0.3.0)

WP0007's three barriers between a microscopic generator and a compressive macroscopic model.

A *finite micro-experiment* `μ` carries an update rule, an initial microstate, an observation
map and a horizon; `data μ` is the finite macrodata record it produces. WP0007 Theorem 1
supplies a computable *embedding* `emb : Str → Exp` — the shift-and-read register seeded with
`y` — whose macrohistory is `y` itself (`Faithful`). Everything below is a reduction along
that embedding.

* `counting_bound` / `few_low_complexity_strings` / `most_states_incompressible` — WP0007
  Theorem 1 (existence barrier), proved outright: distinct strings need distinct shortest
  programs, so at most `|P|` strings have a shortest program in `P`, and the complement is
  therefore a `1 - 2 ^ (-d)` fraction of the state space.
* `no_compression_improver` / `no_compression_improver_micro` — WP0007 Theorem 2 (improvement
  barrier). No computable solver returns a description below a *supplied threshold* whenever
  one exists — a strictly weaker demand than optimality, and still impossible.
* `identification_barrier` — WP0007 Theorem 3 (optimality barrier). No computable solver
  returns a shortest program for the macrodata of every experiment.
* `no_additive_approximation` — WP0007 Proposition 1. Relaxing "shortest" to "within a fixed
  additive constant `c` of shortest" does not help: every total extractor has unbounded regret.
* `conditional_complexity_uncomputable` — WP0007 Corollary 2. Conditioning on the microlaw,
  observation map and horizon does not help. The conditioning varies with the input, so this
  needs its own diagonal argument rather than an appeal to a fixed conditioning string.
* `chaitin_certification_ceiling` — WP0007 Proposition 2. Per-instance, what blocks an agent is
  unprovability rather than uncomputability.

**What is deliberately NOT formalized.** The companion observation to the improvement barrier —
that `K x < b` is *semidecidable*, so dovetailing finds a shorter description whenever one
exists — would need an explicit operational semantics for programs, a halting-in-`t`-steps
predicate and the dovetailing construction itself, none of which this development carries. It is
argued in the paper and assumed nowhere here.

The omission does not touch `no_compression_improver`, which rules out a *total* procedure that
halts on every input while exploiting every available compression. Semidecidability is the
complementary *positive* fact — a partial search succeeds on each positive instance while
possibly running forever on the negative ones — so it bounds what remains possible rather than
supporting any impossibility proved here.

Likewise `identification_barrier_conditional` is a variant kept for the development's own sake;
the paper's Corollary 2 is `conditional_complexity_uncomputable`.

Computability is modeled abstractly, as in `KTAIT.CoarseGraining`: `CompE` / `CompN` are
predicates "this solver is computable" on the two shapes, and `ReductionClosure` states the one
closure property the reductions consume (post-composing a computable solver with the computable
embedding and the computable length function yields a computable numeric function).

The AIT inputs enter as named hypotheses, never as global `axiom`s — the discipline of
`KTAIT.Basic`. There are three, and they are different facts:

* `KUncomputable` — `K` is not computable. Berry/diagonal; WP0007 Appendix A,
  Li–Vitányi Thm 2.3.2.
* `KNotApproximable c` — no computable `f` satisfies `K ≤ f ≤ K + c` everywhere. This is
  *not* implied by `KUncomputable` without argument; it is the Berry argument run with slack
  `c`, proved in WP0007 Proposition 1. Assuming it here is the honest Level-1 reading: the
  paper proves it, the Lean development reduces to it.
* `KThresholdUndecidable` — the predicate `K x < b` is not decidable. Equivalent to
  `KUncomputable` (deciding it for every `b` determines `K x`), but stated in the threshold
  form the improvement barrier consumes. It *is* semidecidable, which is the whole point:
  what the barrier denies is a procedure that always halts, not one that ever succeeds.

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

/-- **WP0007 Theorem 1, fraction form.** If fewer than `2 ^ (n - d)` of the `2 ^ n` initial
states are compressible past the margin, then more than `2 ^ n - 2 ^ (n - d)` are not: "at least a
fraction `1 - 2 ^ (-d)` of initial microstates yield incompressible macrohistories". This is the
step from the counting bound to the statement the paper makes. -/
theorem most_states_incompressible {Str : Type} [Fintype Str] [DecidableEq Str] {n d : ℕ}
    (S : Finset Str) (hcard : Fintype.card Str = 2 ^ n) (hS : S.card < 2 ^ (n - d)) :
    2 ^ n - 2 ^ (n - d) < Sᶜ.card := by
  have hle : S.card ≤ 2 ^ n := hcard ▸ Finset.card_le_univ S
  have hpow : 2 ^ (n - d) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n d)
  rw [Finset.card_compl, hcard]
  omega

/-! ## The improvement barrier

WP0007 Theorem 2. Weaker demand than optimality, and still impossible: a procedure asked only to
return *some* description below a supplied threshold `b`, whenever one exists, cannot be total
computable. The engine is that validity already gives `len (A x b) < b → K x < b`, so the
threshold guarantee turns the undecidable predicate `K x < b` into a decidable one.

The companion observation is not formalized because it is a statement about a search that need
not halt: dovetailing the programs of length `< b` finds one whenever `K x < b`, so available
compression is semidecidable. What fails is termination, not discovery. -/

section Improvement

variable {Exp Str Prog : Type}
  (data : Exp → Str) (emb : Str → Exp) (K : Str → ℕ) (len : Prog → ℕ)
  (DecR : (Str → ℕ → Prop) → Prop)

/-- Validity: every program `A` returns for `x` is at least as long as a shortest one. This is
`K`'s defining minimality, not an extra assumption. -/
def LengthLowerBound (A : Str → ℕ → Prog) : Prop := ∀ x b, K x ≤ len (A x b)

/-- The threshold guarantee: whenever `x` has a description shorter than `b`, `A` returns one. -/
def BeatsThreshold (A : Str → ℕ → Prog) : Prop := ∀ x b, K x < b → len (A x b) < b

/-- Reduction closure: a computable improver makes the length test `len (A x b) < b` decidable —
run it and measure the output. -/
def LengthTestDecidable (CompS2 : (Str → ℕ → Prog) → Prop) (A : Str → ℕ → Prog) : Prop :=
  CompS2 A → DecR (fun x b => len (A x b) < b)

/-- **AIT input 3.** The threshold predicate for `K` is not decidable. Deciding `K x < b` for
every `b` determines `K x`, so this is the uncomputability of `K` in threshold form (WP0007
Appendix A). It is semidecidable, which is exactly why the barrier is about termination. -/
def KThresholdUndecidable : Prop := ¬ DecR (fun x b => K x < b)

/-- **WP0007 Theorem 2 (improvement barrier).** No total computable procedure returns, for every
string and threshold, a description below the threshold whenever one exists. -/
theorem no_compression_improver {CompS2 : (Str → ℕ → Prog) → Prop} {A : Str → ℕ → Prog}
    (hlb : LengthLowerBound K len A) (hbt : BeatsThreshold K len A)
    (hdec : LengthTestDecidable len DecR CompS2 A)
    (hund : KThresholdUndecidable K DecR) :
    ¬ CompS2 A := by
  intro hcomp
  have hEq : (fun x b => len (A x b) < b) = (fun x b => K x < b) := by
    funext x b
    exact propext ⟨fun h => lt_of_le_of_lt (hlb x b) h, hbt x b⟩
  have hD := hdec hcomp
  rw [hEq] at hD
  exact hund hD

/-- The improver induced on strings by an experiment-level improver, along the embedding. -/
def induced (A : Exp → ℕ → Prog) (emb : Str → Exp) : Str → ℕ → Prog := fun y b => A (emb y) b

/-- **WP0007 Corollary (micro-to-macro form).** No total computable procedure returns, for every
finite micro-experiment and threshold, a program for its macrodata below the threshold whenever
one exists. The experiment-level hypotheses transport to the string level along the `Faithful`
embedding of Theorem 1. -/
theorem no_compression_improver_micro {CompE2 : (Exp → ℕ → Prog) → Prop} {A : Exp → ℕ → Prog}
    (hfaith : ∀ y, data (emb y) = y)
    (hlb : ∀ μ b, K (data μ) ≤ len (A μ b))
    (hbt : ∀ μ b, K (data μ) < b → len (A μ b) < b)
    (hdec : CompE2 A → DecR (fun y b => len (induced A emb y b) < b))
    (hund : KThresholdUndecidable K DecR) :
    ¬ CompE2 A := by
  intro hcomp
  have hEq : (fun y b => len (induced A emb y b) < b) = (fun y b => K y < b) := by
    funext y b
    have h1 := hlb (emb y) b
    have h2 := hbt (emb y) b
    rw [hfaith y] at h1 h2
    exact propext ⟨fun h => lt_of_le_of_lt h1 h, h2⟩
  have hD := hdec hcomp
  rw [hEq] at hD
  exact hund hD

end Improvement

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

/-- **WP0007, conditional-solver variant** (not the paper's Corollary 2 — that is
`conditional_complexity_uncomputable`). Stated for a solver whose target is complexity
conditional on the fixed microlaw/observation data `z`: the same reduction applies verbatim,
because the counting and diagonal arguments are uniform in the conditioning string. -/
theorem identification_barrier_conditional (Kc : Str → ℕ)
    (hred : ReductionClosure emb len CompE CompN) (hfaith : Faithful data emb)
    (hKc : KUncomputable Kc CompN) {A : Exp → Prog} (hA : Optimal data Kc len A) :
    ¬ CompE A :=
  identification_barrier data emb Kc len CompE CompN hred hfaith hKc hA

end Identification

/-! ## The conditional form, and per-instance non-certifiability -/

section Conditional

/-- **WP0007 Corollary 2.** Conditional complexity relative to the microlaw, observation map and
horizon is not computable either. The conditioning `z_n = (D_n, C_n, n)` *varies with the input*,
so this does not follow from uncomputability at a fixed conditioning string; the paper gives a
direct diagonal argument, and this is its skeleton.

`Kc y` reads `K(y | z_{|y|})`. `sel n` is the search "the first `y` of length `n` with
`Kc y ≥ n`". Two facts drive the contradiction:

* `hsel` — the search succeeds, because at the *fixed* condition `z_n` a counting argument
  supplies a witness of conditional complexity at least `n` (`few_low_complexity_strings`);
* `hconst` — if `Kc` were computable then, given `z_n`, a program of constant size recovers `n`
  (it is a component of `z_n`) and runs the search, so its output has conditional complexity
  bounded by a constant `c` independent of `n`.

Instantiating at `n = c + 1` gives `c + 1 ≤ Kc (sel (c+1)) ≤ c`. -/
theorem conditional_complexity_uncomputable {Str : Type} {Kc : Str → ℕ}
    {CompN : (Str → ℕ) → Prop} (sel : ℕ → Str) (hsel : ∀ n, n ≤ Kc (sel n)) {c : ℕ}
    (hconst : CompN Kc → ∀ n, Kc (sel n) ≤ c) :
    ¬ CompN Kc := by
  intro h
  have h1 := hsel (c + 1)
  have h2 := hconst h (c + 1)
  omega

/-- **WP0007 Proposition 2 (per-instance non-certifiability).** Read `Cert x m` as "the formal
theory `F` certifies the lower bound `K(x) > m`". Chaitin's incompleteness theorem caps such
certificates at a constant `c_{F,U}` fixed by the theory and the reference machine. Hence no
macromodel longer than that constant can be certified shortest for any record, however finite.

The Chaitin bound is the assumed input, exactly as in `SelfModelLimits.chaitin_blocks_minimality`,
which is the self-model form of the same obstruction. What is proved here is the consequence for
macromodel optimality: uncomputability is uniform over the family, unprovability is per-instance. -/
theorem chaitin_certification_ceiling {Str : Type} (Cert : Str → ℕ → Prop) {cF : ℕ}
    (chaitin : ∀ x m, Cert x m → m ≤ cF) {x : Str} {p : ℕ} (hp : cF < p) :
    ¬ Cert x p := by
  intro h
  have := chaitin x p h
  omega

end Conditional

end AlgorithmicEmergence
end KTAIT
