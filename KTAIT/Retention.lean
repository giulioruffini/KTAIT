/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib

/-!
# KTAIT.Retention — WP0058: the optimal inherited-memory kernel

An inherited-memory **kernel** `q : ℕ → ℝ`, with `0 ≤ q n ≤ 1`, records how much weight a
lineage still places, `n` generations later, on information acquired at generation `g`.
`q n = 1` is full retention, `q n = 0` is complete forgetting. Over a horizon `N` the
lineage's payoff is linear in the kernel,

  `J N v q = ∑ n ∈ Finset.range N, q n * v n`,

where `v n` is the **net value** of still acting on `n`-generation-old information: the
predictive information it still carries, minus the cost of carrying it, minus the mismatch
loss from acting on stale belief.

## What is proved

* `bangbang_optimal` — because `J` is linear in `q` and `q` is box-constrained, the optimum
  is the threshold kernel `qStar v n = if 0 < v n then 1 else 0`. No interior kernel beats it.
* `optimal_kernel_antitone_is_initial_segment` — if `v` is antitone, the retained set is an
  initial segment, so the optimum is "retain for `L` generations, then drop".
* `qStar_eq_one_iff_lt_first_crossing` — that `L` is the *first crossing*: the least lag at
  which the net value stops being positive (`FirstCrossing`, shown to exist whenever the net
  value is nonpositive somewhere, in `exists_firstCrossing`).
* `persistence_is_first_crossing` — with `v n = R n − κ`, `R` the predictive-information
  curve of the environmental feature and `κ > 0` the per-generation cost of carrying and of
  mismatch, the optimum retains exactly the lags at which `R` is still above `κ`. This is
  WP0058's `τ_{ρ,θ}` with `θ = κ`: the matching relation `λ_P* ~ τ_ρ` is the *solution* of a
  linear retention problem, not a conjecture, and the threshold is set by the cost.
* `exponential_crossing`, `exponential_persistence_proportional_to_tau` — for
  `R n = R₀ e^{−n/τ}` the crossing lag is exactly `τ log(R₀/κ)`, hence proportional to the
  environmental correlation time at fixed cost ratio.
* `toyRetention_qStar_beats_full`, `toyRetention_initial_segment` — a numeric witness that
  the optimum is a nontrivial initial segment and strictly beats a competing kernel.

## What is NOT proved

Everything empirical, and every modelling choice:

* that biological (or engineered) inheritance channels actually sit at this optimum;
* that a payoff **linear in `q`** is the right model — a concave payoff would generically
  give an interior optimum and no threshold;
* that the carrying and mismatch costs are **constant in `n`**, as `v n = R n − κ` assumes;
* that predictive information decays **exponentially**, which only
  `exponential_crossing` and its corollary assume.

The empirical matching claim `λ_P ~ τ_ρ` remains a conjecture in the paper. What is
machine-checked here is the optimization result and the form of its solution.
-/

namespace KTAIT
namespace Retention

/-! ### The kernel problem -/

/-- The lineage's payoff over a horizon of `N` generations: `J = ∑_{n<N} q n · v n`, with
`q` the inherited-memory kernel and `v` the net value of acting on `n`-generation-old
information. Linear in `q` by construction — that linearity is what forces the optimum to
be bang-bang, and it is a modelling assumption, not a theorem. -/
def J (N : ℕ) (v q : ℕ → ℝ) : ℝ := ∑ n ∈ Finset.range N, q n * v n

/-- Admissible kernels: weights in `[0, 1]` at every lag. -/
def Admissible (q : ℕ → ℝ) : Prop := ∀ n, 0 ≤ q n ∧ q n ≤ 1

open Classical in
/-- The **threshold (bang-bang) kernel**: retain fully wherever the net value is positive,
forget entirely elsewhere. -/
noncomputable def qStar (v : ℕ → ℝ) : ℕ → ℝ := fun n => if 0 < v n then 1 else 0

theorem qStar_of_pos {v : ℕ → ℝ} {n : ℕ} (h : 0 < v n) : qStar v n = 1 := by
  classical simp [qStar, h]

theorem qStar_of_nonpos {v : ℕ → ℝ} {n : ℕ} (h : v n ≤ 0) : qStar v n = 0 := by
  classical simp [qStar, not_lt.mpr h]

theorem qStar_admissible (v : ℕ → ℝ) : Admissible (qStar v) := by
  intro n
  classical
  by_cases h : 0 < v n
  · simp [qStar_of_pos h]
  · simp [qStar_of_nonpos (not_lt.mp h)]

/-! ### The optimum is a threshold rule -/

/-- **The optimum of the linear kernel problem is bang-bang.** Every admissible kernel is
dominated, termwise and hence in total payoff, by the threshold kernel `qStar v`. Nothing
about `v` is assumed: the argument is that a linear objective on a box attains its maximum
at a vertex. -/
theorem bangbang_optimal (N : ℕ) (v q : ℕ → ℝ) (hq : Admissible q) :
    J N v q ≤ J N v (qStar v) := by
  classical
  refine Finset.sum_le_sum ?_
  intro n _
  by_cases h : 0 < v n
  · rw [qStar_of_pos h, one_mul]
    nlinarith [(hq n).2, h]
  · rw [qStar_of_nonpos (not_lt.mp h), zero_mul]
    nlinarith [(hq n).1, not_lt.mp h]

/-- **The retained set of an antitone net value is an initial segment.** If the net value of
acting on old information never increases with age, then retaining a lag forces retaining
every shorter one. So the optimal kernel is "retain for `L` generations, then drop" — a
persistence length, not an arbitrary set of lags. -/
theorem optimal_kernel_antitone_is_initial_segment {v : ℕ → ℝ}
    (hv : ∀ m n, m ≤ n → v n ≤ v m) {m n : ℕ} (hn : 0 < v n) (hmn : m ≤ n) :
    0 < v m :=
  lt_of_lt_of_le hn (hv m n hmn)

/-- `L` is the **first crossing lag** of the net value: positive at every shorter lag, and no
longer positive at `L` itself. Carried as a hypothesis rather than constructed, so that the
threshold characterization does not depend on how `L` is found. -/
structure FirstCrossing (v : ℕ → ℝ) (L : ℕ) : Prop where
  /-- The net value is still positive at every lag below `L`. -/
  pos_before : ∀ n, n < L → 0 < v n
  /-- At `L` the net value has crossed: it is no longer positive. -/
  nonpos_at : v L ≤ 0

/-- A first crossing exists as soon as the net value fails to be positive somewhere — no
antitonicity needed, by well-ordering of `ℕ`. -/
theorem exists_firstCrossing (v : ℕ → ℝ) (h : ∃ n, v n ≤ 0) : ∃ L, FirstCrossing v L := by
  classical
  exact ⟨Nat.find h, fun n hn => not_le.mp (Nat.find_min h hn), Nat.find_spec h⟩

/-- **The optimal persistence is the first crossing lag.** For an antitone net value with
first crossing `L`, the threshold kernel retains a lag exactly when it is shorter than `L`.
The optimal kernel is therefore the indicator of `[0, L)`, and `L` — the first lag at which
the net value crosses zero — is the lineage's optimal persistence. -/
theorem qStar_eq_one_iff_lt_first_crossing {v : ℕ → ℝ} (hv : ∀ m n, m ≤ n → v n ≤ v m)
    {L : ℕ} (hL : FirstCrossing v L) (n : ℕ) :
    qStar v n = 1 ↔ n < L := by
  classical
  constructor
  · intro h
    by_contra hn
    have hLn : L ≤ n := not_lt.mp hn
    have : v n ≤ 0 := le_trans (hv L n hLn) hL.nonpos_at
    rw [qStar_of_nonpos this] at h
    exact zero_ne_one h
  · intro hn
    exact qStar_of_pos (hL.pos_before n hn)

/-- Below the first crossing the threshold kernel retains, above it forgets — the same
statement as `qStar_eq_one_iff_lt_first_crossing`, read as a kernel rather than a condition. -/
theorem qStar_eq_zero_of_first_crossing_le {v : ℕ → ℝ} (hv : ∀ m n, m ≤ n → v n ≤ v m)
    {L n : ℕ} (hL : FirstCrossing v L) (hn : L ≤ n) :
    qStar v n = 0 :=
  qStar_of_nonpos (le_trans (hv L n hn) hL.nonpos_at)

/-! ### Net value from a predictive-information curve

Instantiate the net value as `v n = R n − κ`: `R n` is the predictive information the
environmental feature still carries at lag `n`, and `κ > 0` is the per-generation cost of
carrying the information plus the mismatch loss from acting on it when stale. The cost is
constant in `n`; that is an assumption of this instantiation, not a result. -/

/-- Net value of acting on `n`-generation-old information: predictive information retained,
less the constant per-generation cost `κ`. -/
def netValue (R : ℕ → ℝ) (κ : ℝ) : ℕ → ℝ := fun n => R n - κ

/-- An antitone predictive-information curve gives an antitone net value, so the optimum is
an initial segment (`optimal_kernel_antitone_is_initial_segment` applies). -/
theorem netValue_antitone {R : ℕ → ℝ} (hR : ∀ m n, m ≤ n → R n ≤ R m) (κ : ℝ) :
    ∀ m n, m ≤ n → netValue R κ n ≤ netValue R κ m := by
  intro m n h
  simpa [netValue] using hR m n h

/-- **Optimal persistence is the first lag at which predictive information crosses the cost
threshold.** The threshold kernel retains lag `n` exactly when `κ < R n`. Read with
`qStar_eq_one_iff_lt_first_crossing`, the optimal persistence length is the first crossing of
`R` through `κ` — WP0058's `τ_{ρ,θ}` with `θ = κ`. The matching of persistence to the
environment is thus the *solution* of the linear retention problem, and the threshold is set
by the cost of carrying information, not chosen. -/
theorem persistence_is_first_crossing (R : ℕ → ℝ) (κ : ℝ) (n : ℕ) :
    qStar (netValue R κ) n = 1 ↔ κ < R n := by
  classical
  by_cases h : κ < R n
  · simp [qStar_of_pos (show 0 < netValue R κ n by simp [netValue]; linarith), h]
  · rw [qStar_of_nonpos (show netValue R κ n ≤ 0 by simp [netValue]; linarith [not_lt.mp h])]
    simp [h]

/-! ### The exponential case: persistence proportional to the correlation time -/

/-- The crossing lag of an exponentially decaying predictive-information curve
`R n = R₀ e^{−n/τ}` against a cost `κ`: `τ log(R₀/κ)`. -/
noncomputable def crossingLag (R₀ κ τ : ℝ) : ℝ := τ * Real.log (R₀ / κ)

/-- **Exponential crossing, exactly.** For `R n = R₀ e^{−n/τ}` with `R₀ > 0`, `τ > 0` and
`0 < κ`, the predictive information is still above the cost precisely below the lag
`τ log(R₀/κ)`. (For `κ ≥ R₀` the right-hand side is `≤ 0` and no lag qualifies, which is the
correct degenerate reading: information too costly to carry at all.) -/
theorem exponential_crossing {R₀ κ τ : ℝ} (hR : 0 < R₀) (hκ : 0 < κ) (hτ : 0 < τ) (n : ℕ) :
    κ < R₀ * Real.exp (-(n : ℝ) / τ) ↔ (n : ℝ) < crossingLag R₀ κ τ := by
  have hstep : κ < R₀ * Real.exp (-(n : ℝ) / τ) ↔ κ / R₀ < Real.exp (-(n : ℝ) / τ) := by
    rw [div_lt_iff₀ hR, mul_comm]
  rw [hstep, ← Real.log_lt_iff_lt_exp (by positivity), Real.log_div (ne_of_gt hκ) (ne_of_gt hR),
    crossingLag, Real.log_div (ne_of_gt hR) (ne_of_gt hκ), neg_div, lt_neg, div_lt_iff₀ hτ,
    neg_sub]
  constructor <;> intro h <;> nlinarith [h]

/-- **Optimal persistence is proportional to the environmental correlation time.** At a fixed
cost ratio `R₀/κ`, scaling the correlation time `τ` by `c` scales the crossing lag by `c`. The
proportionality constant is `log(R₀/κ)`, i.e. it is set by the cost of carrying information
relative to its initial predictive value. -/
theorem exponential_persistence_proportional_to_tau (R₀ κ τ c : ℝ) :
    crossingLag R₀ κ (c * τ) = c * crossingLag R₀ κ τ := by
  simp [crossingLag, mul_assoc]

/-- The optimal kernel in the exponential case: retain exactly the lags below
`τ log(R₀/κ)`. Combines `persistence_is_first_crossing` with `exponential_crossing`. -/
theorem qStar_exponential {R₀ κ τ : ℝ} (hR : 0 < R₀) (hκ : 0 < κ) (hτ : 0 < τ) (n : ℕ) :
    qStar (netValue (fun n => R₀ * Real.exp (-(n : ℝ) / τ)) κ) n = 1
      ↔ (n : ℝ) < crossingLag R₀ κ τ := by
  rw [persistence_is_first_crossing]
  exact exponential_crossing hR hκ hτ n

/-! ### Non-vacuity witness

An explicit antitone net value whose optimal kernel is a nontrivial initial segment — neither
"retain everything" nor "retain nothing" — and which strictly beats the full-retention
kernel. Without this the theorems above could all hold vacuously. -/

/-- Net value `v n = 2 − n`: positive at lags `0, 1`, nonpositive from lag `2` on. -/
noncomputable def vTest : ℕ → ℝ := fun n => 2 - (n : ℝ)

/-- The all-ones kernel: retain everything forever. -/
def qOnes : ℕ → ℝ := fun _ => 1

theorem vTest_antitone : ∀ m n : ℕ, m ≤ n → vTest n ≤ vTest m := by
  intro m n h
  have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr h
  simp only [vTest]
  linarith

/-- `2` is the first crossing lag of `vTest`. -/
theorem vTest_firstCrossing : FirstCrossing vTest 2 := by
  constructor
  · intro n hn
    interval_cases n <;> norm_num [vTest]
  · norm_num [vTest]

/-- The optimal kernel here is a **nontrivial initial segment**: it retains lags `0` and `1`
and drops lag `2`. -/
theorem toyRetention_initial_segment :
    qStar vTest 0 = 1 ∧ qStar vTest 1 = 1 ∧ qStar vTest 2 = 0 := by
  refine ⟨qStar_of_pos ?_, qStar_of_pos ?_, qStar_of_nonpos ?_⟩ <;> norm_num [vTest]

/-- The optimum **strictly** beats full retention over a horizon of `4` generations: `3 > 2`.
So `bangbang_optimal` is not an equality in disguise, and forgetting genuinely pays. -/
theorem toyRetention_qStar_beats_full :
    J 4 vTest qOnes = 2 ∧ J 4 vTest (qStar vTest) = 3 ∧
      J 4 vTest qOnes < J 4 vTest (qStar vTest) := by
  have h1 : J 4 vTest qOnes = 2 := by
    simp only [J, qOnes, vTest, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have h2 : J 4 vTest (qStar vTest) = 3 := by
    have e0 : qStar vTest 0 = 1 := qStar_of_pos (by norm_num [vTest])
    have e1 : qStar vTest 1 = 1 := qStar_of_pos (by norm_num [vTest])
    have e2 : qStar vTest 2 = 0 := qStar_of_nonpos (by norm_num [vTest])
    have e3 : qStar vTest 3 = 0 := qStar_of_nonpos (by norm_num [vTest])
    simp only [J, Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, vTest]
    norm_num
  exact ⟨h1, h2, by rw [h1, h2]; norm_num⟩

end Retention
end KTAIT
