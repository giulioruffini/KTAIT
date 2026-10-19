/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic
import KTAIT.ART
import KTAIT.RegulationBalance
import KTAIT.GroundedRegulation

/-!
# KTAIT.ResidualTransfer — ART's probabilistic reading, repaired through GART

WP0203 (v25, the appendix on probabilistic regulator bounds) shows that the concentration claim the
original ART article states after its probabilistic regulator theorem, the tail bound
`Pr[M(W:R) ≤ Δ − k | x, E_b] ≤ C'·2^{−k}`, does not follow
from the per-explanation bound: a fixed clamp regulating a family of complex worlds keeps
`Θ(1)` posterior mass however large the gap. Counting individual code penalties alone does not
control this aggregate: a class of `2^ℓ` explanations can offset weights of order `2^{−ℓ}`.

What does survive is a *transfer*: GART holds for every explanation in ART's class,
`Δ ≤ I_K(W:R) + L_cf + slack`, so the event "little shared information" is contained in the
event "large residual", and posterior mass is monotone under inclusion. Hence

  `Pr[I_K(W:R) ≤ Δ − k | x, E_b] ≤ Pr[L_cf ≥ k − slack | x, E_b]`,

and conditional on a residual bound `L_cf ≤ λ` the strictly lower-information event has mass
`0`. An exponential information-deficit tail follows if an exponential residual tail is
independently established under the same evidence and with the coding allowance retained.

The statements include:
* `class_mass_transfer` — the abstract inequality for a finite family with nonnegative weights.
* `class_mass_transfer_tsum` — the same over a countable family, in `ℝ≥0∞`, no summability needed.
* `class_mass_transfer_variable_tsum` — allows the gap and coding allowance to vary between
  explanations, so a uniform logarithmic allowance on an unbounded class is not assumed.
* `class_mass_residual_confidence_tsum` — the strict-event transfer used for a probabilistic
  upper bound on the residual.
* `residual_bounded_class_mass_zero` — under a uniform residual bound the low-information class
  is empty, so its mass is `0`.
* `conditional_small_residual_zero` — a normalized posterior conditioned on the evidence and
  `L <= eta` assigns probability zero to `I < gap - eta - h`; the denominator is positive
  and finite.
* `conditional_deficit_zero` and `conditional_art_tail` — the hard cutoff and its ART-shaped
  envelope, with information deficit distinguished from a lower threshold on the gap.
* `conditional_tail_given_residual` — the corresponding finite, unnormalized weight inequality.
* `unadjusted_threshold_counterexample` — GART alone allows `I < gap` with probability one even
  at arbitrarily large gaps and a residual of one bit.
* `posterior_residual_transfer` — a finite weight comparison for the abstract
  `AITProb.post`, with the per-explanation GART premise supplied by named AIT facts.
* `conditional_confidence_transfer`, `conditional_variable_transfer`, and
  `conditional_exponential_transfer` — normalized transfers on positive finite evidence
  mass, with hypotheses restricted to its positive-weight support. The exponential
  residual tail is a separate premise.

The `post` instantiations do not establish a normalized program posterior.
That interpretation requires compatible selected programs, their length offsets,
and agreement of evidence as in `AITProb.compatible_program_factor`.

The tightness side (the clamp family) is a paper-level construction; the finite multiplicity
witnesses in `ModelOrPay` show the generic mechanism.
-/

namespace KTAIT
namespace ResidualTransfer

open Finset

/-! ## Abstract class-mass transfer -/

/-- **Class-mass transfer (finite family).** If every explanation `e` of a finite family `S`
    satisfies the GART-type inequality `Δ ≤ I e + L e + s`, then the total weight of the
    explanations with `I e ≤ Δ − k` is at most the total weight of those with `L e ≥ k − s`,
    for any nonnegative weights `w`. -/
theorem class_mass_transfer {E : Type*} (S : Finset E) (w : E → ℝ)
    (hw : ∀ e ∈ S, 0 ≤ w e) (I L : E → ℤ) (Δ k s : ℤ)
    (hgart : ∀ e ∈ S, Δ ≤ I e + L e + s) :
    (S.filter (fun e => I e ≤ Δ - k)).sum w ≤ (S.filter (fun e => k - s ≤ L e)).sum w := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨he.1, by have := hgart e he.1; omega⟩
  · intro e he _
    exact hw e (Finset.mem_of_mem_filter e he)

/-- **Class-mass transfer (countable family, `ℝ≥0∞`).** The same inequality for a countable
    family of explanations with weights in `ℝ≥0∞`; no summability hypothesis is needed. -/
theorem class_mass_transfer_tsum {E : Type*} (w : E → ENNReal) (I L : E → ℤ) (Δ k s : ℤ)
    (hgart : ∀ e, Δ ≤ I e + L e + s) :
    ∑' e, Set.indicator {e | I e ≤ Δ - k} w e ≤ ∑' e, Set.indicator {e | k - s ≤ L e} w e := by
  apply ENNReal.tsum_le_tsum
  intro e
  apply Set.indicator_le_indicator_of_subset
  · intro e' he'
    simp only [Set.mem_setOf_eq] at he' ⊢
    have := hgart e'
    omega
  · intro _; exact bot_le

/-- **Variable-gap, variable-allowance transfer.** The posterior may range over explanations
    of unbounded size. The applicable coding allowance is then kept inside the event. The
    weights may already be normalized conditional probabilities; no choice of prior is used. -/
theorem class_mass_transfer_variable_tsum {E : Type*} (w : E → ENNReal)
    (gap I L s : E → ℤ) (k : ℤ)
    (hgart : ∀ e, gap e ≤ I e + L e + s e) :
    ∑' e, Set.indicator {e | I e ≤ gap e - k} w e
      ≤ ∑' e, Set.indicator {e | k ≤ L e + s e} w e := by
  apply ENNReal.tsum_le_tsum
  intro e
  apply Set.indicator_le_indicator_of_subset
  · intro e' he'
    simp only [Set.mem_setOf_eq] at he' ⊢
    have := hgart e'
    omega
  · intro _; exact bot_le

/-- **Residual-confidence transfer.** If the gap is at least `d` and the coding allowance is
    at most `s`, the mass below `d - lam - s` bits of shared information is no greater than
    the mass above `lam` bits of residual. Strict inequalities preserve the equality case. -/
theorem class_mass_residual_confidence_tsum {E : Type*} (w : E → ENNReal)
    (I L : E → ℤ) (d lam s : ℤ)
    (hgart : ∀ e, d ≤ I e + L e + s) :
    ∑' e, Set.indicator {e | I e < d - lam - s} w e
      ≤ ∑' e, Set.indicator {e | lam < L e} w e := by
  apply ENNReal.tsum_le_tsum
  intro e
  apply Set.indicator_le_indicator_of_subset
  · intro e' he'
    simp only [Set.mem_setOf_eq] at he' ⊢
    have := hgart e'
    omega
  · intro _; exact bot_le

/-- **Countable zero-mass consequence.** A uniform residual bound excludes information
    strictly below the GART threshold, for any nonnegative weights. -/
theorem residual_bounded_class_mass_zero_tsum {E : Type*} (w : E → ENNReal)
    (I L : E → ℤ) (d lam s : ℤ)
    (hgart : ∀ e, d ≤ I e + L e + s) (hlam : ∀ e, L e ≤ lam) :
    ∑' e, Set.indicator {e | I e < d - lam - s} w e = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro e
  apply Set.indicator_of_notMem
  simp only [Set.mem_setOf_eq, not_lt]
  have := hgart e
  have := hlam e
  omega

/-- **GART instantiated on a countable weighted family.** Each pair may have its own
    regulated and null outputs. The four named AIT hypotheses supply the balance before
    class mass is summed. Conditioning belongs in the nonnegative weights `w`. -/
theorem gart_mass_transfer_tsum (F : AITFrame) {E : Type*} (w : E → ENNReal)
    (W R y y0 : E → F.Obj) (k : ℤ)
    (hmut : ∀ e, RegulationBalance.MutualChain F (y0 e) (R e))
    (hsub : ∀ e, RegulationBalance.CondSubadd F (y e) (y0 e) (R e))
    (hmono : ∀ e, RegulationBalance.CondMono F (y e) (R e))
    (hdp : ∀ e, RegulationBalance.DataProcessing F (y0 e) (W e) (R e)) :
    ∑' e, Set.indicator
      {e | IK F (W e) (R e) ≤ RegulationBalance.gap F (y e) (y0 e) - k} w e
      ≤ ∑' e, Set.indicator
      {e | k ≤ GroundedRegulation.residual F (y e) (y0 e) (R e) + 4 * (F.slack : ℤ)} w e := by
  apply class_mass_transfer_variable_tsum w
    (fun e => RegulationBalance.gap F (y e) (y0 e))
    (fun e => IK F (W e) (R e))
    (fun e => GroundedRegulation.residual F (y e) (y0 e) (R e))
    (fun _ => 4 * (F.slack : ℤ)) k
  intro e
  exact GroundedRegulation.grounded_inequality F (W e) (y e) (y0 e) (R e)
    (hmut e) (hsub e) (hmono e) (hdp e)

/-- **Residual bound kills the low-information class.** If every explanation has residual at
    most `λ`, no explanation has `I e < Δ − λ − s`, so that class has weight `0`. -/
theorem residual_bounded_class_mass_zero {E : Type*} (S : Finset E) (w : E → ℝ)
    (I L : E → ℤ) (Δ lam s : ℤ)
    (hgart : ∀ e ∈ S, Δ ≤ I e + L e + s)
    (hlam : ∀ e ∈ S, L e ≤ lam) :
    (S.filter (fun e => I e < Δ - lam - s)).sum w = 0 := by
  have hempty : S.filter (fun e => I e < Δ - lam - s) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro e he hlt
    have h1 := hgart e he
    have h2 := hlam e he
    omega
  rw [hempty, Finset.sum_empty]

/-! ## Conditional probabilities under a residual bound -/

/-- The total nonnegative weight of an event; no normalization of the ambient weights is needed. -/
noncomputable def eventMass {E : Type*} (w : E → ENNReal) (A : Set E) : ENNReal :=
  ∑' e, A.indicator w e

/-- Conditional event probability under nonnegative weights. Positive finite conditioning mass
    is required to form this expression, rather than left implicit in totalized division. -/
noncomputable def conditionalMass {E : Type*} (w : E → ENNReal) (A B : Set E)
    (_hpos : 0 < eventMass w B) (_hfinite : eventMass w B < ⊤) : ENNReal :=
  eventMass w (A ∩ B) / eventMass w B

/-- Event mass is monotone under inclusion. (Helper.) -/
private theorem eventMass_mono {E : Type*} (w : E → ENNReal) {A B : Set E}
    (hAB : A ⊆ B) : eventMass w A ≤ eventMass w B := by
  apply ENNReal.tsum_le_tsum
  intro e
  exact Set.indicator_le_indicator_of_subset hAB (fun _ => bot_le) e

/-- A normalized conditional event probability is at most one. (Helper.) -/
theorem conditionalMass_le_one {E : Type*} (w : E → ENNReal) (A B : Set E)
    (hpos : 0 < eventMass w B) (hfinite : eventMass w B < ⊤) :
    conditionalMass w A B hpos hfinite ≤ 1 := by
  unfold conditionalMass
  apply (ENNReal.div_le_iff hpos.ne' hfinite.ne).2
  simpa using eventMass_mono w (Set.inter_subset_right : A ∩ B ⊆ B)

/-- Excluding the event on every positive-weight conditioned pair gives zero probability.
    (Helper.) -/
private theorem conditionalMass_zero_of_exclusion {E : Type*} (w : E → ENNReal)
    (A B : Set E) (hpos : 0 < eventMass w B) (hfinite : eventMass w B < ⊤)
    (hex : ∀ e ∈ B, w e ≠ 0 → e ∉ A) : conditionalMass w A B hpos hfinite = 0 := by
  have hnum : eventMass w (A ∩ B) = 0 := by
    apply ENNReal.tsum_eq_zero.mpr
    intro e
    by_cases he : e ∈ A ∩ B
    · rw [Set.indicator_of_mem he]
      by_contra hw
      exact hex e he.2 hw he.1
    · exact Set.indicator_of_notMem he w
  simp only [conditionalMass, hnum, ENNReal.zero_div]

/-- **Posterior inference conditional on a small residual.** Let `B` consist of the evidence
    and the bound `L <= eta`, and assume `B` has positive finite weight. GART on `B`
    excludes `I < gap - eta - h` on `B`, so that event has conditional probability zero.
    The gap may vary across explanations, and the probability law need not be universal. -/
theorem conditional_small_residual_zero {E : Type*} (w : E → ENNReal)
    (gap I L : E → ℤ) (evidence : Set E) (eta h : ℤ)
    (hgart : ∀ e ∈ evidence ∩ {e | L e ≤ eta}, w e ≠ 0 →
      gap e ≤ I e + L e + h)
    (hpos : 0 < eventMass w (evidence ∩ {e | L e ≤ eta}))
    (hfinite : eventMass w (evidence ∩ {e | L e ≤ eta}) < ⊤) :
    conditionalMass w {e | I e < gap e - eta - h}
      (evidence ∩ {e | L e ≤ eta}) hpos hfinite = 0 := by
  apply conditionalMass_zero_of_exclusion
  intro e he hw hbad
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at he hbad
  have := hgart e he hw
  omega

/-- **Hard cutoff for the information deficit.** After conditioning on the evidence and
    `L <= eta`, a deficit `t > eta + h` has zero probability. The strict inequality on `t`
    is necessary: equality at the GART threshold is allowed. -/
theorem conditional_deficit_zero {E : Type*} (w : E → ENNReal)
    (gap I L : E → ℤ) (evidence : Set E) (eta h t : ℤ)
    (hgart : ∀ e ∈ evidence ∩ {e | L e ≤ eta}, w e ≠ 0 →
      gap e ≤ I e + L e + h)
    (hpos : 0 < eventMass w (evidence ∩ {e | L e ≤ eta}))
    (hfinite : eventMass w (evidence ∩ {e | L e ≤ eta}) < ⊤)
    (ht : eta + h < t) :
    conditionalMass w {e | I e ≤ gap e - t}
      (evidence ∩ {e | L e ≤ eta}) hpos hfinite = 0 := by
  apply conditionalMass_zero_of_exclusion
  intro e he hw hbad
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at he hbad
  have := hgart e he hw
  omega

/-- **ART-shaped envelope for the conditional hard cutoff.** Under the same positive-mass
    residual conditioning, `Pr[I <= gap - t] <= min(1, 2^(-(t-eta-h)))`.
    This follows from a stronger zero-probability result for `t > eta + h`; below that cutoff
    the displayed bound is one. It is not an independently derived statistical decay law. -/
theorem conditional_art_tail {E : Type*} (w : E → ENNReal)
    (gap I L : E → ℤ) (evidence : Set E) (eta h t : ℤ)
    (hgart : ∀ e ∈ evidence ∩ {e | L e ≤ eta}, w e ≠ 0 →
      gap e ≤ I e + L e + h)
    (hpos : 0 < eventMass w (evidence ∩ {e | L e ≤ eta}))
    (hfinite : eventMass w (evidence ∩ {e | L e ≤ eta}) < ⊤) :
    conditionalMass w {e | I e ≤ gap e - t}
      (evidence ∩ {e | L e ≤ eta}) hpos hfinite
      ≤ min 1 ((2 : ENNReal) ^ (-(t - eta - h))) := by
  by_cases ht : eta + h < t
  · rw [conditional_deficit_zero w gap I L evidence eta h t hgart hpos hfinite ht]
    exact bot_le
  · have hpow : (1 : ENNReal) ≤ (2 : ENNReal) ^ (-(t - eta - h)) := by
      have hexp : (0 : ℤ) ≤ -(t - eta - h) := by omega
      simpa only [zpow_zero] using ENNReal.zpow_le_of_le (by norm_num : (1 : ENNReal) ≤ 2) hexp
    rw [min_eq_left hpow]
    exact conditionalMass_le_one w _ _ hpos hfinite

/-- **Guard against the unadjusted threshold.** For every `n`, a one-point probability law can
    have `gap = n+1`, `I = n`, `L = 1`, and zero allowance, satisfying the GART inequality.
    Conditional on `gap >= n` and `L <= 1`, the event `I < gap` still has probability one.
    This is a counterexample within the arithmetic GART interface; it does not separately
    construct universal-machine complexities realizing those exact integers. -/
theorem unadjusted_threshold_counterexample (n : ℕ) :
    ((n : ℤ) + 1 ≤ (n : ℤ) + 1 + 0) ∧
    conditionalMass (fun _ : Unit => (1 : ENNReal))
      { _u | (n : ℤ) < (n : ℤ) + 1}
      { _u | (n : ℤ) ≤ (n : ℤ) + 1 ∧ (1 : ℤ) ≤ 1}
      (by simp [eventMass]) (by simp [eventMass]) = 1 := by
  constructor
  · omega
  · simp [conditionalMass, eventMass]

/-! ## The repaired tail in the original's shape -/

/-- **Conditional tail given a residual bound (finite family, real weights).** Among explanations
    with residual at most `η`, the weight of those with `I ≤ Δ − k` is at most
    `2^{−(k−η−s)}` times the weight of the residual-bounded class. With positive denominator,
    their ratio is the conditional probability. For `k > η + s` the numerator is `0`; for
    `k ≤ η + s` the factor is at least `1`. The exponential factor packages the hard cutoff;
    the normalized countable forms above require positive finite conditioning mass explicitly. -/
theorem conditional_tail_given_residual {E : Type*} (S : Finset E) (w : E → ℝ)
    (hw : ∀ e ∈ S, 0 ≤ w e) (I L : E → ℤ) (Δ k η s : ℤ)
    (hgart : ∀ e ∈ S, Δ ≤ I e + L e + s) :
    (S.filter (fun e => I e ≤ Δ - k ∧ L e ≤ η)).sum w
      ≤ (2 : ℝ) ^ (-(k - η - s)) * (S.filter (fun e => L e ≤ η)).sum w := by
  by_cases hk : k ≤ η + s
  · -- the factor is at least one and the numerator class is inside the residual class
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (-(k - η - s)) :=
      one_le_zpow₀ (by norm_num) (by omega)
    have hsub : (S.filter (fun e => I e ≤ Δ - k ∧ L e ≤ η)).sum w
        ≤ (S.filter (fun e => L e ≤ η)).sum w := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        rw [Finset.mem_filter] at he ⊢
        exact ⟨he.1, he.2.2⟩
      · intro e he _
        exact hw e (Finset.mem_of_mem_filter e he)
    have hnn : 0 ≤ (S.filter (fun e => L e ≤ η)).sum w :=
      Finset.sum_nonneg (fun e he => hw e (Finset.mem_of_mem_filter e he))
    calc (S.filter (fun e => I e ≤ Δ - k ∧ L e ≤ η)).sum w
        ≤ (S.filter (fun e => L e ≤ η)).sum w := hsub
      _ = 1 * (S.filter (fun e => L e ≤ η)).sum w := (one_mul _).symm
      _ ≤ (2 : ℝ) ^ (-(k - η - s)) * (S.filter (fun e => L e ≤ η)).sum w :=
          mul_le_mul_of_nonneg_right h1 hnn
  · -- k > η + s: no explanation has both a small residual and a large deficit
    have hempty : S.filter (fun e => I e ≤ Δ - k ∧ L e ≤ η) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro e he ⟨h1, h2⟩
      have := hgart e he
      omega
    rw [hempty, Finset.sum_empty]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun e he => hw e (Finset.mem_of_mem_filter e he)))

/-! ## Instantiation on abstract complexity weights -/

variable (F : AITProb)

/-- The abstract complexity weight is nonnegative: `2^{−K e}/m x ≥ 0`. (Helper.) -/
theorem post_nonneg (e x : F.Obj) : 0 ≤ F.post e x := by
  unfold AITProb.post
  exact div_nonneg (by positivity) (le_of_lt (F.m_pos x))

/-- **ART, residual-transfer form (WP0203, posterior residual-transfer proposition).**
    Index a finite family of specified explanations by `ι`: world `W i`, regulator `R i`, common
    observed (regulated) output `x`, and null output `z0 i`. Suppose each explanation satisfies
    the named chain-rule facts behind GART (`MutualChain`, `CondSubadd`, `CondMono`,
    `DataProcessing`) and belongs to ART's class `E_b`, i.e. `K (z0 i) = b`. Then, for the
    abstract weights `F.post` at `x`, the mass of explanations whose shared
    information falls `k` below the gap `Δ = b − K x` is at most the mass of explanations whose
    counterfactual residual is at least `k − 4·slack`. No normalization or
    program assignment is concluded by this finite-weight comparison. -/
theorem posterior_residual_transfer {ι : Type*} (S : Finset ι)
    (W R z0 : ι → F.Obj) (x : F.Obj) (b : ℕ) (k : ℤ)
    (hb : ∀ i ∈ S, F.K (z0 i) = b)
    (hmut : ∀ i ∈ S, RegulationBalance.MutualChain F.toAITFrame (z0 i) (R i))
    (hsub : ∀ i ∈ S, RegulationBalance.CondSubadd F.toAITFrame x (z0 i) (R i))
    (hmono : ∀ i ∈ S, RegulationBalance.CondMono F.toAITFrame x (R i))
    (hdp : ∀ i ∈ S, RegulationBalance.DataProcessing F.toAITFrame (z0 i) (W i) (R i)) :
    (S.filter (fun i => IK F.toAITFrame (W i) (R i) ≤ ((b : ℤ) - (F.K x : ℤ)) - k)).sum
        (fun i => F.post (F.pair (W i) (R i)) x)
      ≤ (S.filter (fun i => k - 4 * (F.slack : ℤ)
            ≤ GroundedRegulation.residual F.toAITFrame x (z0 i) (R i))).sum
        (fun i => F.post (F.pair (W i) (R i)) x) := by
  apply class_mass_transfer S (fun i => F.post (F.pair (W i) (R i)) x)
    (fun i _ => post_nonneg F _ x)
    (fun i => IK F.toAITFrame (W i) (R i))
    (fun i => GroundedRegulation.residual F.toAITFrame x (z0 i) (R i))
    ((b : ℤ) - (F.K x : ℤ)) k (4 * (F.slack : ℤ))
  intro i hi
  have h := GroundedRegulation.grounded_inequality F.toAITFrame (W i) x (z0 i) (R i)
    (hmut i hi) (hsub i hi) (hmono i hi) (hdp i hi)
  simp only [RegulationBalance.gap] at h
  have hbi := hb i hi
  omega

/-- **Under a residual bound, the low-information class has abstract weight zero.**
    Same setting as `posterior_residual_transfer`, with every explanation's residual at most
    `lam`: no explanation has shared information below `Δ − lam − 4·slack`. -/
theorem posterior_residual_bounded_zero {ι : Type*} (S : Finset ι)
    (W R z0 : ι → F.Obj) (x : F.Obj) (b : ℕ) (lam : ℤ)
    (hb : ∀ i ∈ S, F.K (z0 i) = b)
    (hmut : ∀ i ∈ S, RegulationBalance.MutualChain F.toAITFrame (z0 i) (R i))
    (hsub : ∀ i ∈ S, RegulationBalance.CondSubadd F.toAITFrame x (z0 i) (R i))
    (hmono : ∀ i ∈ S, RegulationBalance.CondMono F.toAITFrame x (R i))
    (hdp : ∀ i ∈ S, RegulationBalance.DataProcessing F.toAITFrame (z0 i) (W i) (R i))
    (hlam : ∀ i ∈ S, GroundedRegulation.residual F.toAITFrame x (z0 i) (R i) ≤ lam) :
    (S.filter (fun i => IK F.toAITFrame (W i) (R i)
        < ((b : ℤ) - (F.K x : ℤ)) - lam - 4 * (F.slack : ℤ))).sum
        (fun i => F.post (F.pair (W i) (R i)) x) = 0 := by
  apply residual_bounded_class_mass_zero S (fun i => F.post (F.pair (W i) (R i)) x)
    (fun i => IK F.toAITFrame (W i) (R i))
    (fun i => GroundedRegulation.residual F.toAITFrame x (z0 i) (R i))
    ((b : ℤ) - (F.K x : ℤ)) lam (4 * (F.slack : ℤ))
  · intro i hi
    have h := GroundedRegulation.grounded_inequality F.toAITFrame (W i) x (z0 i) (R i)
      (hmut i hi) (hsub i hi) (hmono i hi) (hdp i hi)
    simp only [RegulationBalance.gap] at h
    have hbi := hb i hi
    omega
  · exact hlam

/-! ## Evidence-local conditional transfers -/

/-- evidence-local hypotheses with an explicit conditional probability. -/
theorem conditional_confidence_transfer {E : Type*} (w : E → ENNReal)
    (gap I L : E → Int) (evidence : Set E) (d eta h : Int)
    (hgart : ∀ e ∈ evidence, w e ≠ 0 → gap e ≤ I e + L e + h)
    (hgap : ∀ e ∈ evidence, w e ≠ 0 → d ≤ gap e)
    (hpos : 0 < eventMass w evidence) (hfinite : eventMass w evidence < ⊤) :
    conditionalMass w {e | I e < d - eta - h} evidence hpos hfinite
      ≤ conditionalMass w {e | eta < L e} evidence hpos hfinite := by
  have hmass : eventMass w ({e | I e < d - eta - h} ∩ evidence)
      ≤ eventMass w ({e | eta < L e} ∩ evidence) := by
    apply ENNReal.tsum_le_tsum
    intro e
    by_cases he : e ∈ {e | I e < d - eta - h} ∩ evidence
    · by_cases hw : w e = 0
      · rw [Set.indicator_of_mem he, hw]
        exact bot_le
      · have hg := hgart e he.2 hw
        have hd := hgap e he.2 hw
        have hb : e ∈ {e | eta < L e} ∩ evidence := by
          refine ⟨?_, he.2⟩
          have hi := he.1
          simp only [Set.mem_setOf_eq] at hi ⊢
          omega
        simp only [Set.indicator_of_mem he, Set.indicator_of_mem hb, le_refl]
    · rw [Set.indicator_of_notMem he]
      exact bot_le
  simp only [conditionalMass, div_eq_mul_inv]
  exact mul_le_mul' hmass le_rfl

/-- retain a variable coding allowance inside the residual event. -/
theorem conditional_variable_transfer {E : Type*} (w : E → ENNReal)
    (gap I L allowance : E → Int) (evidence : Set E) (k : Int)
    (hgart : ∀ e ∈ evidence, w e ≠ 0 → gap e ≤ I e + L e + allowance e)
    (hpos : 0 < eventMass w evidence) (hfinite : eventMass w evidence < ⊤) :
    conditionalMass w {e | I e ≤ gap e - k} evidence hpos hfinite
      ≤ conditionalMass w {e | k ≤ L e + allowance e} evidence hpos hfinite := by
  have hmass : eventMass w ({e | I e ≤ gap e - k} ∩ evidence)
      ≤ eventMass w ({e | k ≤ L e + allowance e} ∩ evidence) := by
    apply ENNReal.tsum_le_tsum
    intro e
    by_cases he : e ∈ {e | I e ≤ gap e - k} ∩ evidence
    · by_cases hw : w e = 0
      · rw [Set.indicator_of_mem he, hw]
        exact bot_le
      · have hg := hgart e he.2 hw
        have hb : e ∈ {e | k ≤ L e + allowance e} ∩ evidence := by
          refine ⟨?_, he.2⟩
          have hi := he.1
          simp only [Set.mem_setOf_eq] at hi ⊢
          omega
        simp only [Set.indicator_of_mem he, Set.indicator_of_mem hb, le_refl]
    · rw [Set.indicator_of_notMem he]
      exact bot_le
  simp only [conditionalMass, div_eq_mul_inv]
  exact mul_le_mul' hmass le_rfl

/-- a separately supplied residual tail transfers to information deficit. -/
theorem conditional_exponential_transfer {E : Type*} (w : E → ENNReal)
    (gap I L allowance : E → Int) (evidence : Set E) (h k : Int)
    (hgart : ∀ e ∈ evidence, w e ≠ 0 → gap e ≤ I e + L e + allowance e)
    (hallow : ∀ e ∈ evidence, w e ≠ 0 → allowance e ≤ h)
    (hpos : 0 < eventMass w evidence) (hfinite : eventMass w evidence < ⊤)
    (A : ENNReal) (mu : Real) (_hA : 0 < A) (_hAfinite : A < ⊤) (_hmu : 0 < mu)
    (htail : ∀ u : Int, 0 ≤ u →
      conditionalMass w {e | u ≤ L e} evidence hpos hfinite
        ≤ A * (2 : ENNReal) ^ (-mu * (u : Real)))
    (hk : h ≤ k) :
    conditionalMass w {e | I e ≤ gap e - k} evidence hpos hfinite
      ≤ min 1 (A * (2 : ENNReal) ^ (-mu * ((k - h : Int) : Real))) := by
  have hg : ∀ e ∈ evidence, w e ≠ 0 → gap e ≤ I e + L e + h := by
    intro e he hw
    have := hgart e he hw
    have := hallow e he hw
    omega
  have htransfer := conditional_variable_transfer w gap I L (fun _ => h)
    evidence k hg hpos hfinite
  have hevents : {e | k ≤ L e + h} = {e | k - h ≤ L e} := by
    ext e
    simp only [Set.mem_setOf_eq]
    omega
  rw [hevents] at htransfer
  exact le_min (conditionalMass_le_one w _ evidence hpos hfinite)
    (htransfer.trans (htail (k - h) (by omega)))

end ResidualTransfer
end KTAIT
