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
* `posterior_residual_transfer` — the instantiation on the `AITProb` canonical-code posterior
  `post`, with the per-explanation hypothesis supplied by `GroundedRegulation.grounded_inequality`
  (the named chain-rule and data-processing facts) for each explanation.

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
      {e | k ≤ GroundedRegulation.residual F (y e) (y0 e) (R e) + 3 * (F.slack : ℤ)} w e := by
  apply class_mass_transfer_variable_tsum w
    (fun e => RegulationBalance.gap F (y e) (y0 e))
    (fun e => IK F (W e) (R e))
    (fun e => GroundedRegulation.residual F (y e) (y0 e) (R e))
    (fun _ => 3 * (F.slack : ℤ)) k
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

/-! ## Instantiation on the canonical-code posterior -/

variable (F : AITProb)

/-- The canonical-code posterior is nonnegative: `2^{−K e}/m x ≥ 0`. (Helper.) -/
theorem post_nonneg (e x : F.Obj) : 0 ≤ F.post e x := by
  unfold AITProb.post
  exact div_nonneg (by positivity) (le_of_lt (F.m_pos x))

/-- **ART, residual-transfer form (WP0203, posterior residual-transfer proposition).**
    Index a finite family of specified explanations by `ι`: world `W i`, regulator `R i`, common
    observed (regulated) output `x`, and null output `z0 i`. Suppose each explanation satisfies
    the named chain-rule facts behind GART (`MutualChain`, `CondSubadd`, `CondMono`,
    `DataProcessing`) and belongs to ART's class `E_b`, i.e. `K (z0 i) = b`. Then, for the
    canonical-code posterior conditioned on `x`, the mass of explanations whose shared
    information falls `k` below the gap `Δ = b − K x` is at most the mass of explanations whose
    counterfactual residual exceeds `k − 3·slack`. -/
theorem posterior_residual_transfer {ι : Type*} (S : Finset ι)
    (W R z0 : ι → F.Obj) (x : F.Obj) (b : ℕ) (k : ℤ)
    (hb : ∀ i ∈ S, F.K (z0 i) = b)
    (hmut : ∀ i ∈ S, RegulationBalance.MutualChain F.toAITFrame (z0 i) (R i))
    (hsub : ∀ i ∈ S, RegulationBalance.CondSubadd F.toAITFrame x (z0 i) (R i))
    (hmono : ∀ i ∈ S, RegulationBalance.CondMono F.toAITFrame x (R i))
    (hdp : ∀ i ∈ S, RegulationBalance.DataProcessing F.toAITFrame (z0 i) (W i) (R i)) :
    (S.filter (fun i => IK F.toAITFrame (W i) (R i) ≤ ((b : ℤ) - (F.K x : ℤ)) - k)).sum
        (fun i => F.post (F.pair (W i) (R i)) x)
      ≤ (S.filter (fun i => k - 3 * (F.slack : ℤ)
            ≤ GroundedRegulation.residual F.toAITFrame x (z0 i) (R i))).sum
        (fun i => F.post (F.pair (W i) (R i)) x) := by
  apply class_mass_transfer S (fun i => F.post (F.pair (W i) (R i)) x)
    (fun i _ => post_nonneg F _ x)
    (fun i => IK F.toAITFrame (W i) (R i))
    (fun i => GroundedRegulation.residual F.toAITFrame x (z0 i) (R i))
    ((b : ℤ) - (F.K x : ℤ)) k (3 * (F.slack : ℤ))
  intro i hi
  have h := GroundedRegulation.grounded_inequality F.toAITFrame (W i) x (z0 i) (R i)
    (hmut i hi) (hsub i hi) (hmono i hi) (hdp i hi)
  simp only [RegulationBalance.gap] at h
  have hbi := hb i hi
  omega

/-- **Conditional on a residual bound, the low-information class has posterior mass `0`.**
    Same setting as `posterior_residual_transfer`, with every explanation's residual at most
    `lam`: no explanation has shared information below `Δ − lam − 3·slack`. -/
theorem posterior_residual_bounded_zero {ι : Type*} (S : Finset ι)
    (W R z0 : ι → F.Obj) (x : F.Obj) (b : ℕ) (lam : ℤ)
    (hb : ∀ i ∈ S, F.K (z0 i) = b)
    (hmut : ∀ i ∈ S, RegulationBalance.MutualChain F.toAITFrame (z0 i) (R i))
    (hsub : ∀ i ∈ S, RegulationBalance.CondSubadd F.toAITFrame x (z0 i) (R i))
    (hmono : ∀ i ∈ S, RegulationBalance.CondMono F.toAITFrame x (R i))
    (hdp : ∀ i ∈ S, RegulationBalance.DataProcessing F.toAITFrame (z0 i) (W i) (R i))
    (hlam : ∀ i ∈ S, GroundedRegulation.residual F.toAITFrame x (z0 i) (R i) ≤ lam) :
    (S.filter (fun i => IK F.toAITFrame (W i) (R i)
        < ((b : ℤ) - (F.K x : ℤ)) - lam - 3 * (F.slack : ℤ))).sum
        (fun i => F.post (F.pair (W i) (R i)) x) = 0 := by
  apply residual_bounded_class_mass_zero S (fun i => F.post (F.pair (W i) (R i)) x)
    (fun i => IK F.toAITFrame (W i) (R i))
    (fun i => GroundedRegulation.residual F.toAITFrame x (z0 i) (R i))
    ((b : ℤ) - (F.K x : ℤ)) lam (3 * (F.slack : ℤ))
  · intro i hi
    have h := GroundedRegulation.grounded_inequality F.toAITFrame (W i) x (z0 i) (R i)
      (hmut i hi) (hsub i hi) (hmono i hi) (hdp i hi)
    simp only [RegulationBalance.gap] at h
    have hbi := hb i hi
    omega
  · exact hlam

end ResidualTransfer
end KTAIT
