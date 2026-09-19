/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import Mathlib
import KTAIT.Basic
import KTAIT.GroundedRegulation
import KTAIT.ResidualTransfer

/-!
# KTAIT.IndependentRegulation — regulation under independent initial sampling

A fixed AIT frame supplies prefix complexities and the common coding information. Independent
sampling has product weights `p W * q R`; normalized marginals make these a probability law.
`CodingDominated` supplies the standard consequence of a computable marginal law: its point
weights are bounded by a finite constant times `2^(-K)`. `PairKraft` supplies the prefix Kraft
bound for distinct world–regulator pairs. The sampling algorithms and any horizon-dependent
conventions must be included in the frame, or their description costs retained in the constants.

The mutual-information identity then gives the exponential moment

  `sum_(W,R) p W * q R * 2^(IK W R) <= a * b`.

Combining that derived moment with a pointwise regulator inequality gives

  `Pr[gap - residual - allowance >= t] <= min(1, a * b * 2^(-t))`.

The allowance may vary with the pair. All regulator hypotheses are restricted to pairs with
nonzero sampling weight. A uniform bound is needed only on the event used to infer
`Pr[gap >= d and residual <= ell] <= min(1, a * b * 2^(-(d-ell-s)))`.
The final theorem derives its pointwise bound from `GroundedRegulation.grounded_inequality`
and the named chain-rule/data-processing hypotheses, with allowance `3 * F.slack`.

This is a prospective bound under independently sampled initial descriptions. It is not a
posterior concentration theorem under ART's joint universal prior, and it does not assert that
independent random draws have zero algorithmic mutual information in every realization.
`independent_regulation_given_residual` conditions the joint-event bound on a small residual,
retaining the residual-event probability as a divisor.

The coding and Kraft facts are named `Prop` hypotheses, never global axioms. All sums use
`ENNReal`, so no hidden summability assumption is needed; the statements apply in particular to
countable families. Computability-to-coding domination is the classical AIT interface here,
not a theorem about an implemented universal machine.
-/

namespace KTAIT
namespace IndependentRegulation

noncomputable section

/-- **Marginal coding domination.** A finite constant `a` bounds each marginal weight by
    `a * 2^(-K x)`. For a computable probability law, this is the usual prefix-coding bound
    with the sampling specification included in the common frame or charged in `a`. -/
def CodingDominated (F : AITFrame) (p : F.Obj → ENNReal) (a : ENNReal) : Prop :=
  a ≠ ⊤ ∧ ∀ x, p x ≤ a * (2 : ENNReal) ^ (-(F.K x : ℤ))

/-- **Pair Kraft bound.** One shortest prefix description of each distinct encoded pair has
    total weight at most one. An actual prefix machine and injective pairing provide this fact. -/
def PairKraft (F : AITFrame) : Prop :=
  ∑' e : F.Obj × F.Obj, (2 : ENNReal) ^ (-(F.K (F.pair e.1 e.2) : ℤ)) ≤ 1

/-- The joint weights of independently sampled initial world and regulator descriptions. -/
def productWeight {E : Type*} (p q : E → ENNReal) (e : E × E) : ENNReal := p e.1 * q e.2

/-- The mutual-information identity cancels the two marginal code lengths. (Helper.) -/
private theorem pair_weight_identity (F : AITFrame) (a b : ENNReal) (x y : F.Obj) :
    (a * (2 : ENNReal) ^ (-(F.K x : ℤ))) *
        (b * (2 : ENNReal) ^ (-(F.K y : ℤ))) * (2 : ENNReal) ^ IK F x y
      = (a * b) * (2 : ENNReal) ^ (-(F.K (F.pair x y) : ℤ)) := by
  calc
    _ = (a * b) * (((2 : ENNReal) ^ (-(F.K x : ℤ)) *
        (2 : ENNReal) ^ (-(F.K y : ℤ))) * (2 : ENNReal) ^ IK F x y) := by ac_rfl
    _ = (a * b) * (2 : ENNReal) ^
        ((-(F.K x : ℤ)) + (-(F.K y : ℤ)) + IK F x y) := by
      rw [ENNReal.zpow_add (by norm_num) (by norm_num),
        ENNReal.zpow_add (by norm_num) (by norm_num)]
    _ = _ := by congr 2; simp only [IK]; omega

/-- **Exponential information moment under independent sampling.** Marginal coding domination
    and pair Kraft imply that the product-weighted sum of `2^(IK W R)` is at most `a * b`.
    Normalization is unnecessary for this weighted statement. -/
theorem independent_information_moment (F : AITFrame) (p q : F.Obj → ENNReal)
    (a b : ENNReal) (hp : CodingDominated F p a) (hq : CodingDominated F q b)
    (hk : PairKraft F) :
    ∑' e : F.Obj × F.Obj, productWeight p q e * (2 : ENNReal) ^ IK F e.1 e.2 ≤ a * b := by
  calc
    _ ≤ ∑' e : F.Obj × F.Obj,
        (a * b) * (2 : ENNReal) ^ (-(F.K (F.pair e.1 e.2) : ℤ)) := by
      apply ENNReal.tsum_le_tsum
      intro e
      calc
        _ ≤ (a * (2 : ENNReal) ^ (-(F.K e.1 : ℤ))) *
            (b * (2 : ENNReal) ^ (-(F.K e.2 : ℤ))) * (2 : ENNReal) ^ IK F e.1 e.2 := by
          exact mul_le_mul' (mul_le_mul' (hp.2 e.1) (hq.2 e.2)) le_rfl
        _ = _ := pair_weight_identity F a b e.1 e.2
    _ = (a * b) * ∑' e : F.Obj × F.Obj,
        (2 : ENNReal) ^ (-(F.K (F.pair e.1 e.2) : ℤ)) := ENNReal.tsum_mul_left
    _ ≤ (a * b) * 1 := mul_le_mul' le_rfl hk
    _ = _ := mul_one _

/-- Exponential Markov bound as pointwise domination of an event indicator. (Helper.) -/
private theorem weighted_exponential_tail {E : Type*} (w : E → ENNReal) (I : E → ℤ)
    (S : Set E) (t : ℤ) (hS : ∀ e ∈ S, w e ≠ 0 → t ≤ I e) :
    ∑' e, S.indicator w e ≤ (∑' e, w e * (2 : ENNReal) ^ I e) * (2 : ENNReal) ^ (-t) := by
  calc
    _ ≤ ∑' e, (w e * (2 : ENNReal) ^ I e) * (2 : ENNReal) ^ (-t) := by
      apply ENNReal.tsum_le_tsum
      intro e
      by_cases he : e ∈ S
      · rw [Set.indicator_of_mem he]
        by_cases hw : w e = 0
        · simp [hw]
        · have hi : 0 ≤ I e + -t := by have := hS e he hw; omega
          have hpow : (1 : ENNReal) ≤ (2 : ENNReal) ^ (I e + -t) := by
            simpa only [zpow_zero] using ENNReal.zpow_le_of_le (by norm_num : (1 : ENNReal) ≤ 2) hi
          calc
            w e = w e * 1 := (mul_one _).symm
            _ ≤ w e * (2 : ENNReal) ^ (I e + -t) := mul_le_mul' le_rfl hpow
            _ = _ := by rw [ENNReal.zpow_add (by norm_num) (by norm_num), mul_assoc]
      · rw [Set.indicator_of_notMem he]
        exact bot_le
    _ = _ := ENNReal.tsum_mul_right

/-- Normalized marginal weights yield normalized product weights. (Helper.) -/
private theorem productWeight_total {E : Type*} (p q : E → ENNReal)
    (hp : ∑' e, p e = 1) (hq : ∑' e, q e = 1) :
    ∑' e : E × E, productWeight p q e = 1 := by
  unfold productWeight
  rw [ENNReal.tsum_prod']
  simp_rw [ENNReal.tsum_mul_left, hq, mul_one]
  exact hp

/-- Any event under normalized product weights has mass at most one. (Helper.) -/
private theorem event_mass_le_one {E : Type*} (p q : E → ENNReal)
    (hp : ∑' e, p e = 1) (hq : ∑' e, q e = 1) (S : Set (E × E)) :
    ∑' e, S.indicator (productWeight p q) e ≤ 1 := by
  calc
    _ ≤ ∑' e : E × E, productWeight p q e :=
      ENNReal.tsum_le_tsum (Set.indicator_le_self _ _)
    _ = 1 := productWeight_total p q hp hq

/-- **Independent-sampling regulation bound with a variable allowance.** Under normalized
    independent marginals and the inequality `gap <= IK + residual + allowance` on their support,
    the event `gap - residual - allowance >= t` has probability at most
    `min(1, a * b * 2^(-t))`. No uniform bound on the allowance is assumed. -/
theorem independent_regulation_probability (F : AITFrame) (p q : F.Obj → ENNReal)
    (a b : ENNReal) (hp : CodingDominated F p a) (hq : CodingDominated F q b)
    (hk : PairKraft F) (hpMass : ∑' x, p x = 1) (hqMass : ∑' y, q y = 1)
    (gap residual allowance : F.Obj × F.Obj → ℤ)
    (hgart : ∀ e, productWeight p q e ≠ 0 →
      gap e ≤ IK F e.1 e.2 + residual e + allowance e) (t : ℤ) :
    ∑' e, Set.indicator {e | t ≤ gap e - residual e - allowance e}
        (productWeight p q) e
      ≤ min 1 ((a * b) * (2 : ENNReal) ^ (-t)) := by
  apply le_min
  · exact event_mass_le_one p q hpMass hqMass _
  · calc
      _ ≤ (∑' e : F.Obj × F.Obj,
          productWeight p q e * (2 : ENNReal) ^ IK F e.1 e.2) * (2 : ENNReal) ^ (-t) := by
        apply weighted_exponential_tail
        intro e he hw
        have := hgart e hw
        simp only [Set.mem_setOf_eq] at he
        omega
      _ ≤ (a * b) * (2 : ENNReal) ^ (-t) :=
        mul_le_mul' (independent_information_moment F p q a b hp hq hk) le_rfl

/-- **Large gap with small residual under independent sampling.** If the coding allowance is
    at most `s` on positive-weight pairs in the event `gap >= d` and `residual <= ell`, its
    probability is at most `min(1, a * b * 2^(-(d-ell-s)))`. The allowance can be unbounded
    elsewhere. -/
theorem independent_regulation_threshold (F : AITFrame) (p q : F.Obj → ENNReal)
    (a b : ENNReal) (hp : CodingDominated F p a) (hq : CodingDominated F q b)
    (hk : PairKraft F) (hpMass : ∑' x, p x = 1) (hqMass : ∑' y, q y = 1)
    (gap residual allowance : F.Obj × F.Obj → ℤ)
    (hgart : ∀ e, productWeight p q e ≠ 0 →
      gap e ≤ IK F e.1 e.2 + residual e + allowance e)
    (d ell s : ℤ)
    (hs : ∀ e, productWeight p q e ≠ 0 →
      d ≤ gap e → residual e ≤ ell → allowance e ≤ s) :
    ∑' e, Set.indicator {e | d ≤ gap e ∧ residual e ≤ ell} (productWeight p q) e
      ≤ min 1 ((a * b) * (2 : ENNReal) ^ (-(d - ell - s))) := by
  calc
    _ ≤ ∑' e, Set.indicator {e | d - ell - s ≤ gap e - residual e - allowance e}
        (productWeight p q) e := by
      apply ENNReal.tsum_le_tsum
      intro e
      by_cases hw : productWeight p q e = 0
      · simp [Set.indicator_apply, hw]
      · by_cases he : d ≤ gap e ∧ residual e ≤ ell
        · have ht : d - ell - s ≤ gap e - residual e - allowance e := by
            have := hs e hw he.1 he.2
            omega
          simp only [Set.indicator_apply, Set.mem_setOf_eq, if_pos he, if_pos ht, le_refl]
        · simp [Set.indicator_apply, he]
    _ ≤ _ := independent_regulation_probability F p q a b hp hq hk hpMass hqMass
      gap residual allowance hgart (d - ell - s)

/-- **GART under independently sampled initial descriptions.** The named chain-rule and
    data-processing hypotheses imply GART for each positive-weight world–regulator pair. With the
    independent-sampling moment bound, they make a gap at least `d` and counterfactual residual
    at most `ell` exponentially unlikely in `d - ell - 3*slack`, with factor `a * b`.
    Here `x e` and `z0 e` are the regulated and matched-null outputs of pair `e`. -/
theorem independent_gart_probability (F : AITFrame) (p q : F.Obj → ENNReal)
    (a b : ENNReal) (hp : CodingDominated F p a) (hq : CodingDominated F q b)
    (hk : PairKraft F) (hpMass : ∑' x, p x = 1) (hqMass : ∑' y, q y = 1)
    (x z0 : F.Obj × F.Obj → F.Obj)
    (hmut : ∀ e, productWeight p q e ≠ 0 → RegulationBalance.MutualChain F (z0 e) e.2)
    (hsub : ∀ e, productWeight p q e ≠ 0 → RegulationBalance.CondSubadd F (x e) (z0 e) e.2)
    (hmono : ∀ e, productWeight p q e ≠ 0 → RegulationBalance.CondMono F (x e) e.2)
    (hdp : ∀ e, productWeight p q e ≠ 0 → RegulationBalance.DataProcessing F (z0 e) e.1 e.2)
    (d ell : ℤ) :
    ∑' e, Set.indicator
        {e | d ≤ RegulationBalance.gap F (x e) (z0 e) ∧
          GroundedRegulation.residual F (x e) (z0 e) e.2 ≤ ell}
        (productWeight p q) e
      ≤ min 1 ((a * b) * (2 : ENNReal) ^ (-(d - ell - 3 * (F.slack : ℤ)))) := by
  apply independent_regulation_threshold F p q a b hp hq hk hpMass hqMass
    (fun e => RegulationBalance.gap F (x e) (z0 e))
    (fun e => GroundedRegulation.residual F (x e) (z0 e) e.2)
    (fun _ => 3 * (F.slack : ℤ))
  · intro e hw
    exact GroundedRegulation.grounded_inequality F e.1 (x e) (z0 e) e.2
      (hmut e hw) (hsub e hw) (hmono e hw) (hdp e hw)
  · intro _ _ _ _
    exact le_rfl

/-! ## Explicit conditioning of the prospective bound -/

open ResidualTransfer

/-- **Independent sampling conditioned on a small residual.** Dividing the joint-event bound
    by the positive residual-event probability bounds `Pr[gap >= d | residual <= eta]`.
    The denominator is retained; a rare conditioning event can remove the prospective rarity.
    The finite-mass premise is explicit even though normalized marginals already imply it. -/
theorem independent_regulation_given_residual (F : AITFrame) (p q : F.Obj → ENNReal)
    (a b : ENNReal) (hp : CodingDominated F p a) (hq : CodingDominated F q b)
    (hk : PairKraft F) (hpMass : ∑' x, p x = 1) (hqMass : ∑' y, q y = 1)
    (gap residual allowance : F.Obj × F.Obj → ℤ)
    (hgart : ∀ e, productWeight p q e ≠ 0 →
      gap e ≤ IK F e.1 e.2 + residual e + allowance e)
    (d eta h : ℤ)
    (hs : ∀ e, productWeight p q e ≠ 0 →
      d ≤ gap e → residual e ≤ eta → allowance e ≤ h)
    (hpos : 0 < eventMass (productWeight p q) {e | residual e ≤ eta})
    (hfinite : eventMass (productWeight p q) {e | residual e ≤ eta} < ⊤) :
    conditionalMass (productWeight p q) {e | d ≤ gap e} {e | residual e ≤ eta} hpos hfinite
      ≤ min 1 (((a * b) * (2 : ENNReal) ^ (-(d - eta - h))) /
        eventMass (productWeight p q) {e | residual e ≤ eta}) := by
  apply le_min
  · exact conditionalMass_le_one _ _ _ hpos hfinite
  · have hnum : eventMass (productWeight p q)
        ({e | d ≤ gap e} ∩ {e | residual e ≤ eta}) ≤
        (a * b) * (2 : ENNReal) ^ (-(d - eta - h)) :=
      (independent_regulation_threshold F p q a b hp hq hk hpMass hqMass
        gap residual allowance hgart d eta h hs).trans (min_le_right _ _)
    simp only [conditionalMass, div_eq_mul_inv]
    exact mul_le_mul' hnum le_rfl


end
end IndependentRegulation
end KTAIT
