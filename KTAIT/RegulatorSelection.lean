/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic
import KTAIT.ART

/-!
# KTAIT.RegulatorSelection — Proposition 1 (regulator selection) (Phase 3)

WP0162 Appendix D, Proposition 1: under the universal conditional prior the preferred
sufficient regulator minimizes conditional complexity `K(R | W)`, equivalently maximizes
`M(W:R) − K(R)`. The engine is the chain rule / symmetry of information
`K(R | W) = K(R) − M(W:R)` (a standard AIT identity, taken as a named hypothesis).

We also tie this to ART's sharp form: by the same chain rule, the regulator-cost factors
`2^{M(W:R)}·2^{−K(R)}` collapse to `2^{−K(R|W)}`, so the sharp posterior bound reads
`post (W,R) x ≤ C·2^{−K(R|W)}·2^{−Δ}` — the universal posterior favors regulators that are
simple *given the world*.
-/

namespace KTAIT

/-- Chain rule / symmetry of information (named AIT hypothesis):
    `K(R | W) = K(R) − M(W:R)`, with `M(W:R) = IK W R` and `K(R|W) = cond R W`. -/
def ChainRule (F : AITFrame) (W R : F.Obj) : Prop :=
  (F.cond R W : ℤ) = (F.K R : ℤ) - IK F W R

/-- **Proposition 1 (order form).** Under the chain rule, minimizing conditional simplicity
    `K(R|W)` is equivalent to maximizing `M(W:R) − K(R)`. -/
theorem regulator_selection_order (F : AITFrame) (W R₁ R₂ : F.Obj)
    (h₁ : ChainRule F W R₁) (h₂ : ChainRule F W R₂) :
    (F.cond R₁ W : ℤ) ≤ (F.cond R₂ W : ℤ) ↔
      IK F W R₂ - (F.K R₂ : ℤ) ≤ IK F W R₁ - (F.K R₁ : ℤ) := by
  simp only [ChainRule] at h₁ h₂
  constructor <;> intro h <;> omega

/-- **Proposition 1 (selection form).** `R*` minimizes `K(·|W)` over the sufficiency set `S`
    iff it maximizes `M(W:·) − K(·)` over `S`. -/
theorem regulator_selection (F : AITFrame) (W : F.Obj) (S : Set F.Obj) (Rstar : F.Obj)
    (hRstar : Rstar ∈ S) (hchain : ∀ R ∈ S, ChainRule F W R) :
    (∀ R ∈ S, (F.cond Rstar W : ℤ) ≤ (F.cond R W : ℤ)) ↔
      (∀ R ∈ S, IK F W R - (F.K R : ℤ) ≤ IK F W Rstar - (F.K Rstar : ℤ)) := by
  have ho : ∀ R ∈ S, ((F.cond Rstar W : ℤ) ≤ (F.cond R W : ℤ) ↔
      IK F W R - (F.K R : ℤ) ≤ IK F W Rstar - (F.K Rstar : ℤ)) :=
    fun R hR => regulator_selection_order F W Rstar R (hchain Rstar hRstar) (hchain R hR)
  constructor
  · intro hmin R hR; exact (ho R hR).mp (hmin R hR)
  · intro hmax R hR; exact (ho R hR).mpr (hmax R hR)

namespace AITProb

/-- **ART sharp form, conditional reading.** By the chain rule, the sharp regulator bound
    `C·2^{M}·2^{−Δ}·2^{−K(R)}` collapses to `C·2^{−K(R|W)}·2^{−Δ}`: the posterior favors
    regulators simple *given the world*. -/
theorem probabilistic_regulator_theorem_conditional
    (F : AITProb) (W R xon xoff : F.Obj)
    (c0 : ℤ) (hoff : (F.K xoff : ℤ) ≤ (F.K W : ℤ) + c0)
    {c1 : ℝ} (hLB : F.CodingLB c1) (hchain : ChainRule F.toAITFrame W R) :
    ∃ C : ℝ, 0 < C ∧
      F.post (F.pair W R) xon
        ≤ C * (2 : ℝ) ^ (-(F.cond R W : ℤ))
            * (2 : ℝ) ^ (-((F.K xoff : ℤ) - (F.K xon : ℤ))) := by
  obtain ⟨C, hC, hsharp⟩ :=
    probabilistic_regulator_theorem_sharp F W R xon xoff c0 hoff hLB
  refine ⟨C, hC, ?_⟩
  have hexp : IK F.toAITFrame W R + (-(F.K R : ℤ)) = -(F.cond R W : ℤ) := by
    simp only [ChainRule] at hchain; omega
  have key : (2 : ℝ) ^ (IK F.toAITFrame W R) * (2 : ℝ) ^ (-(F.K R : ℤ))
      = (2 : ℝ) ^ (-(F.cond R W : ℤ)) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), hexp]
  calc F.post (F.pair W R) xon
      ≤ C * (2 : ℝ) ^ (IK F.toAITFrame W R)
          * (2 : ℝ) ^ (-((F.K xoff : ℤ) - (F.K xon : ℤ))) * (2 : ℝ) ^ (-(F.K R : ℤ)) := hsharp
    _ = C * (2 : ℝ) ^ (-(F.cond R W : ℤ))
          * (2 : ℝ) ^ (-((F.K xoff : ℤ) - (F.K xon : ℤ))) := by rw [← key]; ring

end AITProb

end KTAIT
