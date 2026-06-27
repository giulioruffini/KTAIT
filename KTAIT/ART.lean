/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic

/-!
# KTAIT.ART — the probabilistic Algorithmic Regulator Theorem (M2.5 + Phase 1)

The faithful, probabilistic ART (Theorems 1–2 of *An Algorithmic-Information-Theoretic
Regulator Theorem*, Entropy 2026, 28, 257).

`AITProb` extends `AITFrame` with the universal semimeasure `m : Obj → ℝ`. The Bayesian
posterior on an explanation `e` given observation `x` is then DEFINED (not assumed) as the
canonical-code posterior `post e x := 2^{-K(e)} / m(x)` — this is Lemma 1 (`Probability.lean`)
specialized to the canonical `|p_e| = K(e)` code.

The only assumption is the **Coding Theorem** on `m` (`CodingLB`/`CodingUB`,
`c₁·2^{-K x} ≤ m x ≤ c₂·2^{-K x}`), a standard AIT fact. From it we DERIVE:

* `wrapper_bound` — Eq. (6): `post e x ≤ (1/c₁)·2^{K(x)−K(e)}` (previously assumed; now proved).
* `theorem1_posterior_tilt` — Theorem 1: `post (W,R) x ∈ [1/c₂, 1/c₁]·2^{K(x)−K(W)−K(R)+M(W:R)}`.
* `probabilistic_regulator_theorem` — Theorem 2: `post (W,R) x ≤ C·2^{M(W:R)}·2^{−Δ}`,
  now resting on the coding theorem + Lemma 2 (no free wrapper hypothesis).
-/

namespace KTAIT

/-- A probabilistic AIT frame: an `AITFrame` plus the universal semimeasure `m`. -/
structure AITProb extends AITFrame where
  /-- The universal a-priori semimeasure `m(x)` (strictly positive on observations). -/
  m : Obj → ℝ
  /-- Positivity of the semimeasure. -/
  m_pos : ∀ x, 0 < m x

namespace AITProb

variable (F : AITProb)

/-- The Bayesian (canonical-code) posterior `P(e | x) = 2^{−K(e)} / m(x)`. -/
noncomputable def post (e x : F.Obj) : ℝ := (2 : ℝ) ^ (-(F.K e : ℤ)) / F.m x

/-- Coding Theorem, lower bound: `c₁·2^{−K x} ≤ m x` (with `c₁ > 0`). -/
def CodingLB (c1 : ℝ) : Prop := 0 < c1 ∧ ∀ x, c1 * (2 : ℝ) ^ (-(F.K x : ℤ)) ≤ F.m x

/-- Coding Theorem, upper bound: `m x ≤ c₂·2^{−K x}` (with `c₂ > 0`). -/
def CodingUB (c2 : ℝ) : Prop := 0 < c2 ∧ ∀ x, F.m x ≤ c2 * (2 : ℝ) ^ (-(F.K x : ℤ))

/-- Helper: the posterior factors as `(2^{−K x}/m x)·2^{K x − K e}`. -/
private theorem post_factor (e x : F.Obj) :
    F.post e x = ((2 : ℝ) ^ (-(F.K x : ℤ)) / F.m x) * (2 : ℝ) ^ ((F.K x : ℤ) - (F.K e : ℤ)) := by
  unfold AITProb.post
  rw [show (-(F.K e : ℤ)) = (-(F.K x : ℤ)) + ((F.K x : ℤ) - (F.K e : ℤ)) from by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), mul_div_right_comm]

/-- **Wrapper bound — Eq. (6).** Derived from the coding theorem (lower bound):
    `post e x ≤ (1/c₁)·2^{K(x) − K(e)}`. -/
theorem wrapper_bound {c1 : ℝ} (hLB : F.CodingLB c1) (e x : F.Obj) :
    F.post e x ≤ (1 / c1) * (2 : ℝ) ^ ((F.K x : ℤ) - (F.K e : ℤ)) := by
  obtain ⟨hc1, hlb⟩ := hLB
  have hm : 0 < F.m x := F.m_pos x
  have h2e : (0 : ℝ) < (2 : ℝ) ^ ((F.K x : ℤ) - (F.K e : ℤ)) := by positivity
  have hratio : (2 : ℝ) ^ (-(F.K x : ℤ)) / F.m x ≤ 1 / c1 := by
    rw [div_le_div_iff₀ hm hc1, one_mul]
    linarith [hlb x, mul_comm c1 ((2 : ℝ) ^ (-(F.K x : ℤ)))]
  rw [post_factor]
  exact mul_le_mul_of_nonneg_right hratio h2e.le

/-- **Theorem 1 (coupled-pair posterior tilt).** With `M(W:R) = IK W R`, the posterior is
    sandwiched: `(1/c₂)·2^{K(x)−K(W)−K(R)+M} ≤ post (W,R) x ≤ (1/c₁)·2^{K(x)−K(W)−K(R)+M}`. -/
theorem theorem1_posterior_tilt {c1 c2 : ℝ}
    (hLB : F.CodingLB c1) (hUB : F.CodingUB c2) (W R x : F.Obj) :
    (1 / c2) * (2 : ℝ) ^ ((F.K x : ℤ) - (F.K W : ℤ) - (F.K R : ℤ) + IK F.toAITFrame W R)
        ≤ F.post (F.pair W R) x ∧
    F.post (F.pair W R) x
        ≤ (1 / c1) * (2 : ℝ) ^ ((F.K x : ℤ) - (F.K W : ℤ) - (F.K R : ℤ) + IK F.toAITFrame W R) := by
  have hexp_eq : ((F.K x : ℤ) - (F.K W : ℤ) - (F.K R : ℤ) + IK F.toAITFrame W R)
      = (F.K x : ℤ) - (F.K (F.pair W R) : ℤ) := by simp only [IK]; ring
  rw [hexp_eq]
  refine ⟨?_, wrapper_bound F hLB _ _⟩
  -- lower bound from the upper coding bound
  obtain ⟨hc2, hub⟩ := hUB
  have hm : 0 < F.m x := F.m_pos x
  have h2e : (0 : ℝ) < (2 : ℝ) ^ ((F.K x : ℤ) - (F.K (F.pair W R) : ℤ)) := by positivity
  have hratio : 1 / c2 ≤ (2 : ℝ) ^ (-(F.K x : ℤ)) / F.m x := by
    rw [div_le_div_iff₀ hc2 hm, one_mul]
    linarith [hub x, mul_comm c2 ((2 : ℝ) ^ (-(F.K x : ℤ)))]
  rw [post_factor]
  exact mul_le_mul_of_nonneg_right hratio h2e.le

/-- **Theorem 2 (Probabilistic Regulator Theorem).** Now resting on the coding theorem
    (`hLB`) and Lemma 2 (`hoff`) — the wrapper bound is derived, not assumed:
    `post (W,R) x ≤ C · 2^{M(W:R)} · 2^{−Δ}` with `Δ = K(O_{W,∅}) − K(O_{W,R})`. -/
theorem probabilistic_regulator_theorem
    (W R xon xoff : F.Obj)
    (c0 : ℤ) (hoff : (F.K xoff : ℤ) ≤ (F.K W : ℤ) + c0)
    {c1 : ℝ} (hLB : F.CodingLB c1) :
    ∃ C : ℝ, 0 < C ∧
      F.post (F.pair W R) xon
        ≤ C * (2 : ℝ) ^ (IK F.toAITFrame W R)
            * (2 : ℝ) ^ (-((F.K xoff : ℤ) - (F.K xon : ℤ))) := by
  have hc1 := hLB.1
  refine ⟨(1 / c1) * (2 : ℝ) ^ c0, by positivity, ?_⟩
  have hexp : (F.K xon : ℤ) - (F.K (F.pair W R) : ℤ)
      ≤ c0 + IK F.toAITFrame W R - ((F.K xoff : ℤ) - (F.K xon : ℤ)) := by
    simp only [IK]; omega
  calc F.post (F.pair W R) xon
      ≤ (1 / c1) * (2 : ℝ) ^ ((F.K xon : ℤ) - (F.K (F.pair W R) : ℤ)) :=
        wrapper_bound F hLB _ _
    _ ≤ (1 / c1) * (2 : ℝ) ^ (c0 + IK F.toAITFrame W R - ((F.K xoff : ℤ) - (F.K xon : ℤ))) := by
        gcongr
        norm_num
    _ = (1 / c1) * (2 : ℝ) ^ c0 * (2 : ℝ) ^ (IK F.toAITFrame W R)
          * (2 : ℝ) ^ (-((F.K xoff : ℤ) - (F.K xon : ℤ))) := by
        rw [show c0 + IK F.toAITFrame W R - ((F.K xoff : ℤ) - (F.K xon : ℤ))
              = c0 + IK F.toAITFrame W R + (-((F.K xoff : ℤ) - (F.K xon : ℤ))) from by ring,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        ring

/-- **Theorem 2 (sharp form), retaining the regulator cost `2^{−K(R)}`.**
    This is clarification (ii) of the ART paper / WP0162 Eq. (22): before dropping
    `2^{−K(R)}≤1`. No extra hypothesis is needed — the exponent identity is exact
    (the `K(R)` term carried through, not bounded away):
    `post (W,R) x ≤ C · 2^{M(W:R)} · 2^{−Δ} · 2^{−K(R)}`.
    Equivalently (by the chain rule `K(W,R)=K(W)+K(R\mid W)`, an AIT axiom) this reads
    `≤ C · 2^{−K(R\mid W)} · 2^{−Δ}`. -/
theorem probabilistic_regulator_theorem_sharp
    (W R xon xoff : F.Obj)
    (c0 : ℤ) (hoff : (F.K xoff : ℤ) ≤ (F.K W : ℤ) + c0)
    {c1 : ℝ} (hLB : F.CodingLB c1) :
    ∃ C : ℝ, 0 < C ∧
      F.post (F.pair W R) xon
        ≤ C * (2 : ℝ) ^ (IK F.toAITFrame W R)
            * (2 : ℝ) ^ (-((F.K xoff : ℤ) - (F.K xon : ℤ)))
            * (2 : ℝ) ^ (-(F.K R : ℤ)) := by
  have hc1 := hLB.1
  refine ⟨(1 / c1) * (2 : ℝ) ^ c0, by positivity, ?_⟩
  -- exact exponent identity (K(R) retained, not dropped):
  have hexp : (F.K xon : ℤ) - (F.K (F.pair W R) : ℤ)
      ≤ c0 + IK F.toAITFrame W R - ((F.K xoff : ℤ) - (F.K xon : ℤ)) - (F.K R : ℤ) := by
    simp only [IK]; omega
  calc F.post (F.pair W R) xon
      ≤ (1 / c1) * (2 : ℝ) ^ ((F.K xon : ℤ) - (F.K (F.pair W R) : ℤ)) :=
        wrapper_bound F hLB _ _
    _ ≤ (1 / c1) * (2 : ℝ) ^ (c0 + IK F.toAITFrame W R
            - ((F.K xoff : ℤ) - (F.K xon : ℤ)) - (F.K R : ℤ)) := by
        gcongr
        norm_num
    _ = (1 / c1) * (2 : ℝ) ^ c0 * (2 : ℝ) ^ (IK F.toAITFrame W R)
          * (2 : ℝ) ^ (-((F.K xoff : ℤ) - (F.K xon : ℤ))) * (2 : ℝ) ^ (-(F.K R : ℤ)) := by
        rw [show c0 + IK F.toAITFrame W R - ((F.K xoff : ℤ) - (F.K xon : ℤ)) - (F.K R : ℤ)
              = c0 + IK F.toAITFrame W R + (-((F.K xoff : ℤ) - (F.K xon : ℤ)))
                  + (-(F.K R : ℤ)) from by ring,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        ring

/-- The published headline (Theorem 2) follows from the sharp form by `2^{−K(R)} ≤ 1`. -/
theorem probabilistic_regulator_theorem_of_sharp
    (W R xon xoff : F.Obj)
    (c0 : ℤ) (hoff : (F.K xoff : ℤ) ≤ (F.K W : ℤ) + c0)
    {c1 : ℝ} (hLB : F.CodingLB c1) :
    ∃ C : ℝ, 0 < C ∧
      F.post (F.pair W R) xon
        ≤ C * (2 : ℝ) ^ (IK F.toAITFrame W R)
            * (2 : ℝ) ^ (-((F.K xoff : ℤ) - (F.K xon : ℤ))) := by
  obtain ⟨C, hC, hsharp⟩ := probabilistic_regulator_theorem_sharp F W R xon xoff c0 hoff hLB
  refine ⟨C, hC, ?_⟩
  have hKR : (2 : ℝ) ^ (-(F.K R : ℤ)) ≤ 1 := by
    apply zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  calc F.post (F.pair W R) xon
      ≤ C * (2 : ℝ) ^ (IK F.toAITFrame W R)
          * (2 : ℝ) ^ (-((F.K xoff : ℤ) - (F.K xon : ℤ))) * (2 : ℝ) ^ (-(F.K R : ℤ)) := hsharp
    _ ≤ C * (2 : ℝ) ^ (IK F.toAITFrame W R)
          * (2 : ℝ) ^ (-((F.K xoff : ℤ) - (F.K xon : ℤ))) * 1 := by gcongr
    _ = C * (2 : ℝ) ^ (IK F.toAITFrame W R)
          * (2 : ℝ) ^ (-((F.K xoff : ℤ) - (F.K xon : ℤ))) := by ring

/-- **Theorem 3 (On/Off evidence equals the complexity gap).** The ON/OFF evidence ratio
    is `2^Δ` up to the coding constants, `Δ = K(O_{W,∅}) − K(O_{W,R})`:
    `(c₁/c₂)·2^{Δ} ≤ m(x_on)/m(x_off) ≤ (c₂/c₁)·2^{Δ}`.
    (Multiplicative form; taking `log₂` gives `log₂(m_on/m_off) = Δ ± log₂(c₂/c₁)`.) -/
theorem theorem3_onoff_evidence {c1 c2 : ℝ}
    (hLB : F.CodingLB c1) (hUB : F.CodingUB c2) (xon xoff : F.Obj) :
    (c1 / c2) * (2 : ℝ) ^ ((F.K xoff : ℤ) - (F.K xon : ℤ)) ≤ F.m xon / F.m xoff ∧
    F.m xon / F.m xoff ≤ (c2 / c1) * (2 : ℝ) ^ ((F.K xoff : ℤ) - (F.K xon : ℤ)) := by
  obtain ⟨hc1, hlb⟩ := hLB
  obtain ⟨hc2, hub⟩ := hUB
  have hmon := F.m_pos xon
  have hmof := F.m_pos xoff
  -- algebra:  (a·2^{-K xon}) / (b·2^{-K xoff})  =  (a/b)·2^{K xoff − K xon}
  have ealg : ∀ a b : ℝ,
      (a * (2 : ℝ) ^ (-(F.K xon : ℤ))) / (b * (2 : ℝ) ^ (-(F.K xoff : ℤ)))
        = (a / b) * (2 : ℝ) ^ ((F.K xoff : ℤ) - (F.K xon : ℤ)) := by
    intro a b
    have hh : ((F.K xoff : ℤ) - (F.K xon : ℤ)) = (-(F.K xon : ℤ)) - (-(F.K xoff : ℤ)) := by ring
    rw [mul_div_mul_comm, hh, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  refine ⟨?_, ?_⟩
  · rw [← ealg c1 c2]
    exact div_le_div₀ hmon.le (hlb xon) hmof (hub xoff)
  · rw [← ealg c2 c1]
    exact div_le_div₀ (by positivity) (hub xon) (by positivity) (hlb xoff)

end AITProb

end KTAIT
