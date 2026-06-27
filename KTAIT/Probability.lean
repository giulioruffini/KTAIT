/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib

/-!
# KTAIT.Probability — the Bayes ↔ Kolmogorov conditioning bridge (M2.5, Stage B)

This file makes explicit the single step that turns *probabilistic* conditioning into
*algorithmic* conditioning — the thing that is genuinely confusing in ART.

`PrefixMachine` carries a program type `Prog`, an output type `Out`, the machine map
`U : Prog → Out`, program length `len`, Kolmogorov complexity `K`, and the universal
a-priori semimeasure `m : Out → ℝ` (with `m x > 0`).

* The **prior** over programs is `P(p) = 2^{−|p|}` (`prior`).
* The **posterior** of a program given the output it produces is, by Bayes with the
  deterministic likelihood `P(x | p) = 1{U p = x}` and evidence `m(x)`,
  `P(p | x) = 2^{−|p|} / m(x)` (`posterior`).
* The **Coding Theorem** `c₁·2^{−K(x)} ≤ m(x) ≤ c₂·2^{−K(x)}` is the *bridge* between
  probability `m` and complexity `K` (`CodingTheorem`, a hypothesis).

**Lemma 1** then sandwiches the Bayesian posterior between complexity expressions:
`(1/c₂)·2^{K(x)−|p|} ≤ P(p | x) ≤ (1/c₁)·2^{K(x)−|p|}`.

This is exactly Lemma 1 of the ART paper, and it is *the* place where `P(· | x)` becomes
a `K`-quantity. Combined with a canonical `K(W,R)+O(1)` code for the explanation `(W,R)`,
it yields the wrapper bound Eq. (6) that `KTAIT.ART` assumes — so Stage B opens the box
that Stage A took as a hypothesis.
-/

namespace KTAIT

/-- A universal prefix machine with its a-priori semimeasure. -/
structure PrefixMachine where
  /-- The type of (self-delimiting) programs. -/
  Prog : Type
  /-- The type of outputs/observations. -/
  Out : Type
  /-- The machine map: program ↦ output. -/
  U : Prog → Out
  /-- Program length `|p|`. -/
  len : Prog → Nat
  /-- Kolmogorov complexity `K(x)`. -/
  K : Out → Nat
  /-- The universal a-priori semimeasure `m(x) = ∑_{U p = x} 2^{−|p|}` (kept abstract). -/
  m : Out → ℝ
  /-- The semimeasure is strictly positive on observed outputs. -/
  m_pos : ∀ x, 0 < m x

namespace PrefixMachine

variable (M : PrefixMachine)

/-- Prior weight of a program: `P(p) = 2^{−|p|}`. -/
noncomputable def prior (p : M.Prog) : ℝ := (2 : ℝ) ^ (-(M.len p : ℤ))

/-- Bayesian posterior of `p` given the output `x = U p` it produces:
    with prior `2^{−|p|}`, deterministic likelihood `1{U p = x}`, evidence `m(x)`,
    Bayes gives `P(p | x) = 2^{−|p|} / m(x)`. -/
noncomputable def posterior (p : M.Prog) : ℝ := M.prior p / M.m (M.U p)

/-- The **Coding Theorem** (Solomonoff–Levin), Eq. (1)/(5): `m(x) = 2^{−K(x)}` up to
    positive multiplicative constants `c₁, c₂`. This is the probability ↔ complexity
    bridge, stated as a hypothesis (a named AIT fact). -/
def CodingTheorem (c1 c2 : ℝ) : Prop :=
  0 < c1 ∧ 0 < c2 ∧
    ∀ x, c1 * (2 : ℝ) ^ (-(M.K x : ℤ)) ≤ M.m x ∧ M.m x ≤ c2 * (2 : ℝ) ^ (-(M.K x : ℤ))

/-- **Lemma 1 (Program posterior given x).** Under the Coding Theorem, the Bayesian
    posterior is sandwiched between complexity expressions:
    `(1/c₂)·2^{K(x)−|p|} ≤ P(p | x) ≤ (1/c₁)·2^{K(x)−|p|}`. -/
theorem lemma1_posterior_bounds (c1 c2 : ℝ) (hC : M.CodingTheorem c1 c2) (p : M.Prog) :
    (1 / c2) * (2 : ℝ) ^ ((M.K (M.U p) : ℤ) - (M.len p : ℤ)) ≤ M.posterior p ∧
    M.posterior p ≤ (1 / c1) * (2 : ℝ) ^ ((M.K (M.U p) : ℤ) - (M.len p : ℤ)) := by
  obtain ⟨hc1, hc2, hcod⟩ := hC
  obtain ⟨hlow, hupp⟩ := hcod (M.U p)
  have hm : 0 < M.m (M.U p) := M.m_pos _
  have h2e : (0 : ℝ) < (2 : ℝ) ^ ((M.K (M.U p) : ℤ) - (M.len p : ℤ)) := by positivity
  -- Rewrite the posterior as  (2^{−K(x)} / m(x)) · 2^{K(x)−|p|}.
  have hpost : M.posterior p
      = ((2 : ℝ) ^ (-(M.K (M.U p) : ℤ)) / M.m (M.U p))
          * (2 : ℝ) ^ ((M.K (M.U p) : ℤ) - (M.len p : ℤ)) := by
    unfold PrefixMachine.posterior PrefixMachine.prior
    rw [show (-(M.len p : ℤ))
          = (-(M.K (M.U p) : ℤ)) + ((M.K (M.U p) : ℤ) - (M.len p : ℤ)) from by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), mul_div_right_comm]
  -- The Coding Theorem sandwiches the ratio  2^{−K(x)} / m(x)  between 1/c₂ and 1/c₁.
  have hlo : 1 / c2 ≤ (2 : ℝ) ^ (-(M.K (M.U p) : ℤ)) / M.m (M.U p) := by
    rw [div_le_div_iff₀ hc2 hm, one_mul]
    linarith [hupp, mul_comm c2 ((2 : ℝ) ^ (-(M.K (M.U p) : ℤ)))]
  have hhi : (2 : ℝ) ^ (-(M.K (M.U p) : ℤ)) / M.m (M.U p) ≤ 1 / c1 := by
    rw [div_le_div_iff₀ hm hc1, one_mul]
    linarith [hlow, mul_comm c1 ((2 : ℝ) ^ (-(M.K (M.U p) : ℤ)))]
  rw [hpost]
  exact ⟨mul_le_mul_of_nonneg_right hlo h2e.le,
         mul_le_mul_of_nonneg_right hhi h2e.le⟩

end PrefixMachine

end KTAIT
