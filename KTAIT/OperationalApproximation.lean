/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import Mathlib

/-!
# Accumulation of operational comparison errors (WP0004)

The estimates require a common operation schedule. Local residual and Lipschitz
bounds are hypotheses on the actual compared trajectories, not conclusions.
No physical or experiential interpretation of the metric is assumed.
-/

namespace KTAIT.OperationalApproximation

open Finset

/-- Iterating an affine error recurrence gives the finite geometric bound. -/
theorem affine_error_bound (E : ℕ → ℝ) (L ε : ℝ) (hL : 0 ≤ L)
    (step : ∀ n, E (n + 1) ≤ L * E n + ε) (n : ℕ) :
    E n ≤ L ^ n * E 0 + ε * ∑ j ∈ range n, L ^ j := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      E (n + 1) ≤ L * E n + ε := step n
      _ ≤ L * (L ^ n * E 0 + ε * ∑ j ∈ range n, L ^ j) + ε :=
        add_le_add (mul_le_mul_of_nonneg_left ih hL) le_rfl
      _ = L ^ (n + 1) * E 0 + ε * ∑ j ∈ range (n + 1), L ^ j := by
        rw [sum_range_succ, pow_succ]
        have hs := geom_sum_mul L n
        linear_combination ε * hs

/-- Nonexpansive operations accumulate at most one local tolerance per step. -/
theorem nonexpansive_error_bound (E : ℕ → ℝ) (ε : ℝ)
    (step : ∀ n, E (n + 1) ≤ E n + ε) (n : ℕ) :
    E n ≤ E 0 + n * ε := by
  simpa [mul_comm] using affine_error_bound E 1 ε (by norm_num) (by simpa using step) n

/-- The contractive form is the same finite geometric sum in closed form. -/
theorem contractive_error_bound (E : ℕ → ℝ) (L ε : ℝ) (hL : 0 ≤ L) (hL1 : L < 1)
    (step : ∀ n, E (n + 1) ≤ L * E n + ε) (n : ℕ) :
    E n ≤ L ^ n * E 0 + ε * ((1 - L ^ n) / (1 - L)) := by
  have hne : L ≠ 1 := ne_of_lt hL1
  have hg : (∑ j ∈ range n, L ^ j) = (1 - L ^ n) / (1 - L) := by
    rw [geom_sum_eq hne]
    have hn : 1 - L ≠ 0 := by linarith
    field_simp
    ring
  simpa [hg] using affine_error_bound E L ε hL step n

/-- A projected local residual and a Lipschitz estimate imply one error step. -/
theorem operational_error_step {X Q : Type*} [PseudoMetricSpace Q]
    (F : X → X) (G : Q → Q) (ρ : X → Q) (x : X) (q : Q) (L ε : ℝ)
    (residual : dist (ρ (F x)) (G (ρ x)) ≤ ε)
    (lip : dist (G (ρ x)) (G q) ≤ L * dist (ρ x) q) :
    dist (ρ (F x)) (G q) ≤ L * dist (ρ x) q + ε := by
  calc
    dist (ρ (F x)) (G q) ≤ dist (ρ (F x)) (G (ρ x)) + dist (G (ρ x)) (G q) :=
      dist_triangle _ _ _
    _ ≤ ε + L * dist (ρ x) q := add_le_add residual lip
    _ = L * dist (ρ x) q + ε := add_comm _ _

/-- The paper's bound follows from local estimates along a common schedule. -/
theorem common_schedule_error_bound {X Q A : Type*} [PseudoMetricSpace Q]
    (F : A → X → X) (G : A → Q → Q) (ρ : X → Q) (a : ℕ → A)
    (x : ℕ → X) (q : ℕ → Q) (L ε : ℝ) (hL : 0 ≤ L)
    (hx : ∀ j, x (j + 1) = F (a j) (x j)) (hq : ∀ j, q (j + 1) = G (a j) (q j))
    (residual : ∀ j, dist (ρ (F (a j) (x j))) (G (a j) (ρ (x j))) ≤ ε)
    (lip : ∀ j, dist (G (a j) (ρ (x j))) (G (a j) (q j)) ≤ L * dist (ρ (x j)) (q j))
    (n : ℕ) :
    dist (ρ (x n)) (q n) ≤ L ^ n * dist (ρ (x 0)) (q 0) + ε * ∑ j ∈ range n, L ^ j := by
  apply affine_error_bound (fun j => dist (ρ (x j)) (q j)) L ε hL
  intro j
  rw [hx, hq]
  exact operational_error_step _ _ _ _ _ L ε (residual j) (lip j)

/-- Uniform Lipschitz hypotheses supply the trajectory-wise estimate. -/
theorem lipschitz_schedule_bound {X Q A : Type*} [PseudoMetricSpace Q]
    (F : A → X → X) (G : A → Q → Q) (ρ : X → Q) (a : ℕ → A)
    (x : ℕ → X) (q : ℕ → Q) (L : NNReal) (ε : ℝ)
    (hx : ∀ j, x (j + 1) = F (a j) (x j)) (hq : ∀ j, q (j + 1) = G (a j) (q j))
    (residual : ∀ a x, dist (ρ (F a x)) (G a (ρ x)) ≤ ε)
    (lip : ∀ a, LipschitzWith L (G a)) (n : ℕ) :
    dist (ρ (x n)) (q n) ≤ (L : ℝ) ^ n * dist (ρ (x 0)) (q 0) +
      ε * ∑ j ∈ range n, (L : ℝ) ^ j := by
  exact common_schedule_error_bound F G ρ a x q L ε L.coe_nonneg hx hq
    (fun j => residual _ _) (fun j => (lip _).dist_le_mul _ _) n

/-- Multiplicative propagation of variable per-step Lipschitz constants. -/
def propagation (L : ℕ → ℝ) (i n : ℕ) : ℝ := ∏ j ∈ Ico i n, L j

/-- Unequal operation constants give weighted products of subsequent constants. -/
theorem varying_error_bound (E L ε : ℕ → ℝ) (hL : ∀ j, 0 ≤ L j)
    (step : ∀ j, E (j + 1) ≤ L j * E j + ε j) (n : ℕ) :
    E n ≤ propagation L 0 n * E 0 +
      ∑ i ∈ range n, ε i * propagation L (i + 1) n := by
  induction n with
  | zero => simp [propagation]
  | succ n ih =>
    have hprod (i : ℕ) (hi : i ≤ n) :
        propagation L i (n + 1) = propagation L i n * L n := by
      exact prod_Ico_succ_top hi _
    calc
      E (n + 1) ≤ L n * E n + ε n := step n
      _ ≤ L n * (propagation L 0 n * E 0 +
          ∑ i ∈ range n, ε i * propagation L (i + 1) n) + ε n :=
        add_le_add (mul_le_mul_of_nonneg_left ih (hL n)) le_rfl
      _ = propagation L 0 (n + 1) * E 0 +
          ∑ i ∈ range (n + 1), ε i * propagation L (i + 1) (n + 1) := by
        rw [sum_range_succ, hprod 0 (Nat.zero_le n)]
        simp only [propagation, Ico_self, prod_empty, mul_one]
        rw [mul_add, mul_sum]
        have hs : (∑ i ∈ range n, L n * (ε i * ∏ j ∈ Ico (i + 1) n, L j)) =
            ∑ i ∈ range n, ε i * ∏ j ∈ Ico (i + 1) (n + 1), L j := by
          apply sum_congr rfl
          intro i hi
          rw [prod_Ico_succ_top (by simpa using mem_range.mp hi)]
          ring
        rw [hs]
        ring

/-- A fixed nonzero metric tolerance need not define a transitive relation. -/
theorem tolerance_not_transitive :
    dist (0 : ℝ) 1 ≤ 1 ∧ dist (1 : ℝ) 2 ≤ 1 ∧ ¬ dist (0 : ℝ) 2 ≤ 1 := by
  norm_num [Real.dist_eq]

/-- A coordinate isometry preserves every comparison distance. -/
theorem transported_distance {Q R : Type*} [PseudoMetricSpace Q] [PseudoMetricSpace R]
    (h : Q → R) (hh : Isometry h) (q r : Q) : dist (h q) (h r) = dist q r :=
  hh.dist_eq q r

end KTAIT.OperationalApproximation
