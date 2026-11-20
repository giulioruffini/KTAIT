/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import Mathlib

/-!
# Prediction at a fixed coarse-graining

An index identifies a retained state and input. Its successor set comprises
the retained outcomes possible across the admitted hidden preparations.
-/

namespace KTAIT.ApproximateClosure

open scoped ENNReal

variable {I Q : Type*} [PseudoEMetricSpace Q]

/-- Worst-case error of one proposed outcome for a set of possible successors. -/
noncomputable def successorError (S : Set Q) (z : Q) : ℝ≥0∞ :=
  ⨆ s : S, edist s.val z

/-- The smallest possible worst-case error at one retained state and input. -/
noncomputable def successorRadius (S : Set Q) : ℝ≥0∞ :=
  ⨅ z : Q, successorError S z

/-- Choosing one deterministic prediction for each index attains the fiberwise
radius in the infimum, whether or not optimal centers exist. -/
theorem deterministic_error_floor (S : I → Set Q) :
    (⨅ T : I → Q, ⨆ i, successorError (S i) (T i)) = ⨆ i, successorRadius (S i) :=
  (iSup_iInf_eq (f := fun i z => successorError (S i) z)).symm

/-- Separated successors force a prediction error of at least half their separation. -/
theorem diameter_le_twice_radius (S : Set Q) :
    Metric.ediam S ≤ 2 * successorRadius S := by
  rw [successorRadius, ENNReal.mul_iInf_of_ne (by norm_num) (by simp)]
  refine le_iInf fun z => Metric.ediam_le fun x hx y hy => ?_
  have h (v : S) : edist v.val z ≤ successorError S z :=
    le_iSup (fun s : S => edist s.val z) v
  calc
    edist x y ≤ edist x z + edist z y := edist_triangle x z y
    _ = edist x z + edist y z := by rw [edist_comm z y]
    _ ≤ successorError S z + successorError S z := add_le_add (h ⟨x, hx⟩) (h ⟨y, hy⟩)
    _ = 2 * successorError S z := (two_mul _).symm

/-- Choosing any admitted successor as the prediction bounds the radius from above. -/
theorem radius_le_diameter {S : Set Q} (hS : S.Nonempty) :
    successorRadius S ≤ Metric.ediam S := by
  obtain ⟨z, hz⟩ := hS
  exact (iInf_le (successorError S) z).trans <|
    iSup_le fun s : S => Metric.edist_le_ediam_of_mem s.property hz

/-- Midpoint prediction matches the endpoint lower bound for an affine hidden drive. -/
theorem affine_hidden_minimax (m k Y : ℝ) (hY : 0 ≤ Y) :
    (∀ y : ℝ, |y| ≤ Y → |(m + k * y) - m| ≤ |k| * Y) ∧
    (∀ z : ℝ, |k| * Y ≤ |(m + k * Y) - z| ∨ |k| * Y ≤ |(m + k * (-Y)) - z|) := by
  constructor
  · intro y hy
    simpa only [add_sub_cancel_left, abs_mul] using
      (mul_le_mul_of_nonneg_left hy (abs_nonneg k))
  · intro z
    have h := abs_sub (m + k * Y - z) (m + k * (-Y) - z)
    have diff : (m + k * Y - z) - (m + k * (-Y) - z) = 2 * (k * Y) := by ring
    rw [diff, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg hY] at h
    by_contra! small
    linarith [small.1, small.2]

/-- Accumulated effect of a unit hidden preparation after a given number of ticks. -/
def weakGain (a b : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => a * weakGain a b n + b ^ n

/-- Retained trajectory driven by the unobserved initial amplitude. -/
def weakRetained (a b η z₀ y₀ : ℝ) : ℕ → ℝ
  | 0 => z₀
  | n + 1 => a * weakRetained a b η z₀ y₀ n + η * (b ^ n * y₀)

theorem weak_retained_affine (a b η z₀ y₀ : ℝ) (n : ℕ) :
    weakRetained a b η z₀ y₀ n = a ^ n * z₀ + (η * weakGain a b n) * y₀ := by
  induction n with
  | zero => simp [weakRetained, weakGain]
  | succ n ih => rw [weakRetained, ih, weakGain, pow_succ]; ring

theorem weak_gain_sum (a b : ℝ) (n : ℕ) :
    weakGain a b n = ∑ j ∈ Finset.range n, a ^ (n - 1 - j) * b ^ j := by
  induction n with
  | zero => simp [weakGain]
  | succ n ih =>
    rw [weakGain, ih, Finset.sum_range_succ, Finset.mul_sum]
    simp only [Nat.add_one_sub_one, Nat.sub_self, pow_zero, one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have he : n - j = (n - 1 - j) + 1 := by omega
    rw [he, pow_succ]
    ring

/-- At every fixed horizon the midpoint of the two extreme trajectories is optimal
among all deterministic predictions initialized from the retained state alone. -/
theorem weak_retained_minimax (a b η z₀ Y : ℝ) (hY : 0 ≤ Y) (n : ℕ) :
    let k := η * weakGain a b n
    (∀ y : ℝ, |y| ≤ Y → |weakRetained a b η z₀ y n - a ^ n * z₀| ≤ |k| * Y) ∧
    (∀ z : ℝ, |k| * Y ≤ |weakRetained a b η z₀ Y n - z| ∨
      |k| * Y ≤ |weakRetained a b η z₀ (-Y) n - z|) := by
  simpa only [weak_retained_affine] using
    affine_hidden_minimax (a ^ n * z₀) (η * weakGain a b n) Y hY

end KTAIT.ApproximateClosure
