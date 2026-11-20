/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import Mathlib

/-! # Uniform error for a finite deterministic tracker of an irrational circle rotation -/

namespace KTAIT.CircleTracking

/-- Under a repeated input a finite emulator has a recurrent phase. If the world's
rotation has infinite order, the true headings at that phase are dense on the circle.
Every uniform tracking error bound therefore reaches at least half a revolution. -/
theorem finite_rotation_error {X : Type*} [Finite X] {P : ℝ} [hP : Fact (0 < P)]
    (step : X → X) (x₀ : X) (read : X → AddCircle P) (θ₀ α : AddCircle P)
    (hirr : addOrderOf α = 0) {ε : ℝ}
    (hfit : ∀ n : ℕ, dist (θ₀ + n • α) (read (step^[n] x₀)) ≤ ε) : P / 2 ≤ ε := by
  classical
  obtain ⟨m, n, hmn, heq⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem
    (f := fun j : ℕ => step^[j] x₀) (fun _ => Set.mem_univ _)
  let p := n - m
  have hp : p ≠ 0 := by dsimp [p]; omega
  have hpm : p + m = n := by dsimp [p]; omega
  have period : Function.IsPeriodicPt step p (step^[m] x₀) := by
    change step^[p] (step^[m] x₀) = step^[m] x₀
    rw [← Function.iterate_add_apply, hpm]
    exact heq.symm
  have hord : addOrderOf (p • α) = 0 := by
    by_contra hn
    have hz := addOrderOf_nsmul_eq_zero (p • α)
    rw [← mul_nsmul] at hz
    have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz
    rw [hirr, Nat.zero_dvd] at hd
    exact Nat.mul_ne_zero hp hn hd
  have dense : DenseRange (fun j : ℕ => j • (p • α)) :=
    denseRange_zsmul_iff_nsmul.mp (AddCircle.denseRange_zsmul_iff.mpr hord)
  let offset := θ₀ + m • α
  let y := read (step^[m] x₀)
  have bound (z : AddCircle P) : dist (offset + z) y ≤ ε := by
    refine dense.induction_on (p := fun w : AddCircle P => dist (offset + w) y ≤ ε) z ?_ ?_
    · exact isClosed_le ((continuous_const.add continuous_id).dist continuous_const)
        continuous_const
    intro j
    have hj := hfit (p * j + m)
    have hx : step^[p * j + m] x₀ = step^[m] x₀ := by
      rw [Function.iterate_add_apply]
      exact (period.mul_const j).eq
    rw [hx, add_nsmul, mul_nsmul] at hj
    simpa only [offset, y, add_assoc, add_comm, add_left_comm] using hj
  let half : AddCircle P := ((P / 2 : ℝ) : AddCircle P)
  have hb := bound (half + y - offset)
  rw [dist_eq_norm] at hb
  have hid : offset + (half + y - offset) - y = half := by abel
  rw [hid] at hb
  simpa only [half, AddCircle.norm_half_period_eq, abs_of_pos hP.out] using hb

/-- The usual angular-velocity statement for a rotation through an irrational
fraction of its period, including an arbitrary initial heading. -/
theorem irrational_rotation_error {X : Type*} [Finite X] {P : ℝ} [Fact (0 < P)]
    (step : X → X) (x₀ : X) (read : X → AddCircle P) (θ₀ : AddCircle P)
    (a : ℝ) (ha : Irrational (a / P)) {ε : ℝ}
    (hfit : ∀ n : ℕ, dist (θ₀ + n • (a : AddCircle P)) (read (step^[n] x₀)) ≤ ε) :
    P / 2 ≤ ε :=
  finite_rotation_error step x₀ read θ₀ a
    (AddCircle.denseRange_zsmul_iff.mp (AddCircle.denseRange_zsmul_coe_iff.mpr ha)) hfit

end KTAIT.CircleTracking
