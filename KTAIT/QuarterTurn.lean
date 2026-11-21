/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude, Codex)
-/
import Mathlib
import KTAIT.SemigroupTracking

/-!
# The quarter-turn group under tracking error below a quarter revolution

`KTAIT.ApproximateEmulation.approximate_emulation_factor` recovers the whole marked
transition quotient of a target when the emulator's error stays below half the separation
of the target's states. For four headings a quarter revolution apart that bound is an eighth
of a revolution. The rotation group alone survives a larger error.

Let an emulator have an input that the world answers with a quarter turn, and let its heading
reading stay strictly within a quarter revolution of the true heading after every number of
repetitions of that input. Then two repetition counts that reach the same emulator state are
congruent modulo four (`cast_eq_of_iterate_eq`); every recurrence period is a multiple of four
(`quarter_turn_period`); the states reached by repeated turns map onto the four-heading
rotation, compatibly with the turn (`quarter_turn_divides`); and a finite emulator contains a
group mapping onto the cyclic group of order four (`quarter_turn_lifts_group`).

The strict inequality is needed. With error equal to a quarter revolution at every step, a
two-state emulator suffices and its turn has period two (`quarter_turn_sharp`).

The hypothesis concerns repeated turns only. Other admitted inputs, such as observations that
overwrite the record, are allowed in the emulator and are not constrained here.
-/

namespace KTAIT.QuarterTurn

open Function
open KTAIT.ComputationCores (run)
open KTAIT.OperationalAlgebra (generated)
open KTAIT.SemigroupCore (Divides Corner)
open KTAIT.SemigroupTracking (division_lifts_group)

variable {X B Y : Type*} {P : ℝ}

/-- A quarter of the period, as a point of the circle. -/
noncomputable def quarter (P : ℝ) : AddCircle P := ((P / 4 : ℝ) : AddCircle P)

/-- A number of quarter turns congruent to two modulo four is a half turn. -/
theorem nsmul_quarter_of_mod_four_eq_two {q : ℕ} (hq : q % 4 = 2) :
    q • quarter P = ((P / 2 : ℝ) : AddCircle P) := by
  obtain ⟨k, rfl⟩ : ∃ k, q = 4 * k + 2 := ⟨q / 4, by omega⟩
  unfold quarter
  rw [← AddCircle.coe_nsmul]
  have h : ((4 * k + 2) • (P / 4) : ℝ) = P / 2 + k • P := by
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [h, AddCircle.coe_add, AddCircle.coe_nsmul, AddCircle.coe_period, nsmul_zero, add_zero]

section Period

variable [hP : Fact (0 < P)] (step : X → X) (x₀ : X) (read : X → AddCircle P)
  (θ₀ : AddCircle P)

/-- If the reading stays strictly within a quarter revolution of the true heading under
repeated quarter turns, every recurrence period of the emulator is a multiple of four.
Otherwise one or two periods would return the emulator to the same state, and the same
reading, while the true heading had reversed. -/
theorem quarter_turn_period
    (hfit : ∀ n : ℕ, dist (θ₀ + n • quarter P) (read (step^[n] x₀)) < P / 4)
    {m p : ℕ} (hper : step^[p] (step^[m] x₀) = step^[m] x₀) : 4 ∣ p := by
  by_contra hdiv
  obtain ⟨q, hq, hqper⟩ : ∃ q, q % 4 = 2 ∧ step^[q] (step^[m] x₀) = step^[m] x₀ := by
    have hp4 : p % 4 = 1 ∨ p % 4 = 2 ∨ p % 4 = 3 := by omega
    rcases hp4 with h | h | h
    · refine ⟨p + p, by omega, ?_⟩
      rw [Function.iterate_add_apply, hper, hper]
    · exact ⟨p, h, hper⟩
    · refine ⟨p + p, by omega, ?_⟩
      rw [Function.iterate_add_apply, hper, hper]
  have h1 := hfit m
  have h2 := hfit (q + m)
  rw [Function.iterate_add_apply, hqper, add_nsmul, nsmul_quarter_of_mod_four_eq_two hq] at h2
  let half : AddCircle P := ((P / 2 : ℝ) : AddCircle P)
  let a : AddCircle P := θ₀ + m • quarter P
  let y : AddCircle P := read (step^[m] x₀)
  have h2' : dist (a + half) y < P / 4 := by
    have hre : θ₀ + (half + m • quarter P) = a + half := by
      simp only [a]
      abel
    simpa only [half, hre] using h2
  have hhalf : dist a (a + half) = P / 2 := by
    rw [dist_eq_norm]
    have hsub : a - (a + half) = -half := by abel
    rw [hsub, norm_neg]
    simpa only [half, abs_of_pos hP.out] using AddCircle.norm_half_period_eq P
  have htri : dist a (a + half) ≤ dist a y + dist y (a + half) := dist_triangle _ _ _
  rw [dist_comm y (a + half)] at htri
  have h1' : dist a y < P / 4 := h1
  linarith

/-- Two numbers of quarter turns that reach the same emulator state are congruent modulo
four, so the state determines the true heading. -/
theorem cast_eq_of_iterate_eq
    (hfit : ∀ n : ℕ, dist (θ₀ + n • quarter P) (read (step^[n] x₀)) < P / 4)
    {i j : ℕ} (h : step^[i] x₀ = step^[j] x₀) : (i : ZMod 4) = (j : ZMod 4) := by
  wlog hij : i ≤ j generalizing i j
  · exact (this h.symm (by omega)).symm
  have hper : step^[j - i] (step^[i] x₀) = step^[i] x₀ := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij]
    exact h.symm
  obtain ⟨t, ht⟩ := quarter_turn_period step x₀ read θ₀ hfit hper
  have hj : j = i + 4 * t := by omega
  rw [hj, Nat.cast_add, Nat.cast_mul]
  have h4 : ((4 : ℕ) : ZMod 4) = 0 := ZMod.natCast_self 4
  rw [h4, zero_mul, add_zero]

/-- A finite emulator has a recurrent state under repeated turns, and its period there is a
positive multiple of four. -/
theorem finite_quarter_turn_cycle [Finite X]
    (hfit : ∀ n : ℕ, dist (θ₀ + n • quarter P) (read (step^[n] x₀)) < P / 4) :
    ∃ m p : ℕ, 0 < p ∧ step^[p] (step^[m] x₀) = step^[m] x₀ ∧ 4 ∣ p := by
  classical
  obtain ⟨m, n, hmn, heq⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem
    (f := fun j : ℕ => step^[j] x₀) (fun _ => Set.mem_univ _)
  have hper : step^[n - m] (step^[m] x₀) = step^[m] x₀ := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hmn.le]
    exact heq.symm
  exact ⟨m, n - m, by omega, hper, quarter_turn_period step x₀ read θ₀ hfit hper⟩

end Period

section Group

/-- The four-heading rotation system: one input, a quarter turn. -/
def fourTurn : Unit → ZMod 4 → ZMod 4 := fun _ z => z + 1

theorem run_fourTurn (z : ZMod 4) (n : ℕ) :
    run fourTurn z (List.replicate n ()) = z + n := by
  induction n generalizing z with
  | zero => simp [run]
  | succ n ih =>
    have hcons : run fourTurn z (List.replicate (n + 1) ()) =
        run fourTurn (z + 1) (List.replicate n ()) := by
      simp [run, List.replicate_succ, fourTurn]
    rw [hcons, ih]
    push_cast
    ring

/-- Rotation by `z` quarter turns, as an element of the generated monoid. -/
def rotation (z : ZMod 4) : generated fourTurn :=
  ⟨fun x => x + z, ⟨List.replicate z.val (), by
    funext x
    rw [run_fourTurn, ZMod.natCast_zmod_val]⟩⟩

/-- The cyclic group of order four inside the monoid generated by the quarter turn. -/
def rotationHom : Multiplicative (ZMod 4) →ₙ* generated fourTurn where
  toFun z := rotation (Multiplicative.toAdd z)
  map_mul' z w := by
    apply Subtype.ext
    funext x
    change x + (Multiplicative.toAdd z + Multiplicative.toAdd w) =
      (x + Multiplicative.toAdd w) + Multiplicative.toAdd z
    abel

theorem rotationHom_injective : Injective rotationHom := by
  intro z w h
  have h0 := congrFun (congrArg Subtype.val h) (0 : ZMod 4)
  change (0 : ZMod 4) + Multiplicative.toAdd z = 0 + Multiplicative.toAdd w at h0
  simpa using h0

variable [hP : Fact (0 < P)] (T : B → Y → Y) (b : B) (y₀ : Y) (read : Y → AddCircle P)
  (θ₀ : AddCircle P)

/-- The emulator states reached by repeated turns map onto the four-heading rotation, and
the map sends the emulator's turn to the quarter turn. Other inputs of the emulator are
not used. -/
noncomputable def quarter_turn_divides
    (hfit : ∀ n : ℕ, dist (θ₀ + n • quarter P) (read ((T b)^[n] y₀)) < P / 4) :
    Divides fourTurn T where
  dom := Set.range (fun n : ℕ => (T b)^[n] y₀)
  ρ y := ((Classical.choose y.property : ℕ) : ZMod 4)
  word _ := [b]
  closed := by
    rintro _ ⟨_, n, rfl⟩
    exact ⟨n + 1, by simp [run, Function.iterate_succ_apply']⟩
  onto := by
    intro z
    refine ⟨⟨(T b)^[z.val] y₀, z.val, rfl⟩, ?_⟩
    have hs := Classical.choose_spec
      (show (T b)^[z.val] y₀ ∈ Set.range (fun n : ℕ => (T b)^[n] y₀) from ⟨z.val, rfl⟩)
    have hc := cast_eq_of_iterate_eq (T b) y₀ read θ₀ hfit hs
    change ((Classical.choose _ : ℕ) : ZMod 4) = z
    rw [hc, ZMod.natCast_zmod_val]
  comm := by
    rintro _ ⟨y, hy⟩
    have hmem : run T y [b] ∈ Set.range (fun n : ℕ => (T b)^[n] y₀) := by
      obtain ⟨n, rfl⟩ := hy
      exact ⟨n + 1, by simp [run, Function.iterate_succ_apply']⟩
    have hs := Classical.choose_spec hy
    have hs' := Classical.choose_spec hmem
    have hstep : (T b)^[Classical.choose hmem] y₀ = (T b)^[Classical.choose hy + 1] y₀ := by
      simp only at hs hs'
      rw [hs', Function.iterate_succ_apply', hs]
      simp [run]
    have hc := cast_eq_of_iterate_eq (T b) y₀ read θ₀ hfit hstep
    change ((Classical.choose hmem : ℕ) : ZMod 4) = ((Classical.choose hy : ℕ) : ZMod 4) + 1
    rw [hc]
    push_cast
    rfl

/-- A finite emulator whose heading error stays strictly below a quarter revolution under
repeated quarter turns contains a group that maps onto the cyclic group of order four. The
group lies in the monoid generated by all the emulator's admitted inputs. -/
theorem quarter_turn_lifts_group [Finite Y]
    (hfit : ∀ n : ℕ, dist (θ₀ + n • quarter P) (read ((T b)^[n] y₀)) < P / 4) :
    ∃ e : {m : generated T // IsIdempotentElem m},
      ∃ H : Subgroup ((Corner e)ˣ), ∃ ψ : H →* Multiplicative (ZMod 4), Surjective ψ :=
  division_lifts_group (quarter_turn_divides T b y₀ read θ₀ hfit) rotationHom
    rotationHom_injective

end Group

section Sharpness

variable [hP : Fact (0 < P)]

/-- The norm of a quarter of the period. -/
theorem norm_quarter : ‖quarter P‖ = P / 4 := by
  have hpos := hP.out
  unfold quarter
  have hle : |P / 4| ≤ |P| / 2 := by
    rw [abs_of_pos (by positivity), abs_of_pos hpos]
    linarith
  rw [(AddCircle.norm_coe_eq_abs_iff P hpos.ne').mpr hle, abs_of_pos (by positivity)]

omit hP in
/-- Four quarter turns are a full turn. -/
theorem four_nsmul_quarter : 4 • quarter P = 0 := by
  unfold quarter
  rw [← AddCircle.coe_nsmul]
  have h : ((4 : ℕ) • (P / 4) : ℝ) = P := by
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [h, AddCircle.coe_period]

/-- The reading of the two-state emulator: the state that stands for north or south reads
east, and the state that stands for east or west reads north. -/
noncomputable def parityRead (P : ℝ) : Bool → AddCircle P
  | false => quarter P
  | true => 0

/-- The strict inequality cannot be weakened. Two states that record the parity of the
number of quarter turns track the heading with error equal to a quarter revolution at every
step, and the turn has period two. -/
theorem quarter_turn_sharp :
    (∀ n : ℕ, dist ((0 : AddCircle P) + n • quarter P) (parityRead P (not^[n] false)) ≤ P / 4)
      ∧ not^[2] false = false ∧ ¬ 4 ∣ 2 := by
  refine ⟨?_, rfl, by decide⟩
  intro n
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 4 ∧ n = 4 * k + r :=
    ⟨n / 4, n % 4, Nat.mod_lt _ (by decide), by omega⟩
  have hsmul : (4 * k + r) • quarter P = r • quarter P := by
    rw [add_nsmul, mul_nsmul, four_nsmul_quarter, nsmul_zero, zero_add]
  have hiter : not^[4 * k + r] false = not^[r] false := by
    rw [add_comm, Function.iterate_add_apply]
    have hk : not^[4 * k] false = false := by
      have he : Even (4 * k) := ⟨2 * k, by ring⟩
      rw [Bool.involutive_not.iterate_even he]
      rfl
    rw [hk]
  rw [hsmul, hiter, zero_add, dist_eq_norm]
  interval_cases r
  · simp only [zero_nsmul, Function.iterate_zero, id_eq, parityRead, zero_sub, norm_neg]
    exact norm_quarter.le
  · simp only [one_nsmul, Function.iterate_one, Bool.not_false, parityRead, sub_zero]
    exact norm_quarter.le
  · have h2 : not^[2] false = false := rfl
    have hq : (2 • quarter P : AddCircle P) - quarter P = quarter P := by
      rw [two_nsmul]
      abel
    rw [h2]
    simp only [parityRead]
    rw [hq]
    exact norm_quarter.le
  · have h3 : not^[3] false = true := rfl
    have hq : (3 • quarter P : AddCircle P) = -quarter P := by
      have h4 := four_nsmul_quarter (P := P)
      have : (4 • quarter P : AddCircle P) = 3 • quarter P + quarter P := by
        rw [succ_nsmul]
      rw [this] at h4
      exact eq_neg_of_add_eq_zero_left h4
    rw [h3]
    simp only [parityRead, sub_zero]
    rw [hq, norm_neg]
    exact norm_quarter.le

end Sharpness

end KTAIT.QuarterTurn
