/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Kaiti/Codex)
-/
import Mathlib

/-!
# Predictive thermostat contraction (WP0215)

The matched controller uses its stored forecast in a clipped heating policy.
The contraction theorem concerns the actual update, including saturation, in the
max norm on temperature and forecast error. No experiential assignment is assumed.
-/
noncomputable section

namespace KTAIT.PredictiveThermostat

/-- Saturation of a heating command to the closed unit interval. -/
def clip (x : ℝ) : ℝ := max 0 (min 1 x)

private theorem clip_mono : Monotone clip := by
  intro x y h
  exact max_le_max_left 0 (min_le_min_left 1 h)

private theorem clip_nonexpansive (x y : ℝ) : |clip x - clip y| ≤ |x - y| := by
  have h : LipschitzWith 1 clip :=
    (LipschitzWith.id.const_min 1).const_max 0
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using h.dist_le_mul x y

/-- Every clipping secant has slope between zero and one, including saturation. -/
theorem clip_secant (x y : ℝ) :
    ∃ d : ℝ, 0 ≤ d ∧ d ≤ 1 ∧ clip x - clip y = d * (x - y) := by
  by_cases hxy : x = y
  · subst y
    exact ⟨0, by norm_num, by norm_num, by simp⟩
  have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
  refine ⟨(clip x - clip y) / (x - y), ?_, ?_, (div_mul_cancel₀ _ hne).symm⟩
  · rcases lt_or_gt_of_ne hxy with h | h
    · exact div_nonneg_of_nonpos (sub_nonpos.mpr (clip_mono h.le)) (sub_nonpos.mpr h.le)
    · exact div_nonneg (sub_nonneg.mpr (clip_mono h.le)) (sub_nonneg.mpr h.le)
  · have habs := clip_nonexpansive x y
    rcases lt_or_gt_of_ne hxy with h | h
    · have hc : clip x - clip y ≤ 0 := sub_nonpos.mpr (clip_mono h.le)
      rw [abs_of_nonpos hc, abs_of_neg (sub_neg.mpr h)] at habs
      apply (div_le_one_of_neg (sub_neg.mpr h)).mpr
      linarith
    · have hc : 0 ≤ clip x - clip y := sub_nonneg.mpr (clip_mono h.le)
      rw [abs_of_nonneg hc, abs_of_pos (sub_pos.mpr h)] at habs
      exact (div_le_one (sub_pos.mpr h)).mpr habs

/-- Fixed matched physical and controller parameters. -/
structure Parameters where
  r : ℝ
  kappa : ℝ
  gain : ℝ
  effort : ℝ
  ambient : ℝ
  target : ℝ
  r_pos : 0 < r
  r_lt_one : r < 1
  kappa_pos : 0 < kappa
  kappa_lt_one : kappa < 1
  gain_pos : 0 < gain
  effort_nonneg : 0 ≤ effort

abbrev State := ℝ × ℝ

def forecastError (z : State) : ℝ := z.1 - z.2

def estimate (P : Parameters) (z : State) : ℝ := z.2 + P.kappa * (z.1 - z.2)

def baseline (P : Parameters) (z : State) : ℝ :=
  P.ambient + P.r * (estimate P z - P.ambient)

def rawCommand (P : Parameters) (z : State) : ℝ :=
  P.gain * (P.target - baseline P z) / (P.gain ^ 2 + P.effort)

def command (P : Parameters) (z : State) : ℝ := clip (rawCommand P z)

/-- Normal reading and writing: the room evolves and the selected forecast is stored. -/
def step (P : Parameters) (z : State) : State :=
  (P.ambient + P.r * (z.1 - P.ambient) + P.gain * command P z,
   baseline P z + P.gain * command P z)

def eta (P : Parameters) : ℝ := P.r * (1 - P.kappa)
def feedbackGain (P : Parameters) : ℝ := P.gain ^ 2 / (P.gain ^ 2 + P.effort)

/-- The paper's max norm applied to a difference of two states. -/
def stateDist (z w : State) : ℝ :=
  max |z.1 - w.1| |forecastError z - forecastError w|

private theorem denom_pos (P : Parameters) : 0 < P.gain ^ 2 + P.effort := by
  have : 0 < P.gain ^ 2 := sq_pos_of_pos P.gain_pos
  linarith [P.effort_nonneg]

private theorem eta_bounds (P : Parameters) : 0 ≤ eta P ∧ eta P ≤ P.r := by
  unfold eta
  constructor
  · exact mul_nonneg P.r_pos.le (sub_nonneg.mpr P.kappa_lt_one.le)
  · nlinarith [P.r_pos, P.kappa_pos]

private theorem feedback_bounds (P : Parameters) :
    0 ≤ feedbackGain P ∧ feedbackGain P ≤ 1 := by
  unfold feedbackGain
  constructor
  · exact div_nonneg (sq_nonneg _) (denom_pos P).le
  · exact (div_le_one (denom_pos P)).mpr (by linarith [P.effort_nonneg])

/-- The forecast discrepancy contracts even when the heating command saturates. -/
theorem forecast_error_step (P : Parameters) (z : State) :
    forecastError (step P z) = eta P * forecastError z := by
  simp only [forecastError, step, baseline, estimate, eta]
  ring

/-- Synchronization of current temperature and its stored forecast is invariant. -/
theorem synchronized_step (P : Parameters) (z : State) (h : z.1 = z.2) :
    (step P z).1 = (step P z).2 := by
  have := forecast_error_step P z
  simp only [forecastError, h, sub_self, mul_zero] at this
  exact sub_eq_zero.mp this

private theorem temperature_secant (P : Parameters) (z w : State) :
    ∃ d : ℝ, 0 ≤ d ∧ d ≤ 1 ∧
      (step P z).1 - (step P w).1 =
        P.r * (1 - feedbackGain P * d) * (z.1 - w.1) +
        feedbackGain P * d * eta P * (forecastError z - forecastError w) := by
  obtain ⟨d,hd0,hd1,hd⟩ := clip_secant (rawCommand P z) (rawCommand P w)
  refine ⟨d,hd0,hd1,?_⟩
  have hden : P.gain ^ 2 + P.effort ≠ 0 := ne_of_gt (denom_pos P)
  change P.ambient + P.r * (z.1 - P.ambient) + P.gain * command P z -
      (P.ambient + P.r * (w.1 - P.ambient) + P.gain * command P w) = _
  have he : P.gain * command P z - P.gain * command P w =
      P.gain * d * (rawCommand P z - rawCommand P w) := by
    simpa only [command, mul_sub, mul_assoc] using congrArg (P.gain * ·) hd
  rw [show P.ambient + P.r * (z.1 - P.ambient) + P.gain * command P z -
      (P.ambient + P.r * (w.1 - P.ambient) + P.gain * command P w) =
      P.r * (z.1 - w.1) + (P.gain * command P z - P.gain * command P w) by ring, he]
  simp only [rawCommand, baseline, estimate, feedbackGain, eta, forecastError]
  field_simp
  ring

/-- Proposition S9: global contraction of the saturated predictive controller. -/
theorem thermostat_contraction (P : Parameters) (z w : State) :
    stateDist (step P z) (step P w) ≤ P.r * stateDist z w := by
  obtain ⟨d,hd0,hd1,hd⟩ := temperature_secant P z w
  obtain ⟨hK0,hK1⟩ := feedback_bounds P
  obtain ⟨heta0,hetar⟩ := eta_bounds P
  have hKd0 : 0 ≤ feedbackGain P * d := mul_nonneg hK0 hd0
  have hKd1 : feedbackGain P * d ≤ 1 := by nlinarith
  have ha0 : 0 ≤ P.r * (1 - feedbackGain P * d) := mul_nonneg P.r_pos.le (by linarith)
  have hb0 : 0 ≤ feedbackGain P * d * eta P := mul_nonneg hKd0 heta0
  have hrow : P.r * (1 - feedbackGain P * d) + feedbackGain P * d * eta P ≤ P.r := by
    nlinarith [mul_nonneg hKd0 (sub_nonneg.mpr hetar)]
  have hz0 : 0 ≤ stateDist z w := (abs_nonneg _).trans (le_max_left _ _)
  unfold stateDist
  apply max_le
  · rw [hd]
    calc
      _ ≤ |P.r * (1 - feedbackGain P * d) * (z.1 - w.1)| +
          |feedbackGain P * d * eta P * (forecastError z - forecastError w)| := abs_add_le _ _
      _ = P.r * (1 - feedbackGain P * d) * |z.1 - w.1| +
          feedbackGain P * d * eta P * |forecastError z - forecastError w| := by
        rw [abs_mul, abs_of_nonneg ha0, abs_mul, abs_of_nonneg hb0]
      _ ≤ P.r * (1 - feedbackGain P * d) * stateDist z w +
          feedbackGain P * d * eta P * stateDist z w := by
        exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha0)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hb0)
      _ = (P.r * (1 - feedbackGain P * d) + feedbackGain P * d * eta P) * stateDist z w := by ring
      _ ≤ P.r * stateDist z w := mul_le_mul_of_nonneg_right hrow hz0
  · rw [forecast_error_step, forecast_error_step, ← mul_sub, abs_mul, abs_of_nonneg heta0]
    exact (mul_le_mul_of_nonneg_left (le_max_right _ _) heta0).trans
      (mul_le_mul_of_nonneg_right hetar hz0)


private theorem abs_diff_triangle (a b c : ℝ) : |a - c| ≤ |a - b| + |b - c| := by
  calc
    |a - c| = |(a - b) + (b - c)| := by congr 1; ring
    _ ≤ |a - b| + |b - c| := abs_add_le _ _

/-- The coordinate max distance satisfies the triangle inequality. -/
theorem stateDist_triangle (z w v : State) :
    stateDist z v ≤ stateDist z w + stateDist w v := by
  apply max_le
  · exact (abs_diff_triangle z.1 w.1 v.1).trans
      (add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact (abs_diff_triangle (forecastError z) (forecastError w) (forecastError v)).trans
      (add_le_add (le_max_right _ _) (le_max_right _ _))

/-- A scalar one-step error recurrence gives the closed geometric finite-horizon bound. -/
theorem error_recurrence_bound (r eps : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (E : ℕ → ℝ) (hstep : ∀ n, E (n + 1) ≤ r * E n + eps) (n : ℕ) :
    E n ≤ r ^ n * E 0 + eps * (1 - r ^ n) / (1 - r) := by
  have hden : 1 - r ≠ 0 := ne_of_gt (sub_pos.mpr hr1)
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      E (n + 1) ≤ r * E n + eps := hstep n
      _ ≤ r * (r ^ n * E 0 + eps * (1 - r ^ n) / (1 - r)) + eps :=
        add_le_add (mul_le_mul_of_nonneg_left ih hr) (le_refl eps)
      _ = r ^ (n + 1) * E 0 + eps * (1 - r ^ (n + 1)) / (1 - r) := by
        rw [pow_succ]
        field_simp
        ring

/-- The paper's perturbation bound for a nominal and a per-step approximate trajectory. -/
theorem thermostat_perturbation_bound (P : Parameters)
    (nominal approximate : ℕ → State) (eps : ℝ)
    (hnominal : ∀ n, nominal (n + 1) = step P (nominal n))
    (herror : ∀ n, stateDist (approximate (n + 1)) (step P (approximate n)) ≤ eps)
    (n : ℕ) :
    stateDist (approximate n) (nominal n) ≤
      P.r ^ n * stateDist (approximate 0) (nominal 0) + eps * (1 - P.r ^ n) / (1 - P.r) := by
  refine error_recurrence_bound P.r eps P.r_pos.le P.r_lt_one
    (fun k => stateDist (approximate k) (nominal k)) ?_ n
  intro k
  calc
    stateDist (approximate (k + 1)) (nominal (k + 1)) ≤
        stateDist (approximate (k + 1)) (step P (approximate k)) +
        stateDist (step P (approximate k)) (nominal (k + 1)) := stateDist_triangle _ _ _
    _ ≤ eps + P.r * stateDist (approximate k) (nominal k) := by
      rw [hnominal k]
      exact add_le_add (herror k) (thermostat_contraction P _ _)
    _ = P.r * stateDist (approximate k) (nominal k) + eps := by ring

/-- The discrepancy norm of an additive perturbation equals the distance it produces. -/
theorem additive_error_distance (z e : State) :
    stateDist (z + e) z = max |e.1| |e.1 - e.2| := by
  simp only [stateDist, forecastError, Prod.fst_add, Prod.snd_add]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-- Specialization to the additive state errors in the manuscript. -/
theorem thermostat_additive_perturbation_bound (P : Parameters)
    (nominal approximate errors : ℕ → State) (eps : ℝ)
    (hnominal : ∀ n, nominal (n + 1) = step P (nominal n))
    (happroximate : ∀ n, approximate (n + 1) = step P (approximate n) + errors n)
    (herror : ∀ n, max |(errors n).1| |(errors n).1 - (errors n).2| ≤ eps)
    (n : ℕ) :
    stateDist (approximate n) (nominal n) ≤
      P.r ^ n * stateDist (approximate 0) (nominal 0) + eps * (1 - P.r ^ n) / (1 - P.r) := by
  apply thermostat_perturbation_bound P nominal approximate eps hnominal
  intro k
  rw [happroximate k, additive_error_distance]
  exact herror k

/-- The affine recoding of the stored forecast used in the worked example. -/
def recode (z : State) : State := (z.1, 2 * z.2 + 7)
def decode (z : State) : State := (z.1, (z.2 - 7) / 2)

theorem decode_recode (z : State) : decode (recode z) = z := by
  apply Prod.ext
  · rfl
  · dsimp [decode, recode]
    ring

/-- Transporting every update through the declared decoder gives exact conjugacy.
This applies separately to normal and gated updates. -/
theorem recoding_conjugacy (f : State → State) (z : State) :
    recode (f (decode (recode z))) = recode (f z) := by
  rw [decode_recode]

/-- Forecast-error balance with sensor error, gain mismatch, and plant disturbance. -/
theorem forecast_error_mismatch (P : Parameters) (z : State)
    (sensorError modeledGain disturbance action : ℝ) :
    (P.ambient + P.r * (z.1 - P.ambient) + P.gain * action + disturbance) -
      (P.ambient + P.r * (z.2 + P.kappa * (z.1 + sensorError - z.2) - P.ambient) +
        modeledGain * action) =
      eta P * forecastError z - P.r * P.kappa * sensorError +
        (P.gain - modeledGain) * action + disturbance := by
  simp only [eta, forecastError]
  ring


/-- Clipping always gives an admissible heating command. -/
theorem clip_bounds (x : ℝ) : 0 ≤ clip x ∧ clip x ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

private theorem clip_projection (x a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    0 ≤ (clip x - x) * (a - clip x) := by
  by_cases hx0 : x ≤ 0
  · have hc : clip x = 0 := by simp [clip, min_eq_right (show x ≤ 1 by linarith), hx0]
    rw [hc]
    exact mul_nonneg (by linarith) (by linarith)
  · have hx0' : 0 ≤ x := le_of_lt (lt_of_not_ge hx0)
    by_cases hx1 : x ≤ 1
    · have hc : clip x = x := by simp [clip, min_eq_right hx1, hx0']
      simp [hc]
    · have hc : clip x = 1 := by simp [clip, min_eq_left (le_of_lt (lt_of_not_ge hx1))]
      rw [hc]
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)

/-- The objective evaluated on an action at the current modeled state. -/
def objective (P : Parameters) (z : State) (a : ℝ) : ℝ :=
  -((P.target - (baseline P z + P.gain * a)) ^ 2 + P.effort * a ^ 2) / 2

private theorem objective_gap (P : Parameters) (z : State) (a : ℝ) :
    objective P z (command P z) - objective P z a =
      (P.gain ^ 2 + P.effort) / 2 * (a - command P z) ^ 2 +
      (P.gain ^ 2 + P.effort) *
        ((command P z - rawCommand P z) * (a - command P z)) := by
  have hden : P.gain ^ 2 + P.effort ≠ 0 := ne_of_gt (denom_pos P)
  unfold objective rawCommand
  field_simp
  ring

/-- The clipped analytic policy is the unique maximizer on the admitted action interval. -/
theorem command_unique_maximizer (P : Parameters) (z : State) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    objective P z a ≤ objective P z (command P z) ∧
      (objective P z a = objective P z (command P z) ↔ a = command P z) := by
  have hproj := clip_projection (rawCommand P z) a ha0 ha1
  change 0 ≤ (command P z - rawCommand P z) * (a - command P z) at hproj
  have hp := mul_nonneg (denom_pos P).le hproj
  have hs := mul_nonneg (half_pos (denom_pos P)).le (sq_nonneg (a - command P z))
  have hgap := objective_gap P z a
  constructor
  · linarith
  · constructor
    · intro he
      by_contra hne
      have hspos : 0 < (P.gain ^ 2 + P.effort) / 2 * (a - command P z) ^ 2 :=
        mul_pos (half_pos (denom_pos P)) (sq_pos_iff.mpr (sub_ne_zero.mpr hne))
      linarith
    · intro he
      rw [he]

/-- Boolean gates for reading, writing, and outward access. -/
structure Gates where
  read : Bool
  write : Bool
  outward : Bool

def gatedEstimate (P : Parameters) (gates : Gates) (z : State) : ℝ :=
  if gates.read then estimate P z else z.1

def gatedBaseline (P : Parameters) (gates : Gates) (z : State) : ℝ :=
  P.ambient + P.r * (gatedEstimate P gates z - P.ambient)

def gatedCommand (P : Parameters) (gates : Gates) (z : State) : ℝ :=
  clip (P.gain * (P.target - gatedBaseline P gates z) / (P.gain ^ 2 + P.effort))

/-- Reading may be bypassed and writing may hold the previous record. -/
def gatedStep (P : Parameters) (gates : Gates) (z : State) : State :=
  (P.ambient + P.r * (z.1 - P.ambient) + P.gain * gatedCommand P gates z,
   if gates.write then gatedBaseline P gates z + P.gain * gatedCommand P gates z else z.2)

/-- Outward access returns the old stored forecast and leaves the state update unchanged. -/
def outwardRead (gates : Gates) (z : State) : Option ℝ :=
  if gates.outward then some z.2 else none

theorem normal_gates_step (P : Parameters) (z : State) (b : Bool) :
    gatedStep P ⟨true, true, b⟩ z = step P z := by
  simp [gatedStep, gatedBaseline, gatedEstimate, gatedCommand, step, command, rawCommand, baseline]

theorem outward_gate_independence (P : Parameters) (s w b b' : Bool) (z : State) :
    gatedStep P ⟨s, w, b⟩ z = gatedStep P ⟨s, w, b'⟩ z := rfl

/-- Upper temperature of the invariant state square. -/
def upperTemperature (P : Parameters) : ℝ := P.ambient + P.gain / (1 - P.r)

def InSquare (P : Parameters) (z : State) : Prop :=
  z.1 ∈ Set.Icc P.ambient (upperTemperature P) ∧
  z.2 ∈ Set.Icc P.ambient (upperTemperature P)

private theorem estimate_in_interval (P : Parameters) (z : State) (h : InSquare P z) :
    estimate P z ∈ Set.Icc P.ambient (upperTemperature P) := by
  obtain ⟨⟨hT0, hT1⟩, ⟨hp0, hp1⟩⟩ := h
  have hk : 0 ≤ 1 - P.kappa := sub_nonneg.mpr P.kappa_lt_one.le
  constructor
  · have h1 := mul_nonneg P.kappa_pos.le (sub_nonneg.mpr hT0)
    have h2 := mul_nonneg hk (sub_nonneg.mpr hp0)
    unfold estimate
    nlinarith
  · have h1 := mul_nonneg P.kappa_pos.le (sub_nonneg.mpr hT1)
    have h2 := mul_nonneg hk (sub_nonneg.mpr hp1)
    unfold estimate
    nlinarith

private theorem plant_interval (P : Parameters) (x a : ℝ)
    (hx : x ∈ Set.Icc P.ambient (upperTemperature P))
    (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    P.ambient + P.r * (x - P.ambient) + P.gain * a ∈
      Set.Icc P.ambient (upperTemperature P) := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨ha0, ha1⟩ := ha
  constructor
  · have h1 := mul_nonneg P.r_pos.le (sub_nonneg.mpr hx0)
    have h2 := mul_nonneg P.gain_pos.le ha0
    linarith
  · have h1 : P.r * (x - P.ambient) ≤ P.r * (P.gain / (1 - P.r)) := by
      apply mul_le_mul_of_nonneg_left _ P.r_pos.le
      unfold upperTemperature at hx1
      linarith
    have h2 := mul_le_mul_of_nonneg_left ha1 P.gain_pos.le
    have hden : 1 - P.r ≠ 0 := ne_of_gt (sub_pos.mpr P.r_lt_one)
    calc
      _ ≤ P.ambient + P.r * (P.gain / (1 - P.r)) + P.gain := by linarith
      _ = upperTemperature P := by
        unfold upperTemperature
        field_simp
        ring

/-- The declared temperature/forecast square is invariant under all three gates. -/
theorem gated_square_invariant (P : Parameters) (gates : Gates) (z : State)
    (hz : InSquare P z) : InSquare P (gatedStep P gates z) := by
  have ha : gatedCommand P gates z ∈ Set.Icc (0 : ℝ) 1 := clip_bounds _
  have hx : gatedEstimate P gates z ∈ Set.Icc P.ambient (upperTemperature P) := by
    cases hs : gates.read with
    | false => simpa [gatedEstimate, hs] using hz.1
    | true => simpa [gatedEstimate, hs] using estimate_in_interval P z hz
  have hT := plant_interval P z.1 (gatedCommand P gates z) hz.1 ha
  have hp := plant_interval P (gatedEstimate P gates z) (gatedCommand P gates z) hx ha
  constructor
  · exact hT
  · cases hw : gates.write with
    | false => simpa [gatedStep, hw] using hz.2
    | true => simpa [gatedStep, gatedBaseline, hw] using hp

/-- The affine recoding has a two-sided inverse. -/
theorem recode_decode (z : State) : recode (decode z) = z := by
  apply Prod.ext
  · rfl
  · dsimp [decode, recode]
    ring

/-- A forecast intervention transports to twice the increment in recoded coordinates. -/
theorem recoding_record_increment (z : State) (q : ℝ) :
    recode (z.1, z.2 + q) = ((recode z).1, (recode z).2 + 2 * q) := by
  apply Prod.ext
  · rfl
  · dsimp [recode]
    ring

/-- Every normal trajectory preserves initial temperature/forecast synchronization. -/
theorem synchronized_trajectory (P : Parameters) (z : ℕ → State)
    (hstep : ∀ n, z (n + 1) = step P (z n)) (hzero : (z 0).1 = (z 0).2) :
    ∀ n, (z n).1 = (z n).2 := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    rw [hstep n]
    exact synchronized_step P (z n) ih

/-- Exact rational parameters of the manuscript's intervention example. -/
def workedParameters : Parameters where
  r := 1 / 2
  kappa := 1 / 2
  gain := 1
  effort := 1
  ambient := 20
  target := 22
  r_pos := by norm_num
  r_lt_one := by norm_num
  kappa_pos := by norm_num
  kappa_lt_one := by norm_num
  gain_pos := by norm_num
  effort_nonneg := by norm_num

/-- Changing only the stored forecast changes the selected command. -/
theorem numerical_record_commands :
    command workedParameters (21, 20) = 7 / 8 ∧
    command workedParameters (21, 22) = 5 / 8 := by
  norm_num [command, rawCommand, baseline, estimate, clip, workedParameters]

/-- The two normal-update contrasts in the paper, stated with exact rationals. -/
theorem numerical_record_states :
    step workedParameters (21, 20) = (171 / 8, 169 / 8) ∧
    step workedParameters (21, 22) = (169 / 8, 171 / 8) := by
  norm_num [step, command, rawCommand, baseline, estimate, clip, workedParameters]

/-- Temperature alone cannot determine the successor throughout this state domain. -/
theorem temperature_projection_not_closed :
    ¬ ∃ f : ℝ → ℝ, ∀ z : State, (step workedParameters z).1 = f z.1 := by
  rintro ⟨f, hf⟩
  have h0 := hf (21, 20)
  have h1 := hf (21, 22)
  rw [numerical_record_states.1] at h0
  rw [numerical_record_states.2] at h1
  dsimp only at h0 h1
  linarith

/-- Bypassing the old forecast makes both displayed interventions yield the same update. -/
theorem numerical_read_bypass :
    gatedCommand workedParameters ⟨false, true, true⟩ (21, 20) = 3 / 4 ∧
    gatedCommand workedParameters ⟨false, true, true⟩ (21, 22) = 3 / 4 ∧
    gatedStep workedParameters ⟨false, true, true⟩ (21, 20) = (85 / 4, 85 / 4) ∧
    gatedStep workedParameters ⟨false, true, true⟩ (21, 22) = (85 / 4, 85 / 4) := by
  norm_num [gatedStep, gatedCommand, gatedBaseline, gatedEstimate, clip, workedParameters]

/-- Blocking the first write changes the second temperature after normal reading resumes. -/
theorem numerical_write_block :
    (step workedParameters
      (gatedStep workedParameters ⟨true, false, true⟩ (21, 20))).1 = 1377 / 64 ∧
    (step workedParameters (step workedParameters (21, 20))).1 = 171 / 8 := by
  norm_num [step, command, rawCommand, baseline, estimate,
    gatedStep, gatedCommand, gatedBaseline, gatedEstimate, clip, workedParameters]

end KTAIT.PredictiveThermostat
