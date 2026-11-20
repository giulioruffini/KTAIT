/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude, Codex)
-/
import Mathlib
import KTAIT.CanonicalPrediction

/-!
# Approximate emulation with a separation margin

`KTAIT.CanonicalPrediction.prediction_factor` treats exact initialized prediction. Here the
emulator's readings are only required to stay within a tolerance `δ` of the target's after
every finite input word. If reachable target states that are not future-equivalent are
separated by more than `2 * δ` after some continuation, the emulator still factors onto the
target's reachable minimal quotient: histories that reach one emulator state reach one target
class. The factor commutes with every admitted update, its readout stays within `δ`, and the
existing division results give the onto map of update monoids and finite group lifting.

The factor `2` is sharp (`half_separation_sharp`). At a bounded horizon only a lower bound
on the number of emulator states survives (`finite_horizon_memory_bound`). The last section
gives the two-point lower bound behind the fixed-grain prediction floor.

All statements are deterministic and set-level. Readings take values in a pseudometric
space; no finiteness is assumed except where stated.
-/

namespace KTAIT.ApproximateEmulation

open Function
open KTAIT.ComputationCores (run run_intertwines Accessible initialized_intertwiner_unique)
open KTAIT.OperationalAlgebra (futureEquivalence generated)
open KTAIT.IS.MinimalRealization
  (Reachable reached reachStep reachContent project project_eq_iff)
open KTAIT.CanonicalPrediction (Reach start step prediction_reach_accessible)
open KTAIT.SemigroupCore (Divides Corner)
open KTAIT.SemigroupTracking (DivisionCorresponds divisionSubmonoid divisionFactor
  division_factor_surjective division_factor_commutes division_sequence_corresponds
  division_lifts_group)

universe u v w z
variable {A : Type u} {X : Type v} {W : Type w} {O : Type z} [PseudoMetricSpace O]

/-- Execution of a concatenated word continues from the state reached by its prefix. -/
theorem run_concat (F : A → X → X) (x : X) (s r : List A) :
    run F x (s ++ r) = run F (run F x s) r := by
  simp [run, List.foldl_append]

/-- Uniform approximate emulation: after every finite input word from the marked states,
the emulator's reading is within `δ` of the target's reading. -/
def EmulatesWithin (F : A → X → X) (π : X → O) (x₀ : X)
    (T : A → W → W) (o : W → O) (w₀ : W) (δ : ℝ) : Prop :=
  ∀ s : List A, dist (π (run F x₀ s)) (o (run T w₀ s)) ≤ δ

/-- Separation margin: two reachable target states that are not future-equivalent have
readings more than `2 * δ` apart after some common continuation. -/
def SeparatedBeyond (T : A → W → W) (o : W → O) (w₀ : W) (δ : ℝ) : Prop :=
  ∀ s t : List A, ¬ futureEquivalence T o (run T w₀ s) (run T w₀ t) →
    ∃ r : List A, 2 * δ < dist (o (run T w₀ (s ++ r))) (o (run T w₀ (t ++ r)))

section Decoder

variable {F : A → X → X} {π : X → O} {x₀ : X} {T : A → W → W} {o : W → O} {w₀ : W} {δ : ℝ}

/-- Two histories that reach one emulator state give target readings within `2 * δ` after
every common continuation. No separation is assumed. -/
theorem same_state_readings_close (hclose : EmulatesWithin F π x₀ T o w₀ δ)
    {s t : List A} (h : run F x₀ s = run F x₀ t) (r : List A) :
    dist (o (run T w₀ (s ++ r))) (o (run T w₀ (t ++ r))) ≤ 2 * δ := by
  have hF : run F x₀ (s ++ r) = run F x₀ (t ++ r) := by
    rw [run_concat, run_concat, h]
  have h1 := hclose (s ++ r)
  have h2 := hclose (t ++ r)
  rw [hF] at h1
  have htri := dist_triangle_left (o (run T w₀ (s ++ r))) (o (run T w₀ (t ++ r)))
    (π (run F x₀ (t ++ r)))
  linarith

/-- Half-separation decoder, key step: histories that reach the same emulator state reach
future-equivalent target states. -/
theorem same_state_same_class (hclose : EmulatesWithin F π x₀ T o w₀ δ)
    (hsep : SeparatedBeyond T o w₀ δ) {s t : List A} (h : run F x₀ s = run F x₀ t) :
    futureEquivalence T o (run T w₀ s) (run T w₀ t) := by
  by_contra hne
  obtain ⟨r, hr⟩ := hsep s t hne
  exact absurd (same_state_readings_close hclose h r) (not_le.mpr hr)

/-- The decoder sends a reachable emulator state to the target class reached by any history
that reaches it. -/
noncomputable def decoder (F : A → X → X) (x₀ : X) (T : A → W → W) (o : W → O) (w₀ : W)
    (x : Reach F x₀) : Reachable T o w₀ :=
  reached T o w₀ (Classical.choose x.property)

/-- The decoder does not depend on the history chosen. -/
theorem decoder_reached (hclose : EmulatesWithin F π x₀ T o w₀ δ)
    (hsep : SeparatedBeyond T o w₀ δ) (x : Reach F x₀) (s : List A)
    (hs : run F x₀ s = x.val) :
    decoder F x₀ T o w₀ x = reached T o w₀ s := by
  apply Subtype.ext
  change project T o (run T w₀ (Classical.choose x.property)) = project T o (run T w₀ s)
  rw [project_eq_iff]
  exact same_state_same_class hclose hsep ((Classical.choose_spec x.property).trans hs.symm)

omit [PseudoMetricSpace O] in
/-- A target update sends the class reached by `s` to the class reached by `s ++ [a]`. -/
theorem reachStep_reached (T : A → W → W) (o : W → O) (w₀ : W) (a : A) (s : List A) :
    reachStep T o w₀ a (reached T o w₀ s) = reached T o w₀ (s ++ [a]) := by
  apply Subtype.ext
  change project T o (T a (run T w₀ s)) = project T o (run T w₀ (s ++ [a]))
  rw [run_concat]
  rfl

/-- A marked approximate factor is onto the reachable target classes, preserves the marking,
commutes with every admitted update, and keeps the readout within `δ`. -/
def ApproximateFactor (F : A → X → X) (π : X → O) (x₀ : X)
    (T : A → W → W) (o : W → O) (w₀ : W) (δ : ℝ)
    (p : Reach F x₀ → Reachable T o w₀) : Prop :=
  Surjective p ∧ p (start F x₀) = reached T o w₀ [] ∧
    (∀ a x, p (step F x₀ a x) = reachStep T o w₀ a (p x)) ∧
    (∀ x, dist (π x.val) (reachContent T o w₀ (p x)) ≤ δ)

/-- The decoder is an approximate factor. -/
theorem decoder_factor (hclose : EmulatesWithin F π x₀ T o w₀ δ)
    (hsep : SeparatedBeyond T o w₀ δ) :
    ApproximateFactor F π x₀ T o w₀ δ (decoder F x₀ T o w₀) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨s, hs⟩ := q.property
    refine ⟨⟨run F x₀ s, s, rfl⟩, ?_⟩
    rw [decoder_reached hclose hsep _ s rfl]
    exact Subtype.ext hs
  · exact decoder_reached hclose hsep (start F x₀) [] rfl
  · intro a x
    obtain ⟨s, hs⟩ := x.property
    have hstep : run F x₀ (s ++ [a]) = (step F x₀ a x).val := by
      rw [run_concat, hs]
      rfl
    rw [decoder_reached hclose hsep _ (s ++ [a]) hstep, decoder_reached hclose hsep x s hs,
      reachStep_reached]
  · intro x
    obtain ⟨s, hs⟩ := x.property
    rw [decoder_reached hclose hsep x s hs, ← hs]
    exact hclose s

/-- Any map from reachable emulator states to reachable target classes that preserves the
marking and commutes with the updates is the decoder. -/
theorem decoder_unique (hclose : EmulatesWithin F π x₀ T o w₀ δ)
    (hsep : SeparatedBeyond T o w₀ δ) (q : Reach F x₀ → Reachable T o w₀)
    (hstart : q (start F x₀) = reached T o w₀ [])
    (hstep : ∀ a x, q (step F x₀ a x) = reachStep T o w₀ a (q x)) :
    q = decoder F x₀ T o w₀ :=
  initialized_intertwiner_unique (step F x₀) (reachStep T o w₀) (start F x₀)
    (prediction_reach_accessible F x₀) q (decoder F x₀ T o w₀)
    (hstart.trans (decoder_factor hclose hsep).2.1.symm) hstep
    (decoder_factor hclose hsep).2.2.1

/-- **Half-separation theorem.** Uniform emulation within `δ` of a target whose reachable
classes are separated by more than `2 * δ` gives a unique marked factor from the reachable
emulator states onto the target's reachable minimal quotient. Uniqueness holds among maps
that preserve the marking and commute with the updates. -/
theorem approximate_emulation_factor (hclose : EmulatesWithin F π x₀ T o w₀ δ)
    (hsep : SeparatedBeyond T o w₀ δ) :
    ∃! p : Reach F x₀ → Reachable T o w₀, ApproximateFactor F π x₀ T o w₀ δ p := by
  have hd := decoder_factor hclose hsep
  refine ⟨decoder F x₀ T o w₀, hd, ?_⟩
  intro q hq
  exact initialized_intertwiner_unique (step F x₀) (reachStep T o w₀) (start F x₀)
    (prediction_reach_accessible F x₀) q (decoder F x₀ T o w₀)
    (hq.2.1.trans hd.2.1.symm) hq.2.2.1 hd.2.2.1

/-- The target's reachable minimal action divides the emulator through single inputs. -/
noncomputable def approximate_emulation_divides (hclose : EmulatesWithin F π x₀ T o w₀ δ)
    (hsep : SeparatedBeyond T o w₀ δ) : Divides (reachStep T o w₀) F where
  dom := {x | ∃ s, run F x₀ s = x}
  ρ := decoder F x₀ T o w₀
  word := fun a => [a]
  closed := fun a x => (step F x₀ a x).property
  onto := (decoder_factor hclose hsep).1
  comm := (decoder_factor hclose hsep).2.2.1

/-- The emulator's update monoid, restricted to the updates that respect the decoder, maps
onto the update monoid of the target's reachable minimal quotient. -/
theorem approximate_emulation_monoid_onto (hclose : EmulatesWithin F π x₀ T o w₀ δ)
    (hsep : SeparatedBeyond T o w₀ δ) :
    Surjective (divisionFactor (approximate_emulation_divides hclose hsep)) :=
  division_factor_surjective _

/-- With single-input implementations, every generated emulator update respects the
decoder. -/
theorem approximate_emulation_submonoid_top (hclose : EmulatesWithin F π x₀ T o w₀ δ)
    (hsep : SeparatedBeyond T o w₀ δ) :
    divisionSubmonoid (approximate_emulation_divides hclose hsep) = ⊤ := by
  rw [eq_top_iff]
  intro m _
  obtain ⟨w, hw⟩ := m.property
  have hflat : w.flatMap (fun a : A => [a]) = w := by
    induction w with
    | nil => rfl
    | cons a w ih => simp
  refine ⟨⟨fun q => run (reachStep T o w₀) q w, w, rfl⟩, ?_⟩
  have h := division_sequence_corresponds (approximate_emulation_divides hclose hsep) w
  have hm : m = ⟨fun y => run F y
      (w.flatMap (approximate_emulation_divides hclose hsep).word), _, rfl⟩ := by
    apply Subtype.ext
    rw [hw]
    funext y
    change run F y w = run F y (w.flatMap fun a : A => [a])
    rw [hflat]
  rw [hm]
  exact h

/-- **Monoid form of the half-separation theorem.** The emulator's update monoid maps onto
the update monoid of the target's reachable minimal quotient, and the map is realized by the
decoder on reachable emulator states. -/
theorem approximate_emulation_update_monoid_onto
    (hclose : EmulatesWithin F π x₀ T o w₀ δ) (hsep : SeparatedBeyond T o w₀ δ) :
    ∃ φ : generated F →* generated (reachStep T o w₀), Surjective φ ∧
      ∀ m : generated F,
        DivisionCorresponds (approximate_emulation_divides hclose hsep) m (φ m) := by
  let d := approximate_emulation_divides hclose hsep
  have htop : divisionSubmonoid d = ⊤ := approximate_emulation_submonoid_top hclose hsep
  let e : generated F ≃* divisionSubmonoid d :=
    Submonoid.topEquiv.symm.trans (MulEquiv.submonoidCongr htop.symm)
  refine ⟨(divisionFactor d).comp e.toMonoidHom, ?_, ?_⟩
  · exact (division_factor_surjective d).comp e.surjective
  · intro m
    have h := division_factor_commutes d (e m)
    have hval : (e m).val = m := rfl
    rw [hval] at h
    exact h

/-- Every group in the target's update monoid lifts to a group divisor of a finite
approximate emulator. -/
theorem approximate_emulation_lifts_group [Finite X] {G : Type*} [Group G]
    (hclose : EmulatesWithin F π x₀ T o w₀ δ) (hsep : SeparatedBeyond T o w₀ δ)
    (ι : G →ₙ* generated (reachStep T o w₀)) (hι : Injective ι) :
    ∃ e : {m : generated F // IsIdempotentElem m},
      ∃ H : Subgroup ((Corner e)ˣ), ∃ ψ : H →* G, Surjective ψ :=
  division_lifts_group (approximate_emulation_divides hclose hsep) ι hι

end Decoder

section FiniteHorizon

variable {F : A → X → X} {π : X → O} {x₀ : X} {T : A → W → W} {o : W → O} {w₀ : W} {δ : ℝ}

/-- Emulation within `δ` after every input word of length at most `H`. -/
def EmulatesWithinUpTo (F : A → X → X) (π : X → O) (x₀ : X)
    (T : A → W → W) (o : W → O) (w₀ : W) (δ : ℝ) (H : ℕ) : Prop :=
  ∀ s : List A, s.length ≤ H → dist (π (run F x₀ s)) (o (run T w₀ s)) ≤ δ

/-- At a bounded horizon, two histories whose target readings are more than `2 * δ` apart
after a continuation inside the horizon reach distinct emulator states. -/
theorem finite_horizon_distinct_states {H : ℕ}
    (hclose : EmulatesWithinUpTo F π x₀ T o w₀ δ H) {s t r : List A}
    (hs : (s ++ r).length ≤ H) (ht : (t ++ r).length ≤ H)
    (hr : 2 * δ < dist (o (run T w₀ (s ++ r))) (o (run T w₀ (t ++ r)))) :
    run F x₀ s ≠ run F x₀ t := by
  intro h
  have hF : run F x₀ (s ++ r) = run F x₀ (t ++ r) := by
    rw [run_concat, run_concat, h]
  have h1 := hclose (s ++ r) hs
  have h2 := hclose (t ++ r) ht
  rw [hF] at h1
  have htri := dist_triangle_left (o (run T w₀ (s ++ r))) (o (run T w₀ (t ++ r)))
    (π (run F x₀ (t ++ r)))
  linarith

/-- **Memory bound at a bounded horizon.** A finite family of histories, pairwise separated
by more than `2 * δ` inside the horizon, needs at least as many emulator states as it has
members. No group is forced. -/
theorem finite_horizon_memory_bound [Fintype X] {H : ℕ}
    (hclose : EmulatesWithinUpTo F π x₀ T o w₀ δ H) (S : Finset (List A))
    (hpair : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ∃ r : List A, (s ++ r).length ≤ H ∧
      (t ++ r).length ≤ H ∧
      2 * δ < dist (o (run T w₀ (s ++ r))) (o (run T w₀ (t ++ r)))) :
    S.card ≤ Fintype.card X := by
  classical
  have hinj : Set.InjOn (fun s : List A => run F x₀ s) (S : Set (List A)) := by
    intro s hs t ht hst
    by_contra hne
    obtain ⟨r, h1, h2, hr⟩ := hpair s hs t ht hne
    exact finite_horizon_distinct_states hclose h1 h2 hr hst
  calc S.card = (S.image (fun s : List A => run F x₀ s)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card X := Finset.card_le_univ _

end FiniteHorizon

section Sharpness

/-- The toggle: one input flips a bit. -/
def toggle : Unit → Bool → Bool := fun _ b => !b

/-- Toggle readings `0` and `2 * δ`. -/
def toggleReading (δ : ℝ) : Bool → ℝ := fun b => if b then 2 * δ else 0

/-- **Sharpness of the factor two.** A toggle with readings `0` and `2 * δ` is emulated
within `δ` by a single state reading `δ`. Its two classes are separated by exactly `2 * δ`,
and no map from the emulator's reachable states onto the target's reachable classes exists.
The strict inequality in `SeparatedBeyond` therefore cannot be weakened. -/
theorem half_separation_sharp (δ : ℝ) (hδ : 0 < δ) :
    EmulatesWithin (fun (_ : Unit) (x : Unit) => x) (fun _ => δ) ()
        toggle (toggleReading δ) false δ ∧
      (∀ s t : List Unit,
        ¬ futureEquivalence toggle (toggleReading δ) (run toggle false s) (run toggle false t) →
        ∃ r : List Unit, 2 * δ ≤ dist (toggleReading δ (run toggle false (s ++ r)))
          (toggleReading δ (run toggle false (t ++ r)))) ∧
      ¬ ∃ p : Reach (fun (_ : Unit) (x : Unit) => x) () →
          Reachable toggle (toggleReading δ) false, Surjective p := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    have hb : ∀ b : Bool, dist δ (toggleReading δ b) ≤ δ := by
      intro b
      cases b
      · simp [toggleReading, abs_of_pos hδ]
      · have : δ - 2 * δ = -δ := by ring
        simp [toggleReading, Real.dist_eq, this, abs_of_pos hδ]
    exact hb _
  · intro s t hne
    refine ⟨[], ?_⟩
    simp only [List.append_nil]
    have hbb : run toggle false s ≠ run toggle false t := by
      intro h
      apply hne
      intro w
      rw [h]
    generalize run toggle false s = b at hbb ⊢
    generalize run toggle false t = b' at hbb ⊢
    cases b <;> cases b' <;>
      simp_all [toggleReading, Real.dist_eq, abs_of_pos]
  · rintro ⟨p, hp⟩
    have hsub : ∀ x y : Reach (fun (_ : Unit) (x : Unit) => x) (), x = y := by
      intro x y
      exact Subtype.ext rfl
    obtain ⟨x, hx⟩ := hp (reached toggle (toggleReading δ) false [])
    obtain ⟨y, hy⟩ := hp (reached toggle (toggleReading δ) false [()])
    have hxy : reached toggle (toggleReading δ) false [] =
        reached toggle (toggleReading δ) false [()] := by
      rw [← hx, ← hy, hsub x y]
    have hcls := (project_eq_iff toggle (toggleReading δ) _ _).mp (congrArg Subtype.val hxy)
    have h0 := hcls []
    simp [run, toggle, toggleReading] at h0
    linarith

end Sharpness

section PredictionFloor

variable {Q : Type*} [PseudoMetricSpace Q]

/-- Any single prediction is at least half the distance between two possible outcomes away
from one of them. -/
theorem two_point_prediction_floor (z s₁ s₂ : Q) :
    dist s₁ s₂ / 2 ≤ max (dist z s₁) (dist z s₂) := by
  have htri := dist_triangle_left s₁ s₂ z
  have h1 := le_max_left (dist z s₁) (dist z s₂)
  have h2 := le_max_right (dist z s₁) (dist z s₂)
  linarith

/-- **Two-preparation floor on deterministic prediction.** If two preparations share the
retained state, any reduced deterministic model errs on one of them by at least half the
distance between their retained successors. -/
theorem deterministic_one_step_floor {Xs U : Type*} (ρ : Xs → Q) (Ψ : U → Xs → Xs)
    (M : U → Q → Q) (u : U) (x₁ x₂ : Xs) (h : ρ x₁ = ρ x₂) :
    dist (ρ (Ψ u x₁)) (ρ (Ψ u x₂)) / 2 ≤
      max (dist (M u (ρ x₁)) (ρ (Ψ u x₁))) (dist (M u (ρ x₂)) (ρ (Ψ u x₂))) := by
  rw [← h]
  exact two_point_prediction_floor (M u (ρ x₁)) (ρ (Ψ u x₁)) (ρ (Ψ u x₂))

end PredictionFloor

end KTAIT.ApproximateEmulation
