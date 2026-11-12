/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import KTAIT.IS.MinimalRealization
import KTAIT.SemigroupTracking

/-!
# Canonical tracking and exact prediction

A closed readout is its own minimal content description. Exact initialized
prediction of an observable world induces a unique factor from reachable agent
states onto reachable world states. These are deterministic set-level results;
they require neither finite state spaces nor a computable quotient construction.
-/

namespace KTAIT.CanonicalPrediction

open ComputationCores OperationalAlgebra
open IS.MinimalRealization

universe u v w z
variable {A : Type u} {X : Type v} {W : Type w} {O : Type z}

/-- Future equivalence of a closed readout is exactly equality of that readout. -/
theorem tracking_canonical (F : A → X → X) (T : A → W → W) (p : X → W)
    (h : ∀ a x, p (F a x) = T a (p x)) :
    futureEquivalence F p = Setoid.ker p := by
  apply le_antisymm (future_equivalence_content F p)
  apply future_equivalence_greatest F p (Setoid.ker p) le_rfl
  intro a x y hxy
  change p (F a x) = p (F a y)
  rw [h, h, hxy]

/-- An onto closed readout identifies the future quotient with its retained space. -/
noncomputable def trackingEquiv (F : A → X → X) (T : A → W → W) (p : X → W)
    (hp : Function.Surjective p) (h : ∀ a x, p (F a x) = T a (p x)) :
    Reduced F p ≃ W :=
  Equiv.ofBijective (reducedContent F p) ⟨by
    intro q r heq
    induction q using Quotient.inductionOn with
    | h x =>
      induction r using Quotient.inductionOn with
      | h y =>
        apply Quotient.sound
        rw [tracking_canonical F T p h]
        exact heq,
    by
      intro w
      obtain ⟨x, rfl⟩ := hp w
      exact ⟨project F p x, rfl⟩⟩

/-- The canonical equivalence reads the same retained state as the original map. -/
@[simp] theorem trackingEquiv_project (F : A → X → X) (T : A → W → W)
    (p : X → W) (hp : Function.Surjective p)
    (h : ∀ a x, p (F a x) = T a (p x)) (x : X) :
    trackingEquiv F T p hp h (project F p x) = p x := rfl

/-- The canonical equivalence transports each retained update. -/
theorem trackingEquiv_step (F : A → X → X) (T : A → W → W)
    (p : X → W) (hp : Function.Surjective p)
    (h : ∀ a x, p (F a x) = T a (p x)) (a : A) (q : Reduced F p) :
    trackingEquiv F T p hp h (reducedStep F p a q) =
      T a (trackingEquiv F T p hp h q) := by
  induction q using Quotient.inductionOn with
  | h x => exact h a x

/-- A state conjugacy identifies the generated monoids of actual transformations. -/
noncomputable def generatedEquiv (F : A → X → X) (T : A → W → W)
    (e : X ≃ W) (h : ∀ a x, e (F a x) = T a (e x)) : generated F ≃* generated T :=
  MulEquiv.ofBijective (generatedFactor F T e e.surjective h) ⟨by
    intro m n hmn
    apply Subtype.ext
    funext x
    apply e.injective
    rw [generated_factor_commutes F T e e.surjective h,
      generated_factor_commutes F T e e.surjective h, hmn],
    generated_factor_surjective F T e e.surjective h⟩

/-- Canonical tracking identifies the generated quotient monoid with the retained one. -/
noncomputable def trackingGeneratedEquiv (F : A → X → X) (T : A → W → W)
    (p : X → W) (hp : Function.Surjective p)
    (h : ∀ a x, p (F a x) = T a (p x)) :
    generated (reducedStep F p) ≃* generated T :=
  generatedEquiv (reducedStep F p) T (trackingEquiv F T p hp h)
    (trackingEquiv_step F T p hp h)

section GroupObservations

variable {G : Type*} [Group G] [MulAction G W]

/-- With all group labels admitted, the canonical monoid is the actual permutation image. -/
noncomputable def trackingGroupEquiv (F : G → X → X) (p : X → W)
    (hp : Function.Surjective p) (h : ∀ g x, p (F g x) = g • p x) :
    generated (reducedStep F p) ≃* SemigroupTracking.WorldActionImage G W :=
  (trackingGeneratedEquiv F (fun g w => g • w) p hp h).trans
    SemigroupTracking.actionGeneratedEquiv

/-- Transformation labels act by the group; each observation label writes its world state. -/
def groupObservationStep : G ⊕ W → W → W
  | .inl g, w => g • w
  | .inr v, _ => v

private theorem group_observation_sequence (s : List (G ⊕ W)) :
    (∃ g : G, ∀ w, ComputationCores.run groupObservationStep w s = g • w) ∨
      (∃ v : W, ∀ w, ComputationCores.run groupObservationStep w s = v) := by
  induction s with
  | nil => exact Or.inl ⟨1, fun _ => (one_smul G _).symm⟩
  | cons a s ih =>
    cases a with
    | inl g =>
      rcases ih with ⟨h, hh⟩ | ⟨v, hv⟩
      · exact Or.inl ⟨h * g, fun w => (hh (g • w)).trans (mul_smul h g w).symm⟩
      · exact Or.inr ⟨v, fun w => hv (g • w)⟩
    | inr v => exact Or.inr ⟨ComputationCores.run groupObservationStep v s, fun _ => rfl⟩

/-- Group operations and complete observation writes generate exactly group maps and constants. -/
theorem group_observation_generated (f : Function.End W) :
    f ∈ generated (groupObservationStep (G := G)) ↔
      (∃ g : G, f = fun w => g • w) ∨ (∃ v : W, f = fun _ => v) := by
  constructor
  · rintro ⟨s, rfl⟩
    rcases group_observation_sequence s with ⟨g, hg⟩ | ⟨v, hv⟩
    · exact Or.inl ⟨g, funext hg⟩
    · exact Or.inr ⟨v, funext hv⟩
  · rintro (⟨g, rfl⟩ | ⟨v, rfl⟩)
    · exact ⟨[Sum.inl g], rfl⟩
    · exact ⟨[Sum.inr v], rfl⟩

/-- Among the generated maps, an idempotent is the identity or an observation constant. -/
theorem group_observation_idempotents
    (m : generated (groupObservationStep (G := G) (W := W))) :
    IsIdempotentElem m ↔ m = 1 ∨ ∃ v : W, m.val = fun _ => v := by
  constructor
  · intro hm
    rcases (group_observation_generated m.val).mp m.property with ⟨g, hg⟩ | hc
    · left
      apply Subtype.ext
      funext w
      have hi := congrArg (fun f : generated (groupObservationStep (G := G) (W := W)) =>
        f.val w) hm
      change m.val (m.val w) = m.val w at hi
      rw [hg] at hi ⊢
      change g • w = w
      exact (MulAction.injective g) hi
    · exact Or.inr hc
  · rintro (rfl | ⟨v, hv⟩)
    · exact mul_one 1
    · apply Subtype.ext
      funext w
      change m.val (m.val w) = m.val w
      rw [hv]

/-- Group maps have inverse maps inside the generated monoid. -/
theorem group_observation_group_isUnit
    (m : generated (groupObservationStep (G := G) (W := W)))
    (g : G) (hg : m.val = fun w => g • w) : IsUnit m := by
  let n : generated (groupObservationStep (G := G) (W := W)) :=
    ⟨fun w => g⁻¹ • w, [Sum.inl g⁻¹], rfl⟩
  refine ⟨⟨m, n, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    funext w
    change m.val (g⁻¹ • w) = w
    rw [hg]
    exact smul_inv_smul g w
  · apply Subtype.ext
    funext w
    change g⁻¹ • m.val w = w
    rw [hg]
    exact inv_smul_smul g w

/-- On a nontrivial world, reversible generated maps are precisely the group maps. -/
theorem group_observation_units [Nontrivial W]
    (m : generated (groupObservationStep (G := G) (W := W))) :
    IsUnit m ↔ ∃ g : G, m.val = fun w => g • w := by
  constructor
  · intro hm
    rcases (group_observation_generated m.val).mp m.property with hg | ⟨v, hv⟩
    · exact hg
    · exfalso
      obtain ⟨u, hu⟩ := hm
      have hinj : Function.Injective m.val := by
        intro x y hxy
        have hleft := u.inv_val
        have hx := congrArg
          (fun f : generated (groupObservationStep (G := G) (W := W)) => f.val x) hleft
        have hy := congrArg
          (fun f : generated (groupObservationStep (G := G) (W := W)) => f.val y) hleft
        change u.inv.val (u.val.val x) = x at hx
        change u.inv.val (u.val.val y) = y at hy
        rw [hu] at hx hy
        exact hx.symm.trans ((congrArg u.inv.val hxy).trans hy)
      obtain ⟨x, y, hne⟩ := exists_pair_ne W
      exact hne (hinj (by rw [hv]))
  · rintro ⟨g, hg⟩
    exact group_observation_group_isUnit m g hg

end GroupObservations

/-- Raw states reachable from the specified marking, before any content quotient. -/
def Reach (F : A → X → X) (x₀ : X) :=
  {x : X // ∃ s : List A, ComputationCores.run F x₀ s = x}

/-- The initial marking belongs to its reachable part. -/
def start (F : A → X → X) (x₀ : X) : Reach F x₀ := ⟨x₀, [], rfl⟩

/-- A primitive admitted update preserves reachability. -/
def step (F : A → X → X) (x₀ : X) (a : A) (x : Reach F x₀) : Reach F x₀ :=
  ⟨F a x.val, by
    obtain ⟨s, hs⟩ := x.property
    refine ⟨s ++ [a], ?_⟩
    simp only [ComputationCores.run, List.foldl_append, List.foldl_cons,
      List.foldl_nil] at *
    rw [hs]⟩

/-- Restricted execution is the source execution on the same initial state. -/
theorem reach_run (F : A → X → X) (x₀ : X) (x : Reach F x₀) (s : List A) :
    (ComputationCores.run (step F x₀) x s).val = ComputationCores.run F x.val s :=
  run_intertwines (step F x₀) F Subtype.val (fun _ _ => rfl) x s

/-- Every restricted state is reached from the restricted marking. -/
theorem prediction_reach_accessible (F : A → X → X) (x₀ : X) :
    Accessible (step F x₀) (start F x₀) := by
  intro x
  obtain ⟨s, hs⟩ := x.property
  exact ⟨s, Subtype.ext ((reach_run F x₀ (start F x₀) s).trans hs)⟩

/-- Projection from raw reachable states to reachable future classes. -/
def reachProject (F : A → X → X) (c : X → O) (x₀ : X)
    (x : Reach F x₀) : IS.MinimalRealization.Reachable F c x₀ :=
  ⟨project F c x.val, by
    obtain ⟨s, hs⟩ := x.property
    exact ⟨s, congrArg (project F c) hs⟩⟩

/-- Every reachable class has a reachable raw representative. -/
theorem reachProject_surjective (F : A → X → X) (c : X → O) (x₀ : X) :
    Function.Surjective (reachProject F c x₀) := by
  intro q
  obtain ⟨s, hs⟩ := q.property
  exact ⟨⟨ComputationCores.run F x₀ s, s, rfl⟩, Subtype.ext hs⟩

/-- Projection preserves the initial marking. -/
@[simp] theorem reachProject_start (F : A → X → X) (c : X → O) (x₀ : X) :
    reachProject F c x₀ (start F x₀) = reached F c x₀ [] := rfl

/-- Projection preserves each admitted update. -/
@[simp] theorem reachProject_step (F : A → X → X) (c : X → O) (x₀ : X)
    (a : A) (x : Reach F x₀) :
    reachProject F c x₀ (step F x₀ a x) = reachStep F c x₀ a (reachProject F c x₀ x) :=
  rfl

/-- Projection preserves the selected content. -/
@[simp] theorem reachProject_content (F : A → X → X) (c : X → O) (x₀ : X)
    (x : Reach F x₀) : reachContent F c x₀ (reachProject F c x₀ x) = c x.val := rfl

/-- An observable world's reachable raw states already form its future quotient. -/
noncomputable def observableReachEquiv (T : A → W → W) (o : W → O) (w₀ : W)
    (obs : Observable (step T w₀) (fun w : Reach T w₀ => o w.val)) :
    Reach T w₀ ≃ IS.MinimalRealization.Reachable T o w₀ :=
  Equiv.ofBijective (reachProject T o w₀) ⟨by
    intro x y hxy
    apply obs x y
    intro s
    have hh := (project_eq_iff T o x.val y.val).mp (congrArg Subtype.val hxy)
    simpa only [reach_run] using hh s,
    reachProject_surjective T o w₀⟩

/-- A marked prediction factor carries all admitted steps and the selected content. -/
def PredictionFactor (F : A → X → X) (π : X → O) (x₀ : X)
    (T : A → W → W) (o : W → O) (w₀ : W) (p : Reach F x₀ → Reach T w₀) : Prop :=
  Function.Surjective p ∧ p (start F x₀) = start T w₀ ∧
    (∀ a x, p (step F x₀ a x) = step T w₀ a (p x)) ∧
    (∀ x, o (p x).val = π x.val)

/-- Exact initialized prediction factors uniquely onto the reachable observable world. -/
theorem prediction_factor (F : A → X → X) (π : X → O) (x₀ : X)
    (T : A → W → W) (o : W → O) (w₀ : W)
    (obs : Observable (step T w₀) (fun w : Reach T w₀ => o w.val))
    (same : ∀ s, π (ComputationCores.run F x₀ s) = o (ComputationCores.run T w₀ s)) :
    ∃! p : Reach F x₀ → Reach T w₀, PredictionFactor F π x₀ T o w₀ p := by
  classical
  obtain ⟨e⟩ := reachable_quotient_iso F π x₀ T o w₀ same
  let d := observableReachEquiv T o w₀ obs
  let p : Reach F x₀ → Reach T w₀ := fun x => d.symm (e.toEquiv (reachProject F π x₀ x))
  have hp : ∀ x, d (p x) = e.toEquiv (reachProject F π x₀ x) := fun x => d.apply_symm_apply _
  have hstart : p (start F x₀) = start T w₀ := by
    apply d.injective
    rw [hp, reachProject_start, e.map_start]
    rfl
  have hstep : ∀ a x, p (step F x₀ a x) = step T w₀ a (p x) := by
    intro a x
    apply d.injective
    rw [hp, reachProject_step, e.map_step]
    change reachStep T o w₀ a (e.toEquiv (reachProject F π x₀ x)) =
      reachProject T o w₀ (step T w₀ a (p x))
    rw [reachProject_step, ← hp]
    rfl
  have hc : ∀ x, o (p x).val = π x.val := by
    intro x
    calc
      o (p x).val = reachContent T o w₀ (d (p x)) := rfl
      _ = reachContent T o w₀ (e.toEquiv (reachProject F π x₀ x)) := congrArg _ (hp x)
      _ = π x.val := e.map_content _
  have honto : Function.Surjective p :=
    d.symm.surjective.comp (e.toEquiv.surjective.comp (reachProject_surjective F π x₀))
  refine ⟨p, ⟨honto, hstart, hstep, hc⟩, ?_⟩
  intro q hq
  exact initialized_intertwiner_unique (step F x₀) (step T w₀) (start F x₀)
    (prediction_reach_accessible F x₀) q p (hq.2.1.trans hstart.symm) hq.2.2.1 hstep

/-- The prediction factor identifies precisely the future-indistinguishable reachable states. -/
theorem prediction_factor_kernel (F : A → X → X) (π : X → O) (x₀ : X)
    (T : A → W → W) (o : W → O) (w₀ : W)
    (obs : Observable (step T w₀) (fun w : Reach T w₀ => o w.val))
    (p : Reach F x₀ → Reach T w₀) (hp : PredictionFactor F π x₀ T o w₀ p) :
    futureEquivalence (step F x₀) (fun x => π x.val) = Setoid.ker p := by
  apply le_antisymm
  · intro x y hxy
    apply obs (p x) (p y)
    intro s
    have hx := run_intertwines (step F x₀) (step T w₀) p hp.2.2.1 x s
    have hy := run_intertwines (step F x₀) (step T w₀) p hp.2.2.1 y s
    change o (ComputationCores.run (step T w₀) (p x) s).val =
      o (ComputationCores.run (step T w₀) (p y) s).val
    rw [← hx, ← hy, hp.2.2.2, hp.2.2.2]
    exact hxy s
  · apply future_equivalence_greatest _ _ (Setoid.ker p)
    · intro x y hxy
      change π x.val = π y.val
      rw [← hp.2.2.2, ← hp.2.2.2, hxy]
    · intro a x y hxy
      change p (step F x₀ a x) = p (step F x₀ a y)
      rw [hp.2.2.1, hp.2.2.1, hxy]

/-- The reachable observable world divides the agent via the single-input implementation. -/
noncomputable def prediction_divides (F : A → X → X) (π : X → O) (x₀ : X)
    (T : A → W → W) (o : W → O) (w₀ : W)
    (obs : Observable (step T w₀) (fun w : Reach T w₀ => o w.val))
    (same : ∀ s, π (ComputationCores.run F x₀ s) = o (ComputationCores.run T w₀ s)) :
    SemigroupCore.Divides (step T w₀) F := by
  classical
  let ex := (prediction_factor F π x₀ T o w₀ obs same).exists
  let p := Classical.choose ex
  have hp := Classical.choose_spec ex
  exact {
    dom := {x | ∃ s, ComputationCores.run F x₀ s = x}
    ρ := p
    word := fun a => [a]
    closed := fun a x => (step F x₀ a x).property
    onto := hp.1
    comm := hp.2.2.1 }

end KTAIT.CanonicalPrediction
