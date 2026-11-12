/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import KTAIT.OperationalAlgebra
import KTAIT.ClosureInvariance

/-!
# Quotient realization of future equivalence (WP0215)

The equivalence, its stability, greatest-property characterization, and both
refinement laws are supplied by `OperationalAlgebra` (WP0004). This module
constructs its quotient updates and readout, specializes the existing unique
factorization theorem, and applies `ComputationCores.observable_conjugacy` to
reachable quotients. A short strengthening covers arbitrary stable relations.
No effectiveness, smoothness, physical admissibility, or experiential assignment
is inferred from these deterministic set-level constructions.
-/

namespace KTAIT.IS.MinimalRealization

universe u v w z
variable {X : Type u} {U : Type v} {V : Type w}

/-- The existing execution map, with the input sequence before the initial state. -/
abbrev run (Ψ : U → X → X) (is : List U) (x : X) : X :=
  ComputationCores.run Ψ x is

/-- WP0004 future equivalence in the paper's terminology. -/
abbrev Indist (Ψ : U → X → X) (c : X → V) (x y : X) : Prop :=
  OperationalAlgebra.futureEquivalence Ψ c x y

/-- Concatenation composes the existing execution map. -/
theorem run_sequence_append (Ψ : U → X → X) (is js : List U) (x : X) :
    run Ψ (is ++ js) x = run Ψ js (run Ψ is x) := by
  simp only [run, ComputationCores.run, List.foldl_append]

/-- The greatest-property argument also applies to relations that need not be equivalences. -/
theorem indist_coarsest (Ψ : U → X → X) (c : X → V) (R : X → X → Prop)
    (hclosed : ∀ x y, R x y → ∀ i, R (Ψ i x) (Ψ i y))
    (hcontent : ∀ x y, R x y → c x = c y) {x y : X}
    (h : R x y) : Indist Ψ c x y := by
  intro is
  induction is generalizing x y with
  | nil => exact hcontent x y h
  | cons i is ih => exact ih (hclosed x y h i)

/-- Retained states are the classes of the existing future equivalence. -/
abbrev Reduced (Ψ : U → X → X) (c : X → V) :=
  Quotient (OperationalAlgebra.futureEquivalence Ψ c)

/-- Send a source state to its future-equivalence class. -/
def project (Ψ : U → X → X) (c : X → V) (x : X) : Reduced Ψ c :=
  Quotient.mk (OperationalAlgebra.futureEquivalence Ψ c) x

/-- Quotient equality is exactly future equivalence. -/
theorem project_eq_iff (Ψ : U → X → X) (c : X → V) (x y : X) :
    project Ψ c x = project Ψ c y ↔ Indist Ψ c x y := Quotient.eq

/-- The retained update is well defined by WP0004 stability. -/
def reducedStep (Ψ : U → X → X) (c : X → V) (i : U) : Reduced Ψ c → Reduced Ψ c :=
  Quotient.map (Ψ i) (OperationalAlgebra.future_equivalence_stable Ψ c i)

/-- The retained readout is well defined by WP0004 content preservation. -/
def reducedContent (Ψ : U → X → X) (c : X → V) : Reduced Ψ c → V :=
  Quotient.lift c (fun _ _ h => OperationalAlgebra.future_equivalence_content Ψ c h)

/-- The quotient commutes with every admitted update. -/
theorem project_closed (Ψ : U → X → X) (c : X → V) (i : U) (x : X) :
    project Ψ c (Ψ i x) = reducedStep Ψ c i (project Ψ c x) := rfl

/-- The quotient retains the selected content. -/
theorem project_content (Ψ : U → X → X) (c : X → V) (x : X) :
    reducedContent Ψ c (project Ψ c x) = c x := rfl

/-- An onto closed content-preserving reduction factors through the future quotient. -/
theorem coarsest_factorization (Ψ : U → X → X) (c : X → V)
    {Q : Type z} (ρ : X → Q) (honto : Function.Surjective ρ)
    (hclosed : ∀ x y, ρ x = ρ y → ∀ i, ρ (Ψ i x) = ρ (Ψ i y))
    (hcontent : ∀ x y, ρ x = ρ y → c x = c y) :
    ∃! g : Q → Reduced Ψ c, ∀ x, g (ρ x) = project Ψ c x := by
  have hle : Setoid.ker ρ ≤ OperationalAlgebra.futureEquivalence Ψ c :=
    OperationalAlgebra.future_equivalence_greatest Ψ c (Setoid.ker ρ)
      (fun {x y} h => hcontent x y h) (fun i x y h => hclosed x y h i)
  have hf : ClosureInvariance.FiberConstant ρ (project Ψ c) :=
    fun x y h => (project_eq_iff Ψ c x y).2 (hle h)
  obtain ⟨g, hg, huniq⟩ :=
    (ClosureInvariance.factor_iff_fiber_constant ρ honto (project Ψ c)).2 hf
  exact ⟨g, fun x => (hg x).symm, fun f hf => huniq f (fun x => (hf x).symm)⟩

/-- The factor map carries the reduced updates and selected content. -/
theorem factorization_preserves (Ψ : U → X → X) (c : X → V)
    {Q : Type z} (ρ : X → Q) (honto : Function.Surjective ρ)
    (T : U → Q → Q) (d : Q → V)
    (hT : ∀ i x, ρ (Ψ i x) = T i (ρ x)) (hd : ∀ x, d (ρ x) = c x)
    (g : Q → Reduced Ψ c) (hg : ∀ x, g (ρ x) = project Ψ c x) :
    (∀ i q, g (T i q) = reducedStep Ψ c i (g q)) ∧
    (∀ q, reducedContent Ψ c (g q) = d q) := by
  constructor
  · intro i q
    obtain ⟨x, rfl⟩ := honto q
    rw [← hT, hg, hg]
    rfl
  · intro q
    obtain ⟨x, rfl⟩ := honto q
    rw [hg, project_content, hd]

/-- The quotient commutes with finite execution by the existing intertwining theorem. -/
theorem project_run (Ψ : U → X → X) (c : X → V) (is : List U) (x : X) :
    ComputationCores.run (reducedStep Ψ c) (project Ψ c x) is =
      project Ψ c (run Ψ is x) :=
  (ComputationCores.run_intertwines Ψ (reducedStep Ψ c) (project Ψ c)
    (fun _ _ => rfl) x is).symm

/-- Distinct quotient states are distinguishable by future content. -/
theorem reduced_observable (Ψ : U → X → X) (c : X → V) :
    ComputationCores.Observable (reducedStep Ψ c) (reducedContent Ψ c) := by
  intro q r h
  induction q using Quotient.inductionOn with
  | h x =>
    induction r using Quotient.inductionOn with
    | h y =>
      apply (project_eq_iff Ψ c x y).2
      intro is
      have hi := h is
      change reducedContent Ψ c (ComputationCores.run (reducedStep Ψ c) (project Ψ c x) is) =
        reducedContent Ψ c (ComputationCores.run (reducedStep Ψ c) (project Ψ c y) is) at hi
      simpa only [project_run, project_content] using hi

/-- The part of the quotient reachable from a specified initial state. -/
def Reachable (Ψ : U → X → X) (c : X → V) (m : X) :=
  {q : Reduced Ψ c // ∃ is, project Ψ c (run Ψ is m) = q}

/-- A retained state reached by an input sequence. -/
def reached (Ψ : U → X → X) (c : X → V) (m : X) (is : List U) : Reachable Ψ c m :=
  ⟨project Ψ c (run Ψ is m), is, rfl⟩

/-- Selected content on the reachable part. -/
def reachContent (Ψ : U → X → X) (c : X → V) (m : X) (q : Reachable Ψ c m) : V :=
  reducedContent Ψ c q.val

/-- An input update stays within the reachable part. -/
def reachStep (Ψ : U → X → X) (c : X → V) (m : X) (i : U)
    (q : Reachable Ψ c m) : Reachable Ψ c m :=
  ⟨reducedStep Ψ c i q.val, by
    obtain ⟨is, his⟩ := q.property
    refine ⟨is ++ [i], ?_⟩
    rw [run_sequence_append]
    change reducedStep Ψ c i (project Ψ c (run Ψ is m)) = _
    rw [his]⟩

/-- Restriction to reachable states commutes with execution. -/
theorem reach_val_run (Ψ : U → X → X) (c : X → V) (m : X)
    (q : Reachable Ψ c m) (is : List U) :
    (ComputationCores.run (reachStep Ψ c m) q is).val =
      ComputationCores.run (reducedStep Ψ c) q.val is :=
  ComputationCores.run_intertwines (reachStep Ψ c m) (reducedStep Ψ c)
    Subtype.val (fun _ _ => rfl) q is

/-- Every state in the restricted quotient is accessible from its initial marking. -/
theorem reach_accessible (Ψ : U → X → X) (c : X → V) (m : X) :
    ComputationCores.Accessible (reachStep Ψ c m) (reached Ψ c m []) := by
  intro q
  obtain ⟨is, his⟩ := q.property
  refine ⟨is, Subtype.ext ?_⟩
  rw [reach_val_run]
  change ComputationCores.run (reducedStep Ψ c) (project Ψ c m) is = _
  rw [project_run]
  exact his

/-- Restricting an observable quotient to its reachable states preserves observability. -/
theorem reach_observable (Ψ : U → X → X) (c : X → V) (m : X) :
    ComputationCores.Observable (reachStep Ψ c m) (reachContent Ψ c m) := by
  intro q r h
  apply Subtype.ext
  apply reduced_observable Ψ c
  intro is
  have hi := h is
  change reducedContent Ψ c (ComputationCores.run (reachStep Ψ c m) q is).val =
    reducedContent Ψ c (ComputationCores.run (reachStep Ψ c m) r is).val at hi
  simpa only [reach_val_run] using hi

/-- The reachable quotient reproduces the source's initialized content responses. -/
theorem reach_initial_output (Ψ : U → X → X) (c : X → V) (m : X) (is : List U) :
    reachContent Ψ c m (ComputationCores.run (reachStep Ψ c m) (reached Ψ c m []) is) =
      c (run Ψ is m) := by
  unfold reachContent
  rw [reach_val_run]
  change reducedContent Ψ c (ComputationCores.run (reducedStep Ψ c) (project Ψ c m) is) = _
  rw [project_run, project_content]

variable {Y : Type z}

/-- A reachable-quotient isomorphism carries updates, content, and initial marking. -/
structure ReachableIso (Ψ : U → X → X) (c : X → V) (m : X)
    (Φ : U → Y → Y) (d : Y → V) (n : Y) where
  toEquiv : Reachable Ψ c m ≃ Reachable Φ d n
  map_start : toEquiv (reached Ψ c m []) = reached Φ d n []
  map_step : ∀ i q, toEquiv (reachStep Ψ c m i q) = reachStep Φ d n i (toEquiv q)
  map_content : ∀ q, reachContent Φ d n (toEquiv q) = reachContent Ψ c m q

/-- Apply the existing observable-realization theorem to the reachable future quotients. -/
theorem reachable_quotient_iso (Ψ : U → X → X) (c : X → V) (m : X)
    (Φ : U → Y → Y) (d : Y → V) (n : Y)
    (h : ∀ is, c (run Ψ is m) = d (run Φ is n)) :
    Nonempty (ReachableIso Ψ c m Φ d n) := by
  obtain ⟨e, hm, hs, hc⟩ := ComputationCores.observable_conjugacy
    (reachStep Ψ c m) (reachStep Φ d n) (reachContent Ψ c m) (reachContent Φ d n)
    (reached Ψ c m []) (reached Φ d n [])
    (reach_accessible Ψ c m) (reach_accessible Φ d n)
    (reach_observable Ψ c m) (reach_observable Φ d n)
    (fun is => by rw [reach_initial_output, reach_initial_output]; exact h is)
  exact ⟨⟨e, hm, hs, hc⟩⟩

end KTAIT.IS.MinimalRealization
