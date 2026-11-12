/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import KTAIT.IS.Boundary

/-!
# Coarsest exact reduction retaining selected content

Two states are indistinguishable when every finite input sequence gives the same
selected content, including the empty sequence. This equivalence gives the
coarsest deterministic closed reduction retaining that content. All update maps
are total on the declared state type. No finiteness, decidability, smoothness,
physical admissibility, or experiential assignment is assumed or concluded.
-/

namespace KTAIT.IS.MinimalRealization

universe u v w z
variable {X : Type u} {U : Type v} {V : Type w}

/-- Apply an input sequence in its listed order. -/
def run (Ψ : U → X → X) : List U → X → X
  | [], x => x
  | i :: is, x => run Ψ is (Ψ i x)

/-- Selected content agrees after every finite input sequence. -/
def Indist (Ψ : U → X → X) (c : X → V) (x y : X) : Prop :=
  ∀ is, c (run Ψ is x) = c (run Ψ is y)

/-- Concatenating input sequences composes their executions. -/
theorem run_sequence_append (Ψ : U → X → X) (is js : List U) (x : X) :
    run Ψ (is ++ js) x = run Ψ js (run Ψ is x) := by
  induction is generalizing x with
  | nil => rfl
  | cons i is ih => exact ih (Ψ i x)

/-- Indistinguishability is an equivalence relation. -/
theorem indist_equivalence (Ψ : U → X → X) (c : X → V) :
    Equivalence (Indist Ψ c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x is; rfl
  · intro x y h is; exact (h is).symm
  · intro x y z hxy hyz is; exact (hxy is).trans (hyz is)

/-- Each admitted update preserves indistinguishability. -/
theorem indist_closed (Ψ : U → X → X) (c : X → V) {x y : X}
    (h : Indist Ψ c x y) (i : U) : Indist Ψ c (Ψ i x) (Ψ i y) := by
  intro is
  exact h (i :: is)

/-- The empty input sequence ensures retention of current content. -/
theorem indist_content (Ψ : U → X → X) (c : X → V) {x y : X}
    (h : Indist Ψ c x y) : c x = c y := h []

/-- Every stable, content-preserving relation refines indistinguishability. -/
theorem indist_coarsest (Ψ : U → X → X) (c : X → V) (R : X → X → Prop)
    (hclosed : ∀ x y, R x y → ∀ i, R (Ψ i x) (Ψ i y))
    (hcontent : ∀ x y, R x y → c x = c y) {x y : X}
    (h : R x y) : Indist Ψ c x y := by
  intro is
  induction is generalizing x y with
  | nil => exact hcontent x y h
  | cons i is ih => exact ih (hclosed x y h i)

/-- The indistinguishability equivalence used to form the retained state type. -/
def indistSetoid (Ψ : U → X → X) (c : X → V) : Setoid X :=
  ⟨Indist Ψ c, indist_equivalence Ψ c⟩

/-- The coarsest exact retained state type. -/
abbrev Reduced (Ψ : U → X → X) (c : X → V) := Quotient (indistSetoid Ψ c)

/-- Send a source state to its indistinguishability class. -/
def project (Ψ : U → X → X) (c : X → V) (x : X) : Reduced Ψ c :=
  Quotient.mk (indistSetoid Ψ c) x

/-- Quotient equality is exactly indistinguishability. -/
theorem project_eq_iff (Ψ : U → X → X) (c : X → V) (x y : X) :
    project Ψ c x = project Ψ c y ↔ Indist Ψ c x y := Quotient.eq

/-- The supported update on retained states. -/
def reducedStep (Ψ : U → X → X) (c : X → V) (i : U) : Reduced Ψ c → Reduced Ψ c :=
  Quotient.map (Ψ i) (fun _ _ h => indist_closed Ψ c h i)

/-- The selected-content readout on retained states. -/
def reducedContent (Ψ : U → X → X) (c : X → V) : Reduced Ψ c → V :=
  Quotient.lift c (fun _ _ h => indist_content Ψ c h)

/-- The quotient commutes with every admitted update. -/
theorem project_closed (Ψ : U → X → X) (c : X → V) (i : U) (x : X) :
    project Ψ c (Ψ i x) = reducedStep Ψ c i (project Ψ c x) := rfl

/-- The quotient retains the selected content. -/
theorem project_content (Ψ : U → X → X) (c : X → V) (x : X) :
    reducedContent Ψ c (project Ψ c x) = c x := rfl

/-- Every onto closed content-preserving reduction factors uniquely onto this quotient. -/
theorem coarsest_factorization (Ψ : U → X → X) (c : X → V)
    {Q : Type z} (ρ : X → Q) (honto : Function.Surjective ρ)
    (hclosed : ∀ x y, ρ x = ρ y → ∀ i, ρ (Ψ i x) = ρ (Ψ i y))
    (hcontent : ∀ x y, ρ x = ρ y → c x = c y) :
    ∃! g : Q → Reduced Ψ c, ∀ x, g (ρ x) = project Ψ c x := by
  classical
  let g : Q → Reduced Ψ c := fun q => project Ψ c (honto q).choose
  have hg : ∀ x, g (ρ x) = project Ψ c x := by
    intro x
    apply (project_eq_iff Ψ c _ _).2
    apply indist_coarsest Ψ c (fun a b => ρ a = ρ b) hclosed hcontent
    exact (honto (ρ x)).choose_spec
  refine ⟨g, hg, ?_⟩
  intro f hf
  funext q
  obtain ⟨x, rfl⟩ := honto q
  exact (hf x).trans (hg x).symm

/-- A factor map carries the reduced updates and selected content. -/
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

/-- Refining selected content refines indistinguishability. -/
theorem indist_mono_content (Ψ : U → X → X) {W : Type z}
    (c : X → V) (d : X → W) (f : W → V) (hfactor : ∀ x, c x = f (d x))
    {x y : X} (h : Indist Ψ d x y) : Indist Ψ c x y := by
  intro is
  rw [hfactor, hfactor, h is]

/-- Relabeling an input sequence with compatible updates preserves execution. -/
theorem run_map_inputs (Ψ : U → X → X) {I : Type z} (Φ : I → X → X)
    (e : U → I) (hstep : ∀ i x, Φ (e i) x = Ψ i x) (is : List U) (x : X) :
    run Φ (is.map e) x = run Ψ is x := by
  induction is generalizing x with
  | nil => rfl
  | cons i is ih => simpa only [List.map_cons, run, hstep] using ih (Ψ i x)

/-- Adding admitted updates refines indistinguishability. -/
theorem indist_mono_inputs (Ψ : U → X → X) {I : Type z} (Φ : I → X → X)
    (e : U → I) (hstep : ∀ i x, Φ (e i) x = Ψ i x) (c : X → V)
    {x y : X} (h : Indist Φ c x y) : Indist Ψ c x y := by
  intro is
  simpa only [run_map_inputs Ψ Φ e hstep] using h (is.map e)

/-- The unmarked execution agrees with the existing marked-machine execution. -/
theorem run_machine {S I O : Type} (M : Machine S I O) (is : List I) (s : S) :
    run (fun i x => M.step x i) is s = M.run s is := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih => exact ih (M.step s i)


/-- The part of the quotient reachable from a specified initial state. -/
def Reachable (Ψ : U → X → X) (c : X → V) (m : X) :=
  {q : Reduced Ψ c // ∃ is, project Ψ c (run Ψ is m) = q}

/-- A retained state reached by an input sequence. -/
def reached (Ψ : U → X → X) (c : X → V) (m : X) (is : List U) : Reachable Ψ c m :=
  ⟨project Ψ c (run Ψ is m), is, rfl⟩

/-- Every reachable quotient state has an input-sequence representative. -/
theorem reached_surjective (Ψ : U → X → X) (c : X → V) (m : X) :
    Function.Surjective (reached Ψ c m) := by
  intro q
  obtain ⟨is, his⟩ := q.property
  exact ⟨is, Subtype.ext his⟩

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

/-- The reachable update appends one input to a representative sequence. -/
theorem reachStep_reached (Ψ : U → X → X) (c : X → V) (m : X) (i : U)
    (is : List U) :
    reachStep Ψ c m i (reached Ψ c m is) = reached Ψ c m (is ++ [i]) := by
  apply Subtype.ext
  simp only [reachStep, reached, run_sequence_append]
  rfl

variable {Y : Type z}

/-- Equal initialized responses identify the same pairs of input-sequence states. -/
theorem same_path_classes (Ψ : U → X → X) (c : X → V) (m : X)
    (Φ : U → Y → Y) (d : Y → V) (n : Y)
    (h : ∀ is, c (run Ψ is m) = d (run Φ is n)) (is js : List U) :
    project Ψ c (run Ψ is m) = project Ψ c (run Ψ js m) ↔
    project Φ d (run Φ is n) = project Φ d (run Φ js n) := by
  rw [project_eq_iff, project_eq_iff]
  constructor
  · intro hij ks
    calc
      d (run Φ ks (run Φ is n)) = c (run Ψ ks (run Ψ is m)) := by
        simpa only [run_sequence_append] using (h (is ++ ks)).symm
      _ = c (run Ψ ks (run Ψ js m)) := hij ks
      _ = d (run Φ ks (run Φ js n)) := by
        simpa only [run_sequence_append] using h (js ++ ks)
  · intro hij ks
    calc
      c (run Ψ ks (run Ψ is m)) = d (run Φ ks (run Φ is n)) := by
        simpa only [run_sequence_append] using h (is ++ ks)
      _ = d (run Φ ks (run Φ js n)) := hij ks
      _ = c (run Ψ ks (run Ψ js m)) := by
        simpa only [run_sequence_append] using (h (js ++ ks)).symm

/-- Transport a reachable class by a sequence reaching it. -/
noncomputable def reachMap (Ψ : U → X → X) (c : X → V) (m : X)
    (Φ : U → Y → Y) (d : Y → V) (n : Y)
    (q : Reachable Ψ c m) : Reachable Φ d n :=
  reached Φ d n q.property.choose

/-- Equal responses make the transported class independent of its chosen sequence. -/
theorem reachMap_reached (Ψ : U → X → X) (c : X → V) (m : X)
    (Φ : U → Y → Y) (d : Y → V) (n : Y)
    (h : ∀ is, c (run Ψ is m) = d (run Φ is n)) (is : List U) :
    reachMap Ψ c m Φ d n (reached Ψ c m is) = reached Φ d n is := by
  apply Subtype.ext
  apply (same_path_classes Ψ c m Φ d n h _ is).mp
  exact (reached Ψ c m is).property.choose_spec

/-- An isomorphism of reachable quotients carries updates, content, and initial marking. -/
structure ReachableIso (Ψ : U → X → X) (c : X → V) (m : X)
    (Φ : U → Y → Y) (d : Y → V) (n : Y) where
  toEquiv : Reachable Ψ c m ≃ Reachable Φ d n
  map_start : toEquiv (reached Ψ c m []) = reached Φ d n []
  map_step : ∀ i q, toEquiv (reachStep Ψ c m i q) = reachStep Φ d n i (toEquiv q)
  map_content : ∀ q, reachContent Φ d n (toEquiv q) = reachContent Ψ c m q

/-- Equal responses for every input sequence give isomorphic reachable minimal quotients. -/
theorem reachable_quotient_iso (Ψ : U → X → X) (c : X → V) (m : X)
    (Φ : U → Y → Y) (d : Y → V) (n : Y)
    (h : ∀ is, c (run Ψ is m) = d (run Φ is n)) :
    Nonempty (ReachableIso Ψ c m Φ d n) := by
  classical
  let f := reachMap Ψ c m Φ d n
  let g := reachMap Φ d n Ψ c m
  have hf : ∀ is, f (reached Ψ c m is) = reached Φ d n is :=
    reachMap_reached Ψ c m Φ d n h
  have hg : ∀ is, g (reached Φ d n is) = reached Ψ c m is :=
    reachMap_reached Φ d n Ψ c m (fun is => (h is).symm)
  let e : Reachable Ψ c m ≃ Reachable Φ d n :=
    { toFun := f
      invFun := g
      left_inv := by
        intro q
        obtain ⟨is, rfl⟩ := reached_surjective Ψ c m q
        rw [hf, hg]
      right_inv := by
        intro q
        obtain ⟨is, rfl⟩ := reached_surjective Φ d n q
        rw [hg, hf] }
  refine ⟨{ toEquiv := e, map_start := hf [], map_step := ?_, map_content := ?_ }⟩
  · intro i q
    obtain ⟨is, rfl⟩ := reached_surjective Ψ c m q
    change f (reachStep Ψ c m i (reached Ψ c m is)) =
      reachStep Φ d n i (f (reached Ψ c m is))
    rw [reachStep_reached, hf, hf, reachStep_reached]
  · intro q
    obtain ⟨is, rfl⟩ := reached_surjective Ψ c m q
    change reachContent Φ d n (f (reached Ψ c m is)) = _
    rw [hf]
    exact (h is).symm

end KTAIT.IS.MinimalRealization
