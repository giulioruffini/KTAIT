/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import Mathlib

/-!
# Closure, representative invariance, and symmetry quotients (WP0215)

These results concern arbitrary state spaces. A surjective state map admits a
unique reduced update exactly when the projected update is independent of its
microscopic representative. All permutations within fibers detect this condition.
For bijective updates, closure in both directions is equivalent to normalization
of the fiber-preserving permutation group. The resulting conserved quantity is
an equivalence relation on paired states, not a constant macrostate value.

The group-action quotient construction uses no finiteness, computability,
smoothness, or physical-realization assumptions. Those are separate requirements
when applying these set-level results.
-/

namespace KTAIT.ClosureInvariance

variable {X Q Y : Type*}

/-- A readout is constant on the fibers of the chosen state map. -/
def FiberConstant (ρ : X → Q) (a : X → Y) : Prop :=
  ∀ x y, ρ x = ρ y → a x = a y

/-- Exact closure as factorization of the projected update. -/
def Closed (ρ : X → Q) (f : X → X) : Prop :=
  ∃ g : Q → Q, ∀ x, ρ (f x) = g (ρ x)

/-- Surjectivity makes the reduced readout unique; existence is fiber constancy. -/
theorem factor_iff_fiber_constant (ρ : X → Q) (hρ : Function.Surjective ρ)
    (a : X → Y) :
    (∃! b : Q → Y, ∀ x, a x = b (ρ x)) ↔ FiberConstant ρ a := by
  classical
  constructor
  · rintro ⟨b, hb, _⟩ x y hxy
    rw [hb x, hb y, hxy]
  · intro h
    let s : Q → X := fun q => Classical.choose (hρ q)
    have hs : ∀ q, ρ (s q) = q := fun q => Classical.choose_spec (hρ q)
    refine ⟨fun q => a (s q), ?_, ?_⟩
    · intro x
      exact h x (s (ρ x)) (hs (ρ x)).symm
    · intro b hb
      funext q
      obtain ⟨x, rfl⟩ := hρ q
      exact (hb x).symm.trans (h x (s (ρ x)) (hs (ρ x)).symm)

/-- Exact closure is precisely preservation of same-macrostate membership. -/
theorem closure_iff_fiber_constant (ρ : X → Q) (hρ : Function.Surjective ρ)
    (f : X → X) : Closed ρ f ↔ FiberConstant ρ (ρ ∘ f) := by
  constructor
  · rintro ⟨g, hg⟩ x y hxy
    change ρ (f x) = ρ (f y)
    rw [hg x, hg y, hxy]
  · intro h
    obtain ⟨g, hg, _⟩ := (factor_iff_fiber_constant ρ hρ (ρ ∘ f)).mpr h
    exact ⟨g, hg⟩

/-- All bijections changing only the microscopic representative. -/
def fiberPerms (ρ : X → Q) : Subgroup (Equiv.Perm X) where
  carrier := {σ | ∀ x, ρ (σ x) = ρ x}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro a b ha hb x
    change ρ (a (b x)) = ρ x
    rw [ha, hb]
  inv_mem' := by
    intro a ha x
    simpa using (ha (a.symm x)).symm

/-- The projected update is invariant under every within-fiber permutation. -/
def RepresentativeInvariant (ρ : X → Q) (f : X → X) : Prop :=
  ∀ σ ∈ fiberPerms ρ, ∀ x, ρ (f (σ x)) = ρ (f x)

private theorem swap_mem_fiberPerms [DecidableEq X] (ρ : X → Q) {x y : X} (hxy : ρ x = ρ y) :
    Equiv.swap x y ∈ fiberPerms ρ := by
  classical
  intro z
  by_cases hz : z = x
  · subst z
    simpa using hxy.symm
  · by_cases hz' : z = y
    · subst z
      simpa using hxy
    · simp [Equiv.swap_apply_of_ne_of_ne hz hz']

/-- All fiber-preserving permutations suffice to test representative independence. -/
theorem fiber_constant_iff_representative_invariant (ρ : X → Q) (f : X → X) :
    FiberConstant ρ (ρ ∘ f) ↔ RepresentativeInvariant ρ f := by
  classical
  constructor
  · intro h σ hσ x
    exact h (σ x) x (hσ x)
  · intro h x y hxy
    have hs := h (Equiv.swap x y) (swap_mem_fiberPerms ρ hxy) x
    simpa using hs.symm

/-- The first assertion of WP0215 Proposition S1, including uniqueness. -/
theorem unique_reduced_iff_representative_invariant
    (ρ : X → Q) (hρ : Function.Surjective ρ) (f : X → X) :
    (∃! g : Q → Q, ∀ x, ρ (f x) = g (ρ x)) ↔ RepresentativeInvariant ρ f := by
  exact (factor_iff_fiber_constant ρ hρ (ρ ∘ f)).trans
    (fiber_constant_iff_representative_invariant ρ f)

/-- The existence-only version used for composition and reversible dynamics. -/
theorem closure_iff_representative_invariant
    (ρ : X → Q) (hρ : Function.Surjective ρ) (f : X → X) :
    Closed ρ f ↔ RepresentativeInvariant ρ f :=
  (closure_iff_fiber_constant ρ hρ f).trans
    (fiber_constant_iff_representative_invariant ρ f)

/-- Conjugation by a bijective update, acting on permutations. -/
def conjugate (e σ : Equiv.Perm X) : Equiv.Perm X := e * σ * e⁻¹

/-- Forward closure of a bijection gives inclusion under conjugation. -/
theorem closure_iff_conjugate_subset (ρ : X → Q) (hρ : Function.Surjective ρ)
    (e : Equiv.Perm X) :
    Closed ρ e ↔ ∀ σ ∈ fiberPerms ρ, conjugate e σ ∈ fiberPerms ρ := by
  rw [closure_iff_representative_invariant ρ hρ]
  constructor
  · intro h σ hσ x
    have hx := h σ hσ (e.symm x)
    simpa [conjugate, Equiv.Perm.mul_apply] using hx
  · intro h σ hσ x
    have hx := h σ hσ (e x)
    simpa [conjugate, Equiv.Perm.mul_apply] using hx

/-- Normalization is equality, rather than only inclusion, of the conjugate group. -/
def Normalizes (ρ : X → Q) (e : Equiv.Perm X) : Prop :=
  conjugate e '' (fiberPerms ρ : Set (Equiv.Perm X)) = fiberPerms ρ

/-- Closure in both time directions is precisely normalization of representative changes. -/
theorem closure_both_iff_normalizes (ρ : X → Q) (hρ : Function.Surjective ρ)
    (e : Equiv.Perm X) : (Closed ρ e ∧ Closed ρ e.symm) ↔ Normalizes ρ e := by
  rw [closure_iff_conjugate_subset ρ hρ, closure_iff_conjugate_subset ρ hρ]
  constructor
  · rintro ⟨h, hi⟩
    apply Set.Subset.antisymm
    · rintro σ ⟨τ, hτ, rfl⟩
      exact h τ hτ
    · intro σ hσ
      refine ⟨conjugate e.symm σ, hi σ hσ, ?_⟩
      ext x
      simp [conjugate, Equiv.Perm.mul_apply]
  · intro h
    constructor
    · intro σ hσ
      change conjugate e σ ∈ (fiberPerms ρ : Set (Equiv.Perm X))
      rw [← h]
      exact ⟨σ, hσ, rfl⟩
    · intro σ hσ
      have hm : σ ∈ conjugate e '' (fiberPerms ρ : Set (Equiv.Perm X)) := by
        rw [h]; exact hσ
      obtain ⟨τ, hτ, hτσ⟩ := hm
      have he : conjugate e.symm σ = τ := by
        rw [← hτσ]
        ext x
        simp [conjugate, Equiv.Perm.mul_apply]
      rw [he]
      exact hτ

/-- The time-family form of Proposition S1. A two-sided flow supplies this inverse law;
no continuity or differentiability is needed for the set-level argument. -/
theorem flow_closure_iff_normalizes {T : Type*} [AddGroup T]
    (ρ : X → Q) (hρ : Function.Surjective ρ) (Ψ : T → Equiv.Perm X)
    (hinv : ∀ t, Ψ (-t) = (Ψ t).symm) :
    (∀ t, Closed ρ (Ψ t)) ↔ ∀ t, Normalizes ρ (Ψ t) := by
  constructor
  · intro h t
    apply (closure_both_iff_normalizes ρ hρ (Ψ t)).mp
    refine ⟨h t, ?_⟩
    rw [← hinv]
    exact h (-t)
  · intro h t
    exact ((closure_both_iff_normalizes ρ hρ (Ψ t)).mpr (h t)).1

/-- A closed update preserves equivalence even when it is not invertible. -/
theorem Closed.preserves {ρ : X → Q} {f : X → X} (hf : Closed ρ f)
    {x y : X} (hxy : ρ x = ρ y) : ρ (f x) = ρ (f y) := by
  obtain ⟨g, hg⟩ := hf
  rw [hg x, hg y, hxy]

/-- Closed operations remain closed under composition. -/
theorem closed_composition {ρ : X → Q} {f g : X → X}
    (hf : Closed ρ f) (hg : Closed ρ g) : Closed ρ (g ∘ f) := by
  obtain ⟨fQ, hfQ⟩ := hf
  obtain ⟨gQ, hgQ⟩ := hg
  refine ⟨gQ ∘ fQ, fun x => ?_⟩
  change ρ (g (f x)) = gQ (fQ (ρ x))
  rw [hgQ, hfQ]

/-- The declared reduced operations compose in the same order as their source operations. -/
theorem reduced_composition (ρ : X → Q) (f g : X → X) (fQ gQ : Q → Q)
    (hf : ∀ x, ρ (f x) = fQ (ρ x)) (hg : ∀ x, ρ (g x) = gQ (ρ x))
    (x : X) : ρ ((g ∘ f) x) = (gQ ∘ fQ) (ρ x) := by
  change ρ (g (f x)) = gQ (fQ (ρ x))
  rw [hg, hf]

/-- Exact closure holds at every ordinary finite iterate. -/
theorem reduced_iterates (ρ : X → Q) (f : X → X) (g : Q → Q)
    (h : ∀ x, ρ (f x) = g (ρ x)) (n : Nat) (x : X) :
    ρ ((f^[n]) x) = (g^[n]) (ρ x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h, ih]

/-- Existence of a reduced iterate follows from closure of one update. -/
theorem closed_iterates {ρ : X → Q} {f : X → X} (hf : Closed ρ f)
    (n : Nat) : Closed ρ (f^[n]) := by
  obtain ⟨g, hg⟩ := hf
  exact ⟨g^[n], reduced_iterates ρ f g hg n⟩

/-- Two-sided closure preserves and reflects macrostate equivalence. -/
theorem same_macrostate_iff (ρ : X → Q) (e : Equiv.Perm X)
    (hf : Closed ρ e) (hi : Closed ρ e.symm) (x y : X) :
    ρ (e x) = ρ (e y) ↔ ρ x = ρ y := by
  constructor
  · intro h
    simpa using hi.preserves h
  · exact hf.preserves

/-- A set-level indicator on a pair of states, with no smoothness assumption. -/
noncomputable def equivalenceIndicator (ρ : X → Q) (x y : X) : Nat := by
  classical
  exact if ρ x = ρ y then 1 else 0

/-- The equivalence indicator is conserved when both states follow a two-sided closed update. -/
theorem equivalence_indicator_conserved (ρ : X → Q) (e : Equiv.Perm X)
    (hf : Closed ρ e) (hi : Closed ρ e.symm) (x y : X) :
    equivalenceIndicator ρ (e x) (e y) = equivalenceIndicator ρ x y := by
  classical
  simp only [equivalenceIndicator, same_macrostate_iff ρ e hf hi x y]

/-- For an onto state map, forward closure is equivalent to nondecrease of the
same-macrostate indicator along paired updates. Different classes may merge. -/
theorem closed_iff_indicator_nondecreasing (ρ : X → Q)
    (hρ : Function.Surjective ρ) (f : X → X) :
    Closed ρ f ↔ ∀ x y,
      equivalenceIndicator ρ x y ≤ equivalenceIndicator ρ (f x) (f y) := by
  classical
  constructor
  · intro hf x y
    by_cases hxy : ρ x = ρ y
    · simp [equivalenceIndicator, hxy, hf.preserves hxy]
    · simp [equivalenceIndicator, hxy]
  · intro h
    apply (closure_iff_fiber_constant ρ hρ f).mpr
    intro x y hxy
    change ρ (f x) = ρ (f y)
    by_contra hne
    have hi := h x y
    simp [equivalenceIndicator, hxy, hne] at hi

/-- For an onto state map and a bijective update, closure in both directions
is equivalent to conservation of the same-macrostate indicator on pairs. -/
theorem closed_both_iff_indicator_conserved (ρ : X → Q)
    (hρ : Function.Surjective ρ) (e : Equiv.Perm X) :
    (Closed ρ e ∧ Closed ρ e.symm) ↔ ∀ x y,
      equivalenceIndicator ρ (e x) (e y) = equivalenceIndicator ρ x y := by
  constructor
  · rintro ⟨hf, hi⟩ x y
    exact equivalence_indicator_conserved ρ e hf hi x y
  · intro h
    constructor
    · apply (closed_iff_indicator_nondecreasing ρ hρ e).mpr
      intro x y
      exact le_of_eq (h x y).symm
    · apply (closed_iff_indicator_nondecreasing ρ hρ e.symm).mpr
      intro x y
      have hi := h (e.symm x) (e.symm y)
      simpa using le_of_eq hi

/-- The discrete-time equivalence relation is invariant at every finite iterate. -/
theorem same_macrostate_iterate_iff (ρ : X → Q) (e : Equiv.Perm X)
    (hf : Closed ρ e) (hi : Closed ρ e.symm) (n : Nat) (x y : X) :
    ρ ((e^[n]) x) = ρ ((e^[n]) y) ↔ ρ x = ρ y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      same_macrostate_iff ρ e hf hi, ih]

/-- A globally invertible closed flow conserves the indicator of same-macrostate membership. -/
theorem flow_equivalence_indicator_conserved {T : Type*} [AddGroup T]
    (ρ : X → Q) (Ψ : T → Equiv.Perm X)
    (hinv : ∀ t, Ψ (-t) = (Ψ t).symm) (hclosed : ∀ t, Closed ρ (Ψ t))
    (t : T) (x y : X) :
    equivalenceIndicator ρ (Ψ t x) (Ψ t y) = equivalenceIndicator ρ x y := by
  apply equivalence_indicator_conserved ρ (Ψ t) (hclosed t)
  rw [← hinv]
  exact hclosed (-t)

section OrbitQuotient

variable {G : Type*} [Group G] [MulAction G X]

/-- An equivariant map preserves the group-orbit equivalence relation. -/
theorem equivariant_preserves_orbits (f : X → X)
    (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)
    {x y : X} (hxy : MulAction.orbitRel G X x y) :
    MulAction.orbitRel G X (f x) (f y) := by
  obtain ⟨g, hg⟩ := hxy
  change g • y = x at hg
  refine ⟨g, ?_⟩
  change g • f y = f x
  rw [← hf, hg]

/-- The induced update on the actual abstract orbit quotient, without choosing representatives. -/
def orbitUpdate (f : X → X)
    (hf : ∀ (g : G) (x : X), f (g • x) = g • f x) :
    Quotient (MulAction.orbitRel G X) → Quotient (MulAction.orbitRel G X) :=
  Quotient.map f (fun _ _ h => equivariant_preserves_orbits f hf h)

/-- WP0215 Proposition S2 for arbitrary groups and arbitrary state spaces. -/
theorem symmetry_quotient (f : X → X)
    (hf : ∀ (g : G) (x : X), f (g • x) = g • f x) :
    Closed (Quotient.mk (MulAction.orbitRel G X)) f := by
  exact ⟨orbitUpdate f hf, fun _ => rfl⟩

/-- The orbit-quotient transition is independent of the representative. -/
theorem orbit_update_commutes (f : X → X)
    (hf : ∀ (g : G) (x : X), f (g • x) = g • f x) (x : X) :
    Quotient.mk (MulAction.orbitRel G X) (f x) =
      orbitUpdate f hf (Quotient.mk (MulAction.orbitRel G X) x) := rfl

end OrbitQuotient

end KTAIT.ClosureInvariance
