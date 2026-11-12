/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude)
-/
import KTAIT.ClosureInvariance

/-!
# Symmetry quotients, reversibility, and what a symmetry removes (WP0255)

Set-level counterparts of WP0255, *Coarse Graining, Symmetry, and Conservation*,
Sections 2 to 4. Conservation of the co-membership indicator is forward closure
with an injective reduced update, whether or not the microscopic update is
invertible; for a bijective update it is closure of the update and of its
inverse, with a bijective reduced update. A group action commuting with a
bijective update commutes with its inverse, so its orbit quotient is closed in
both directions and its reduced update is injective. A symmetry that fixes
every macrostate induces the identity on the quotient; one that carries fibers
onto fibers normalizes the relabeling group and descends to a map that
commutes with the reduced update. An orbit of a finite group is no larger than
the group, and a commuting update carries fixed points to fixed points. For the
trivial partition, a transitive commuting group forces equal return-time sets;
the converse construction is not formalized here.

No finiteness beyond the stated one, no smoothness, and no physical-realization
assumption enters; those are separate requirements when applying these results.
-/

namespace KTAIT.ClosureSymmetry

open KTAIT.ClosureInvariance

variable {X Q : Type*}

/-- Forward closure with an injective reduced update: distinct macrostates stay distinct. -/
def ClosedInjective (ρ : X → Q) (f : X → X) : Prop :=
  ∃ g : Q → Q, (∀ x, ρ (f x) = g (ρ x)) ∧ Function.Injective g

/-- WP0255 co-membership lemma, conservation clause. For an onto state map, the co-membership
indicator is conserved exactly when the update is forward closed with an injective
reduced update. The microscopic update need not be invertible. -/
theorem indicator_conserved_iff_closed_injective (ρ : X → Q)
    (hρ : Function.Surjective ρ) (f : X → X) :
    (∀ x y, equivalenceIndicator ρ (f x) (f y) = equivalenceIndicator ρ x y) ↔
      ClosedInjective ρ f := by
  classical
  constructor
  · intro h
    have hc : Closed ρ f := by
      apply (closed_iff_indicator_nondecreasing ρ hρ f).mpr
      intro x y
      exact le_of_eq (h x y).symm
    obtain ⟨g, hg⟩ := hc
    refine ⟨g, hg, ?_⟩
    intro q q' hqq'
    obtain ⟨x, rfl⟩ := hρ q
    obtain ⟨y, rfl⟩ := hρ q'
    have hxy : ρ (f x) = ρ (f y) := by rw [hg x, hg y, hqq']
    have hi := h x y
    by_contra hne
    simp [equivalenceIndicator, hxy, hne] at hi
  · rintro ⟨g, hg, hinj⟩ x y
    have hiff : ρ (f x) = ρ (f y) ↔ ρ x = ρ y := by
      rw [hg x, hg y]
      exact hinj.eq_iff
    simp only [equivalenceIndicator, hiff]

/-- WP0255 co-membership lemma, bijective clause. For a bijective update, conservation of the
indicator is closure of the update and of its inverse, which is forward closure with an
injective reduced update. -/
theorem closed_both_iff_closed_injective (ρ : X → Q) (hρ : Function.Surjective ρ)
    (e : Equiv.Perm X) :
    (Closed ρ e ∧ Closed ρ e.symm) ↔ ClosedInjective ρ e := by
  rw [closed_both_iff_indicator_conserved ρ hρ e]
  exact indicator_conserved_iff_closed_injective ρ hρ e

/-- The reduced update of a two-sided closed bijection is a bijection of macrostates, and
it reduces the inverse update to the inverse reduced update. -/
theorem reduced_bijective_of_closed_both (ρ : X → Q) (hρ : Function.Surjective ρ)
    (e : Equiv.Perm X) (hf : Closed ρ e) (hi : Closed ρ e.symm) :
    ∃ g : Q → Q, (∀ x, ρ (e x) = g (ρ x)) ∧ Function.Bijective g ∧
      ∀ x, g (ρ (e.symm x)) = ρ x := by
  obtain ⟨g, hg, hinj⟩ := (closed_both_iff_closed_injective ρ hρ e).mp ⟨hf, hi⟩
  have hsymm : ∀ x, g (ρ (e.symm x)) = ρ x := by
    intro x
    rw [← hg, Equiv.apply_symm_apply]
  refine ⟨g, hg, ⟨hinj, ?_⟩, hsymm⟩
  intro q
  obtain ⟨x, rfl⟩ := hρ q
  exact ⟨ρ (e.symm x), hsymm x⟩

/-- The partition to a single macrostate is closed under every update. -/
theorem trivial_partition_closed (f : X → X) : Closed (fun _ : X => ()) f :=
  ⟨id, fun _ => rfl⟩

/-- WP0255 two-positions proposition, part (a): a symmetry that fixes every macrostate induces the identity
on the macrostates. -/
theorem fiberPerm_induces_id (ρ : X → Q) (σ : Equiv.Perm X) (hσ : σ ∈ fiberPerms ρ)
    (x : X) : ρ (σ x) = ρ x :=
  hσ x

/-- WP0255 two-positions proposition, part (b), first clause: a bijection carries fibers onto fibers exactly
when it normalizes the relabeling group. -/
theorem maps_fibers_iff_normalizes (ρ : X → Q) (hρ : Function.Surjective ρ)
    (g : Equiv.Perm X) :
    (∀ x y, ρ (g x) = ρ (g y) ↔ ρ x = ρ y) ↔ Normalizes ρ g := by
  rw [← closure_both_iff_normalizes ρ hρ g]
  constructor
  · intro h
    constructor
    · apply (closure_iff_fiber_constant ρ hρ g).mpr
      intro x y hxy
      change ρ (g x) = ρ (g y)
      exact (h x y).mpr hxy
    · apply (closure_iff_fiber_constant ρ hρ g.symm).mpr
      intro x y hxy
      change ρ (g.symm x) = ρ (g.symm y)
      apply (h (g.symm x) (g.symm y)).mp
      simpa using hxy
  · rintro ⟨hf, hi⟩ x y
    exact same_macrostate_iff ρ g hf hi x y

/-- WP0255 two-positions proposition, part (b), second clause: a symmetry that carries fibers onto fibers
descends to a map of macrostates that commutes with the reduced update. -/
theorem descended_commutes (ρ : X → Q) (hρ : Function.Surjective ρ)
    (f g : X → X) (fQ gQ : Q → Q)
    (hf : ∀ x, ρ (f x) = fQ (ρ x)) (hg : ∀ x, ρ (g x) = gQ (ρ x))
    (hcomm : ∀ x, g (f x) = f (g x)) (q : Q) : fQ (gQ q) = gQ (fQ q) := by
  obtain ⟨x, rfl⟩ := hρ q
  rw [← hg x, ← hf (g x), ← hcomm x, hg (f x), hf x]

section OrbitQuotient

variable {G : Type*} [Group G] [MulAction G X]

/-- The orbit map is onto. -/
theorem orbit_mk_surjective :
    Function.Surjective (Quotient.mk (MulAction.orbitRel G X)) :=
  fun q => Quotient.inductionOn q (fun x => ⟨x, rfl⟩)

/-- A fiber of the orbit map is an orbit. -/
theorem orbit_mk_eq_iff (x y : X) :
    Quotient.mk (MulAction.orbitRel G X) y = Quotient.mk (MulAction.orbitRel G X) x ↔
      y ∈ MulAction.orbit G x := by
  rw [Quotient.eq]
  exact MulAction.orbitRel_apply

/-- A group action commuting with a bijection commutes with its inverse. -/
theorem equivariant_symm (e : Equiv.Perm X)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) (g : G) (x : X) :
    e.symm (g • x) = g • e.symm x := by
  apply e.injective
  rw [Equiv.apply_symm_apply, he, Equiv.apply_symm_apply]

/-- WP0255 two-sided corollary: the orbit quotient of an equivariant bijection is closed in both
time directions. -/
theorem symmetry_quotient_both (e : Equiv.Perm X)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    Closed (Quotient.mk (MulAction.orbitRel G X)) e ∧
      Closed (Quotient.mk (MulAction.orbitRel G X)) e.symm :=
  ⟨symmetry_quotient (G := G) e he,
    symmetry_quotient (G := G) e.symm (equivariant_symm e he)⟩

/-- The orbit indicator of an equivariant bijection is conserved. -/
theorem symmetry_quotient_indicator_conserved (e : Equiv.Perm X)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) (x y : X) :
    equivalenceIndicator (Quotient.mk (MulAction.orbitRel G X)) (e x) (e y) =
      equivalenceIndicator (Quotient.mk (MulAction.orbitRel G X)) x y :=
  equivalence_indicator_conserved _ e (symmetry_quotient_both e he).1
    (symmetry_quotient_both e he).2 x y

/-- The reduced update of a symmetry quotient of a bijection is injective. A forward-closed
partition of invertible dynamics whose reduced update merges classes is therefore not an
orbit quotient by a commuting group. -/
theorem symmetry_quotient_reduced_injective (e : Equiv.Perm X)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    ClosedInjective (Quotient.mk (MulAction.orbitRel G X)) e :=
  (closed_both_iff_closed_injective _ orbit_mk_surjective e).mp (symmetry_quotient_both e he)

/-- WP0255 labels-and-dimensions proposition, part (a), set level: an orbit of a finite group, which is a fiber of the
orbit map, has at most as many points as the group. -/
theorem card_orbit_le_card_group [Finite G] (x : X) :
    Nat.card (MulAction.orbit G x) ≤ Nat.card G := by
  have hs : Function.Surjective
      (fun g : G => (⟨g • x, MulAction.mem_orbit x g⟩ : MulAction.orbit G x)) := by
    rintro ⟨y, hy⟩
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    exact ⟨g, rfl⟩
  exact Nat.card_le_card_of_surjective _ hs

/-- WP0255 labels-and-dimensions proposition, part (c): a commuting update carries fixed points of the action to
fixed points. -/
theorem fixedPoints_invariant (f : X → X)
    (hf : ∀ (g : G) (x : X), f (g • x) = g • f x) {x : X}
    (hx : x ∈ MulAction.fixedPoints G X) : f x ∈ MulAction.fixedPoints G X := by
  rw [MulAction.mem_fixedPoints] at hx ⊢
  intro g
  rw [← hf, hx g]

end OrbitQuotient

section ReturnTimes

/-- Return times of a state under a bijective update. -/
def returnTimes (e : Equiv.Perm X) (x : X) : Set ℤ := {n | (e ^ n) x = x}

/-- Powers of the update pass through a commuting bijection. -/
theorem zpow_apply_comm (e g : Equiv.Perm X) (hc : Commute e g) (n : ℤ) (x : X) :
    (e ^ n) (g x) = g ((e ^ n) x) := by
  have h := (hc.zpow_left n).eq
  rw [← Equiv.Perm.mul_apply, h, Equiv.Perm.mul_apply]

/-- A bijection commuting with the update preserves return times. -/
theorem returnTimes_eq_of_commute (e g : Equiv.Perm X) (hc : Commute e g) (x : X) :
    returnTimes e (g x) = returnTimes e x := by
  ext n
  simp only [returnTimes, Set.mem_setOf_eq, zpow_apply_comm e g hc n x]
  exact g.injective.eq_iff

/-- WP0255 trivial-partition proposition, necessity: if a group of bijections commuting with the update is
transitive on the state space, every state has the same return times. -/
theorem returnTimes_const_of_transitive (e : Equiv.Perm X) (H : Subgroup (Equiv.Perm X))
    (hcomm : ∀ g ∈ H, Commute e g) (htrans : ∀ x y : X, ∃ g ∈ H, g x = y) (x y : X) :
    returnTimes e x = returnTimes e y := by
  obtain ⟨g, hg, rfl⟩ := htrans x y
  exact (returnTimes_eq_of_commute e g (hcomm g hg) x).symm

end ReturnTimes

end KTAIT.ClosureSymmetry
