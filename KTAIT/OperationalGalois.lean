/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude)
-/
import KTAIT.ClosureInvariance

/-!
# Galois connections for program equivalence (WP0004, Section 4)

Set-level counterparts of WP0004, *Computation as Algebras of Operations*, Sections
4.2 to 4.4. Descriptions form a type `P` with a semantic map `D : P → F`. The
function-preserving permutations `Γ_D` are the fiber permutations of `D`, reused from
`ClosureInvariance`. A subgroup `H` of `Γ_D` induces its orbit equivalence `E_H`; an
equivalence `E` refining `ker D` has its class-preserving group `Stab(E)`, the members
of `Γ_D` that fix every class of `E`. The two assignments form a Galois connection,
`Stab` recovers every equivalence refining `ker D` (a transposition of two equivalent
descriptions lies in `Stab(E)`), the composite `H ↦ Stab(E_H)` is a closure operator
on subgroups, and its fixed subgroups correspond exactly to the equivalences refining
`ker D`. The same adjunction holds relative to a supplied ambient group.

An extractor `S : P → T` gives the structural group `Γ_Σ = Stab(ker S)`; a forgetting
map between extractors orders kernels and structural groups; invariance of `S` under
`H` places `E_H` below `ker S`, with equality exactly when `S` separates `H`-orbits.

For a family of one-hole contexts, contextual congruences, the congruence generated
by a set of rewrite pairs, the rule set of a congruence, their adjunction and fixed
points, and the contextual kernel of an extractor as the greatest contextual
congruence below its kernel are stated for an arbitrary context family; the kernel
result needs the identity context and closure under composition. The inversion
automorphism of `ZMod 4` relates `1` and `3` while the context `a ↦ a + 1` sends them
to `2` and `0`, which are unrelated, so an orbit equivalence of automorphisms need not
be a congruence.

No finiteness, computability, or effectiveness assumption enters; the permutations
are set-theoretic bijections, as in the paper.
-/

namespace KTAIT.OperationalGalois

open KTAIT.ClosureInvariance

variable {P F : Type*}

/-! ### Section 4.2: the orbit--class-preserver correspondence -/

/-- `Γ_D`, Eq. (program-group): permutations of descriptions preserving the computed
function. This is `fiberPerms D` from `ClosureInvariance`. -/
abbrev functionGroup (D : P → F) : Subgroup (Equiv.Perm P) := fiberPerms D

theorem mem_functionGroup {D : P → F} {γ : Equiv.Perm P} :
    γ ∈ functionGroup D ↔ ∀ p, D (γ p) = D p := Iff.rfl

/-- `E_H`, Eq. (orbit): `p` and `q` are related when some member of `H` carries `p` to `q`. -/
def orbitRel (H : Subgroup (Equiv.Perm P)) : Setoid P where
  r p q := ∃ γ ∈ H, γ p = q
  iseqv :=
    { refl := fun p => ⟨1, H.one_mem, rfl⟩
      symm := by
        rintro p q ⟨γ, hγ, rfl⟩
        exact ⟨γ⁻¹, H.inv_mem hγ, by simp⟩
      trans := by
        rintro p q r ⟨γ, hγ, rfl⟩ ⟨δ, hδ, rfl⟩
        exact ⟨δ * γ, H.mul_mem hδ hγ, by simp⟩ }

theorem orbitRel_apply {H : Subgroup (Equiv.Perm P)} {p q : P} :
    orbitRel H p q ↔ ∃ γ ∈ H, γ p = q := Iff.rfl

/-- A larger transformation group identifies more descriptions. -/
theorem orbitRel_mono {H H' : Subgroup (Equiv.Perm P)} (h : H ≤ H') :
    orbitRel H ≤ orbitRel H' := by
  rw [Setoid.le_def]
  rintro p q ⟨γ, hγ, rfl⟩
  exact ⟨γ, h hγ, rfl⟩

/-- Orbits of function-preserving transformations refine the semantic kernel. -/
theorem orbitRel_le_ker (D : P → F) (H : Subgroup (Equiv.Perm P))
    (hH : H ≤ functionGroup D) : orbitRel H ≤ Setoid.ker D := by
  rw [Setoid.le_def]
  rintro p q ⟨γ, hγ, rfl⟩
  exact Setoid.ker_def.2 ((hH hγ) p).symm

/-- `Stab(E)`, Eq. (class-group): members of `Γ_D` carrying every description to an
`E`-equivalent description. Each class is preserved individually. -/
def classGroup (D : P → F) (E : Setoid P) : Subgroup (Equiv.Perm P) where
  carrier := {γ | γ ∈ functionGroup D ∧ ∀ p, E p (γ p)}
  one_mem' := ⟨(functionGroup D).one_mem, fun p => E.refl' p⟩
  mul_mem' := by
    rintro γ δ ⟨hγ, hγE⟩ ⟨hδ, hδE⟩
    refine ⟨(functionGroup D).mul_mem hγ hδ, fun p => ?_⟩
    change E p (γ (δ p))
    exact E.trans' (hδE p) (hγE (δ p))
  inv_mem' := by
    rintro γ ⟨hγ, hγE⟩
    refine ⟨(functionGroup D).inv_mem hγ, fun p => ?_⟩
    have h := hγE (γ⁻¹ p)
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h
    exact E.symm' h

theorem mem_classGroup {D : P → F} {E : Setoid P} {γ : Equiv.Perm P} :
    γ ∈ classGroup D E ↔ γ ∈ functionGroup D ∧ ∀ p, E p (γ p) := Iff.rfl

theorem classGroup_le_functionGroup (D : P → F) (E : Setoid P) :
    classGroup D E ≤ functionGroup D := fun _ hγ => hγ.1

/-- For an equivalence refining `ker D`, membership in `Γ_D` is automatic. -/
theorem mem_classGroup_of_le_ker {D : P → F} {E : Setoid P} (hE : E ≤ Setoid.ker D)
    {γ : Equiv.Perm P} : γ ∈ classGroup D E ↔ ∀ p, E p (γ p) := by
  refine ⟨fun h => h.2, fun h => ⟨fun p => ?_, h⟩⟩
  exact (Setoid.ker_def.1 (Setoid.le_def.1 hE (h p))).symm

/-- A finer equivalence has a smaller class-preserving group. -/
theorem classGroup_mono (D : P → F) {E E' : Setoid P} (h : E ≤ E') :
    classGroup D E ≤ classGroup D E' :=
  fun _ hγ => ⟨hγ.1, fun p => Setoid.le_def.1 h (hγ.2 p)⟩

/-- WP0004 Proposition (Orbit--class-preserver adjunction), Eq. (galois): for
`H ≤ Γ_D`, `E_H ⊆ E` exactly when `H ⊆ Stab(E)`. -/
theorem orbitRel_le_iff_le_classGroup (D : P → F) {H : Subgroup (Equiv.Perm P)}
    (hH : H ≤ functionGroup D) (E : Setoid P) :
    orbitRel H ≤ E ↔ H ≤ classGroup D E := by
  constructor
  · intro h γ hγ
    exact ⟨hH hγ, fun p => Setoid.le_def.1 h ⟨γ, hγ, rfl⟩⟩
  · intro h
    rw [Setoid.le_def]
    rintro p q ⟨γ, hγ, rfl⟩
    exact (h hγ).2 p

/-- The transposition of two `E`-equivalent descriptions, fixing all others, lies in
`Stab(E)` when `E` refines `ker D`. -/
theorem swap_mem_classGroup [DecidableEq P] (D : P → F) {E : Setoid P}
    (hE : E ≤ Setoid.ker D) {p q : P} (hpq : E p q) :
    Equiv.swap p q ∈ classGroup D E := by
  rw [mem_classGroup_of_le_ker hE]
  intro z
  by_cases hz : z = p
  · subst hz
    simpa using hpq
  · by_cases hz' : z = q
    · subst hz'
      simpa using E.symm' hpq
    · simp [Equiv.swap_apply_of_ne_of_ne hz hz']

/-- WP0004 Proposition (Orbit--class-preserver adjunction), second assertion: the
class-preserving group recovers every equivalence refining `ker D`. -/
theorem orbitRel_classGroup (D : P → F) (E : Setoid P) (hE : E ≤ Setoid.ker D) :
    orbitRel (classGroup D E) = E := by
  classical
  apply le_antisymm
  · rw [Setoid.le_def]
    rintro p q ⟨γ, hγ, rfl⟩
    exact hγ.2 p
  · rw [Setoid.le_def]
    intro p q hpq
    exact ⟨Equiv.swap p q, swap_mem_classGroup D hE hpq, Equiv.swap_apply_left p q⟩

/-- The saturation `H ↦ Stab(E_H)`: all permutations acting within the orbits of `H`. -/
def saturate (D : P → F) (H : Subgroup (Equiv.Perm P)) : Subgroup (Equiv.Perm P) :=
  classGroup D (orbitRel H)

/-- Saturation is extensive on subgroups of `Γ_D`. -/
theorem le_saturate (D : P → F) {H : Subgroup (Equiv.Perm P)} (hH : H ≤ functionGroup D) :
    H ≤ saturate D H :=
  (orbitRel_le_iff_le_classGroup D hH (orbitRel H)).1 le_rfl

/-- Saturation is monotone. -/
theorem saturate_mono (D : P → F) {H H' : Subgroup (Equiv.Perm P)} (h : H ≤ H') :
    saturate D H ≤ saturate D H' :=
  classGroup_mono D (orbitRel_mono h)

/-- Saturation is idempotent on subgroups of `Γ_D`. -/
theorem saturate_saturate (D : P → F) {H : Subgroup (Equiv.Perm P)}
    (hH : H ≤ functionGroup D) : saturate D (saturate D H) = saturate D H := by
  unfold saturate
  rw [orbitRel_classGroup D (orbitRel H) (orbitRel_le_ker D H hH)]

/-- WP0004 Proposition (Orbit--class-preserver adjunction), last assertion: the fixed
subgroups of saturation inside `Γ_D` correspond exactly to the equivalences refining
`ker D`, by `H ↦ E_H` and `E ↦ Stab(E)`. -/
def restrictedEquiv (D : P → F) :
    {H : Subgroup (Equiv.Perm P) // H ≤ functionGroup D ∧ saturate D H = H} ≃
      {E : Setoid P // E ≤ Setoid.ker D} where
  toFun H := ⟨orbitRel H.1, orbitRel_le_ker D H.1 H.2.1⟩
  invFun E := ⟨classGroup D E.1, classGroup_le_functionGroup D E.1, by
    change classGroup D (orbitRel (classGroup D E.1)) = classGroup D E.1
    rw [orbitRel_classGroup D E.1 E.2]⟩
  left_inv H := Subtype.ext H.2.2
  right_inv E := Subtype.ext (orbitRel_classGroup D E.1 E.2)

/-- The class-preserving group of an equivalence refining `ker D` is a fixed subgroup. -/
theorem saturate_classGroup (D : P → F) (E : Setoid P) (hE : E ≤ Setoid.ker D) :
    saturate D (classGroup D E) = classGroup D E := by
  change classGroup D (orbitRel (classGroup D E)) = classGroup D E
  rw [orbitRel_classGroup D E hE]

/-- A fixed subgroup is the class-preserving group of its own orbit equivalence. -/
theorem fixed_eq_classGroup {D : P → F} {H : Subgroup (Equiv.Perm P)}
    (hH : saturate D H = H) : classGroup D (orbitRel H) = H := hH

/-- On fixed subgroups, inclusion of groups is inclusion of orbit equivalences, so the
correspondence of `restrictedEquiv` preserves the inclusion orders on both sides. -/
theorem fixed_le_iff (D : P → F) {H H' : Subgroup (Equiv.Perm P)}
    (hH : H ≤ functionGroup D) (hH' : saturate D H' = H') :
    H ≤ H' ↔ orbitRel H ≤ orbitRel H' := by
  rw [orbitRel_le_iff_le_classGroup D hH (orbitRel H'), fixed_eq_classGroup hH']

/-- With the ambient group restricted to a supplied `Γ₀ ≤ Γ_D`, the adjunction holds for
the relative class-preserver `Stab(E) ⊓ Γ₀`. -/
theorem orbitRel_le_iff_le_relative (D : P → F) {Γ₀ H : Subgroup (Equiv.Perm P)}
    (hΓ₀ : Γ₀ ≤ functionGroup D) (hH : H ≤ Γ₀) (E : Setoid P) :
    orbitRel H ≤ E ↔ H ≤ classGroup D E ⊓ Γ₀ := by
  rw [le_inf_iff, orbitRel_le_iff_le_classGroup D (hH.trans hΓ₀) E]
  exact ⟨fun h => ⟨h, hH⟩, fun h => h.1⟩

/-- The relative class-preserver recovers at most `E`; `relative_recovery_strict` below shows
that it can recover strictly less. -/
theorem orbitRel_relative_le (D : P → F) (Γ₀ : Subgroup (Equiv.Perm P)) (E : Setoid P) :
    orbitRel (classGroup D E ⊓ Γ₀) ≤ E := by
  rw [Setoid.le_def]
  rintro p q ⟨γ, hγ, rfl⟩
  exact (Subgroup.mem_inf.1 hγ).1.2 p

/-! ### Section 4.3: extracted structure as intermediate universes -/

section Extraction

variable {T T' : Type*}

/-- `Γ_Σ`, Eq. (structural-program-group): function-preserving transformations that also
preserve the extracted structure `S`. -/
def structuralGroup (D : P → F) (S : P → T) : Subgroup (Equiv.Perm P) where
  carrier := {γ | γ ∈ functionGroup D ∧ ∀ p, S (γ p) = S p}
  one_mem' := ⟨(functionGroup D).one_mem, fun _ => rfl⟩
  mul_mem' := by
    rintro γ δ ⟨hγ, hγS⟩ ⟨hδ, hδS⟩
    refine ⟨(functionGroup D).mul_mem hγ hδ, fun p => ?_⟩
    change S (γ (δ p)) = S p
    rw [hγS, hδS]
  inv_mem' := by
    rintro γ ⟨hγ, hγS⟩
    refine ⟨(functionGroup D).inv_mem hγ, fun p => ?_⟩
    have h := hγS (γ⁻¹ p)
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h
    exact h.symm

/-- Eq. (structural-program-group): `Γ_Σ = Stab(E_Σ)` with `E_Σ = ker S`. -/
theorem structuralGroup_eq_classGroup (D : P → F) (S : P → T) :
    structuralGroup D S = classGroup D (Setoid.ker S) := by
  ext γ
  change (γ ∈ functionGroup D ∧ ∀ p, S (γ p) = S p) ↔
    (γ ∈ functionGroup D ∧ ∀ p, Setoid.ker S p (γ p))
  simp only [Setoid.ker_def]
  exact and_congr_right fun _ => forall_congr' fun _ => eq_comm

/-- Eq. (extractor-equivalence): an extractor that records `D` has a kernel refining
`ker D`. -/
theorem ker_pair_le_ker (D : P → F) (A : P → T) :
    Setoid.ker (fun p => (D p, A p)) ≤ Setoid.ker D := by
  rw [Setoid.le_def]
  intro p q h
  rw [Setoid.ker_def] at h ⊢
  exact (Prod.mk.inj h).1

/-- Eq. (hierarchy-galois): when a richer extractor forgets to a poorer one through `J`,
the richer kernel is finer and its structural group is smaller. -/
theorem forget_le (D : P → F) (S : P → T) (S' : P → T') (J : T' → T)
    (hJ : ∀ p, S p = J (S' p)) :
    Setoid.ker S' ≤ Setoid.ker S ∧ structuralGroup D S' ≤ structuralGroup D S := by
  have hker : Setoid.ker S' ≤ Setoid.ker S := by
    rw [Setoid.le_def]
    intro p q h
    rw [Setoid.ker_def] at h ⊢
    rw [hJ p, hJ q, h]
  refine ⟨hker, ?_⟩
  rw [structuralGroup_eq_classGroup, structuralGroup_eq_classGroup]
  exact classGroup_mono D hker

/-- The extractor is invariant under a transformation group. -/
def Invariant (H : Subgroup (Equiv.Perm P)) (S : P → T) : Prop :=
  ∀ γ ∈ H, ∀ p, S (γ p) = S p

/-- WP0004 Proposition (Completeness relative to supplied transformations), first part:
invariance gives `E_H ⊆ E_Σ`. -/
theorem orbitRel_le_ker_of_invariant {H : Subgroup (Equiv.Perm P)} {S : P → T}
    (h : Invariant H S) : orbitRel H ≤ Setoid.ker S := by
  rw [Setoid.le_def]
  rintro p q ⟨γ, hγ, rfl⟩
  exact Setoid.ker_def.2 (h γ hγ p).symm

/-- WP0004 Proposition (Completeness relative to supplied transformations), second part:
under invariance, `E_H = E_Σ` exactly when equal extractor values lie in one `H`-orbit. -/
theorem orbitRel_eq_ker_iff {H : Subgroup (Equiv.Perm P)} {S : P → T}
    (h : Invariant H S) :
    orbitRel H = Setoid.ker S ↔ ∀ p q, S p = S q → orbitRel H p q := by
  constructor
  · intro heq p q hpq
    rw [heq]
    exact Setoid.ker_def.2 hpq
  · intro hsep
    apply le_antisymm (orbitRel_le_ker_of_invariant h)
    rw [Setoid.le_def]
    intro p q hpq
    exact hsep p q (Setoid.ker_def.1 hpq)

end Extraction

/-! ### Section 4.4: contextual congruences -/

section Contexts

variable (Ctx : Set (P → P))

/-- Eq. (congruence): an equivalence respected by every admitted one-hole context. -/
def IsCongruence (E : Setoid P) : Prop :=
  ∀ C ∈ Ctx, ∀ p q, E p q → E (C p) (C q)

/-- `Cg(S)`: the least contextual congruence containing the rewrite pairs `S`, as the
intersection of all contextual congruences containing them. -/
def generated (S : Set (P × P)) : Setoid P where
  r p q := ∀ E : Setoid P, IsCongruence Ctx E → (∀ x ∈ S, E x.1 x.2) → E p q
  iseqv :=
    { refl := fun p E _ _ => E.refl' p
      symm := fun h E hE hS => E.symm' (h E hE hS)
      trans := fun h₁ h₂ E hE hS => E.trans' (h₁ E hE hS) (h₂ E hE hS) }

theorem generated_isCongruence (S : Set (P × P)) : IsCongruence Ctx (generated Ctx S) :=
  fun C hC _ _ h E hE hS => hE C hC _ _ (h E hE hS)

theorem subset_generated (S : Set (P × P)) : ∀ x ∈ S, generated Ctx S x.1 x.2 :=
  fun x hx _ _ hS => hS x hx

theorem generated_le {S : Set (P × P)} {E : Setoid P} (hE : IsCongruence Ctx E)
    (hS : ∀ x ∈ S, E x.1 x.2) : generated Ctx S ≤ E := by
  rw [Setoid.le_def]
  intro p q h
  exact h E hE hS

/-- Equality is a contextual congruence for every context family. -/
theorem isCongruence_bot : IsCongruence Ctx (⊥ : Setoid P) := by
  intro C _ p q h
  simp only [Setoid.bot_def] at h ⊢
  rw [h]

/-- The total relation is a contextual congruence for every context family. -/
theorem isCongruence_top : IsCongruence Ctx (⊤ : Setoid P) := fun _ _ _ _ _ => trivial

/-- The empty rule set generates equality. -/
theorem generated_empty : generated Ctx (∅ : Set (P × P)) = ⊥ :=
  le_antisymm (generated_le Ctx (isCongruence_bot Ctx) (by simp)) bot_le

/-- `Rules(E) = E ∩ R`: the candidate rewrite pairs that a congruence validates. -/
def rules (R : Set (P × P)) (E : Setoid P) : Set (P × P) := {x ∈ R | E x.1 x.2}

/-- WP0004 Proposition (Rewrite--congruence adjunction), Eq. (rewrite-adjunction): for
`S ⊆ R` and a contextual congruence `E`, `Cg(S) ⊆ E` exactly when `S ⊆ Rules(E)`. -/
theorem generated_le_iff {R S : Set (P × P)} (hS : S ⊆ R) {E : Setoid P}
    (hE : IsCongruence Ctx E) : generated Ctx S ≤ E ↔ S ⊆ rules R E := by
  constructor
  · intro h x hx
    exact ⟨hS hx, Setoid.le_def.1 h (subset_generated Ctx S x hx)⟩
  · intro h
    exact generated_le Ctx hE fun x hx => (h hx).2

/-- WP0004 Proposition (Rewrite--congruence adjunction): a generated congruence is
recovered from its rule set. -/
theorem generated_rules_generated {R S : Set (P × P)} (hS : S ⊆ R) :
    generated Ctx (rules R (generated Ctx S)) = generated Ctx S := by
  apply le_antisymm
  · exact (generated_le_iff Ctx (fun _ hx => hx.1) (generated_isCongruence Ctx S)).2 le_rfl
  · exact generated_le Ctx (generated_isCongruence Ctx _) fun x hx =>
      subset_generated Ctx _ x ⟨hS hx, subset_generated Ctx S x hx⟩

/-- WP0004 Proposition (Rewrite--congruence adjunction): a rule set of a congruence is a
fixed point of `S ↦ Rules(Cg(S))`. -/
theorem rules_generated_rules (R : Set (P × P)) {E : Setoid P} (hE : IsCongruence Ctx E) :
    rules R (generated Ctx (rules R E)) = rules R E := by
  ext x
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, h E hE fun y hy => hy.2⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, subset_generated Ctx _ x ⟨hx, h⟩⟩

/-- When the semantics is compositional (`ker D` is a contextual congruence), sound rewrite
pairs generate a congruence refining `ker D`. -/
theorem generated_le_ker (D : P → F) (hD : IsCongruence Ctx (Setoid.ker D))
    {S : Set (P × P)} (hS : ∀ x ∈ S, D x.1 = D x.2) : generated Ctx S ≤ Setoid.ker D :=
  generated_le Ctx hD fun x hx => Setoid.ker_def.2 (hS x hx)

variable {T : Type*}

/-- `E^ctx_Σ`, Eq. (contextual-kernel): equal extracted structure in every admitted context. -/
def contextualKer (S : P → T) : Setoid P where
  r p q := ∀ C ∈ Ctx, S (C p) = S (C q)
  iseqv :=
    { refl := fun _ _ _ => rfl
      symm := fun h C hC => (h C hC).symm
      trans := fun h₁ h₂ C hC => (h₁ C hC).trans (h₂ C hC) }

/-- Under closure of the contexts under composition, the contextual kernel is a contextual
congruence. -/
theorem contextualKer_isCongruence (hcomp : ∀ C ∈ Ctx, ∀ C' ∈ Ctx, (C' ∘ C) ∈ Ctx)
    (S : P → T) : IsCongruence Ctx (contextualKer Ctx S) :=
  fun C hC _ _ h C' hC' => h (C' ∘ C) (hcomp C hC C' hC')

/-- With the identity context admitted, the contextual kernel refines the kernel. -/
theorem contextualKer_le_ker (hid : id ∈ Ctx) (S : P → T) :
    contextualKer Ctx S ≤ Setoid.ker S := by
  rw [Setoid.le_def]
  intro p q h
  exact Setoid.ker_def.2 (h id hid)

/-- Every contextual congruence below the kernel lies below the contextual kernel. -/
theorem le_contextualKer {E : Setoid P} (hE : IsCongruence Ctx E) {S : P → T}
    (hEk : E ≤ Setoid.ker S) : E ≤ contextualKer Ctx S := by
  rw [Setoid.le_def]
  intro p q h C hC
  exact Setoid.ker_def.1 (Setoid.le_def.1 hEk (hE C hC p q h))

/-- The contextual kernel is the greatest contextual congruence contained in `ker S`
when the contexts contain the identity and are closed under composition. -/
theorem contextualKer_greatest (hid : id ∈ Ctx)
    (hcomp : ∀ C ∈ Ctx, ∀ C' ∈ Ctx, (C' ∘ C) ∈ Ctx) (S : P → T) :
    IsCongruence Ctx (contextualKer Ctx S) ∧ contextualKer Ctx S ≤ Setoid.ker S ∧
      ∀ E : Setoid P, IsCongruence Ctx E → (E ≤ Setoid.ker S ↔ E ≤ contextualKer Ctx S) :=
  ⟨contextualKer_isCongruence Ctx hcomp S, contextualKer_le_ker Ctx hid S, fun _ hE =>
    ⟨le_contextualKer Ctx hE, fun h => h.trans (contextualKer_le_ker Ctx hid S)⟩⟩

end Contexts

/-! ### A congruence with no restricted basis -/

section RestrictedBasis

/-- Not every contextual congruence is generated by a restricted basis: on `Bool`, with the
empty basis, every rule set generates equality, while the total relation is a contextual
congruence. -/
theorem top_not_generated_bool (Ctx : Set (Bool → Bool)) :
    IsCongruence Ctx (⊤ : Setoid Bool) ∧
      ∀ S ⊆ (∅ : Set (Bool × Bool)), generated Ctx S ≠ ⊤ := by
  refine ⟨isCongruence_top Ctx, fun S hS h => ?_⟩
  rw [Set.subset_empty_iff] at hS
  subst hS
  rw [generated_empty] at h
  have htf : (⊥ : Setoid Bool) true false := by
    rw [h]
    trivial
  simp only [Setoid.bot_def] at htf
  exact absurd htf (by decide)

end RestrictedBasis

/-! ### The inversion automorphism of `ZMod 4` -/

section Inversion

/-- The automorphism `a ↦ -a` of `(ZMod 4, +)` as a permutation. -/
def negPerm : Equiv.Perm (ZMod 4) := Equiv.neg (ZMod 4)

/-- Inversion respects addition: it is an automorphism of the algebra. -/
theorem negPerm_add (a b : ZMod 4) : negPerm (a + b) = negPerm a + negPerm b := by
  simp [negPerm, add_comm]

theorem negPerm_mul_self : negPerm * negPerm = 1 := by
  ext a
  simp [negPerm]

/-- The group generated by inversion. -/
def inversionGroup : Subgroup (Equiv.Perm (ZMod 4)) := Subgroup.zpowers negPerm

/-- The inversion group has two elements, the identity and inversion. -/
theorem mem_inversionGroup_iff (γ : Equiv.Perm (ZMod 4)) :
    γ ∈ inversionGroup ↔ γ = 1 ∨ γ = negPerm := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    have h2 : negPerm ^ (2 : ℤ) = 1 := by rw [zpow_two, negPerm_mul_self]
    have hk : negPerm ^ k = negPerm ^ (k % 2) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
      rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
    rw [hk]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [h0, zpow_zero]
    · right
      rw [h1, zpow_one]
  · rintro (rfl | rfl)
    · exact inversionGroup.one_mem
    · exact Subgroup.mem_zpowers negPerm

/-- The orbits of inversion: `b` lies in the orbit of `a` exactly when `b = a` or `b = -a`. -/
theorem orbitRel_inversion_iff (a b : ZMod 4) :
    orbitRel inversionGroup a b ↔ b = a ∨ b = -a := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    rcases (mem_inversionGroup_iff γ).1 hγ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact (orbitRel inversionGroup).refl' _
    · exact ⟨negPerm, Subgroup.mem_zpowers negPerm, rfl⟩

/-- The orbit partition of inversion is `{0}`, `{2}`, `{1, 3}`. -/
theorem inversion_orbits (a b : ZMod 4) :
    orbitRel inversionGroup a b ↔ a = b ∨ (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) := by
  rw [orbitRel_inversion_iff]
  revert a b
  decide

/-- `1` and `3` lie in one orbit of inversion. -/
theorem orbitRel_one_three : orbitRel inversionGroup 1 3 :=
  ⟨negPerm, Subgroup.mem_zpowers negPerm, by decide⟩

/-- `2` and `0` do not lie in one orbit of inversion. -/
theorem not_orbitRel_two_zero : ¬ orbitRel inversionGroup 2 0 := by
  rw [inversion_orbits]
  decide

/-- The one-hole contexts of `(ZMod 4, +)`: the translations `a ↦ a + c`. An equivalence
stable under every translation is an additive congruence. -/
def translations : Set (ZMod 4 → ZMod 4) := Set.range fun c : ZMod 4 => fun a => a + c

/-- The context that adds `1`. -/
def addOne : ZMod 4 → ZMod 4 := fun a => a + 1

theorem addOne_mem_translations : addOne ∈ translations := ⟨1, rfl⟩

/-- The orbit equivalence of the inversion automorphism is not a contextual congruence for
the context `a ↦ a + 1`: it relates `1` and `3`, whose images `2` and `0` it does not
relate. -/
theorem inversion_not_congruence :
    ¬ IsCongruence ({addOne} : Set (ZMod 4 → ZMod 4)) (orbitRel inversionGroup) := by
  intro h
  have h13 := h addOne (Set.mem_singleton addOne) 1 3 orbitRel_one_three
  have e1 : addOne 1 = 2 := by decide
  have e2 : addOne 3 = 0 := by decide
  rw [e1, e2] at h13
  exact not_orbitRel_two_zero h13

/-- The same failure under the full family of translations. -/
theorem inversion_not_congruence_translations :
    ¬ IsCongruence translations (orbitRel inversionGroup) := by
  intro h
  have h13 := h addOne addOne_mem_translations 1 3 orbitRel_one_three
  have e1 : addOne 1 = 2 := by decide
  have e2 : addOne 3 = 0 := by decide
  rw [e1, e2] at h13
  exact not_orbitRel_two_zero h13

/-- Parity on `ZMod 4`: the kernel of doubling, with classes `{0, 2}` and `{1, 3}`. -/
def parity : Setoid (ZMod 4) := Setoid.ker fun a : ZMod 4 => a + a

theorem parity_iff (a b : ZMod 4) : parity a b ↔ b = a ∨ b = a + 2 := by
  change a + a = b + b ↔ _
  revert a b
  decide

/-- Parity is an additive congruence. -/
theorem parity_isCongruence : IsCongruence translations parity := by
  rintro C ⟨c, rfl⟩ a b h
  rw [parity_iff] at h ⊢
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · right
    ring

/-- The orbit relation of inversion as a set of rewrite pairs. -/
def inversionPairs : Set (ZMod 4 × ZMod 4) := {x | orbitRel inversionGroup x.1 x.2}

/-- The least additive congruence containing the inversion orbits is parity. -/
theorem generated_inversion_eq_parity : generated translations inversionPairs = parity := by
  apply le_antisymm
  · apply generated_le translations parity_isCongruence
    rintro ⟨a, b⟩ hab
    change orbitRel inversionGroup a b at hab
    rw [orbitRel_inversion_iff] at hab
    rcases hab with rfl | rfl
    · exact parity.refl' _
    · change a + a = -a + -a
      revert a
      decide
  · rw [Setoid.le_def]
    intro a b hab
    rw [parity_iff] at hab
    rcases hab with rfl | rfl
    · exact (generated translations inversionPairs).refl' _
    · have h13 : generated translations inversionPairs 1 3 :=
        subset_generated translations inversionPairs (1, 3) orbitRel_one_three
      have h := generated_isCongruence translations inversionPairs
        (fun x => x + (a - 1)) ⟨a - 1, rfl⟩ 1 3 h13
      have e1 : (1 : ZMod 4) + (a - 1) = a := by ring
      have e2 : (3 : ZMod 4) + (a - 1) = a + 2 := by ring
      simp only [e1, e2] at h
      exact h

/-- The orbit class of inversion, as an extractor valued in the orbit quotient. -/
def orbitClass : ZMod 4 → Quotient (orbitRel inversionGroup) := Quotient.mk _

/-- Under translations, the contextual kernel of the inversion orbit class is equality: any two
distinct elements can be translated so that one lands on the singleton orbit of `0`. -/
theorem contextualKer_inversion_eq_bot : contextualKer translations orbitClass = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [Setoid.le_def]
  intro a b h
  have h0 := h (fun x => x + -a) ⟨-a, rfl⟩
  simp only [orbitClass, add_neg_cancel] at h0
  have hq := (orbitRel_inversion_iff 0 (b + -a)).1 (Quotient.exact h0)
  have hb : b + -a = 0 := by
    rcases hq with hq | hq
    · exact hq
    · simpa using hq
  simp only [Setoid.bot_def]
  rw [← sub_eq_add_neg, sub_eq_zero] at hb
  exact hb.symm

end Inversion

/-! ### Three descriptions of one function: `C₃` saturates to `S₃` -/

section CyclicExample

/-- The three-cycle on three descriptions. -/
def threeCycle : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

/-- The cyclic group `C₃` generated by the three-cycle. -/
def cyclicThree : Subgroup (Equiv.Perm (Fin 3)) := Subgroup.zpowers threeCycle

/-- All three descriptions compute one function. -/
def constantSemantics : Fin 3 → Unit := fun _ => ()

theorem cyclicThree_le : cyclicThree ≤ functionGroup constantSemantics := fun _ _ _ => rfl

/-- `C₃` acts transitively on the three descriptions: it induces one class. -/
theorem orbitRel_cyclicThree : orbitRel cyclicThree = ⊤ := by
  apply le_antisymm le_top
  rw [Setoid.le_def]
  intro p q _
  have key : ∀ p q : Fin 3, (threeCycle ^ (0 : ℕ)) p = q ∨ (threeCycle ^ (1 : ℕ)) p = q ∨
      (threeCycle ^ (2 : ℕ)) p = q := by decide
  rcases key p q with h | h | h
  · exact ⟨_, Subgroup.npow_mem_zpowers threeCycle 0, h⟩
  · exact ⟨_, Subgroup.npow_mem_zpowers threeCycle 1, h⟩
  · exact ⟨_, Subgroup.npow_mem_zpowers threeCycle 2, h⟩

/-- The saturation of `C₃` is the full symmetric group `S₃`. -/
theorem saturate_cyclicThree : saturate constantSemantics cyclicThree = ⊤ := by
  rw [eq_top_iff]
  intro γ _
  refine ⟨fun _ => rfl, fun p => ?_⟩
  rw [orbitRel_cyclicThree]
  trivial

/-- `C₃` has order three. -/
theorem card_cyclicThree : Nat.card cyclicThree = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [cyclicThree, Nat.card_zpowers,
    orderOf_eq_prime (p := 3) (by decide : threeCycle ^ (3 : ℕ) = 1) (by decide)]

/-- `S₃` has order six. -/
theorem card_symmetricThree : Nat.card (⊤ : Subgroup (Equiv.Perm (Fin 3))) = 6 := by
  rw [Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

/-- The saturation of `C₃` has order six. -/
theorem card_saturate_cyclicThree : Nat.card (saturate constantSemantics cyclicThree) = 6 := by
  rw [saturate_cyclicThree, card_symmetricThree]

/-- `C₃` is a proper subgroup of `S₃`. -/
theorem cyclicThree_ne_top : cyclicThree ≠ ⊤ := by
  intro h
  have h3 := card_cyclicThree
  rw [h, card_symmetricThree] at h3
  omega

/-- A supplied ambient group containing only the swap of the first two descriptions. -/
def swapGroup : Subgroup (Equiv.Perm (Fin 3)) := Subgroup.zpowers (Equiv.swap 0 1)

theorem swapGroup_le : swapGroup ≤ functionGroup constantSemantics := fun _ _ _ => rfl

/-- Every member of the swap group fixes the third description. -/
theorem swapGroup_fix_two {γ : Equiv.Perm (Fin 3)} (hγ : γ ∈ swapGroup) : γ 2 = 2 := by
  have hstab : swapGroup ≤ MulAction.stabilizer (Equiv.Perm (Fin 3)) (2 : Fin 3) := by
    rw [swapGroup, Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
    decide
  have h := hstab hγ
  rwa [MulAction.mem_stabilizer_iff] at h

/-- With the ambient group restricted to the swap group, the relative class-preserver of the
total relation recovers only the swap orbits, strictly finer than the total relation. -/
theorem relative_recovery_strict :
    orbitRel (classGroup constantSemantics ⊤ ⊓ swapGroup) < ⊤ := by
  refine lt_of_le_of_ne le_top fun h => ?_
  have h20 : orbitRel (classGroup constantSemantics ⊤ ⊓ swapGroup) 2 0 := by
    rw [h]
    trivial
  obtain ⟨γ, hγ, hγ2⟩ := h20
  rw [swapGroup_fix_two (Subgroup.mem_inf.1 hγ).2] at hγ2
  exact absurd hγ2 (by decide)

/-- `C₃` is not a restricted subgroup: saturation enlarges it to `S₃`. -/
theorem cyclicThree_not_fixed : saturate constantSemantics cyclicThree ≠ cyclicThree := by
  rw [saturate_cyclicThree]
  exact fun h => cyclicThree_ne_top h.symm

end CyclicExample

end KTAIT.OperationalGalois
