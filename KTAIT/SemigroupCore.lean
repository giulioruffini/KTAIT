/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import Mathlib
import KTAIT.OperationalAlgebra

/-!
# Local groups and operational division (WP0004, WP0215)

An idempotent has its own local monoid, whose identity need not be the
ambient identity. Its units describe reversible operations on the states
retained by that idempotent. Operation sequences use the existing chronological
execution map. Division retains a fixed implementation for each operation and
an invariant domain on which the readout is onto.
-/

namespace KTAIT.SemigroupCore

open Function
open KTAIT.ComputationCores (run run_intertwines)

section Corners

variable {M : Type*} [Semigroup M]

/-- The local monoid at an idempotent, with ambient membership retained. -/
def Corner (e : {m : M // IsIdempotentElem m}) :=
  {m : M // (e : M) * m = m ∧ m * (e : M) = m}

instance (e : {m : M // IsIdempotentElem m}) : Mul (Corner e) where
  mul a b := ⟨a.val * b.val, by
    constructor
    · rw [← mul_assoc, a.property.1]
    · rw [mul_assoc, b.property.2]⟩

instance (e : {m : M // IsIdempotentElem m}) : One (Corner e) where
  one := ⟨e.val, e.property, e.property⟩

instance (e : {m : M // IsIdempotentElem m}) : Monoid (Corner e) where
  mul_assoc a b c := Subtype.ext (mul_assoc a.val b.val c.val)
  one_mul a := Subtype.ext a.property.1
  mul_one a := Subtype.ext a.property.2

/-- The local inclusion preserves multiplication, but not generally identity. -/
def cornerValue (e : {m : M // IsIdempotentElem m}) : Corner e →ₙ* M where
  toFun := Subtype.val
  map_mul' _ _ := rfl

@[simp] theorem cornerValue_one (e : {m : M // IsIdempotentElem m}) :
    cornerValue e 1 = e.val := rfl

@[simp] theorem cornerValue_mul (e : {m : M // IsIdempotentElem m}) (a b : Corner e) :
    cornerValue e (a * b) = cornerValue e a * cornerValue e b := rfl

/-- Local inclusion is faithful as a map into the ambient semigroup. -/
theorem cornerValue_injective (e : {m : M // IsIdempotentElem m}) :
    Injective (cornerValue e) := Subtype.val_injective

variable {G K : Type*} [Group G] [Group K]

/-- A semigroup map into a group sends every idempotent to the group identity. -/
theorem idempotent_map_eq_one (φ : M →ₙ* G) (e : {m : M // IsIdempotentElem m}) :
    φ e.val = 1 := by
  apply IsIdempotentElem.iff_eq_one.mp
  change φ e.val * φ e.val = φ e.val
  rw [← φ.map_mul, e.property]

/-- A semigroup factor induces a group map on each local group. -/
def cornerGroupMap (φ : M →ₙ* G) (e : {m : M // IsIdempotentElem m}) :
    (Corner e)ˣ →* G where
  toFun u := φ u.val.val
  map_one' := idempotent_map_eq_one φ e
  map_mul' u v := φ.map_mul u.val.val v.val.val

@[simp] theorem cornerGroupMap_apply (φ : M →ₙ* G)
    (e : {m : M // IsIdempotentElem m}) (u : (Corner e)ˣ) :
    cornerGroupMap φ e u = φ u.val.val := rfl

/-- The identity of a represented group is an idempotent in the semigroup. -/
def groupIdentity (f : K →ₙ* M) : {m : M // IsIdempotentElem m} :=
  ⟨f 1, by change f 1 * f 1 = f 1; rw [← f.map_mul, one_mul]⟩

/-- Every group representation takes values in the corner at its own identity. -/
def groupToCornerValue (f : K →ₙ* M) (k : K) : Corner (groupIdentity f) :=
  ⟨f k, by
    constructor
    · change f 1 * f k = f k
      rw [← f.map_mul, one_mul]
    · change f k * f 1 = f k
      rw [← f.map_mul, mul_one]⟩

/-- A group represented in a semigroup lands in the units of its local monoid. -/
def groupToCorner (f : K →ₙ* M) : K →* (Corner (groupIdentity f))ˣ where
  toFun k :=
    { val := groupToCornerValue f k
      inv := groupToCornerValue f k⁻¹
      val_inv := by
        apply Subtype.ext
        change f k * f k⁻¹ = f 1
        rw [← f.map_mul, mul_inv_cancel]
      inv_val := by
        apply Subtype.ext
        change f k⁻¹ * f k = f 1
        rw [← f.map_mul, inv_mul_cancel] }
  map_one' := by apply Units.ext; apply Subtype.ext; rfl
  map_mul' k l := by
    apply Units.ext
    apply Subtype.ext
    exact f.map_mul k l

@[simp] theorem groupToCorner_value (f : K →ₙ* M) (k : K) :
    (groupToCorner f k).val.val = f k := rfl

@[simp] theorem cornerGroupMap_groupToCorner (φ : M →ₙ* G) (f : K →ₙ* M) (k : K) :
    cornerGroupMap φ (groupIdentity f) (groupToCorner f k) = φ (f k) := rfl

/-- A faithful group representation remains faithful in its local group. -/
theorem groupToCorner_injective (f : K →ₙ* M) (hf : Injective f) :
    Injective (groupToCorner f) := by
  intro k l h
  apply hf
  exact congrArg (fun u : (Corner (groupIdentity f))ˣ => u.val.val) h


/-- A local group contains no idempotent except its own identity. -/
theorem idempotent_unit_eq_one (e : {m : M // IsIdempotentElem m})
    (u : (Corner e)ˣ) (h : IsIdempotentElem u.val.val) : u = 1 := by
  apply IsIdempotentElem.iff_eq_one.mp
  apply Units.ext
  exact Subtype.ext h

/-- A represented group can lie in a local group only at its own identity. -/
theorem group_identity_unique (f : K →ₙ* M)
    (e : {m : M // IsIdempotentElem m})
    (h : ∀ k, ∃ u : (Corner e)ˣ, u.val.val = f k) : (groupIdentity f).val = e.val := by
  obtain ⟨u, hu⟩ := h 1
  have hi : IsIdempotentElem u.val.val := hu ▸ (groupIdentity f).property
  have he := idempotent_unit_eq_one e u hi
  exact hu.symm.trans (congrArg (fun v : (Corner e)ˣ => v.val.val) he)

variable {N : Type*} [Semigroup N]

/-- A semigroup equivalence transports idempotents. -/
def mapWrite (φ : M ≃* N) (e : {m : M // IsIdempotentElem m}) :
    {n : N // IsIdempotentElem n} :=
  ⟨φ e.val, by change φ e.val * φ e.val = φ e.val; rw [← φ.map_mul, e.property]⟩

/-- A semigroup equivalence transports each local monoid. -/
def cornerCongr (φ : M ≃* N) (e : {m : M // IsIdempotentElem m}) :
    Corner e ≃* Corner (mapWrite φ e) where
  toEquiv := φ.toEquiv.subtypeEquiv (fun m => by
    change (e.val * m = m ∧ m * e.val = m) ↔
      (φ e.val * φ m = φ m ∧ φ m * φ e.val = φ m)
    simp only [← φ.map_mul, φ.injective.eq_iff])
  map_mul' a b := Subtype.ext (φ.map_mul a.val b.val)

/-- A semigroup equivalence transports the groups at corresponding writes. -/
def cornerGroupCongr (φ : M ≃* N) (e : {m : M // IsIdempotentElem m}) :
    (Corner e)ˣ ≃* (Corner (mapWrite φ e))ˣ :=
  Units.mapEquiv (cornerCongr φ e)

end Corners


section Transformations

variable {X : Type*}

/-- A finite self-map composite is bijective exactly when both factors are. -/
theorem bijective_comp_iff [Finite X] (f g : X → X) :
    Bijective (g ∘ f) ↔ Bijective f ∧ Bijective g := by
  constructor
  · intro h
    exact ⟨Finite.injective_iff_bijective.mp h.1.of_comp,
      Finite.surjective_iff_bijective.mp h.2.of_comp⟩
  · rintro ⟨hf, hg⟩
    exact hg.comp hf

/-- Reversibility means an inverse in the admitted monoid, not in all self-maps. -/
theorem unit_iff_bijective [Finite X] (M : Submonoid (Function.End X)) (m : M) :
    IsUnit m ↔ Bijective (m.val : X → X) := by
  constructor
  · rintro ⟨u, rfl⟩
    exact (Equiv.Perm.equivUnitsEnd.symm (Units.map M.subtype u)).bijective
  · intro h
    letI : Finite (Function.End X) := inferInstanceAs (Finite (X → X))
    letI : Finite M := Finite.of_injective Subtype.val Subtype.val_injective
    apply IsUnit.isUnit_iff_mulLeft_bijective.mpr
    apply Finite.injective_iff_bijective.mp
    intro a b hab
    apply Subtype.ext
    funext x
    apply h.1
    exact congrArg (fun k : M => k.val x) hab

/-- On finite states, a nonunit factor makes a composite a nonunit. -/
theorem irreversible_ideal [Finite X] (M : Submonoid (Function.End X)) (a b : M)
    (h : ¬ IsUnit a ∨ ¬ IsUnit b) : ¬ IsUnit (a * b) := by
  simp only [unit_iff_bijective] at *
  have hh := (bijective_comp_iff b.val a.val).mp
  rintro hab
  rcases h with ha | hb
  · exact ha (hh hab).2
  · exact hb (hh hab).1

/-- The range of a composite has no more elements than the outer range. -/
theorem card_image_comp_le_left [Fintype X] [DecidableEq X] (f g : X → X) :
    (Finset.univ.image (g ∘ f)).card ≤ (Finset.univ.image g).card := by
  apply Finset.card_le_card
  intro y hy
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
  exact Finset.mem_image.mpr ⟨f x, Finset.mem_univ _, rfl⟩

/-- The range of a composite has no more elements than the inner range. -/
theorem card_image_comp_le_right [Fintype X] [DecidableEq X] (f g : X → X) :
    (Finset.univ.image (g ∘ f)).card ≤ (Finset.univ.image f).card := by
  rw [← Finset.image_image]
  exact Finset.card_image_le

/-- Every update factors injectively through the equivalence induced by its values. -/
theorem kernel_factorization (m : X → X) :
    ∃ ι : Quotient (Setoid.ker m) → X,
      Injective ι ∧ m = ι ∘ Quotient.mk (Setoid.ker m) :=
  ⟨Setoid.kerLift m, Setoid.kerLift_injective m, rfl⟩

variable (M : Submonoid (Function.End X))

/-- States retained by the idempotent operation. -/
def Retained (e : {m : M // IsIdempotentElem m}) := Set.range (e.val.val : X → X)

/-- The idempotent fixes each retained state. -/
theorem write_fixes_range (e : {m : M // IsIdempotentElem m}) (y : Retained M e) :
    e.val.val y.val = y.val := by
  obtain ⟨x, hx⟩ := y.property
  rw [← hx]
  exact congrArg (fun k : M => k.val x) e.property

/-- Corner operations act on the retained states. -/
def cornerAction (e : {m : M // IsIdempotentElem m}) :
    Corner e →* Function.End (Retained M e) where
  toFun a y := ⟨a.val.val y.val, ⟨a.val.val y.val,
    congrArg (fun k : M => k.val y.val) a.property.1⟩⟩
  map_one' := by
    funext y
    apply Subtype.ext
    exact write_fixes_range M e y
  map_mul' _ _ := rfl

@[simp] theorem cornerAction_apply (e : {m : M // IsIdempotentElem m})
    (a : Corner e) (y : Retained M e) :
    (cornerAction M e a y).val = a.val.val y.val := rfl

/-- The action on retained states determines the full corner operation. -/
theorem corner_ext (e : {m : M // IsIdempotentElem m}) (a b : Corner e)
    (h : ∀ y : Retained M e, a.val.val y.val = b.val.val y.val) : a = b := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have ha := congrArg (fun k : M => k.val x) a.property.2
  have hb := congrArg (fun k : M => k.val x) b.property.2
  exact ha.symm.trans ((h ⟨e.val.val x, ⟨x, rfl⟩⟩).trans hb)

/-- Restriction to retained states is a faithful monoid action. -/
theorem cornerAction_injective (e : {m : M // IsIdempotentElem m}) :
    Injective (cornerAction M e) := by
  intro a b h
  apply corner_ext M e a b
  intro y
  exact congrArg (fun f : Function.End (Retained M e) => (f y).val) h

/-- The units of the corner permute the retained states. -/
def cornerPerm (e : {m : M // IsIdempotentElem m}) :
    (Corner e)ˣ →* Equiv.Perm (Retained M e) :=
  Equiv.Perm.equivUnitsEnd.symm.toMonoidHom.comp (Units.map (cornerAction M e))

/-- The local group acts faithfully on the retained states. -/
theorem corner_group_faithful (e : {m : M // IsIdempotentElem m}) :
    Injective (cornerPerm M e) := by
  intro a b h
  apply Units.ext
  apply cornerAction_injective M e
  exact congrArg (fun p : Equiv.Perm (Retained M e) => (p : Retained M e → Retained M e)) h

end Transformations


section EquivariantTracking

variable {X G A : Type*} [Group G]

/-- Equivariance conjugates updates when the input label is transformed. -/
def Equivariant [MulAction G A] (σ : G →* Equiv.Perm X) (F : A → X → X) : Prop :=
  ∀ (g : G) (a : A), (σ g) ∘ F a ∘ (σ g).symm = F (g • a)

/-- A transformed constant write records the transformed state. -/
theorem writes_orbit [MulAction G A] {σ : G →* Equiv.Perm X} {F : A → X → X}
    (hE : Equivariant σ F) {a : A} {x : X} (ha : F a = fun _ => x) (g : G) :
    F (g • a) = fun _ => σ g x := by
  rw [← hE g a, ha]
  rfl


/-- Relabeling states conjugates their transformation monoids. -/
def conjugation (s : Equiv.Perm X) : Function.End X ≃* Function.End X where
  toEquiv := s.conj
  map_mul' f g := s.conj_comp f g

/-- Equivariance is preserved by every finite sequence of inputs. -/
theorem equivariant_run [MulAction G A] {σ : G →* Equiv.Perm X} {F : A → X → X}
    (hE : Equivariant σ F) (g : G) (x : X) (w : List A) :
    σ g (run F x w) = run F (σ g x) (w.map (g • ·)) := by
  have he : ∀ a x, σ g (F a x) = F (g • a) (σ g x) := by
    intro a x
    simpa using congrFun (hE g a) (σ g x)
  induction w generalizing x with
  | nil => rfl
  | cons a w ih => simpa [run, he] using ih (F a x)

/-- Conjugation by an equivariance preserves the generated update monoid. -/
theorem conjugation_generated [MulAction G A] {σ : G →* Equiv.Perm X}
    {F : A → X → X} (hE : Equivariant σ F) (g : G) (m : Function.End X)
    (hm : m ∈ KTAIT.OperationalAlgebra.generated F) :
    conjugation (σ g) m ∈ KTAIT.OperationalAlgebra.generated F := by
  obtain ⟨w, rfl⟩ := hm
  refine ⟨w.map (g • ·), ?_⟩
  funext x
  exact (equivariant_run hE g ((σ g).symm x) w).trans (by simp)

/-- Equivariance induces an automorphism of the admitted generated monoid. -/
def generatedConjugation [MulAction G A] {σ : G →* Equiv.Perm X}
    {F : A → X → X} (hE : Equivariant σ F) (g : G) :
    KTAIT.OperationalAlgebra.generated F ≃* KTAIT.OperationalAlgebra.generated F where
  toEquiv := (conjugation (σ g)).toEquiv.subtypeEquiv (fun m => by
    constructor
    · exact conjugation_generated hE g m
    · intro hm
      have hh := conjugation_generated hE g⁻¹ (conjugation (σ g) m) hm
      have hi : conjugation (σ g⁻¹) (conjugation (σ g) m) = m := by
        funext x
        change (σ g⁻¹) (σ g (m ((σ g).symm ((σ g⁻¹).symm x)))) = m x
        simp only [map_inv]
        change (σ g).symm (σ g (m ((σ g).symm (σ g x)))) = m x
        simp
      rwa [hi] at hh)
  map_mul' a b := Subtype.ext ((conjugation (σ g)).map_mul a.val b.val)

variable (M : Submonoid (Function.End X))

/-- Tracking on the retained states, with every update in the admitted monoid. -/
structure Tracks (σ : G →* Equiv.Perm X) (F : G → M)
    (e : {m : M // IsIdempotentElem m}) : Prop where
  invariant : ∀ (g : G) (y : Retained M e), σ g y.val ∈ Retained M e
  agrees : ∀ (g : G) (y : Retained M e), (F g).val y.val = σ g y.val

/-- The tracked operation is restricted on both sides by the write. -/
def track (F : G → M) (e : {m : M // IsIdempotentElem m}) (g : G) : Corner e :=
  ⟨e.val * F g * e.val, by
    have he : e.val * e.val = e.val := e.property
    constructor
    · simp only [← mul_assoc, he]
    · simp only [mul_assoc, he]⟩

/-- On retained states the tracked operation agrees with the world action. -/
theorem track_on_range {σ : G →* Equiv.Perm X} {F : G → M}
    {e : {m : M // IsIdempotentElem m}} (ht : Tracks M σ F e)
    (g : G) (y : Retained M e) :
    (track M F e g).val.val y.val = σ g y.val := by
  change e.val.val ((F g).val (e.val.val y.val)) = σ g y.val
  rw [write_fixes_range M e y, ht.agrees]
  exact write_fixes_range M e ⟨σ g y.val, ht.invariant g y⟩

/-- The tracked operations respect group multiplication. -/
theorem track_mul {σ : G →* Equiv.Perm X} {F : G → M}
    {e : {m : M // IsIdempotentElem m}} (ht : Tracks M σ F e) (g h : G) :
    track M F e (g * h) = track M F e g * track M F e h := by
  apply corner_ext M e
  intro y
  change (track M F e (g * h)).val.val y.val =
    (track M F e g).val.val ((track M F e h).val.val y.val)
  rw [track_on_range M ht h y]
  rw [track_on_range M ht g ⟨σ h y.val, ht.invariant h y⟩]
  rw [track_on_range M ht (g * h) y, map_mul]
  rfl

/-- The group identity is represented by the local identity, the write. -/
theorem track_one {σ : G →* Equiv.Perm X} {F : G → M}
    {e : {m : M // IsIdempotentElem m}} (ht : Tracks M σ F e) :
    track M F e 1 = 1 := by
  apply corner_ext M e
  intro y
  rw [track_on_range M ht 1 y, map_one]
  exact (write_fixes_range M e y).symm

/-- Tracking determines a homomorphism into the units of the retained corner. -/
def trackingHom {σ : G →* Equiv.Perm X} {F : G → M}
    {e : {m : M // IsIdempotentElem m}} (ht : Tracks M σ F e) :
    G →* (Corner e)ˣ where
  toFun g :=
    { val := track M F e g
      inv := track M F e g⁻¹
      val_inv := by rw [← track_mul M ht, mul_inv_cancel, track_one M ht]
      inv_val := by rw [← track_mul M ht, inv_mul_cancel, track_one M ht] }
  map_one' := Units.ext (track_one M ht)
  map_mul' g h := Units.ext (track_mul M ht g h)

/-- The kernel consists exactly of world transformations fixing all retained states. -/
theorem tracking_kernel {σ : G →* Equiv.Perm X} {F : G → M}
    {e : {m : M // IsIdempotentElem m}} (ht : Tracks M σ F e) (g : G) :
    trackingHom M ht g = 1 ↔ ∀ y : Retained M e, σ g y.val = y.val := by
  constructor
  · intro h y
    have hh := congrArg (fun a : (Corner e)ˣ => a.val.val.val y.val) h
    change (track M F e g).val.val y.val = e.val.val y.val at hh
    rw [track_on_range M ht g y, write_fixes_range M e y] at hh
    exact hh
  · intro h
    apply Units.ext
    apply corner_ext M e
    intro y
    change (track M F e g).val.val y.val = e.val.val y.val
    rw [track_on_range M ht g y, write_fixes_range M e y]
    exact h y

end EquivariantTracking


section Division

variable {X Y Z A B C : Type*}

/-- Operational division uses fixed implementing sequences and an invariant domain. -/
structure Divides (S : A → X → X) (T : B → Y → Y) where
  dom : Set Y
  ρ : dom → X
  word : A → List B
  closed : ∀ a (y : dom), run T y.val (word a) ∈ dom
  onto : Surjective ρ
  comm : ∀ a (y : dom), ρ ⟨run T y.val (word a), closed a y⟩ = S a (ρ y)

namespace Divides

variable {S : A → X → X} {T : B → Y → Y} {R : C → Z → Z}

/-- An implementing sequence induces an update on the invariant domain. -/
def realizedUpdate (d : Divides S T) (a : A) (y : d.dom) : d.dom :=
  ⟨run T y.val (d.word a), d.closed a y⟩

/-- Domain updates intertwine all finite experiments, including the empty one. -/
theorem run_comm (d : Divides S T) (y : d.dom) (w : List A) :
    d.ρ (run d.realizedUpdate y w) = run S (d.ρ y) w :=
  run_intertwines d.realizedUpdate S d.ρ d.comm y w

/-- Concatenating the implementing sequences realizes a sequence of target updates. -/
theorem realizedRun_val (d : Divides S T) (y : d.dom) (w : List A) :
    (run d.realizedUpdate y w).val = run T y.val (w.flatMap d.word) := by
  induction w generalizing y with
  | nil => rfl
  | cons a w ih =>
    simpa [run, List.flatMap_cons, List.foldl_append, realizedUpdate] using
      ih (d.realizedUpdate a y)

/-- Each operation family divides itself. -/
def refl (S : A → X → X) : Divides S S where
  dom := Set.univ
  ρ := Subtype.val
  word a := [a]
  closed _ _ := Set.mem_univ _
  onto x := ⟨⟨x, Set.mem_univ x⟩, rfl⟩
  comm _ _ := rfl

/-- Implementations compose by concatenating their fixed input sequences. -/
noncomputable def trans (d₁ : Divides S T) (d₂ : Divides T R) : Divides S R := by
  let dom : Set Z := {z | ∃ hz : z ∈ d₂.dom, d₂.ρ ⟨z, hz⟩ ∈ d₁.dom}
  let lift : dom → d₂.dom := fun z => ⟨z.val, z.property.choose⟩
  let proj : dom → d₁.dom := fun z => ⟨d₂.ρ (lift z), z.property.choose_spec⟩
  let encode : A → List C := fun a => (d₁.word a).flatMap d₂.word
  have cl : ∀ a (z : dom), run R z.val (encode a) ∈ dom := by
    intro a z
    let out := run d₂.realizedUpdate (lift z) (d₁.word a)
    have hv : out.val = run R z.val (encode a) := d₂.realizedRun_val (lift z) _
    have hp : d₂.ρ out ∈ d₁.dom := by
      rw [d₂.run_comm]
      exact d₁.closed a (proj z)
    refine ⟨hv ▸ out.property, ?_⟩
    convert hp using 1
    congr 1
    exact Subtype.ext hv.symm
  refine
    { dom := dom
      ρ := fun z => d₁.ρ (proj z)
      word := encode
      closed := cl
      onto := ?_
      comm := ?_ }
  · intro x
    obtain ⟨y, hy⟩ := d₁.onto x
    obtain ⟨z, hz⟩ := d₂.onto y.val
    have hmem : z.val ∈ dom := ⟨z.property, hz ▸ y.property⟩
    refine ⟨⟨z.val, hmem⟩, ?_⟩
    have hp : proj ⟨z.val, hmem⟩ = y := Subtype.ext hz
    simpa [hp] using hy
  · intro a z
    let out : dom := ⟨run R z.val (encode a), cl a z⟩
    have hl : lift out = run d₂.realizedUpdate (lift z) (d₁.word a) := by
      apply Subtype.ext
      exact (d₂.realizedRun_val (lift z) _).symm
    have hp : proj out =
        ⟨run T (proj z).val (d₁.word a), d₁.closed a (proj z)⟩ := by
      apply Subtype.ext
      change d₂.ρ (lift out) = _
      rw [hl, d₂.run_comm]
    change d₁.ρ (proj out) = S a (d₁.ρ (proj z))
    rw [hp]
    exact d₁.comm a (proj z)

end Divides
end Division

end KTAIT.SemigroupCore
