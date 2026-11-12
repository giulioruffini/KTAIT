/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import Mathlib
import KTAIT.OperationalAlgebra
import KTAIT.SemigroupCore

/-!
# Finite group lifting and tracked transformations

A finite semigroup mapping onto a group contains a group mapping onto it.
The identity of the lifted group can be an idempotent other than the
identity of an ambient monoid. Tracking a group action through an onto
readout supplies the homomorphism to which the lifting theorem applies.
-/

namespace KTAIT.SemigroupTracking

open Function
open KTAIT.SemigroupCore
open KTAIT.OperationalAlgebra (generated generatedFactor generated_factor_surjective)
open KTAIT.ComputationCores (run)

variable {M G : Type*} [Semigroup M] [Group G]

private def leftTranslate (R : Subsemigroup M) (s : R) : Subsemigroup M where
  carrier := (fun x : M => (s : M) * x) '' (R : Set M)
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    refine ⟨a * s * b, R.mul_mem (R.mul_mem ha s.property) hb, ?_⟩
    simp only [mul_assoc]

private def rightTranslate (R : Subsemigroup M) (s : R) : Subsemigroup M where
  carrier := (fun x : M => x * (s : M)) '' (R : Set M)
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    refine ⟨a * s * b, R.mul_mem (R.mul_mem ha s.property) hb, ?_⟩
    simp only [mul_assoc]

private theorem leftTranslate_le (R : Subsemigroup M) (s : R) :
    leftTranslate R s ≤ R := by
  rintro _ ⟨a, ha, rfl⟩
  exact R.mul_mem s.property ha

private theorem rightTranslate_le (R : Subsemigroup M) (s : R) :
    rightTranslate R s ≤ R := by
  rintro _ ⟨a, ha, rfl⟩
  exact R.mul_mem ha s.property

private theorem leftTranslate_onto (φ : M →ₙ* G) (R : Subsemigroup M)
    (hR : Surjective (fun r : R => φ r)) (s : R) :
    Surjective (fun r : leftTranslate R s => φ r) := by
  intro g
  obtain ⟨a, ha⟩ := hR ((φ s)⁻¹ * g)
  change φ (a : M) = (φ s)⁻¹ * g at ha
  refine ⟨⟨s * a, a, a.property, rfl⟩, ?_⟩
  change φ ((s : M) * a) = g
  rw [map_mul, ha, mul_inv_cancel_left]

private theorem rightTranslate_onto (φ : M →ₙ* G) (R : Subsemigroup M)
    (hR : Surjective (fun r : R => φ r)) (s : R) :
    Surjective (fun r : rightTranslate R s => φ r) := by
  intro g
  obtain ⟨a, ha⟩ := hR (g * (φ s)⁻¹)
  change φ (a : M) = g * (φ s)⁻¹ at ha
  refine ⟨⟨a * s, a, a.property, rfl⟩, ?_⟩
  change φ ((a : M) * s) = g
  rw [map_mul, ha, inv_mul_cancel_right]

private theorem minimal_onto_subsemigroup [Finite M] (φ : M →ₙ* G)
    (hφ : Surjective φ) :
    ∃ R : Subsemigroup M, Surjective (fun r : R => φ r) ∧
      ∀ s : R, Surjective (fun r : R => s * r) ∧
        Surjective (fun r : R => r * s) := by
  have htop : ∃ R : Subsemigroup M, Surjective (fun r : R => φ r) := by
    refine ⟨⊤, fun g => ?_⟩
    obtain ⟨m, hm⟩ := hφ g
    exact ⟨⟨m, trivial⟩, hm⟩
  obtain ⟨R, hR⟩ := exists_minimalFor_of_wellFoundedLT
    (fun R : Subsemigroup M => Surjective (fun r : R => φ r))
    (fun R => Nat.card R) htop
  have minimal : ∀ S : Subsemigroup M, S ≤ R →
      Surjective (fun s : S => φ s) → S = R := by
    intro S hSR hS
    apply SetLike.coe_injective
    apply (Set.toFinite (R : Set M)).eq_of_subset_of_card_le hSR
    apply hR.2 hS
    exact Nat.card_le_card_of_injective
      (fun s : S => (⟨s, hSR s.property⟩ : R))
      (fun a b hab => Subtype.ext (congrArg (fun r : R => (r : M)) hab))
  refine ⟨R, hR.prop, fun s => ⟨?_, ?_⟩⟩
  · have hs : leftTranslate R s = R :=
      minimal _ (leftTranslate_le R s) (leftTranslate_onto φ R hR.prop s)
    intro x
    have hx : (x : M) ∈ leftTranslate R s := hs.symm ▸ x.property
    obtain ⟨a, ha, hax⟩ := hx
    exact ⟨⟨a, ha⟩, Subtype.ext hax⟩
  · have hs : rightTranslate R s = R :=
      minimal _ (rightTranslate_le R s) (rightTranslate_onto φ R hR.prop s)
    intro x
    have hx : (x : M) ∈ rightTranslate R s := hs.symm ▸ x.property
    obtain ⟨a, ha, hax⟩ := hx
    exact ⟨⟨a, ha⟩, Subtype.ext hax⟩

private theorem group_data_of_translations {S : Type*} [Semigroup S]
    [Finite S] [Nonempty S]
    (htrans : ∀ s : S, Surjective (fun r : S => s * r) ∧
      Surjective (fun r : S => r * s)) :
    ∃ e : S, (∀ x : S, e * x = x ∧ x * e = x) ∧
      ∀ x : S, ∃ y : S, y * x = e ∧ x * y = e := by
  obtain ⟨a⟩ := ‹Nonempty S›
  obtain ⟨e, he⟩ := (htrans a).1 a
  change a * e = a at he
  have left_id : ∀ x : S, e * x = x := by
    intro x
    apply (Finite.injective_iff_surjective.mpr (htrans a).1)
    change a * (e * x) = a * x
    rw [← mul_assoc, he]
  have right_id : ∀ x : S, x * e = x := by
    intro x
    obtain ⟨y, rfl⟩ := (htrans a).2 x
    change (y * a) * e = y * a
    rw [mul_assoc, he]
  refine ⟨e, fun x => ⟨left_id x, right_id x⟩, fun x => ?_⟩
  obtain ⟨y, hy⟩ := (htrans x).2 e
  change y * x = e at hy
  refine ⟨y, hy, ?_⟩
  apply (Finite.injective_iff_surjective.mpr (htrans x).2)
  change (x * y) * x = e * x
  rw [mul_assoc, hy, right_id, left_id]

/-- A group quotient of a finite semigroup is already a quotient of one local group. -/
theorem finite_group_lifting [Finite M] (φ : M →ₙ* G) (hφ : Surjective φ) :
    ∃ e : {m : M // IsIdempotentElem m}, Surjective (cornerGroupMap φ e) := by
  obtain ⟨R, hR, htrans⟩ := minimal_onto_subsemigroup φ hφ
  haveI : Nonempty R := ⟨(hR 1).choose⟩
  obtain ⟨e, he, hinv⟩ := group_data_of_translations htrans
  let eM : {m : M // IsIdempotentElem m} :=
    ⟨e, congrArg (fun r : R => (r : M)) (he e).1⟩
  refine ⟨eM, fun g => ?_⟩
  obtain ⟨x, hx⟩ := hR g
  obtain ⟨y, hyx, hxy⟩ := hinv x
  let lift : R → Corner eM := fun r =>
    ⟨r, congrArg (fun r : R => (r : M)) (he r).1,
      congrArg (fun r : R => (r : M)) (he r).2⟩
  let u : (Corner eM)ˣ :=
    { val := lift x
      inv := lift y
      val_inv := Subtype.ext (congrArg (fun r : R => (r : M)) hxy)
      inv_val := Subtype.ext (congrArg (fun r : R => (r : M)) hyx) }
  exact ⟨u, hx⟩

/-- Every group divisor of a finite semigroup divides one of its local groups. -/
theorem group_divisor_lifts [Finite M] (R : Subsemigroup M) (φ : R →ₙ* G)
    (hφ : Surjective φ) :
    ∃ e : {m : M // IsIdempotentElem m}, ∃ H : Subgroup ((Corner e)ˣ),
      ∃ ψ : H →* G, Surjective ψ := by
  obtain ⟨e, he⟩ := finite_group_lifting φ hφ
  let f : (Corner e)ˣ →ₙ* M :=
    { toFun := fun u => u.val.val.val
      map_mul' _ _ := rfl }
  have hf : Injective f := by
    intro u v huv
    apply Units.ext
    apply Subtype.ext
    apply Subtype.ext
    exact huv
  let i := groupToCorner f
  let j := MonoidHom.ofInjective (groupToCorner_injective f hf)
  refine ⟨groupIdentity f, i.range,
    (cornerGroupMap φ e).comp j.symm.toMonoidHom, ?_⟩
  exact he.comp j.symm.surjective

section Tracking

variable {N W : Type*} [MulAction G W]

/-- The group of permutations actually induced on world configurations. -/
abbrev WorldActionImage (G W : Type*) [Group G] [MulAction G W] :=
  (MulAction.toPermHom G W).range

private theorem action_sequence (w : List G) :
    ∃ g : G, ∀ x : W, run (fun h : G => fun y : W => h • y) x w = g • x := by
  induction w with
  | nil => exact ⟨1, fun x => (one_smul G x).symm⟩
  | cons h w ih =>
    obtain ⟨g, hg⟩ := ih
    refine ⟨g * h, fun x => ?_⟩
    change run (fun h : G => fun y : W => h • y) (h • x) w = (g * h) • x
    rw [hg, mul_smul]

private def actionImageToGenerated :
    WorldActionImage G W →* generated (fun h : G => fun x : W => h • x) where
  toFun g := ⟨(fun x => (g : Equiv.Perm W) x), by
    obtain ⟨h, hh⟩ := g.property
    refine ⟨[h], ?_⟩
    funext x
    change (g : Equiv.Perm W) x = h • x
    exact (congrArg (fun p : Equiv.Perm W => p x) hh).symm⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem actionImageToGenerated_bijective :
    Bijective (actionImageToGenerated (G := G) (W := W)) := by
  constructor
  · intro g h hgh
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact congrArg (fun f : generated (fun h : G => fun y : W => h • y) => f.val x) hgh
  · rintro ⟨f, w, rfl⟩
    obtain ⟨g, hg⟩ := action_sequence (G := G) (W := W) w
    refine ⟨⟨MulAction.toPermHom G W g, g, rfl⟩, ?_⟩
    apply Subtype.ext
    funext x
    exact (hg x).symm

/-- Generated transformations of a group action coincide with its permutation image. -/
noncomputable def actionGeneratedEquiv :
    generated (fun h : G => fun x : W => h • x) ≃* WorldActionImage G W :=
  (MulEquiv.ofBijective (actionImageToGenerated (G := G) (W := W))
    actionImageToGenerated_bijective).symm

@[simp] theorem actionGeneratedEquiv_apply
    (m : generated (fun h : G => fun x : W => h • x)) (x : W) :
    (actionGeneratedEquiv m : Equiv.Perm W) x = m.val x := by
  exact congrArg
    (fun f : generated (fun h : G => fun y : W => h • y) => f.val x)
    ((MulEquiv.ofBijective (actionImageToGenerated (G := G) (W := W))
      actionImageToGenerated_bijective).apply_symm_apply m)

/-- An onto tracking readout induces a homomorphism to the realized world action. -/
noncomputable def trackingFactor (F : G → N → N) (p : N → W) (hp : Surjective p)
    (htrack : ∀ h y, p (F h y) = h • p y) :
    generated F →* WorldActionImage G W :=
  (actionGeneratedEquiv (G := G) (W := W)).toMonoidHom.comp
    (generatedFactor F (fun h : G => fun x : W => h • x) p hp htrack)

/-- Every world transformation is represented by a transformation of the tracking system. -/
theorem tracking_factor_surjective (F : G → N → N) (p : N → W) (hp : Surjective p)
    (htrack : ∀ h y, p (F h y) = h • p y) :
    Surjective (trackingFactor F p hp htrack) :=
  (actionGeneratedEquiv (G := G) (W := W)).surjective.comp
    (generated_factor_surjective F (fun h : G => fun x : W => h • x) p hp htrack)

/-- The factor carries every agent transformation to its tracked world transformation. -/
theorem tracking_factor_commutes (F : G → N → N) (p : N → W) (hp : Surjective p)
    (htrack : ∀ h y, p (F h y) = h • p y) (m : generated F) (y : N) :
    p (m.val y) = (trackingFactor F p hp htrack m : Equiv.Perm W) (p y) := by
  change p (m.val y) =
    (actionGeneratedEquiv
      (generatedFactor F (fun h : G => fun x : W => h • x) p hp htrack m) :
        Equiv.Perm W) (p y)
  rw [actionGeneratedEquiv_apply]
  exact KTAIT.OperationalAlgebra.generated_factor_commutes
    F (fun h : G => fun x : W => h • x) p hp htrack m y

/-- Finite tracking forces a local group mapping onto the tracked permutation group. -/
theorem tracking_forces_group [Finite N] (F : G → N → N) (p : N → W)
    (hp : Surjective p) (htrack : ∀ h y, p (F h y) = h • p y) :
    ∃ e : {m : generated F // IsIdempotentElem m},
      Surjective (cornerGroupMap (trackingFactor F p hp htrack).toMulHom e) := by
  letI : Fintype N := Fintype.ofFinite N
  letI : Finite (Function.End N) := inferInstanceAs (Finite (N → N))
  letI : Finite (generated F) := Finite.of_injective
    (fun m : generated F => m.val) Subtype.val_injective
  exact finite_group_lifting (trackingFactor F p hp htrack).toMulHom
    (tracking_factor_surjective F p hp htrack)

end Tracking

section OperationalDivision

variable {X Y A B : Type*} {S : A → X → X} {T : B → Y → Y}

/-- A generated emulator map realizes a target map through the fixed domain readout. -/
def DivisionCorresponds (d : Divides S T) (m : generated T) (q : generated S) : Prop :=
  ∀ y : d.dom, ∃ hy : m.val y.val ∈ d.dom,
    d.ρ ⟨m.val y.val, hy⟩ = q.val (d.ρ y)

private theorem division_correspondence_unique (d : Divides S T) (m : generated T)
    (q r : generated S) (hq : DivisionCorresponds d m q)
    (hr : DivisionCorresponds d m r) : q = r := by
  apply Subtype.ext
  funext x
  obtain ⟨y, rfl⟩ := d.onto x
  obtain ⟨hy, hqy⟩ := hq y
  obtain ⟨hy', hry⟩ := hr y
  exact hqy.symm.trans hry

/-- The emulator transformations that descend through the fixed readout form a submonoid. -/
def divisionSubmonoid (d : Divides S T) : Submonoid (generated T) where
  carrier := {m | ∃ q : generated S, DivisionCorresponds d m q}
  one_mem' := ⟨1, fun y => ⟨y.property, rfl⟩⟩
  mul_mem' := by
    rintro m n ⟨q, hq⟩ ⟨r, hr⟩
    refine ⟨q * r, fun y => ?_⟩
    obtain ⟨hy, hry⟩ := hr y
    obtain ⟨hz, hqz⟩ := hq ⟨n.val y.val, hy⟩
    refine ⟨hz, ?_⟩
    change d.ρ ⟨m.val (n.val y.val), hz⟩ = q.val (r.val (d.ρ y))
    rw [hqz, hry]

private noncomputable def divisionChosenMap (d : Divides S T)
    (m : divisionSubmonoid d) : generated S := m.property.choose

private theorem divisionChosenMap_corresponds (d : Divides S T)
    (m : divisionSubmonoid d) : DivisionCorresponds d m.val (divisionChosenMap d m) :=
  m.property.choose_spec

/-- Restriction to the invariant domain induces a homomorphism of generated monoids. -/
noncomputable def divisionFactor (d : Divides S T) : divisionSubmonoid d →* generated S where
  toFun := divisionChosenMap d
  map_one' := division_correspondence_unique d 1 _ 1
    (divisionChosenMap_corresponds d 1) (fun y => ⟨y.property, rfl⟩)
  map_mul' m n := by
    apply division_correspondence_unique d (m.val * n.val)
      _ (divisionChosenMap d m * divisionChosenMap d n)
      (divisionChosenMap_corresponds d (m * n))
    intro y
    obtain ⟨hy, hny⟩ := divisionChosenMap_corresponds d n y
    obtain ⟨hz, hmz⟩ := divisionChosenMap_corresponds d m ⟨n.val.val y.val, hy⟩
    refine ⟨hz, ?_⟩
    change d.ρ ⟨m.val.val (n.val.val y.val), hz⟩ =
      (divisionChosenMap d m).val ((divisionChosenMap d n).val (d.ρ y))
    rw [hmz, hny]

/-- The induced map preserves the readout at the ends of admitted implementations. -/
theorem division_factor_commutes (d : Divides S T) (m : divisionSubmonoid d) :
    DivisionCorresponds d m.val (divisionFactor d m) :=
  divisionChosenMap_corresponds d m

/-- Concatenated compiled operations give a counterpart to every target input sequence. -/
theorem division_sequence_corresponds (d : Divides S T) (w : List A) :
    DivisionCorresponds d
      ⟨fun y => run T y (w.flatMap d.word), w.flatMap d.word, rfl⟩
      ⟨fun x => run S x w, w, rfl⟩ := by
  intro y
  let out := run d.realizedUpdate y w
  have hv : out.val = run T y.val (w.flatMap d.word) := d.realizedRun_val y w
  have hy : run T y.val (w.flatMap d.word) ∈ d.dom := hv ▸ out.property
  refine ⟨hy, ?_⟩
  change d.ρ ⟨run T y.val (w.flatMap d.word), _⟩ = run S (d.ρ y) w
  have hs : (⟨run T y.val (w.flatMap d.word), hy⟩ : d.dom) = out :=
    Subtype.ext hv.symm
  rw [hs]
  exact d.run_comm y w

/-- Operational division gives a quotient of a submonoid of the full-state emulator monoid. -/
theorem division_factor_surjective (d : Divides S T) : Surjective (divisionFactor d) := by
  rintro ⟨q, w, rfl⟩
  let m : generated T :=
    ⟨fun y => run T y (w.flatMap d.word), w.flatMap d.word, rfl⟩
  let q' : generated S := ⟨fun x => run S x w, w, rfl⟩
  have hmq : DivisionCorresponds d m q' := division_sequence_corresponds d w
  let m' : divisionSubmonoid d := ⟨m, q', hmq⟩
  refine ⟨m', ?_⟩
  exact division_correspondence_unique d m _ q'
    (division_factor_commutes d m') hmq

/-- A finite operational emulator contains a local group with the tracked action as a divisor.
Only compiled-operation endpoints must remain in the declared domain. -/
theorem division_forces_group [Finite Y] [MulAction G X]
    (d : Divides (fun h : G => fun x : X => h • x) T) :
    ∃ e : {m : generated T // IsIdempotentElem m},
      ∃ H : Subgroup ((Corner e)ˣ), ∃ ψ : H →* WorldActionImage G X, Surjective ψ := by
  letI : Fintype Y := Fintype.ofFinite Y
  letI : Finite (Function.End Y) := inferInstanceAs (Finite (Y → Y))
  letI : Finite (generated T) := Finite.of_injective
    (fun m : generated T => m.val) Subtype.val_injective
  let φ : divisionSubmonoid d →* WorldActionImage G X :=
    (actionGeneratedEquiv (G := G) (W := X)).toMonoidHom.comp (divisionFactor d)
  have hφ : Surjective φ :=
    (actionGeneratedEquiv (G := G) (W := X)).surjective.comp
      (division_factor_surjective d)
  exact group_divisor_lifts (divisionSubmonoid d).toSubsemigroup φ.toMulHom hφ

end OperationalDivision

end KTAIT.SemigroupTracking
