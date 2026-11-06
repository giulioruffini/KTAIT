/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude)
-/
import Mathlib
import KTAIT.ComputationCores

/-!
# Action kernels, faithful images, and action isomorphisms (WP0004)

A group `G` acts on states `X` through a homomorphism `ρ : G →* Equiv.Perm X`. Two
elements realize the same transformation exactly when they differ by an element of the
kernel, the realized transformation group `ρ.range` acts faithfully, and the quotient
`G ⧸ ρ.ker` is isomorphic to `ρ.range` by Mathlib's first isomorphism theorem; the
induced action of the quotient is injective and has the same range.

Two explicit examples separate the abstract group from its realized action. The cyclic
groups of orders four and two act on one bit through the parity of the exponent: their
images coincide, both equal to the identity and negation, while the order-four action has
a nontrivial kernel. Two faithful actions of the group of order two on four states, by a
transposition and by a double transposition, are not isomorphic as actions, even allowing
a group automorphism, because conjugation preserves the number of fixed states and the
counts are two and zero.

A bijection of states that intertwines labeled operations carries every run to the
corresponding run; when it also preserves the input and output maps, readouts and any
transported completion predicate agree word by word.
-/

namespace KTAIT.OperationalActions

open KTAIT.ComputationCores (run run_intertwines)

/-! ### Kernel, faithful image, and the first isomorphism theorem -/

section Kernel

variable {G X : Type*} [Group G]

/-- Two group elements realize the same transformation exactly when they differ by a
kernel element. -/
theorem apply_eq_iff_inv_mul_mem_ker (ρ : G →* Equiv.Perm X) (g h : G) :
    ρ g = ρ h ↔ g⁻¹ * h ∈ ρ.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]

/-- Pointwise agreement on every state is the same as a kernel difference. -/
theorem apply_pointwise_eq_iff (ρ : G →* Equiv.Perm X) (g h : G) :
    (∀ x, ρ g x = ρ h x) ↔ g⁻¹ * h ∈ ρ.ker := by
  rw [← apply_eq_iff_inv_mul_mem_ker]
  exact ⟨fun H => Equiv.ext H, fun H x => by rw [H]⟩

/-- The realized transformation group acts faithfully: equal actions on every state give
equal elements. -/
theorem range_faithful (ρ : G →* Equiv.Perm X) (σ τ : ρ.range)
    (h : ∀ x, (σ : Equiv.Perm X) x = (τ : Equiv.Perm X) x) : σ = τ :=
  Subtype.ext (Equiv.ext h)

instance range_faithfulSMul (ρ : G →* Equiv.Perm X) : FaithfulSMul ρ.range X :=
  ⟨fun h => Subtype.ext (Equiv.ext fun x => h x)⟩

/-- The first isomorphism theorem for an action, `G ⧸ ker ρ ≃* range ρ`; this is Mathlib's
`QuotientGroup.quotientKerEquivRange`. -/
noncomputable def quotientEquivRange (ρ : G →* Equiv.Perm X) : G ⧸ ρ.ker ≃* ρ.range :=
  QuotientGroup.quotientKerEquivRange ρ

/-- The action of `G ⧸ ker ρ` on states through the realized transformations. -/
noncomputable def quotientAction (ρ : G →* Equiv.Perm X) : G ⧸ ρ.ker →* Equiv.Perm X :=
  ρ.range.subtype.comp (quotientEquivRange ρ).toMonoidHom

theorem quotientAction_mk (ρ : G →* Equiv.Perm X) (g : G) :
    quotientAction ρ (QuotientGroup.mk g) = ρ g := rfl

/-- The quotient action is faithful: it is injective into permutations. -/
theorem quotientAction_injective (ρ : G →* Equiv.Perm X) :
    Function.Injective (quotientAction ρ) :=
  ρ.range.subtype_injective.comp (quotientEquivRange ρ).injective

theorem quotientAction_ker (ρ : G →* Equiv.Perm X) : (quotientAction ρ).ker = ⊥ :=
  (MonoidHom.ker_eq_bot_iff _).2 (quotientAction_injective ρ)

/-- The quotient action realizes exactly the transformations of `ρ`. -/
theorem quotientAction_range (ρ : G →* Equiv.Perm X) : (quotientAction ρ).range = ρ.range := by
  ext σ
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨g, (quotientAction_mk ρ g).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨QuotientGroup.mk g, quotientAction_mk ρ g⟩

end Kernel

/-! ### One bit: the orders-four and -two cyclic groups realize the same action -/

section BoolExample

/-- Negation of a bit as a permutation. -/
def flip : Equiv.Perm Bool := Equiv.swap false true

theorem flip_mul_self : flip * flip = 1 := by decide

/-- The cyclic group of order four acting on a bit by negation to the power of the exponent. -/
def c4Action : Multiplicative (ZMod 4) →* Equiv.Perm Bool :=
  MonoidHom.mk' (fun g => flip ^ (Multiplicative.toAdd g).val) (by decide)

/-- The cyclic group of order two acting on a bit by negation. -/
def c2Action : Multiplicative (ZMod 2) →* Equiv.Perm Bool :=
  MonoidHom.mk' (fun g => flip ^ (Multiplicative.toAdd g).val) (by decide)

/-- The order-four action depends only on the parity of the exponent. -/
theorem c4Action_apply : ∀ g : Multiplicative (ZMod 4),
    c4Action g = if (Multiplicative.toAdd g).val % 2 = 0 then 1 else flip := by decide

/-- The realized transformations of the order-four action are the identity and negation. -/
theorem c4Action_range : ∀ σ : Equiv.Perm Bool, σ ∈ c4Action.range ↔ σ = 1 ∨ σ = flip := by
  intro σ
  rw [MonoidHom.mem_range]
  revert σ
  decide

/-- The realized transformations of the order-two action are the identity and negation. -/
theorem c2Action_range : ∀ σ : Equiv.Perm Bool, σ ∈ c2Action.range ↔ σ = 1 ∨ σ = flip := by
  intro σ
  rw [MonoidHom.mem_range]
  revert σ
  decide

/-- Both actions realize the same transformation group. -/
theorem c4Action_range_eq_c2Action_range : c4Action.range = c2Action.range := by
  ext σ
  rw [c4Action_range, c2Action_range]

/-- The kernel of the order-four action consists of the even exponents. -/
theorem c4Action_ker_iff : ∀ g : Multiplicative (ZMod 4),
    g ∈ c4Action.ker ↔ g = 1 ∨ g = Multiplicative.ofAdd 2 := by
  intro g
  rw [MonoidHom.mem_ker]
  revert g
  decide

/-- The order-four action has a nontrivial kernel: the element of exponent two acts as the
identity. -/
theorem c4Action_ker_nontrivial :
    Multiplicative.ofAdd (2 : ZMod 4) ∈ c4Action.ker ∧
      Multiplicative.ofAdd (2 : ZMod 4) ≠ 1 := by
  rw [MonoidHom.mem_ker]
  decide

theorem c4Action_ker_ne_bot : c4Action.ker ≠ ⊥ := by
  intro h
  have hk := c4Action_ker_nontrivial
  rw [h, Subgroup.mem_bot] at hk
  exact hk.2 hk.1

/-- The order-two action is faithful. -/
theorem c2Action_injective : Function.Injective c2Action := by decide

theorem c2Action_ker : c2Action.ker = ⊥ :=
  (MonoidHom.ker_eq_bot_iff _).2 c2Action_injective

/-- The two groups realizing the same bit transformations are nonisomorphic. -/
theorem c4_not_isomorphic_c2 :
    ¬ Nonempty (Multiplicative (ZMod 4) ≃* Multiplicative (ZMod 2)) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e.toEquiv
  norm_num at h

end BoolExample

/-! ### Action isomorphisms and fixed-state counts -/

section Intertwining

/-- An isomorphism of actions: a group isomorphism and a state bijection that commute with
the two actions. -/
def Intertwines {G G' X X' : Type*} [Group G] [Group G']
    (ρ : G →* Equiv.Perm X) (ρ' : G' →* Equiv.Perm X') (φ : G ≃* G') (h : X ≃ X') : Prop :=
  ∀ g x, h (ρ g x) = ρ' (φ g) (h x)

/-- The number of states a permutation fixes. -/
def fixedCount {X : Type*} [Fintype X] [DecidableEq X] (σ : Equiv.Perm X) : ℕ :=
  Fintype.card {x // σ x = x}

/-- A state bijection carrying one permutation to another preserves the number of fixed
states. -/
theorem fixedCount_conj {X X' : Type*} [Fintype X] [DecidableEq X] [Fintype X']
    [DecidableEq X'] (σ : Equiv.Perm X) (σ' : Equiv.Perm X') (h : X ≃ X')
    (hc : ∀ x, h (σ x) = σ' (h x)) : fixedCount σ' = fixedCount σ := by
  unfold fixedCount
  exact (Fintype.card_congr (Equiv.subtypeEquiv h fun x => by
    rw [← hc]
    exact h.injective.eq_iff.symm)).symm

end Intertwining

/-! ### Four states: a transposition and a double transposition are not isomorphic actions -/

section FinFourExample

/-- The transposition of the first two states. -/
def transposition : Equiv.Perm (Fin 4) := Equiv.swap 0 1

/-- The product of two disjoint transpositions. -/
def doubleTransposition : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

/-- The order-two group acting by the transposition. -/
def transpositionAction : Multiplicative (ZMod 2) →* Equiv.Perm (Fin 4) :=
  MonoidHom.mk' (fun g => transposition ^ (Multiplicative.toAdd g).val) (by decide)

/-- The order-two group acting by the double transposition. -/
def doubleTranspositionAction : Multiplicative (ZMod 2) →* Equiv.Perm (Fin 4) :=
  MonoidHom.mk' (fun g => doubleTransposition ^ (Multiplicative.toAdd g).val) (by decide)

theorem transpositionAction_injective : Function.Injective transpositionAction := by decide

theorem doubleTranspositionAction_injective :
    Function.Injective doubleTranspositionAction := by decide

theorem transpositionAction_gen :
    transpositionAction (Multiplicative.ofAdd 1) = transposition := by decide

theorem doubleTranspositionAction_gen :
    doubleTranspositionAction (Multiplicative.ofAdd 1) = doubleTransposition := by decide

/-- The transposition fixes two states. -/
theorem transposition_fixedCount : fixedCount transposition = 2 := by decide

/-- The double transposition fixes no state. -/
theorem doubleTransposition_fixedCount : fixedCount doubleTransposition = 0 := by decide

theorem c2_elements : ∀ g : Multiplicative (ZMod 2), g = 1 ∨ g = Multiplicative.ofAdd 1 := by
  decide

/-- The two faithful actions are not isomorphic as actions: no state bijection and group
automorphism intertwine them, since the generator would have to be carried to the generator,
and conjugation preserves the fixed-state count. -/
theorem transposition_not_intertwines_double :
    ¬ ∃ (φ : Multiplicative (ZMod 2) ≃* Multiplicative (ZMod 2)) (h : Fin 4 ≃ Fin 4),
      Intertwines transpositionAction doubleTranspositionAction φ h := by
  rintro ⟨φ, h, hI⟩
  have hgen : φ (Multiplicative.ofAdd 1) = Multiplicative.ofAdd 1 := by
    rcases c2_elements (φ (Multiplicative.ofAdd 1)) with h1 | h1
    · exact absurd (φ.map_eq_one_iff.1 h1) (by decide)
    · exact h1
  have hc : ∀ x, h (transposition x) = doubleTransposition (h x) := by
    intro x
    have hx := hI (Multiplicative.ofAdd 1) x
    rwa [hgen, transpositionAction_gen, doubleTranspositionAction_gen] at hx
  have hcount := fixedCount_conj transposition doubleTransposition h hc
  rw [transposition_fixedCount, doubleTransposition_fixedCount] at hcount
  exact absurd hcount (by decide)

end FinFourExample

/-! ### Conjugate labeled operations have corresponding runs -/

section Runs

variable {A X X' I O : Type*}

/-- A state bijection intertwining labeled operations. -/
def IntertwinesOps (F : A → X → X) (F' : A → X' → X') (h : X ≃ X') : Prop :=
  ∀ a x, h (F a x) = F' a (h x)

/-- Every run is carried to the corresponding run. -/
theorem run_conj {F : A → X → X} {F' : A → X' → X'} {h : X ≃ X'} (hI : IntertwinesOps F F' h)
    (x : X) (w : List A) : h (run F x w) = run F' (h x) w :=
  run_intertwines F F' h hI x w

/-- With the input map preserved, marked runs correspond word by word. -/
theorem marked_run_conj {F : A → X → X} {F' : A → X' → X'} {h : X ≃ X'}
    (hI : IntertwinesOps F F' h) {inp : I → X} {inp' : I → X'} (hin : ∀ i, h (inp i) = inp' i)
    (i : I) (w : List A) : h (run F (inp i) w) = run F' (inp' i) w := by
  rw [run_conj hI, hin]

/-- With the input and output maps preserved, readouts agree. -/
theorem readout_conj {F : A → X → X} {F' : A → X' → X'} {h : X ≃ X'}
    (hI : IntertwinesOps F F' h) {inp : I → X} {inp' : I → X'} (hin : ∀ i, h (inp i) = inp' i)
    {out : X → O} {out' : X' → O} (hout : ∀ x, out' (h x) = out x) (i : I) (w : List A) :
    out' (run F' (inp' i) w) = out (run F (inp i) w) := by
  rw [← marked_run_conj hI hin, hout]

/-- A completion predicate transported along the bijection holds after the same words, so
the completing words, and hence the completion time of any word sequence, coincide. -/
theorem completion_conj {F : A → X → X} {F' : A → X' → X'} {h : X ≃ X'}
    (hI : IntertwinesOps F F' h) {inp : I → X} {inp' : I → X'} (hin : ∀ i, h (inp i) = inp' i)
    {done : X → Prop} {done' : X' → Prop} (hdone : ∀ x, done' (h x) ↔ done x)
    (i : I) (w : List A) : done' (run F' (inp' i) w) ↔ done (run F (inp i) w) := by
  rw [← marked_run_conj hI hin, hdone]

end Runs

/-! ### The monoid analogue: irreversible operations -/

section MonoidKernel

variable {M X : Type*} [Monoid M]

/-- The kernel congruence of a monoid acting by endomorphisms: two elements are related
exactly when they realize the same transformation. This is Mathlib's `Con.ker`. -/
def kernelCon (α : M →* Function.End X) : Con M := Con.ker α

theorem kernelCon_iff (α : M →* Function.End X) (a b : M) :
    kernelCon α a b ↔ α a = α b :=
  Con.ker_rel α

/-- Pointwise agreement on every state is the kernel congruence. -/
theorem kernelCon_iff_pointwise (α : M →* Function.End X) (a b : M) :
    kernelCon α a b ↔ ∀ x, α a x = α b x := by
  rw [kernelCon_iff]
  exact ⟨fun h x => by rw [h], fun h => funext h⟩

/-- The realized transformation monoid acts faithfully. -/
theorem mrange_faithful (α : M →* Function.End X) (f g : MonoidHom.mrange α)
    (h : ∀ x, (f : Function.End X) x = (g : Function.End X) x) : f = g :=
  Subtype.ext (funext h)

instance mrange_faithfulSMul (α : M →* Function.End X) :
    FaithfulSMul (MonoidHom.mrange α) X :=
  ⟨fun h => Subtype.ext (funext fun x => h x)⟩

/-- The first isomorphism theorem for monoids: the quotient by the kernel congruence is
isomorphic to the realized transformation monoid; Mathlib's `Con.quotientKerEquivRange`. -/
noncomputable def quotientEquivMrange (α : M →* Function.End X) :
    (kernelCon α).Quotient ≃* MonoidHom.mrange α :=
  Con.quotientKerEquivRange α

/-- The induced realized action of the quotient monoid: Mathlib's `Con.kerLift`. -/
def quotientMonoidAction (α : M →* Function.End X) :
    (kernelCon α).Quotient →* Function.End X :=
  Con.kerLift α

theorem quotientMonoidAction_mk (α : M →* Function.End X) (a : M) :
    quotientMonoidAction α (a : (kernelCon α).Quotient) = α a :=
  Con.kerLift_mk a

/-- The induced action of the quotient monoid is faithful. -/
theorem quotientMonoidAction_injective (α : M →* Function.End X) :
    Function.Injective (quotientMonoidAction α) :=
  Con.kerLift_injective α

/-- The quotient monoid realizes exactly the transformations of `α`. -/
theorem quotientMonoidAction_mrange (α : M →* Function.End X) :
    MonoidHom.mrange (quotientMonoidAction α) = MonoidHom.mrange α :=
  Con.kerLift_range_eq

end MonoidKernel

end KTAIT.OperationalActions
