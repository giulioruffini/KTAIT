/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib

/-!
# KTAIT.NoetherFlow — generalized Noether: symmetry ⇒ conserved quantity (geometry track)

The KT content of the "(generalized) Noether's theorem" of *Structured Dynamics in the
Algorithmic Agent* (Entropy 2025, 27:90): a continuous symmetry of the dynamics yields a
conserved quantity, and conserved quantities are the trajectory labels — constant along the flow.

We model the flow abstractly as the action of a time group `T` on the state space `X`
(`AddAction T X`); this is the continuous-time analogue of the discrete `OrbitLabel`. No
differential geometry is needed for this layer, and it is axiom-free. (The genuine Lie-group /
manifold theorems of the paper — transitivity, homogeneous spaces `G/H`, moduli stacks — are the
heavier geometry track and are not attempted here.)
-/

namespace KTAIT
namespace Noether

/-- A quantity `C` is **conserved** by the `T`-flow if it is constant along every trajectory:
    `C (t +ᵥ x) = C x` for all times `t`. -/
def Conserved (T : Type) [AddGroup T] {X : Type} [AddAction T X] {L : Type} (C : X → L) : Prop :=
  ∀ (t : T) (x : X), C (t +ᵥ x) = C x

variable (T : Type) [AddGroup T] (X : Type) [AddAction T X]

/-- Same-trajectory relation: `y` is reached from `x` by flowing for some (signed) time. -/
def coflow (x y : X) : Prop := ∃ t : T, t +ᵥ x = y

theorem coflow_refl (x : X) : coflow T X x x := ⟨0, by simp⟩

theorem coflow_symm {x y : X} (h : coflow T X x y) : coflow T X y x := by
  obtain ⟨t, h⟩ := h
  exact ⟨-t, by rw [← h, ← add_vadd, neg_add_cancel, zero_vadd]⟩

theorem coflow_trans {x y z : X} (hxy : coflow T X x y) (hyz : coflow T X y z) :
    coflow T X x z := by
  obtain ⟨s, hs⟩ := hxy
  obtain ⟨t, ht⟩ := hyz
  exact ⟨t + s, by rw [add_vadd, hs, ht]⟩

/-- Trajectories partition the state space (the flow-orbit equivalence). -/
def trajSetoid : Setoid X :=
  ⟨coflow T X, coflow_refl T X, fun {_ _} => coflow_symm T X, fun {_ _ _} => coflow_trans T X⟩

/-- The **trajectory label** of a state: which trajectory it lies on. -/
def trajLabel (x : X) : Quotient (trajSetoid T X) := Quotient.mk (trajSetoid T X) x

/-- **Generalized Noether (core).** The trajectory label is a conserved quantity — constant
    along the flow. (Every conserved quantity factors through it; it is the universal one.) -/
theorem trajLabel_conserved : Conserved T (trajLabel T X) := by
  intro t x
  apply Quotient.sound
  exact ⟨-t, by rw [← add_vadd, neg_add_cancel, zero_vadd]⟩

/-- **Noether correspondence.** A symmetry `σ` that commutes with the flow (maps solutions to
    solutions) carries conserved quantities to conserved quantities: if `C` is conserved, so is
    `C ∘ σ`. Thus the symmetry group acts on the conserved quantities of the dynamics. -/
theorem conserved_comp_symm {L : Type} {C : X → L} (hC : Conserved T C) (σ : X → X)
    (hcomm : ∀ (t : T) (x : X), σ (t +ᵥ x) = t +ᵥ σ x) :
    Conserved T (fun x => C (σ x)) := by
  intro t x
  change C (σ (t +ᵥ x)) = C (σ x)
  rw [hcomm]
  exact hC t (σ x)

end Noether
end KTAIT
