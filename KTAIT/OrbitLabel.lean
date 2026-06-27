/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib

/-!
# KTAIT.OrbitLabel — generalized energy as a conserved orbit label (WP0162 App. C)

If information conservation forces the dynamics to be a bijection `F` on the (reachable) state
space, the relation "reachable from one another under some signed power of `F`" is an
equivalence, and the orbit label `E(x) = ⟦x⟧` is conserved: `E(F x) = E(x)`. This is KT's
*generalized energy*. It is pure dynamics — no AIT axioms — so it is fully proved here.
-/

namespace KTAIT
namespace OrbitLabel

variable {X : Type} (F : Equiv.Perm X)

/-- States in the same orbit: `y` is reached from `x` under some signed power of `F`. -/
def Rel (x y : X) : Prop := ∃ n : ℤ, (F ^ n) x = y

theorem rel_refl (x : X) : Rel F x x := ⟨0, by simp⟩

theorem rel_symm {x y : X} (h : Rel F x y) : Rel F y x := by
  obtain ⟨n, hn⟩ := h
  refine ⟨-n, ?_⟩
  rw [← hn, ← Equiv.Perm.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero, Equiv.Perm.coe_one,
    id_eq]

theorem rel_trans {x y z : X} (hxy : Rel F x y) (hyz : Rel F y z) : Rel F x z := by
  obtain ⟨m, hm⟩ := hxy
  obtain ⟨n, hn⟩ := hyz
  exact ⟨n + m, by rw [zpow_add, Equiv.Perm.mul_apply, hm, hn]⟩

/-- The orbit equivalence induced by the bijective dynamics `F`. -/
def setoid : Setoid X := ⟨Rel F, rel_refl F, fun {_ _} => rel_symm F, fun {_ _ _} => rel_trans F⟩

/-- **Generalized energy** = the orbit label of a state. -/
def genEnergy (x : X) : Quotient (setoid F) := Quotient.mk (setoid F) x

/-- **Orbit-label theorem (generalized energy is conserved).** The orbit label is invariant
    under the dynamics: `E(F x) = E(x)`. -/
theorem genEnergy_conserved (x : X) : genEnergy F (F x) = genEnergy F x := by
  apply Quotient.sound
  exact ⟨-1, by simp⟩

end OrbitLabel
end KTAIT
