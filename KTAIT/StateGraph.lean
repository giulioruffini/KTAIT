/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.OrbitLabel

/-!
# KTAIT.StateGraph — singleton support layers are the graph of a permutation (WP0218 App. E)

Susskind's conservation of information asks that a complete state have exactly one allowed
successor and exactly one allowed predecessor. On a transition-support relation `R` (`R i j`
when `j` is a dynamically possible successor of `i`) this is `UniqueSucc R ∧ UniquePred R`.
The results here:

* `permGraph_of_unique` / `unique_of_permGraph`: that condition holds if and only if `R` is
  the graph of a permutation `σ` of the state space (`R i j ↔ σ i = j`). No finiteness is
  assumed, and the empty state space is covered (`Equiv.Perm` of the empty type exists).
* `Steps R k`: the exact-`k`-step relation. `steps_iff_pow` identifies it with `σ ^ k`, so
  every exact-time future and past layer is a singleton (`steps_unique_succ`,
  `steps_unique_pred`): the one-step condition already gives all `k`.
* `orbit_label_of_unique`: the permutation's orbit label (`OrbitLabel.genEnergy`) is conserved,
  closing the chain "singleton layers ⇒ permutation ⇒ conserved orbit label" used in WP0218's
  appendix on information conservation.

Pure relation and permutation algebra; no AIT frame and no axioms beyond Lean's core.
Bounded recovery advice (`O(1)` bits, the form WP0218's Lemma 2 consumes) is weaker than the
singleton condition and is deliberately not identified with it here.
-/

namespace KTAIT
namespace StateGraph

variable {X : Type} (R : X → X → Prop)

/-- Every state has exactly one allowed successor. -/
def UniqueSucc : Prop := ∀ i, ∃! j, R i j

/-- Every state has exactly one allowed predecessor. -/
def UniquePred : Prop := ∀ j, ∃! i, R i j

/-- `R` is the graph of a permutation: `R i j ↔ σ i = j` for some `σ : Equiv.Perm X`. -/
def IsPermGraph : Prop := ∃ σ : Equiv.Perm X, ∀ i j, R i j ↔ σ i = j

/-- **Singleton support layers give a permutation.** Unique successors and unique predecessors
    make the successor map injective and surjective, hence a permutation whose graph is `R`. -/
theorem permGraph_of_unique (hs : UniqueSucc R) (hp : UniquePred R) : IsPermGraph R := by
  classical
  let f : X → X := fun i => Classical.choose (hs i).exists
  have hf : ∀ i, R i (f i) := fun i => Classical.choose_spec (hs i).exists
  have hf_unique : ∀ i j, R i j → j = f i := fun i j h => (hs i).unique h (hf i)
  have hinj : Function.Injective f := by
    intro a b hab
    have ha : R a (f a) := hf a
    have hb : R b (f a) := by rw [hab]; exact hf b
    exact (hp (f a)).unique ha hb
  have hsurj : Function.Surjective f := by
    intro j
    obtain ⟨i, hi, _⟩ := hp j
    exact ⟨i, (hf_unique i j hi).symm⟩
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun i j => ?_⟩
  constructor
  · intro h
    change f i = j
    exact (hf_unique i j h).symm
  · intro h
    have hfi : f i = j := h
    rw [← hfi]
    exact hf i

/-- **A permutation graph has singleton support layers.** -/
theorem unique_of_permGraph (h : IsPermGraph R) : UniqueSucc R ∧ UniquePred R := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨fun i => ⟨σ i, (hσ i (σ i)).mpr rfl, fun j hj => ((hσ i j).mp hj).symm⟩,
    fun j => ⟨σ.symm j, (hσ _ _).mpr (σ.apply_symm_apply j), fun i hi => ?_⟩⟩
  exact σ.eq_symm_apply.mpr ((hσ i j).mp hi)

/-- The singleton-support condition is equivalent to being a permutation graph. -/
theorem unique_iff_permGraph : (UniqueSucc R ∧ UniquePred R) ↔ IsPermGraph R :=
  ⟨fun h => permGraph_of_unique R h.1 h.2, unique_of_permGraph R⟩

/-- Exactly `k` allowed steps lead from `i` to `j`. -/
def Steps : ℕ → X → X → Prop
  | 0, i, j => i = j
  | k + 1, i, j => ∃ m, R i m ∧ Steps k m j

/-- On a permutation graph, `k` exact steps are the `k`-th power of the permutation. -/
theorem steps_iff_pow (σ : Equiv.Perm X) (hσ : ∀ i j, R i j ↔ σ i = j) :
    ∀ (k : ℕ) (i j : X), Steps R k i j ↔ (σ ^ k) i = j := by
  intro k
  induction k with
  | zero => intro i j; simp [Steps]
  | succ k ih =>
    intro i j
    rw [pow_succ, Equiv.Perm.mul_apply]
    constructor
    · rintro ⟨m, hm, hk⟩
      rw [(hσ i m).mp hm]
      exact (ih m j).mp hk
    · intro h
      exact ⟨σ i, (hσ i (σ i)).mpr rfl, (ih (σ i) j).mpr h⟩

/-- Every exact-time future layer of a permutation graph is a singleton. -/
theorem steps_unique_succ (h : IsPermGraph R) (k : ℕ) (i : X) : ∃! j, Steps R k i j := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨(σ ^ k) i, (steps_iff_pow R σ hσ k i _).mpr rfl, fun j hj => ?_⟩
  exact ((steps_iff_pow R σ hσ k i j).mp hj).symm

/-- Every exact-time past layer of a permutation graph is a singleton. -/
theorem steps_unique_pred (h : IsPermGraph R) (k : ℕ) (j : X) : ∃! i, Steps R k i j := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨(σ ^ k).symm j, (steps_iff_pow R σ hσ k _ j).mpr ((σ ^ k).apply_symm_apply j),
    fun i hi => ?_⟩
  exact (σ ^ k).eq_symm_apply.mpr ((steps_iff_pow R σ hσ k i j).mp hi)

/-- **Singleton layers give a conserved orbit label.** The permutation obtained from
    `permGraph_of_unique` carries the orbit label of `KTAIT.OrbitLabel`, which is invariant
    along every allowed transition. -/
theorem orbit_label_of_unique (hs : UniqueSucc R) (hp : UniquePred R) :
    ∃ σ : Equiv.Perm X, (∀ i j, R i j ↔ σ i = j) ∧
      ∀ i j, R i j → OrbitLabel.genEnergy σ j = OrbitLabel.genEnergy σ i := by
  obtain ⟨σ, hσ⟩ := permGraph_of_unique R hs hp
  refine ⟨σ, hσ, fun i j hij => ?_⟩
  rw [← (hσ i j).mp hij]
  exact OrbitLabel.genEnergy_conserved σ i

end StateGraph
end KTAIT
