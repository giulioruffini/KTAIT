/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
# Persistent marking for enumerable equivalence classes (WP0228)

This executable finite-state variant scans certified neighborhoods, rather than maintaining
connected components. An emission marks all fresh vertices in its observed neighborhood,
at least `h` of them. The charging inequality is sufficient; no marks are erased. A full
enumeration of the relation, including certificates through longer intermediate programs,
is restricted to the finite vertex set only after taking the relation's closure.

The definitions use only finite tests and the supplied stream. The proofs do not consult a
decision procedure for the final equivalence relation. This module does not establish a
Mathlib `Computable` instance for the parameterized stream transformer.
-/

namespace KTAIT.CertifiedPrograms

variable {α : Type} [DecidableEq α]

structure MarkState (α : Type) where
  marked : Finset α
  emitted : List α

def emptyState : MarkState α := ⟨∅, []⟩

/-- A single emission charges every fresh vertex of a certified neighborhood. -/
def markStep (h : Nat) (p : α) (S : Finset α) (s : MarkState α) : MarkState α :=
  if h ≤ (S \ s.marked).card then
    ⟨s.marked ∪ (S \ s.marked), p :: s.emitted⟩
  else s

def MarkInvariant (R : α → α → Prop) (h : Nat) (s : MarkState α) : Prop :=
  s.emitted.length * h ≤ s.marked.card ∧
  ∀ a ∈ s.marked, ∃ p ∈ s.emitted, R p a

omit [DecidableEq α] in
theorem marking_empty_invariant (R : α → α → Prop) (h : Nat) :
    MarkInvariant R h (emptyState : MarkState α) := by
  simp [MarkInvariant, emptyState]

/-- Persistent marks charge distinct vertices and retain the representative of every mark. -/
theorem marking_step_invariant (R : α → α → Prop) (h : Nat) (p : α)
    (S : Finset α) (s : MarkState α) (hs : MarkInvariant R h s)
    (hS : ∀ a ∈ S, R p a) : MarkInvariant R h (markStep h p S s) := by
  unfold markStep
  split_ifs with hc
  · rcases hs with ⟨hb, hw⟩
    constructor
    · simp only [List.length_cons]
      rw [Finset.card_union_of_disjoint (by
        apply Finset.disjoint_left.mpr
        intro a ha hb
        exact (Finset.mem_sdiff.mp hb).2 ha)]
      nlinarith
    · intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · obtain ⟨q, hq, hr⟩ := hw a ha
        exact ⟨q, List.mem_cons_of_mem p hq, hr⟩
      · exact ⟨p, List.mem_cons_self, hS a (Finset.mem_sdiff.mp ha).1⟩
  · exact hs

theorem marking_step_preserves_events (h : Nat) (p : α) (S : Finset α)
    (s : MarkState α) : s.emitted ⊆ (markStep h p S s).emitted := by
  unfold markStep
  split_ifs <;> simp

/-- A fully observed large class is covered immediately, or was covered by an earlier mark. -/
theorem marking_step_covers (R : α → α → Prop) (hR : Equivalence R)
    (h : Nat) (p : α) (C S : Finset α) (s : MarkState α)
    (hs : MarkInvariant R h s) (hC : ∀ a ∈ C, R p a)
    (hCS : C ⊆ S) (hlarge : h ≤ C.card) :
    ∃ q ∈ (markStep h p S s).emitted, R p q := by
  classical
  by_cases hex : ∃ a ∈ C, a ∈ s.marked
  · obtain ⟨a, haC, ham⟩ := hex
    obtain ⟨q, hq, hqa⟩ := hs.2 a ham
    exact ⟨q, marking_step_preserves_events h p S s hq,
      hR.trans (hC a haC) (hR.symm hqa)⟩
  · have hsub : C ⊆ S \ s.marked := by
      intro a ha
      exact Finset.mem_sdiff.mpr ⟨hCS ha, fun hm => hex ⟨a, ha, hm⟩⟩
    have hc : h ≤ (S \ s.marked).card :=
      hlarge.trans (Finset.card_le_card hsub)
    exact ⟨p, by simp [markStep, hc], hR.refl p⟩

variable [Fintype α]

/-- Relation pairs observed in the finite prefix; membership of the final relation is unused. -/
def observed (e : Nat → Option (α × α)) (n : Nat) (p : α) : Finset α :=
  Finset.univ.filter fun a => ∃ j ∈ Finset.range n, e j = some (p, a)

theorem observed_mono (e : Nat → Option (α × α)) (p : α) {n m : Nat}
    (hnm : n ≤ m) : observed e n p ⊆ observed e m p := by
  intro a ha
  simp only [observed, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_range] at ha ⊢
  obtain ⟨j, hj, he⟩ := ha
  exact ⟨j, lt_of_lt_of_le hj hnm, he⟩

theorem observed_sound (R : α → α → Prop) (e : Nat → Option (α × α))
    (he : ∀ j p a, e j = some (p, a) → R p a) (n : Nat) (p : α) :
    ∀ a ∈ observed e n p, R p a := by
  intro a ha
  simp only [observed, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  obtain ⟨j, _, hj⟩ := ha
  exact he j p a hj

/-- Every finite family of certified pairs is eventually observed together. -/
theorem observed_eventually_contains (R : α → α → Prop)
    (e : Nat → Option (α × α))
    (he : ∀ p a, R p a → ∃ j, e j = some (p, a))
    (p : α) (C : Finset α) (hC : ∀ a ∈ C, R p a) :
    ∃ n, C ⊆ observed e n p := by
  classical
  induction C using Finset.induction_on with
  | empty => exact ⟨0, Finset.empty_subset _⟩
  | @insert a C _ ih =>
    obtain ⟨j, hj⟩ := he p a (hC a (by simp))
    obtain ⟨n, hn⟩ := ih (fun b hb => hC b (Finset.mem_insert_of_mem hb))
    refine ⟨max n (j + 1), ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · simp only [observed, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_range]
      exact ⟨j, lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_right _ _), hj⟩
    · exact observed_mono e p (le_max_left _ _) (hn hb)

/-- Round-robin representative; all finite vertices are visited after every cutoff. -/
def scanVertex (m n : Nat) : Fin (m + 1) :=
  ⟨n % (m + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

def markingRun {m : Nat} (e : Nat → Option (Fin (m + 1) × Fin (m + 1)))
    (h : Nat) : Nat → MarkState (Fin (m + 1))
  | 0 => emptyState
  | n + 1 => markStep h (scanVertex m n) (observed e n (scanVertex m n))
      (markingRun e h n)

/-- The executable scan preserves charging and witness tracking at every finite stage. -/
theorem marking_run_invariant {m : Nat} (R : Fin (m + 1) → Fin (m + 1) → Prop)
    (e : Nat → Option (Fin (m + 1) × Fin (m + 1)))
    (he : ∀ j p a, e j = some (p, a) → R p a) (h n : Nat) :
    MarkInvariant R h (markingRun e h n) := by
  induction n with
  | zero => exact marking_empty_invariant R h
  | succ n ih =>
    exact marking_step_invariant R h _ _ _ ih (observed_sound R e he _ _)

/-- The budget is derived from fresh marks, with no hypothesis about the number of events. -/
theorem marking_event_budget {m : Nat} (R : Fin (m + 1) → Fin (m + 1) → Prop)
    (e : Nat → Option (Fin (m + 1) × Fin (m + 1)))
    (he : ∀ j p a, e j = some (p, a) → R p a) (h n : Nat) :
    (markingRun e h n).emitted.length * h ≤ m + 1 := by
  exact (marking_run_invariant R e he h n).1.trans
    (by simpa using Finset.card_le_univ (markingRun e h n).marked)

/-- Every sufficiently large final class eventually receives a representative. This theorem
proves the eventual claim from completeness of the original pair stream and the actual scan. -/
theorem marking_eventual_coverage {m : Nat}
    (R : Fin (m + 1) → Fin (m + 1) → Prop) (hR : Equivalence R)
    (e : Nat → Option (Fin (m + 1) × Fin (m + 1)))
    (hes : ∀ j p a, e j = some (p, a) → R p a)
    (hec : ∀ p a, R p a → ∃ j, e j = some (p, a))
    (h : Nat) (p : Fin (m + 1)) (C : Finset (Fin (m + 1)))
    (hC : ∀ a ∈ C, R p a) (hlarge : h ≤ C.card) :
    ∃ n q, q ∈ (markingRun e h n).emitted ∧ R p q := by
  obtain ⟨N, hN⟩ := observed_eventually_contains R e hec p C hC
  let n := N * (m + 1) + p.val
  have hNn : N ≤ n := by dsimp [n]; nlinarith
  have hp : scanVertex m n = p := by
    apply Fin.ext
    simp [scanVertex, n, Nat.add_mod, Nat.mod_eq_of_lt p.isLt]
  have hsub : C ⊆ observed e n (scanVertex m n) := by
    rw [hp]
    exact hN.trans (observed_mono e p hNn)
  have hCn : ∀ a ∈ C, R (scanVertex m n) a := by simpa [hp] using hC
  obtain ⟨q, hq, hr⟩ := marking_step_covers R hR h _ C _ _
    (marking_run_invariant R e hes h n) hCn hsub hlarge
  exact ⟨n + 1, q, hq, by simpa [hp] using hr⟩

omit [Fintype α] [DecidableEq α] in
/-- Taking a structural class of each candidate cannot increase the number of candidates. -/
theorem structure_image_card_le {β : Type} [DecidableEq β]
    (S : Finset α) (structureClass : α → β) :
    (S.image structureClass).card ≤ S.card := Finset.card_image_le

end KTAIT.CertifiedPrograms
