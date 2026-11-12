/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import Mathlib

/-!
# Reversible simulation by recording history (WP0004)

A total transition on a decidable state space is simulated by a permutation
on states with finite histories and a direction bit. Both generators are
involutions. Completion is an observation, not a fixed point of the permutation.
-/

namespace KTAIT.OperationalReversibility

variable {S : Type*}

/-- Current state and a stack of previous states. -/
abbrev History (S : Type*) := S × List S

/-- The direction bit distinguishes the two ends of each reversible edge. -/
abbrev State (S : Type*) := History S × Bool

/-- Store the previous state before executing the transition. -/
def record (F : S → S) (c : History S) : History S := (F c.1, c.1 :: c.2)

theorem record_injective (F : S → S) : Function.Injective (record F) := by
  rintro ⟨s, h⟩ ⟨t, k⟩ he
  simpa [record] using congrArg Prod.snd he

/-- Reverse the direction bit. -/
def turn : Equiv.Perm (State S) where
  toFun z := (z.1, !z.2)
  invFun z := (z.1, !z.2)
  left_inv z := by simp
  right_inv z := by simp

/-- Pair each positive state with its recorded successor; leave unmatched
negative states fixed. Testing membership in the image requires one call to F. -/
def crossFun [DecidableEq S] (F : S → S) : State S → State S
  | (c, true) => (record F c, false)
  | ((s, []), false) => ((s, []), false)
  | ((s, t :: h), false) =>
      if F t = s then ((t, h), true) else ((s, t :: h), false)

theorem cross_involutive [DecidableEq S] (F : S → S) : Function.Involutive (crossFun F) := by
  rintro ⟨⟨s, h⟩, b⟩
  cases b
  · cases h with
    | nil => rfl
    | cons t h =>
      by_cases e : F t = s <;> simp [crossFun, record, e]
  · simp [crossFun, record]

/-- The history-edge matching is a permutation. -/
def cross [DecidableEq S] (F : S → S) : Equiv.Perm (State S) :=
  (cross_involutive F).toPerm (crossFun F)

theorem turn_involutive : Function.Involutive (turn (S := S)) := by
  intro z
  simp [turn]

theorem turn_sq : (turn (S := S)) ^ 2 = 1 := by
  apply Equiv.ext
  intro z
  exact turn_involutive z

theorem cross_sq [DecidableEq S] (F : S → S) : cross F ^ 2 = 1 := by
  apply Equiv.ext
  intro z
  exact cross_involutive F z

/-- One simulated step: cross a history edge, then turn toward the next edge. -/
def advance [DecidableEq S] (F : S → S) : Equiv.Perm (State S) := turn * cross F

variable [DecidableEq S]

theorem advance_positive (F : S → S) (c : History S) :
    advance F (c, true) = (record F c, true) := rfl

theorem advance_iterate_positive (F : S → S) (c : History S) (n : ℕ) :
    (advance F)^[n] (c, true) = ((record F)^[n] c, true) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, advance_positive]

omit [DecidableEq S] in
theorem record_iterate_state (F : S → S) (c : History S) (n : ℕ) :
    ((record F)^[n] c).1 = F^[n] c.1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', record, ih]

omit [DecidableEq S] in
theorem record_iterate_length (F : S → S) (c : History S) (n : ℕ) :
    ((record F)^[n] c).2.length = c.2.length + n := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply', record, ih, Nat.add_assoc]

/-- Prepare a fresh forward computation. -/
def prepare (s : S) : State S := ((s, []), true)

/-- Every finite forward run is simulated with the same number of steps. -/
theorem simulates (F : S → S) (s : S) (n : ℕ) :
    ((advance F)^[n] (prepare s)).1.1 = F^[n] s := by
  rw [prepare, advance_iterate_positive]
  exact record_iterate_state F (s, []) n

/-- The length of retained history records the number of simulated steps. -/
theorem simulation_history_length (F : S → S) (s : S) (n : ℕ) :
    ((advance F)^[n] (prepare s)).1.2.length = n := by
  rw [prepare, advance_iterate_positive, record_iterate_length]
  simp

/-- Halting and output observations are preserved at every finite time. -/
theorem observation_simulates {O : Type*} (F : S → S) (observe : S → O)
    (s : S) (n : ℕ) :
    observe (((advance F)^[n] (prepare s)).1.1) = observe (F^[n] s) := by
  rw [simulates]

/-- The abstract reversible machine uses a fixed pair of involutions. -/
def machineGroup (F : S → S) : Subgroup (Equiv.Perm (State S)) :=
  Subgroup.closure {turn, cross F}

theorem advance_mem (F : S → S) : advance F ∈ machineGroup F := by
  apply Subgroup.mul_mem
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- The positive-time evolution is an element of the generated group. -/
theorem advance_pow_mem (F : S → S) (n : ℕ) : advance F ^ n ∈ machineGroup F :=
  Subgroup.pow_mem _ (advance_mem F) n

/-- Different times give different transformations, even for a constant F. -/
theorem advance_powers_injective (F : S → S) (s : S) :
    Function.Injective (fun n : ℕ => advance F ^ n) := by
  intro m n e
  have h := congrArg (fun p : Equiv.Perm (State S) => (p (prepare s)).1.2.length) e
  simpa only [Equiv.Perm.coe_pow, simulation_history_length] using h

/-- The same evolution gives a faithful action of the integers for every F. -/
theorem advance_integer_powers_injective (F : S → S) (s : S) :
    Function.Injective (fun n : ℤ => advance F ^ n) :=
  injective_zpow_iff_not_isOfFinOrder.mpr
    (injective_pow_iff_not_isOfFinOrder.mp (advance_powers_injective F s))

/-- Its realized cyclic group is isomorphic to Z, irrespective of the computation. -/
noncomputable def integerActionEquiv (F : S → S) (s : S) :
    Multiplicative ℤ ≃* ((zpowersHom (Equiv.Perm (State S))) (advance F)).range :=
  MonoidHom.ofInjective (advance_integer_powers_injective F s)

section Effectivity

variable [Primcodable S]

omit [DecidableEq S] in
/-- Recording finite history is primitive recursive when the transition is. -/
theorem primrec_record {F : S → S} (hF : Primrec F) : Primrec (record F) :=
  (hF.comp Primrec.fst).pair (Primrec.list_cons.comp Primrec.fst Primrec.snd)

omit [DecidableEq S] in
theorem primrec_turn : Primrec (turn (S := S)) :=
  Primrec.fst.pair (Primrec.not.comp Primrec.snd)

/-- The completed inverse uses only equality, list operations, and one F step. -/
theorem primrec_cross {F : S → S} (hF : Primrec F) : Primrec (cross F) := by
  have hp : Primrec (fun c : History S => (record F c, false)) :=
    (primrec_record hF).pair (Primrec.const false)
  have hn : Primrec (fun c : History S =>
      List.casesOn (motive := fun _ => State S) c.2 (c, false) fun t h =>
        if F t = c.1 then ((t, h), true) else (c, false)) := by
    refine Primrec.list_casesOn (h := fun c th =>
      if F th.1 = c.1 then (th, true) else (c, false))
      Primrec.snd (Primrec.id.pair (Primrec.const false)) ?_
    exact Primrec.ite
      (Primrec.eq.comp (hF.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.pair (Primrec.const true))
      (Primrec.fst.pair (Primrec.const false))
  refine (Primrec.cond Primrec.snd (hp.comp Primrec.fst)
    (hn.comp Primrec.fst)).of_eq ?_
  rintro ⟨⟨s, h⟩, b⟩
  cases b <;> cases h <;> rfl

theorem primrec_advance {F : S → S} (hF : Primrec F) : Primrec (advance F) :=
  primrec_turn.comp (primrec_cross hF)

theorem primrec_advance_inverse {F : S → S} (hF : Primrec F) :
    Primrec (advance F).symm := by
  convert (primrec_cross hF).comp primrec_turn using 1
  funext z
  rfl

omit [DecidableEq S] in
theorem primrec_prepare : Primrec (prepare (S := S)) :=
  (Primrec.id.pair (Primrec.const [])).pair (Primrec.const true)

end Effectivity

end KTAIT.OperationalReversibility
