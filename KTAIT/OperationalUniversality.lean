/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import KTAIT.OperationalReversibility

/-!
# A concrete universal effective monoid and group action (WP0004)

The fixed transition evaluates a program with successively larger finite bounds.
The bounded evaluator is Mathlib's primitive-recursive `Nat.Partrec.Code.evaln`.
Its bound is not a Turing-machine time bound; no unit-cost simulation is asserted.
The output is stored in the state, so observation only reads a field.
-/

namespace KTAIT.OperationalUniversality

open KTAIT.OperationalReversibility

/-- Run a computable transition until the observation first returns a result. -/
def execute {I S O : Type*} (F : S → S) (input : I → S) (observe : S → Option O)
    (x : I) : Part O :=
  Nat.rfindOpt fun n => observe (F^[n] (input x))

/-- Effective sequential actions with computable preparation and observation
compute only partial-recursive functions. No algebraic word-problem oracle is used. -/
theorem execute_partrec {I S O : Type*} [Primcodable I] [Primcodable S] [Primcodable O]
    {F : S → S} {input : I → S} {observe : S → Option O}
    (hF : Computable F) (hi : Computable input) (ho : Computable observe) :
    Partrec (execute F input observe) := by
  have hit : Computable (fun p : I × ℕ => F^[p.2] (input p.1)) := by
    have h := Computable.nat_rec Computable.snd (hi.comp Computable.fst)
      (hF.comp (Computable.snd.comp Computable.snd)).to₂
    refine h.of_eq ?_
    intro p
    induction p.2 with
    | zero => rfl
    | succ n ih => simp only [ih, Function.iterate_succ_apply']
  exact Partrec.rfindOpt (ho.comp hit).to₂

abbrev Code := Nat.Partrec.Code

local instance : DecidableEq Code := Encodable.decidableEqOfEncodable Code

/-- Program, input, current evaluation bound, and the latest bounded result. -/
abbrev Config := (Code × ℕ) × (ℕ × Option ℕ)

/-- Increase the finite evaluation bound and store the resulting output option. -/
def step (s : Config) : Config :=
  (s.1, (s.2.1 + 1, Nat.Partrec.Code.evaln (s.2.1 + 1) s.1.1 s.1.2))

/-- Input preparation performs no evaluation. -/
def initial (p : Code × ℕ) : Config := (p, (0, none))

/-- Completion and readout inspect the stored result. -/
def observe (s : Config) : Option ℕ := s.2.2

theorem step_primrec : Primrec step := by
  have hk : Primrec (fun s : Config => s.2.1 + 1) :=
    Primrec.succ.comp (Primrec.fst.comp Primrec.snd)
  exact Primrec.fst.pair (hk.pair (Nat.Partrec.Code.primrec_evaln.comp
    ((hk.pair (Primrec.fst.comp Primrec.fst)).pair (Primrec.snd.comp Primrec.fst))))

theorem initial_primrec : Primrec initial :=
  Primrec.id.pair ((Primrec.const 0).pair (Primrec.const none))

theorem observe_primrec : Primrec observe := Primrec.snd.comp Primrec.snd

theorem iterate_step (p : Code × ℕ) (n : ℕ) :
    step^[n] (initial p) = (p, (n, Nat.Partrec.Code.evaln n p.1 p.2)) := by
  induction n with
  | zero => simp [initial, Nat.Partrec.Code.evaln]
  | succ n ih => simp only [Function.iterate_succ_apply', ih, step]

/-- The fixed ordinary transition evaluates every code exactly, including divergence. -/
theorem monoid_evaluates (c : Code) (x : ℕ) :
    execute step initial observe (c, x) = c.eval x := by
  unfold execute
  simp only [iterate_step, observe]
  exact (Nat.Partrec.Code.eval_eq_rfindOpt c x).symm

/-- The ordinary universal transition overwrites the previous bounded result. -/
theorem step_not_injective : ¬ Function.Injective step := by
  intro h
  have e := h (a₁ := ((Nat.Partrec.Code.zero, 0), (0, none)))
    (a₂ := ((Nat.Partrec.Code.zero, 0), (0, some 0))) rfl
  cases e

/-- One fixed reversible transition, independent of the program and input. -/
def universalStep : Equiv.Perm (State Config) := advance step

def reversibleInitial (p : Code × ℕ) : State Config := prepare (initial p)

def reversibleObserve (z : State Config) : Option ℕ := observe z.1.1

theorem universal_step_primrec : Primrec universalStep := primrec_advance step_primrec

theorem universal_inverse_primrec : Primrec universalStep.symm :=
  primrec_advance_inverse step_primrec

theorem reversible_initial_primrec : Primrec reversibleInitial :=
  primrec_prepare.comp initial_primrec

theorem reversible_observe_primrec : Primrec reversibleObserve :=
  observe_primrec.comp (Primrec.fst.comp Primrec.fst)

theorem reversible_observation (p : Code × ℕ) (n : ℕ) :
    reversibleObserve (universalStep^[n] (reversibleInitial p)) =
      Nat.Partrec.Code.evaln n p.1 p.2 := by
  change observe (((advance step)^[n] (prepare (initial p))).1.1) = _
  rw [simulates, iterate_step]
  rfl

/-- Reversible execution has exactly the original program's partial semantics. -/
theorem group_evaluates (c : Code) (x : ℕ) :
    execute universalStep reversibleInitial reversibleObserve (c, x) = c.eval x := by
  unfold execute
  simp only [reversible_observation]
  exact (Nat.Partrec.Code.eval_eq_rfindOpt c x).symm

/-- Every partial-recursive function is computed by the same pair of involutions;
only the prepared code changes. -/
theorem universal_group {f : ℕ →. ℕ} (hf : Nat.Partrec f) :
    ∃ c : Code, ∀ x, execute universalStep reversibleInitial reversibleObserve (c, x) = f x := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hf
  exact ⟨c, fun x => (group_evaluates c x).trans (congrFun hc x)⟩

theorem universal_monoid {f : ℕ →. ℕ} (hf : Nat.Partrec f) :
    ∃ c : Code, ∀ x, execute step initial observe (c, x) = f x := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hf
  exact ⟨c, fun x => (monoid_evaluates c x).trans (congrFun hc x)⟩

/-- The fixed universal reversible action computes exactly the partial-recursive
functions under its stated preparation and completion/readout protocol. -/
theorem group_computability_iff (f : ℕ →. ℕ) :
    Nat.Partrec f ↔ ∃ c : Code, ∀ x,
      execute universalStep reversibleInitial reversibleObserve (c, x) = f x := by
  constructor
  · exact universal_group
  · rintro ⟨c, hc⟩
    apply Partrec.nat_iff.mp
    have h := execute_partrec universal_step_primrec.to_comp
      reversible_initial_primrec.to_comp reversible_observe_primrec.to_comp
    exact (h.comp ((Computable.const c).pair Computable.id)).of_eq hc

theorem monoid_computability_iff (f : ℕ →. ℕ) :
    Nat.Partrec f ↔ ∃ c : Code, ∀ x, execute step initial observe (c, x) = f x := by
  constructor
  · exact universal_monoid
  · rintro ⟨c, hc⟩
    apply Partrec.nat_iff.mp
    have h := execute_partrec step_primrec.to_comp initial_primrec.to_comp observe_primrec.to_comp
    exact (h.comp ((Computable.const c).pair Computable.id)).of_eq hc

end KTAIT.OperationalUniversality
