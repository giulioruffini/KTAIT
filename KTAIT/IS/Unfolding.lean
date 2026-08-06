/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib

/-!
# KTAIT.IS.Unfolding — WP0215: finite-horizon unfolding, and what it does not give

BCOM WP0215 retracts one formulation of an earlier KT reply to the unfolding argument. The
earlier note argued that a fixed class of feedforward networks is not Turing complete and that
this weakens the unfolding construction. It does not. For a fixed recurrent machine and a fixed
finite horizon, the computation unrolls into an acyclic layered evaluator computing the same map.
This module supplies that construction, so the retraction rests on a proof rather than on a
concession.

**The state carries everything that changes.** `Recurrent X S Y` puts weights, learning-rate
schedules, plasticity variables, and any other quantity that the dynamics updates inside the
state `S`. This is the load-bearing modelling choice: with it, adaptation is no obstacle to
unfolding, because an adapting machine is just a machine whose state is bigger. An argument that
plasticity defeats finite-horizon unfolding must therefore deny this representation — it cannot
be won inside it. The paper says so in prose; here it is forced by the type.

**Acyclicity is typed, not asserted.** In `Layered X Y T` each layer has its own carrier type and
layer `k` produces only a `Carrier (k+1)`. A feedback edge is not a rejected term; it is
unwritable.

**There is no cost model here**, so no size, depth, or width bound is stated asymptotically.
`unfolding_layers_eq_state` records the construction's shape definitionally — `T` layers, each
carrying a copy of the recurrent state — and nothing more. Claims about growth need a resource
measure this development does not have.

**The honest negative.** A depth-`T` evaluator is a function of the first `T` inputs alone
(`depth_bounded_ignores_late_input`), so one fixed unfolding cannot serve every horizon
(`no_fixed_unfolding_covers_all_horizons`). What cannot be written in this development is the
uniform statement quantifying over a single acyclic machine "for all horizons": the type
`Layered X Y T` depends on `T`, so "a single `U` covering every `T`" has no type. The refutation
below is the statable form — one `U`, one horizon it fails at — and it is what the paper's
argument actually needs.

Mathlib only; no AIT interface and no axioms beyond Lean core.
-/

namespace KTAIT
namespace IS

variable {X Y S : Type}

/-! ### Recurrent machines -/

/-- A deterministic recurrent machine. The state `S` carries **everything that changes** —
activations, weights, plasticity variables, optimizer state. Nothing that the dynamics updates
sits outside it. -/
structure Recurrent (X S Y : Type) where
  /-- Initial state, including the initial weights. -/
  start : S
  /-- One update: the state absorbs the current input. Weight changes are state changes. -/
  step : S → X → S
  /-- Readout. -/
  out : S → Y

namespace Recurrent

/-- The state after `k` steps on the input stream `x`. -/
def stateAfter (M : Recurrent X S Y) (x : ℕ → X) : ℕ → S
  | 0 => M.start
  | k + 1 => M.step (M.stateAfter x k) (x k)

/-- The finite-horizon input–output map: run `T` steps, then read out. -/
def evalHorizon (M : Recurrent X S Y) (T : ℕ) (x : ℕ → X) : Y := M.out (M.stateAfter x T)

end Recurrent

/-! ### Acyclic layered evaluators -/

/-- A depth-`T` acyclic evaluator. Layer `k` has its own carrier type and feeds only layer
`k + 1`, so the graph is acyclic by typing: there is no term of any type that could send layer
`k + 1` back into layer `k`. The readout sits at layer `T`, and the `k < T` argument of `layer`
keeps the construction to exactly `T` layers. -/
structure Layered (X Y : Type) (T : ℕ) where
  /-- The carrier of each layer. -/
  Carrier : ℕ → Type
  /-- The input layer's value. -/
  init : Carrier 0
  /-- Layer `k`, defined only for `k < T`, consuming the `k`-th input. -/
  layer : ∀ k, k < T → Carrier k → X → Carrier (k + 1)
  /-- The readout, at layer `T`. -/
  readout : Carrier T → Y

namespace Layered

/-- The value at layer `k ≤ T` on the input stream `x`. -/
def valueAt {T : ℕ} (U : Layered X Y T) (x : ℕ → X) : ∀ k, k ≤ T → U.Carrier k
  | 0, _ => U.init
  | k + 1, h => U.layer k (by omega) (U.valueAt x k (by omega)) (x k)

/-- Evaluate the whole stack. -/
def eval {T : ℕ} (U : Layered X Y T) (x : ℕ → X) : Y := U.readout (U.valueAt x T le_rfl)

end Layered

/-! ### The construction -/

/-- The unfolding of `M` to horizon `T`: `T` copies of the recurrent state, wired in a line. -/
def unfold (M : Recurrent X S Y) (T : ℕ) : Layered X Y T where
  Carrier := fun _ => S
  init := M.start
  layer := fun _ _ s a => M.step s a
  readout := M.out

theorem unfold_valueAt (M : Recurrent X S Y) (T : ℕ) (x : ℕ → X) :
    ∀ (k : ℕ) (h : k ≤ T), (unfold M T).valueAt x k h = M.stateAfter x k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro h
      simp only [Layered.valueAt, Recurrent.stateAfter, ih (by omega)]
      rfl

/-- **Finite-horizon unfolding.** For every recurrent machine and every finite horizon there is
an acyclic depth-`T` evaluator computing the same input–output map. Constructive: the witness is
`unfold M T`.

This is the statement WP0215 concedes. Adaptation does not block it, because weights live in the
state `S` and are unrolled with everything else. -/
theorem finite_unfolding (M : Recurrent X S Y) (T : ℕ) :
    ∃ U : Layered X Y T, ∀ x, U.eval x = M.evalHorizon T x := by
  refine ⟨unfold M T, fun x => ?_⟩
  simp only [Layered.eval, Recurrent.evalHorizon, unfold_valueAt M T x T le_rfl]
  rfl

/-- **The shape of the unfolding, definitionally.** Every layer carries a copy of the recurrent
state, every layer applies the recurrent update, and the readout is the recurrent readout. There
are `T` layers because `layer` is defined exactly on `k < T`.

Deliberately not stated: any asymptotic size or depth bound. This development carries no cost
model — no notion of gate count, parameter count, or time — so "size grows linearly in `T`" is
not a proposition here. It is a claim about a resource measure that would first have to be
defined. -/
theorem unfolding_layers_eq_state (M : Recurrent X S Y) (T k : ℕ) :
    (unfold M T).Carrier k = S ∧
      (∀ (h : k < T) (s : S) (a : X), (unfold M T).layer k h s a = M.step s a) ∧
      (unfold M T).readout = M.out :=
  ⟨rfl, fun _ _ _ => rfl, rfl⟩

/-! ### What finite-horizon unfolding does not give -/

/-- **A depth-bounded evaluator is a function of the first `T` inputs alone.** Two input streams
agreeing up to `T` are indistinguishable to any depth-`T` layered evaluator, whatever it computes
and however it was built.

This is the precise residue of the resource argument: the unfolding is horizon-indexed, and the
horizon is part of what is being held fixed when one says two systems "compute the same
function". -/
theorem depth_bounded_ignores_late_input {T : ℕ} (U : Layered X Y T) (x x' : ℕ → X)
    (h : ∀ i, i < T → x i = x' i) : U.eval x = U.eval x' := by
  have key : ∀ (k : ℕ) (hk : k ≤ T), U.valueAt x k hk = U.valueAt x' k hk := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
        intro hk
        simp only [Layered.valueAt, ih (by omega), h k (by omega)]
  simp only [Layered.eval, key T le_rfl]

/-- The same statement for the recurrent machine at a fixed horizon: what happens after step `T`
cannot reach the horizon-`T` readout. -/
theorem evalHorizon_ignores_late_input (M : Recurrent X S Y) (T : ℕ) (x x' : ℕ → X)
    (h : ∀ i, i < T → x i = x' i) : M.evalHorizon T x = M.evalHorizon T x' := by
  have key : ∀ k, k ≤ T → M.stateAfter x k = M.stateAfter x' k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih => intro hk; simp only [Recurrent.stateAfter, ih (by omega), h k (by omega)]
  simp only [Recurrent.evalHorizon, key T le_rfl]

/-- An echo machine: the state is the last input seen, and the readout returns it. Its
horizon-`(T+1)` map depends on the input at index `T`, which is exactly what a depth-`T`
unfolding cannot see. -/
def echo : Recurrent Bool Bool Bool where
  start := false
  step := fun _ a => a
  out := fun s => s

/-- **No fixed unfolding covers every horizon.** For the echo machine there is no depth and no
acyclic evaluator of that depth that reproduces the machine's map at all horizons: any candidate
of depth `T` is already wrong at horizon `T + 1`.

This is the statable form of the paper's point. The uniform version — "no single acyclic machine
covers all horizons", quantifying over one machine and all `T` — is not expressible here, because
the type `Layered X Y T` is indexed by `T` and a single term of it has one fixed depth. What is
proved is the contrapositive service the argument needs: the unfolding must be re-chosen as the
horizon grows. -/
theorem no_fixed_unfolding_covers_all_horizons :
    ¬ ∃ (T : ℕ) (U : Layered Bool Bool T), ∀ (T' : ℕ) (x : ℕ → Bool),
        U.eval x = echo.evalHorizon T' x := by
  rintro ⟨T, U, hU⟩
  have hlate : ∀ i, i < T → decide (i = T) = false := by
    intro i hi
    simp only [decide_eq_false_iff_not]
    omega
  have hagree : U.eval (fun i => decide (i = T)) = U.eval (fun _ => false) :=
    depth_bounded_ignores_late_input U _ _ hlate
  rw [hU (T + 1) (fun i => decide (i = T)), hU (T + 1) (fun _ => false)] at hagree
  simp only [Recurrent.evalHorizon, Recurrent.stateAfter, echo] at hagree
  simp at hagree

#check @finite_unfolding
#check @unfolding_layers_eq_state
#check @depth_bounded_ignores_late_input
#check @no_fixed_unfolding_covers_all_horizons

end IS
end KTAIT
