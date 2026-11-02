/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Kaiti/Codex)
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ring

/-!
# First-order generator extraction from arithmetic expressions

WP0215 worked example. A finite expression uses rational literals, a declared
step parameter, fixed state variables, addition, negation, and multiplication.
Division by a nonzero rational is multiplication by its reciprocal.
`jet` computes value and step derivative at zero. Its soundness and uniqueness
are proved over real arithmetic, without any AIT or realization assumption.
This does not verify a C compiler, LLVM parser, IEEE rounding, or state selection.
-/
namespace KTAIT.ProgramGenerator

inductive Expr (n : Nat) where
  | lit : ℚ → Expr n
  | state : Fin n → Expr n
  | step : Expr n
  | add : Expr n → Expr n → Expr n
  | neg : Expr n → Expr n
  | mul : Expr n → Expr n → Expr n

def eval {n : Nat} (e : Expr n) (q : Fin n → ℝ) (h : ℝ) : ℝ :=
  match e with
  | .lit c => c
  | .state i => q i
  | .step => h
  | .add a b => eval a q h + eval b q h
  | .neg a => -eval a q h
  | .mul a b => eval a q h * eval b q h

def jet {n : Nat} (e : Expr n) (q : Fin n → ℝ) : ℝ × ℝ :=
  match e with
  | .lit c => (c, 0)
  | .state i => (q i, 0)
  | .step => (0, 1)
  | .add a b => ((jet a q).1 + (jet b q).1, (jet a q).2 + (jet b q).2)
  | .neg a => (-(jet a q).1, -(jet a q).2)
  | .mul a b => ((jet a q).1 * (jet b q).1,
      (jet a q).2 * (jet b q).1 + (jet a q).1 * (jet b q).2)

theorem jet_value {n : Nat} (e : Expr n) (q : Fin n → ℝ) :
    (jet e q).1 = eval e q 0 := by
  induction e with
  | lit c => rfl
  | state i => rfl
  | step => rfl
  | add a b ha hb => simp only [jet, eval, ha, hb]
  | neg a ha => simp only [jet, eval, ha]
  | mul a b ha hb => simp only [jet, eval, ha, hb]

theorem jet_derivative {n : Nat} (e : Expr n) (q : Fin n → ℝ) :
    HasDerivAt (eval e q) (jet e q).2 0 := by
  induction e with
  | lit c => simpa only [eval, jet] using hasDerivAt_const (0 : ℝ) (c : ℝ)
  | state i => simpa only [eval, jet] using hasDerivAt_const (0 : ℝ) (q i)
  | step => convert hasDerivAt_id (0 : ℝ) using 1 <;> rfl
  | add a b ha hb => convert ha.add hb using 1 <;> rfl
  | neg a ha => convert ha.neg using 1 <;> rfl
  | mul a b ha hb =>
    convert ha.mul hb using 1 <;> first | rfl | simp [jet, jet_value]

theorem generator_unique {n : Nat} (e : Expr n) (q : Fin n → ℝ) (v : ℝ)
    (hv : HasDerivAt (eval e q) v 0) : v = (jet e q).2 := by
  exact hv.unique (jet_derivative e q)

/-- Syntax-to-syntax extraction; it needs no state values and no target ODE. -/
def symbolicJet {n : Nat} (e : Expr n) : Expr n × Expr n :=
  match e with
  | .lit c => (.lit c, .lit 0)
  | .state i => (.state i, .lit 0)
  | .step => (.lit 0, .lit 1)
  | .add a b => (.add (symbolicJet a).1 (symbolicJet b).1,
      .add (symbolicJet a).2 (symbolicJet b).2)
  | .neg a => (.neg (symbolicJet a).1, .neg (symbolicJet a).2)
  | .mul a b => (.mul (symbolicJet a).1 (symbolicJet b).1,
      .add (.mul (symbolicJet a).2 (symbolicJet b).1)
        (.mul (symbolicJet a).1 (symbolicJet b).2))

theorem symbolic_jet_correct {n : Nat} (e : Expr n) (q : Fin n → ℝ) (h : ℝ) :
    eval (symbolicJet e).1 q h = (jet e q).1 ∧
    eval (symbolicJet e).2 q h = (jet e q).2 := by
  induction e with
  | lit c => simp [symbolicJet, jet, eval]
  | state i => simp [symbolicJet, jet, eval]
  | step => simp [symbolicJet, jet, eval]
  | add a b ha hb => simp [symbolicJet, jet, eval, ha.1, ha.2, hb.1, hb.2]
  | neg a ha => simp [symbolicJet, jet, eval, ha.1, ha.2]
  | mul a b ha hb => simp [symbolicJet, jet, eval, ha.1, ha.2, hb.1, hb.2]

theorem symbolic_generator_sound {n : Nat} (e : Expr n) (q : Fin n → ℝ) :
    HasDerivAt (eval e q) (eval (symbolicJet e).2 q 0) 0 := by
  rw [(symbolic_jet_correct e q 0).2]
  exact jet_derivative e q

/-! ### Declared state and auxiliary-input interface

A vector program has one expression per retained coordinate. State and auxiliary
coordinates occupy separate blocks of the fixed expression-variable vector.
The zero-step identity and independence of the linear coefficient from auxiliary
inputs are supplied conditions; this does not claim a verified equality checker.
-/

open Filter
open scoped Topology

/-- Evaluate a vector program at the declared state, auxiliary input, and step. -/
def interfaceUpdate {d m : Nat} (e : Fin d → Expr (d + m))
    (q : Fin d → ℝ) (a : Fin m → ℝ) (h : ℝ) : Fin d → ℝ :=
  fun i => eval (e i) (Fin.append q a) h

/-- The constant coefficient returned by symbolic extraction. -/
def constantCoefficient {d m : Nat} (e : Fin d → Expr (d + m))
    (q : Fin d → ℝ) (a : Fin m → ℝ) : Fin d → ℝ :=
  fun i => eval (symbolicJet (e i)).1 (Fin.append q a) 0

/-- The linear coefficient returned by symbolic extraction. -/
def linearCoefficient {d m : Nat} (e : Fin d → Expr (d + m))
    (q : Fin d → ℝ) (a : Fin m → ℝ) : Fin d → ℝ :=
  fun i => eval (symbolicJet (e i)).2 (Fin.append q a) 0

/-- Symbolic coefficients give the actual zero-step value and derivative with
all state and auxiliary coordinates held fixed. -/
theorem interface_coefficients {d m : Nat} (e : Fin d → Expr (d + m))
    (q : Fin d → ℝ) (a : Fin m → ℝ) (i : Fin d) :
    constantCoefficient e q a i = interfaceUpdate e q a 0 i ∧
    HasDerivAt (fun h => interfaceUpdate e q a h i) (linearCoefficient e q a i) 0 := by
  constructor
  · exact ((symbolic_jet_correct (e i) (Fin.append q a) 0).1).trans
      (jet_value (e i) (Fin.append q a))
  · exact symbolic_generator_sound (e i) (Fin.append q a)

/-- The scalar difference quotient converges to the extracted derivative once
the supplied zero-step value matches the retained coordinate. -/
theorem scalar_recovery_limit {n : Nat} (e : Expr n) (x : Fin n → ℝ)
    (q : ℝ) (hzero : eval e x 0 = q) :
    Tendsto (fun h : ℝ => (eval e x h - q) / h) (𝓝[≠] 0)
      (𝓝 (eval (symbolicJet e).2 x 0)) := by
  have hd := (symbolic_generator_sound e x).tendsto_slope_zero
  simpa only [zero_add, hzero, smul_eq_mul, div_eq_mul_inv, mul_comm] using hd

/-- Conditional generator recovery with an explicit state/auxiliary split.
The constant coefficient is the retained state, and the linear coefficient
factors through that state alone. No auxiliary input is silently fixed by the
recovered field: the conclusion holds for every admitted value of a. -/
theorem recovery_with_auxiliary_inputs {d m : Nat} (e : Fin d → Expr (d + m))
    (f : (Fin d → ℝ) → Fin d → ℝ)
    (hzero : ∀ q a, constantCoefficient e q a = q)
    (hclosed : ∀ q a, linearCoefficient e q a = f q)
    (q : Fin d → ℝ) (a : Fin m → ℝ) (i : Fin d) :
    Tendsto (fun h : ℝ => (interfaceUpdate e q a h i - q i) / h)
      (𝓝[≠] 0) (𝓝 (f q i)) := by
  have hz : eval (e i) (Fin.append q a) 0 = q i :=
    (interface_coefficients e q a i).1.symm.trans (congrFun (hzero q a) i)
  have hr := scalar_recovery_limit (e i) (Fin.append q a) (q i) hz
  change Tendsto (fun h : ℝ => (interfaceUpdate e q a h i - q i) / h)
    (𝓝[≠] 0) (𝓝 (linearCoefficient e q a i)) at hr
  rw [hclosed q a] at hr
  exact hr

/-- Any vector field satisfying the same difference-quotient limits equals the
recovered field at the declared coordinates and step parameter. -/
theorem recovered_vector_field_unique {d m : Nat} (e : Fin d → Expr (d + m))
    (f g : (Fin d → ℝ) → Fin d → ℝ)
    (hzero : ∀ q a, constantCoefficient e q a = q)
    (hclosed : ∀ q a, linearCoefficient e q a = f q)
    (hg : ∀ q a i, Tendsto
      (fun h : ℝ => (interfaceUpdate e q a h i - q i) / h)
      (𝓝[≠] 0) (𝓝 (g q i))) : g = f := by
  funext q i
  exact tendsto_nhds_unique (hg q (fun _ => 0) i)
    (recovery_with_auxiliary_inputs e f hzero hclosed q (fun _ => 0) i)

def eulerDecay : Expr 1 :=
  .add (.state 0) (.mul .step (.neg (.state 0)))

def rk4Decay : Expr 1 :=
  let q := Expr.state 0
  let h := Expr.step
  let half := Expr.lit (1/2)
  let two := Expr.lit 2
  let a := Expr.neg q
  let b := Expr.neg (.add q (.mul (.mul half h) a))
  let c := Expr.neg (.add q (.mul (.mul half h) b))
  let d := Expr.neg (.add q (.mul h c))
  .add q (.mul (.mul (.lit (1/6)) h)
    (.add (.add a (.mul two b)) (.add (.mul two c) d)))

theorem decay_common_core (q : Fin 1 → ℝ) :
    jet eulerDecay q = (q 0, -q 0) ∧
    jet rk4Decay q = (q 0, -q 0) := by
  simp [eulerDecay, rk4Decay, jet]
  ring

end KTAIT.ProgramGenerator
