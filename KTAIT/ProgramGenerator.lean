/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Kaiti/Codex)
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
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
