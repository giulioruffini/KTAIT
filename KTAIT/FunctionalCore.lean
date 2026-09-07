/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic

/-!
# Task-relative functional descriptions (WP0007)

A fixed task interface and finite prior code determine which programs reproduce a declared
behavior. `functionalCoreComplexity` minimizes their description lengths; `IsFunctionalCore`
identifies any shortest representative. Every task output is preserved, including errors or
exceptions in an imperfect predictor. Neither predictive loss nor execution time is minimized.

The interpreter is supplied as an abstract partial semantics. Its task and prior inputs are
finite binary strings. `Input` is the declared admissible domain; `Output` is the task readout.
Operational computability, universal-machine coding, and the interface's fixed wrapper are
not constructed here. The implementation bound takes wrapper correctness and length as
explicit hypotheses. No result computes a core or transfers a discovery barrier to a new
predictive success criterion.

The approximate benchmark retains the same task and prior inputs and minimizes over programs
whose total task behaviors lie within a declared discrepancy tolerance. A tolerance neighborhood
need not be an equivalence class. Both minima require a nonempty candidate set.
-/

namespace KTAIT.FunctionalCore

abbrev Bits := List Bool

/-- The fixed task and pre-acquisition frame supplied to the interpreter. `none` records
absence of a returned output; no runtime or halting bound is part of this semantics. -/
structure TaskInterface (Input Output : Type) where
  taskCode : Bits
  priorCode : Bits
  run : Bits → Bits → Bits → Input → Option Output

variable {Input Output : Type}

/-- Equality of the complete behavior selected by the declared task. -/
def taskEquivalent (F G : Input → Output) : Prop := ∀ x, F x = G x

/-- The program returns the declared task output on every admissible input. -/
def RealizesTask (I : TaskInterface Input Output) (F : Input → Output) (p : Bits) : Prop :=
  ∀ x, I.run p I.taskCode I.priorCode x = some (F x)

/-- There is an exact conditional description of length `n`. -/
def HasExactDescription (I : TaskInterface Input Output) (F : Input → Output) (n : Nat) : Prop :=
  ∃ p, p.length = n ∧ RealizesTask I F p

noncomputable section

/-- Shortest description length at the fixed interface, given a finite realization. -/
def functionalCoreComplexity (I : TaskInterface Input Output) (F : Input → Output)
    (h : ∃ n, HasExactDescription I F n) : Nat := by
  classical
  exact Nat.find h

/-- Any shortest representative is a functional core. It need not be a subprogram of
the acquired implementation, and there can be more than one shortest representative. -/
def IsFunctionalCore (I : TaskInterface Input Output) (F : Input → Output)
    (h : ∃ n, HasExactDescription I F n) (p : Bits) : Prop :=
  RealizesTask I F p ∧ p.length = functionalCoreComplexity I F h

/-- A realizable task behavior has a shortest representative. This is an ideal existence
statement, with no computable selection procedure. -/
theorem exists_functional_core (I : TaskInterface Input Output) (F : Input → Output)
    (h : ∃ n, HasExactDescription I F n) : ∃ p, IsFunctionalCore I F h p := by
  classical
  obtain ⟨p, hlen, hrealizes⟩ := Nat.find_spec h
  exact ⟨p, hrealizes, hlen⟩

/-- The shortest exact behavior description is no longer than any compiled implementation.
The acquired implementation's incremental cost is `cost`; the fixed interface wrapper costs
at most `overhead` additional bits. Correctness and that cost bound are explicit hypotheses. -/
theorem functional_core_le_implementation (I : TaskInterface Input Output) (F : Input → Output)
    (h : ∃ n, HasExactDescription I F n)
    (compiled : Bits) (hrealizes : RealizesTask I F compiled)
    (cost overhead : Nat) (hcost : compiled.length ≤ cost + overhead) :
    functionalCoreComplexity I F h ≤ cost + overhead := by
  classical
  exact Nat.le_trans (Nat.find_min' h ⟨compiled, rfl, hrealizes⟩) hcost

/-- A program of length `n` returns a total task behavior within the declared discrepancy
tolerance. Task and prior information remain supplied through the same interface `I`. -/
def HasApproxDescription (I : TaskInterface Input Output) (F : Input → Output)
    (discrepancy : (Input → Output) → (Input → Output) → ℝ) (tolerance : ℝ) (n : Nat) : Prop :=
  ∃ p G, p.length = n ∧ RealizesTask I G p ∧ discrepancy G F ≤ tolerance

/-- Shortest admissible approximate description. The comparison minimizes code length
within a fixed tolerance; it does not optimize predictive performance or runtime. -/
def approximateCoreComplexity (I : TaskInterface Input Output) (F : Input → Output)
    (discrepancy : (Input → Output) → (Input → Output) → ℝ) (tolerance : ℝ)
    (h : ∃ n, HasApproxDescription I F discrepancy tolerance n) : Nat := by
  classical
  exact Nat.find h

end
end KTAIT.FunctionalCore
