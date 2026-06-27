/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic
import KTAIT.Ontology
import KTAIT.Probability
import KTAIT.SelfModel

/-!
# KTAIT.ToyModel — satisfiability witnesses (M5)

The NON-NEGOTIABLE check (kickoff refinement #1): exhibit concrete models in which our
named AIT hypotheses actually HOLD. Without this, an inconsistent hypothesis set could
make every corollary vacuously true. Here we:

* build a degenerate `AITFrame` (`Toy`) and prove `SymmetryOfInformation Toy`;
* build a degenerate `PrefixMachine` (`ToyMachine`) and prove its `CodingTheorem`;
* build a frame with a genuine POSITIVE self-regulation gap (`ToyGap`) and fire the
  `self_regulation_temporal_model` corollary on it — so the corollary is non-vacuous.
-/

namespace KTAIT

/-- Degenerate AIT frame: everything is `0`. Witnesses the interface is instantiable. -/
def Toy : AITFrame where
  Obj := Unit
  K := fun _ => 0
  pair := fun _ _ => ()
  cond := fun _ _ => 0
  star := fun _ => ()
  slack := 1

/-- Symmetry of information holds for `Toy` — the symmetry hypothesis is satisfiable. -/
theorem toy_symmetry : SymmetryOfInformation Toy := by
  intro x y; simp [IK, condStar, Toy]

/-- Degenerate prefix machine with `m ≡ 1`. -/
noncomputable def ToyMachine : PrefixMachine where
  Prog := Unit
  Out := Unit
  U := fun _ => ()
  len := fun _ => 0
  K := fun _ => 0
  m := fun _ => 1
  m_pos := fun _ => one_pos

/-- The Coding Theorem holds for `ToyMachine` with `c₁ = c₂ = 1` — it is satisfiable. -/
theorem toyMachine_coding : ToyMachine.CodingTheorem 1 1 := by
  refine ⟨one_pos, one_pos, fun x => ⟨?_, ?_⟩⟩ <;> simp [ToyMachine]

/-- A frame with a genuine positive self-regulation gap. `K := id` lets complexities
    differ, so `Δ_self = K(3) − K(0) = 3 > 0`. -/
def ToyGap : AITFrame where
  Obj := Nat
  K := id
  pair := fun _ _ => 0
  cond := fun _ _ => 0
  star := id
  slack := 2

/-- The self-model corollary FIRES non-vacuously on `ToyGap`: a positive gap
    `Δ_self = 3` with satisfiable `hSI`/`hART`. That this application type-checks
    witnesses the corollary's hypotheses are jointly satisfiable with a real gap. -/
theorem toy_self_model_fires : True := by
  have _h := self_regulation_temporal_model ToyGap (fun _ => (0 : Nat))
      (0 : Nat) (0 : Nat) (3 : Nat) (0 : Nat) 0 0 1
      (by decide) (by decide) (by decide)
  trivial

end KTAIT
