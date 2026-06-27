/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib

/-!
# KTAIT.Basic — the abstract AIT interface (M2)

`AITFrame` is the Level-1 AIT interface: it bundles the *data* of an algorithmic
information setting — a carrier `Obj`, complexity `K`, pairing, conditional
complexity `cond` (= `K(x | y)`), the shortest-program map `star` (`y ↦ y*`),
and a `slack` standing for the `O(log)` / `O(1)` correction terms.

From this data we DEFINE mutual algorithmic information `IK` (an `Int`, since it
can be negative before correction) and its normalization `NMAI` (a `Rat`).

The AIT *facts* (invariance, symmetry of information) are stated as named
`Prop`s ABOUT a frame — i.e. as hypotheses — NOT as global `axiom`s. A global
`axiom (F : AITFrame) : P F` would assert the law for every frame, including
hand-built frames that violate it (set `slack := 0` with mismatched `K`), which
makes the theory inconsistent. Stating them as hypotheses keeps every corollary
a sound implication; the toy model (M5) then witnesses they are satisfiable.
-/

namespace KTAIT

/-- The abstract AIT interface. At Level 1, `K` and friends are opaque data. -/
structure AITFrame where
  /-- The carrier of descriptions (bitstrings, tape configs, …). -/
  Obj : Type
  /-- Kolmogorov complexity `K(x)`. -/
  K : Obj → Nat
  /-- Pairing `⟨x, y⟩` into a single object. -/
  pair : Obj → Obj → Obj
  /-- Conditional complexity `K(x | y)`. -/
  cond : Obj → Obj → Nat
  /-- Shortest-program form `y ↦ y*` (carries `y` together with `K(y)`). -/
  star : Obj → Obj
  /-- Placeholder for the `O(log)` / `O(1)` correction terms. -/
  slack : Nat

variable (F : AITFrame)

/-- Conditioning on the SHORTEST PROGRAM `y*`, i.e. `K(x | y*)`. -/
def condStar (x y : F.Obj) : Nat := F.cond x (F.star y)

/-- Mutual algorithmic information `I_K(x : y) = K(x) + K(y) − K(⟨x,y⟩)`.
    An `Int` because it can be negative before the `O(log)` correction. -/
def IK (x y : F.Obj) : Int :=
  (F.K x : Int) + (F.K y : Int) - (F.K (F.pair x y) : Int)

/-- Normalized mutual algorithmic information, a `Rat` in `[-1, 1]` (morally).
    Division by `0` yields `0` in Lean, which is fine for the degenerate frame. -/
def NMAI (x y : F.Obj) : Rat :=
  (IK F x y : Rat) / (max (F.K x) (F.K y) : Rat)

/-! ### The AIT facts, as named hypotheses (sound stand-ins for "axioms") -/

/-- **Invariance theorem** (schema). Any frame `G` simulates `F` up to a single
    additive constant via some encoding `e`. (The classic `K_U ≤ K_M + c_M`.) -/
def Invariance (F G : AITFrame) (e : F.Obj → G.Obj) : Prop :=
  ∃ c : Nat, ∀ x, G.K (e x) ≤ F.K x + c

/-- **Symmetry of information**, in its CORRECT form:
    `I_K(x : y) = K(x) − K(x | y*) + O(log)`.
    Crucially this uses `y*` (via `condStar`) and the `O(log)` `slack` — NOT a
    single `O(1)` constant. We encode "`= … + O(log)`" as "the two sides differ
    by at most `slack`". -/
def SymmetryOfInformation (F : AITFrame) : Prop :=
  ∀ x y : F.Obj,
    (IK F x y - ((F.K x : Int) - (condStar F x y : Int))).natAbs ≤ F.slack

-- Sanity: the definitions and the law-statements type-check.
#check @IK
#check @NMAI
#check @condStar
#check @Invariance
#check @SymmetryOfInformation

end KTAIT
