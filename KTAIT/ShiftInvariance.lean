/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic

/-!
# KTAIT.ShiftInvariance — a cheaply-computable transform preserves algorithmic MI

Motivated by a concrete empirical failure in BCOM WP0202 (*Gaia, Compressed*), where a
**circular shift was used as a null hypothesis** for algorithmic mutual information, and a
real effect was consequently withdrawn as "indistinguishable from noise".

The error is exactly the kind Lean is good at exposing, because it is a confusion of two
different quantities under one name:

* **Whole-object MAI** `I_K(x : y) = K(x) + K(y) − K(⟨x,y⟩)` is *alignment-free*. If `y` is
  computable from `x` plus a short index — a circular shift, a reversal, a relabelling — then
  `y` shares nearly all of its algorithmic information with `x`. **A shift is a POSITIVE
  CONTROL, not a null.**
* A time-aligned **mutual information rate** is a different object, and a shift *is* a valid
  null for it. That object is not formalized here; it is not an AIT quantity.

The theorem below is the first bullet, stated for an arbitrary family of transformations that
are cheap to describe. Specializing the index to a shift amount `s` (with `K(s) = O(log n)`)
gives the circular-shift corollary.

Following the discipline of `KTAIT.Basic`, the AIT *facts* are named `Prop`s about a frame
(hypotheses), never global `axiom`s: a global axiom would assert the law for every frame,
including hand-built frames that violate it.
-/

namespace KTAIT

variable (F : AITFrame)

/-! ### Two frame-level hypotheses -/

/-- **Pairing is symmetric up to `slack`.** `K(⟨x,y⟩)` and `K(⟨y,x⟩)` differ only by the cost
of a swap program, which is `O(1)`. Needed because `IK` is *defined* via `pair` and is
therefore not symmetric on the nose. -/
def PairSymmetric : Prop :=
  ∀ x y : F.Obj, ((F.K (F.pair x y) : Int) - (F.K (F.pair y x) : Int)).natAbs ≤ F.slack

/-- **A cheaply-computable transform family.** `T i x` is describable from the shortest program
`x*` together with a description of the index `i`:

  `K(T i x | x*) ≤ K(code i) + O(1)`.

A circular shift by `s` satisfies this with `code s` an encoding of `s`: the program is
"decode `x` from `x*`, rotate by `s`, print". So does reversal, complementation, or any
member of a uniformly computable family. -/
def CheapTransform {Idx : Type} (T : Idx → F.Obj → F.Obj) (code : Idx → F.Obj) : Prop :=
  ∀ (i : Idx) (x : F.Obj), F.cond (T i x) (F.star x) ≤ F.K (code i) + F.slack

/-! ### The theorem -/

/-- **A cheaply-computable transform preserves algorithmic mutual information.**

If `y = T i x` is computable from `x*` plus a short index, then

  `I_K(x : T i x) ≥ K(T i x) − K(code i) − 3·slack`.

That is: `y` retains *all* of its own algorithmic information about `x`, minus only the cost of
naming the transform. When `K(code i)` is `O(log n)` and `K(T i x)` is `Ω(n)`, the mutual
information is very nearly maximal. -/
theorem transform_preserves_IK
    {Idx : Type} (T : Idx → F.Obj → F.Obj) (code : Idx → F.Obj)
    (hsym : SymmetryOfInformation F)
    (hpair : PairSymmetric F)
    (hT : CheapTransform F T code)
    (i : Idx) (x : F.Obj) :
    (F.K (T i x) : Int) - (F.K (code i) : Int) - 3 * (F.slack : Int)
      ≤ IK F x (T i x) := by
  -- (1) symmetry of information at (T i x, x):  IK ≥ K y − K(y | x*) − slack
  have h1 := hsym (T i x) x
  -- (2) the transform is cheap:  K(y | x*) ≤ K(code i) + slack
  have h2 := hT i x
  -- (3) pairing is symmetric up to slack, so IK F x y ≥ IK F y x − slack
  have h3 := hpair x (T i x)
  -- Unfold the definitions; `omega` handles `Int.natAbs` and the linear arithmetic.
  simp only [IK, condStar] at h1 h3 ⊢
  omega

/-! ### The corollary that names the mistake -/

/-- **A circular shift is not a null for algorithmic mutual information.**

Specialize `transform_preserves_IK` to a shift family `shift : Idx → Obj → Obj`. The shifted
copy `shift s x` retains its algorithmic information with `x` up to the cost `K(code s)` of
naming the shift — which for a shift by `s < n` is `O(log n)`.

A *valid* null must drive `I_K` to `≈ 0`. This bound shows a shift cannot: it leaves
`I_K ≥ K(shift s x) − O(log n)`. Using it as a null subtracts the signal. -/
theorem shift_is_not_a_null
    {Idx : Type} (shift : Idx → F.Obj → F.Obj) (code : Idx → F.Obj)
    (hsym : SymmetryOfInformation F)
    (hpair : PairSymmetric F)
    (hshift : CheapTransform F shift code)
    (s : Idx) (x : F.Obj) :
    (F.K (shift s x) : Int) - (F.K (code s) : Int) - 3 * (F.slack : Int)
      ≤ IK F x (shift s x) :=
  transform_preserves_IK F shift code hsym hpair hshift s x

/-- **What a valid null would have to satisfy.** A surrogate family `π` is a null for
whole-object MAI at `(x, y)` only if it drives the mutual information to within `ε` of zero.
Stated so that `shift_is_not_a_null` can be seen to contradict it whenever
`K(shift s x) > K(code s) + 3·slack + ε`. -/
def IsNullFor (π : F.Obj → F.Obj) (x : F.Obj) (ε : Nat) : Prop :=
  (IK F x (π x)).natAbs ≤ ε

/-- **The contradiction, explicitly.** If the transform is cheap and its output is complex,
then it is *not* a null: no `ε` smaller than `K(shift s x) − K(code s) − 3·slack` will do.

This is the formal content of the WP0202 correction: the circular-shift surrogate was being
used as `IsNullFor`, while the theorem says its `IK` is bounded *below* by a large number. -/
theorem cheap_transform_not_null
    {Idx : Type} (shift : Idx → F.Obj → F.Obj) (code : Idx → F.Obj)
    (hsym : SymmetryOfInformation F)
    (hpair : PairSymmetric F)
    (hshift : CheapTransform F shift code)
    (s : Idx) (x : F.Obj) (ε : Nat)
    (hbig : (ε : Int) < (F.K (shift s x) : Int) - (F.K (code s) : Int) - 3 * (F.slack : Int)) :
    ¬ IsNullFor F (shift s) x ε := by
  intro hnull
  have hlb := shift_is_not_a_null F shift code hsym hpair hshift s x
  have hn : (IK F x (shift s x)).natAbs ≤ ε := hnull
  omega

/-! ### Non-vacuity: a frame that satisfies all three hypotheses

A theorem whose hypotheses no frame satisfies is worthless. We witness satisfiability with a
concrete frame in which the bound is *tight*.

Read `Obj := ℕ` as "a string of complexity `x`". A shift does not change a string's complexity,
so `shift s x = x`; naming the shift is free, so `code s = 0` with `K 0 = 0`. -/

/-- A frame witnessing `SymmetryOfInformation`, `PairSymmetric` and `CheapTransform`
simultaneously, with `slack = 0`. -/
def ShiftFrame : AITFrame where
  Obj := Nat
  K := id
  pair := fun x y => max x y            -- so IK x y = x + y − max x y = min x y
  cond := fun x y => x - min x y        -- truncated ℕ-subtraction
  star := id
  slack := 0

-- `ShiftFrame.Obj` is definitionally `Nat`; let numerals elaborate through it.
instance instOfNatShiftObj (n : Nat) : OfNat ShiftFrame.Obj n := ⟨(n : Nat)⟩

/-- The shift family on `ShiftFrame`: a shift leaves complexity untouched. -/
def shiftOn : Nat → ShiftFrame.Obj → ShiftFrame.Obj := fun _ x => x

/-- Naming a shift is free in this frame. -/
def codeOn : Nat → ShiftFrame.Obj := fun _ => (0 : Nat)

example : SymmetryOfInformation ShiftFrame := by
  intro x y
  simp only [IK, condStar, ShiftFrame, id_eq]
  omega

example : PairSymmetric ShiftFrame := by
  intro x y
  simp only [ShiftFrame, id_eq]
  omega

example : CheapTransform ShiftFrame shiftOn codeOn := by
  intro i x
  simp only [ShiftFrame, shiftOn, codeOn, id_eq]
  omega

/-- **The bound is tight, and the conclusion is not vacuous.** In `ShiftFrame`,
`I_K(x : shift s x) = x = K(shift s x)`: the shifted copy retains *all* of its algorithmic
information. A surrogate that claimed `|I_K| ≤ ε` for any `ε < x` is refuted. -/
example (s x : Nat) : IK ShiftFrame x (shiftOn s x) = (x : Int) := by
  simp only [IK, ShiftFrame, shiftOn, id_eq]
  omega

/-- Concretely: at `x = 100`, a "null" asserting `|I_K| ≤ 50` is false. -/
example : ¬ IsNullFor ShiftFrame (shiftOn 7) (100 : Nat) 50 := by
  intro h
  have h' : (IK ShiftFrame (100 : Nat) (shiftOn 7 (100 : Nat))).natAbs ≤ 50 := h
  simp only [IK, ShiftFrame, shiftOn, id_eq] at h'
  omega

#check @transform_preserves_IK
#check @shift_is_not_a_null
#check @cheap_transform_not_null

end KTAIT
