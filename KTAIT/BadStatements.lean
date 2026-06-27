/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic
import KTAIT.Ontology

/-!
# KTAIT.BadStatements — the guards biting (M5)

Documentation-by-compilation of the two error classes the project exists to catch.

## 1. Whole-vs-part (`IK(A : S)` with `S ⊂ A`)
Handled by the typed ontology: `Pattern` and `SelfCode` are distinct types, so feeding a
`SelfCode` where a `Pattern` peer is expected fails to type-check. See `KTAIT.Ontology`'s
`#check_failure peers A S`. Re-stated here for the record: -/

namespace KTAIT

-- The part-whole guard, re-demonstrated: a `SelfCode` is not a `Pattern`.
#check_failure (peers A S)

/-! ## 2. Conditioning on `y` vs `y*` (the symmetry-of-information error source)

Symmetry of information is `I_K(x:y) = K(x) − K(x | y*) + O(log)` — it MUST use `y*`
(`condStar`), not the raw `y` (`cond`). We make this bite in a concrete frame: at a
specific point the `y*`-form holds within `slack`, while the raw-`y` form is violated. -/

/-- A frame engineered so that, at `(x,y) = (10,3)`:
    `K(10)=10`, `K(⟨10,3⟩)=5` so `I_K = 8`; the raw conditioning `K(10|3)=10` gives no
    help, but the starred conditioning `K(10|3*) = K(10|100) = 2` does. -/
def FrameYStar : AITFrame where
  Obj := Nat
  K := id
  pair := fun x y => if x = 10 ∧ y = 3 then 5 else x + y
  cond := fun x y => if 100 ≤ y then x - 8 else x
  star := fun _ => 100
  slack := 1

/-- GOOD: the `y*` (starred) form of symmetry of information holds at `(10,3)`. -/
theorem ystar_form_holds :
    (IK FrameYStar (10 : Nat) (3 : Nat)
        - ((FrameYStar.K (10 : Nat) : ℤ)
            - (condStar FrameYStar (10 : Nat) (3 : Nat) : ℤ))).natAbs
      ≤ FrameYStar.slack := by decide

/-- BAD: the raw-`y` form of symmetry of information FAILS at the same point — using
    `cond` (= `K(x|y)`) instead of `condStar` (= `K(x|y*)`) breaks the identity. -/
theorem rawy_form_fails :
    ¬ ((IK FrameYStar (10 : Nat) (3 : Nat)
          - ((FrameYStar.K (10 : Nat) : ℤ)
              - (FrameYStar.cond (10 : Nat) (3 : Nat) : ℤ))).natAbs
        ≤ FrameYStar.slack) := by decide

end KTAIT
