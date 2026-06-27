/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/

/-!
# KTAIT.Ontology — the typed KT ontology (M1)

We give each KT role its OWN type, all wrapping a common carrier `C`
(the substrate alphabet / bitstrings — abstract at Level 1). Distinct
types mean Lean refuses to silently mix roles. The only bridge from a
role to the common carrier is the explicit `.carrier` projection, so any
role-mixing is *visible* in the source (we deliberately register NO
automatic `Coe` instances — that would make mixing silent again).

The crucial type is `SelfCode`: it cannot be constructed without `isSub`,
a proof that it really is a sub-pattern of its parent `Pattern`. This is
what turns the whole-vs-part vacuity bug into a *typed obligation*.
-/

namespace KTAIT

/-- Discrete time index `t, τ`. -/
abbrev Time := Nat

/-- The fixed substrate ("physics") tape configuration. -/
structure SubstrateState (C : Type) where
  carrier : C

/-- An agent `A`, as a pattern on the substrate. -/
structure Pattern (C : Type) where
  carrier : C

/-- A length-`N` readout / output `O^{(N)}`. -/
structure Readout (C : Type) where
  carrier : C

/-- The maintaining sub-pattern `E = A \ S`. -/
structure Regulator (C : Type) where
  carrier : C

/-- A self-code `S = M_t`: a bounded **sub-pattern** of a given `Pattern A`.
    It cannot exist without `isSub`: evidence that its carrier really is a
    sub-pattern (under the abstract relation `Sub`) of the parent's carrier. -/
structure SelfCode (C : Type) (Sub : C → C → Prop) where
  parent  : Pattern C
  carrier : C
  isSub   : Sub carrier parent.carrier

/-! ### M1 acceptance demonstrations

A concrete witness that the ontology is *inhabited* and that the part-whole
guard actually bites. Concrete only so we can run it; the types above stay
abstract over `C`. -/

section Demo

/-- Concrete carrier for the demo: bit strings. -/
abbrev Bits := List Bool

/-- Toy sub-pattern relation for the demo: `s` is a prefix of `a`. -/
def IsPrefixOf (s a : Bits) : Prop := ∃ t, a = s ++ t

/-- A parent agent-pattern `A` on three bits. -/
def A : Pattern Bits := ⟨[true, false, true]⟩

/-- A self-code `S = M_t` of `A`: the single bit `[true]`, carrying PROOF it is
    a sub-pattern (here: a prefix) of `A`. Delete `⟨[false, true], rfl⟩` and Lean
    refuses to build `S` — the evidence is mandatory, not optional. -/
def S : SelfCode Bits IsPrefixOf := ⟨A, [true], ⟨[false, true], rfl⟩⟩

-- `S` really does know its parent and carry its evidence:
#check (S.parent : Pattern Bits)
#check (S.isSub  : IsPrefixOf S.carrier A.carrier)

/-- A role-typed operation: it accepts only `Pattern`s as peers. -/
def peers (_x _y : Pattern Bits) : Unit := ()

-- GOOD: two genuine patterns are fine.
#check peers A A

-- THE GUARD BITES. `A` is a `Pattern`, `S` is a `SelfCode` — different types,
-- so they are not peers. `#check_failure` SUCCEEDS precisely because the line
-- inside FAILS to type-check. (Hover it in Cursor: the error is the point.)
#check_failure peers A S

-- To relate them at all you must drop to the common carrier EXPLICITLY via the
-- visible `.carrier` projection — at which point the part-whole relation
-- (`S` is a prefix of `A`) is right there in front of you, not hidden.
#check (A.carrier, S.carrier)

end Demo

end KTAIT
