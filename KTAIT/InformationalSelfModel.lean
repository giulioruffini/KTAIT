/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import KTAIT.WriteBack

/-!
# Informational self-models at a declared grain (WP0215)

The proposed criterion asks whether an admissibly realized modeling program shares more
than a fixed tolerance of conditional algorithmic information with the remaining program
organization. Candidates are indexed by their realizations, so two occurrences of the same
program may have different remainders. The boundary, grain, admissibility, descriptions,
background, and tolerance are supplied; the module does not establish their physical
interpretation or the proposed criterion's experiential significance.

The proved consequence is conditional: if every admissible candidate has conditional
complexity at most `B`, the fixed right-projection law bounds its signed information by
`B + c`. A predeclared tolerance covering that bound excludes the criterion. The projection
law is a named standard AIT premise, not a global axiom. No physical thermostat is modeled.
-/

namespace KTAIT.InformationalSelfModel

/-- Candidate descriptions at one declared agent boundary and grain. The caller supplies
the realization relation and the remainder excluding the particular realizing part;
program descriptions alone do not identify occurrences. -/
structure ModelParts (F : AITFrame) where
  Realization : Type
  admissible : Realization → Prop
  program : Realization → F.Obj
  remainder : Realization → F.Obj

/-- Standard fixed-projection coding premise: extracting the second component of a
joint description costs at most `c`, uniformly in both descriptions at background `b`. -/
def RightProjection (F : AITFrame) (b : F.Obj) (c : Nat) : Prop :=
  ∀ x y : F.Obj, F.cond y b ≤ F.cond (F.pair x y) b + c

/-- The proposed informational criterion, using signed symmetric conditional information.
`epsilon` is fixed before examining candidates; no regulation or reporting condition is added. -/
def HasSelfModel (F : AITFrame) (parts : ModelParts F) (b : F.Obj)
    (epsilon : Nat) : Prop :=
  ∃ r : parts.Realization, parts.admissible r ∧
    (epsilon : Int) < WriteBack.condIK F (parts.program r) (parts.remainder r) b

/-- A uniform complexity bound on all admissible modeling parts bounds each part's
conditional information with its remainder by `B + c`. -/
theorem candidate_information_bound (F : AITFrame) (parts : ModelParts F)
    (b : F.Obj) (B c : Nat) (hprojection : RightProjection F b c)
    (hbound : ∀ r, parts.admissible r → F.cond (parts.program r) b ≤ B)
    (r : parts.Realization) (hr : parts.admissible r) :
    WriteBack.condIK F (parts.program r) (parts.remainder r) b ≤ (B : Int) + c := by
  have hp := hprojection (parts.program r) (parts.remainder r)
  have hb := hbound r hr
  unfold WriteBack.condIK
  omega

/-- A predeclared tolerance covering the uniform complexity and projection costs bounds
the signed information of every admissible realization. -/
theorem all_information_le_tolerance (F : AITFrame) (parts : ModelParts F)
    (b : F.Obj) (B c epsilon : Nat) (hprojection : RightProjection F b c)
    (hbound : ∀ r, parts.admissible r → F.cond (parts.program r) b ≤ B)
    (htolerance : B + c ≤ epsilon) :
    ∀ r, parts.admissible r →
      WriteBack.condIK F (parts.program r) (parts.remainder r) b ≤ (epsilon : Int) := by
  intro r hr
  have h := candidate_information_bound F parts b B c hprojection hbound r hr
  omega

/-- Under the uniform candidate bound and fixed projection premise, a tolerance of at
least `B + c` rules out every witness to the proposed informational self-model criterion. -/
theorem no_informational_self_model (F : AITFrame) (parts : ModelParts F)
    (b : F.Obj) (B c epsilon : Nat) (hprojection : RightProjection F b c)
    (hbound : ∀ r, parts.admissible r → F.cond (parts.program r) b ≤ B)
    (htolerance : B + c ≤ epsilon) :
    ¬ HasSelfModel F parts b epsilon := by
  rintro ⟨r, hr, hinfo⟩
  have h := all_information_le_tolerance F parts b B c epsilon hprojection hbound
    htolerance r hr
  omega

end KTAIT.InformationalSelfModel
