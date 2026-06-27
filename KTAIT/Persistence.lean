/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic
import KTAIT.Ontology

/-!
# KTAIT.Persistence — persistence as temporal self-information (M3)

Persistence of a time-indexed pattern is the normalized mutual algorithmic information
between the self-code now and its future self:
  `Pers F S t τ := NMAI (S t) (S (t+τ))`.
This is the temporal quantity the ontology forces us toward (a pattern with its FUTURE
self), as opposed to the vacuous static `IK(A : S)`.
-/

namespace KTAIT

/-- **Temporal self-information** `I_K(S_t : S_{t+τ})` (un-normalized, may be negative
    before the `O(log)` correction). -/
def TemporalSelfInfo (F : AITFrame) (S : Time → F.Obj) (t τ : Time) : ℤ :=
  IK F (S t) (S (t + τ))

/-- **Persistence**: normalized temporal self-information of the self-code with its
    future self, `NMAI(S_t, S_{t+τ}) ∈ [−1, 1]` (morally). -/
def Pers (F : AITFrame) (S : Time → F.Obj) (t τ : Time) : ℚ :=
  NMAI F (S t) (S (t + τ))

/-- The persistence-threshold predicate: the trajectory is `θ-persistent` at `(t, τ)`. -/
def Persistent (F : AITFrame) (S : Time → F.Obj) (t τ : Time) (θ : ℚ) : Prop :=
  θ ≤ Pers F S t τ

/-- The persistence equation, as a `sorry`-free definitional lemma:
    persistence is the normalized temporal self-information. -/
theorem pers_eq_nmai (F : AITFrame) (S : Time → F.Obj) (t τ : Time) :
    Pers F S t τ = NMAI F (S t) (S (t + τ)) := rfl

/-- Above a positive threshold, persistence is strictly positive — the self-code keeps
    real shared structure with its future self. -/
theorem persistent_pos (F : AITFrame) (S : Time → F.Obj) (t τ : Time) {θ : ℚ}
    (hθ : 0 < θ) (h : Persistent F S t τ θ) : 0 < Pers F S t τ :=
  lt_of_lt_of_le hθ h

/-! ## Proposition 2 — persistence conservation (WP0162 Appendix D)

The conservation ledger: world-output complexity decomposes into the mutual algorithmic
information with the regulator plus a conditional residual (the "innovation"), via the
symmetry of algorithmic information `K(O_W) = I_K(O_W:R) + K(O_W | R*)`. -/

/-- The conservation ledger (exact form), WP0162 Eq. (31):
    `K(O_W) = I_K(O_W:R) + K(O_W | R*)`. (The residual `K(O_W|R*)` splits further into the
    action-discharged and innovation sinks — the third sink — not modeled here.) -/
def ConservationLedger (F : AITFrame) (OW R : F.Obj) : Prop :=
  (F.K OW : ℤ) = IK F OW R + (condStar F OW R : ℤ)

/-- **Proposition 2 (persistence conservation), bounded form.** From the symmetry of
    algorithmic information, world-output complexity is accounted for up to `slack`:
    `|K(O_W) − (I_K(O_W:R) + K(O_W|R*))| ≤ slack`. -/
theorem persistence_conservation (F : AITFrame) (hsym : SymmetryOfInformation F)
    (OW R : F.Obj) :
    ((F.K OW : ℤ) - (IK F OW R + (condStar F OW R : ℤ))).natAbs ≤ F.slack := by
  have h := hsym OW R
  rw [show ((F.K OW : ℤ) - (IK F OW R + (condStar F OW R : ℤ)))
        = -(IK F OW R - ((F.K OW : ℤ) - (condStar F OW R : ℤ))) from by ring, Int.natAbs_neg]
  exact h

/-- **Conservation trade-off.** At fixed world-output complexity `K(O_W)` (exact ledger),
    maximizing the mutual algorithmic information `I_K(O_W:R)` is equivalent to minimizing the
    conditional residual / innovation `K(O_W | R*)`. (Maximizing persistence `≡` maximizing
    shared structure at fixed budget — WP0162.) -/
theorem conservation_tradeoff (F : AITFrame) (OW R₁ R₂ : F.Obj)
    (h₁ : ConservationLedger F OW R₁) (h₂ : ConservationLedger F OW R₂) :
    IK F OW R₂ ≤ IK F OW R₁ ↔ (condStar F OW R₁ : ℤ) ≤ (condStar F OW R₂ : ℤ) := by
  simp only [ConservationLedger] at h₁ h₂
  constructor <;> intro h <;> omega

end KTAIT
