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

end KTAIT
