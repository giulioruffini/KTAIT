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

/-! ## Appendix E — the thin boundary as a compressed sufficient statistic -/

/-- **WP0162 Appendix E.** If the boundary `∂` screens off the world's past `W_{≤t}` (the future
    self-code is no more expensive given `∂` than given the full past, up to `slack`) AND the past
    is at least as informative as the boundary (up to `slack`), then the boundary is a sufficient
    statistic: the two conditional complexities agree up to `slack`. -/
theorem boundary_sufficient (F : AITFrame) (Mfut Mt bdy Wpast C : F.Obj)
    (hscreen : (F.cond Mfut (F.pair Mt (F.pair bdy C)) : ℤ)
                ≤ (F.cond Mfut (F.pair Mt (F.pair Wpast C)) : ℤ) + (F.slack : ℤ))
    (hpast : (F.cond Mfut (F.pair Mt (F.pair Wpast C)) : ℤ)
                ≤ (F.cond Mfut (F.pair Mt (F.pair bdy C)) : ℤ) + (F.slack : ℤ)) :
    ((F.cond Mfut (F.pair Mt (F.pair bdy C)) : ℤ)
      - (F.cond Mfut (F.pair Mt (F.pair Wpast C)) : ℤ)).natAbs ≤ F.slack := by
  omega

/-! ## Meta-persistence — persistence one scale up (WP0162 §Evolving, Prop. 1)

A collective of best-responding agents `A₁,…,A_N` has, under a coarse-graining `Φ` of its
mesoscale configuration, a **collective submodel** `Sc : Time → Obj`. Collective persistence
is the persistence equation one scale up, `Pers F Sc`. Two conditions on the pair
`(𝒟, Φ)` — *closure* (`Sc` is an algorithmic Markov blanket) and a *Foster–Lyapunov
contraction* of the constituent flow — deliver a bounded transient
`K(Sc t | (Sc (t+τ))*) ≤ L` with `L = O(log τ)`, at stable complexity `K(Sc) = k`. The bound
below follows. Its hypotheses mention only `Sc, k, L, slack`: **no property of the individual
objectives enters** — the parts act only through the closed-loop dynamics that fix `Sc`, and
need share no objective. -/

/-- **WP0162 Proposition 1 (meta-persistence).** With the symmetry of algorithmic information,
    a collective submodel `Sc` of stable complexity `k > 0` (`K(Sc t) = K(Sc (t+τ)) = k`), and a
    bounded transient `K(Sc t | (Sc (t+τ))*) ≤ L`, collective persistence obeys
    `1 − (L + slack)/k ≤ Pers F Sc t τ`. No constituent objective appears in the hypotheses. -/
theorem meta_persistence (F : AITFrame) (hsym : SymmetryOfInformation F)
    (Sc : Time → F.Obj) (t τ : Time) (k L : Nat) (hpos : 0 < k)
    (hkt : F.K (Sc t) = k) (hktau : F.K (Sc (t + τ)) = k)
    (hdrift : condStar F (Sc t) (Sc (t + τ)) ≤ L) :
    (1 : ℚ) - ((L : ℚ) + (F.slack : ℚ)) / (k : ℚ) ≤ Pers F Sc t τ := by
  -- symmetry of information + the transient bound give a lower bound on the shared information.
  have hs := hsym (Sc t) (Sc (t + τ))
  have hktZ : (F.K (Sc t) : ℤ) = (k : ℤ) := by exact_mod_cast hkt
  have hcondZ : (condStar F (Sc t) (Sc (t + τ)) : ℤ) ≤ (L : ℤ) := by exact_mod_cast hdrift
  have hIK : (k : ℤ) - (L : ℤ) - (F.slack : ℤ) ≤ IK F (Sc t) (Sc (t + τ)) := by omega
  have hkQ : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hpos
  have hIKQ : (k : ℚ) - (L : ℚ) - (F.slack : ℚ) ≤ (IK F (Sc t) (Sc (t + τ)) : ℚ) := by
    exact_mod_cast hIK
  -- collapse the normalizer `max (K(Sc t)) (K(Sc (t+τ))) = k`, then a division bound.
  unfold Pers NMAI
  rw [hkt, hktau, max_self]
  rw [show (1 : ℚ) - ((L : ℚ) + (F.slack : ℚ)) / (k : ℚ)
        = ((k : ℚ) - (L : ℚ) - (F.slack : ℚ)) / (k : ℚ) from by field_simp; ring]
  gcongr

/-- **`K(S^C) → ∞` limit of Prop. 1.** If the transient is a vanishing fraction of the
    collective complexity, `L + slack ≤ ε·k`, then collective persistence exceeds `1 − ε`. -/
theorem meta_persistence_limit (F : AITFrame) (hsym : SymmetryOfInformation F)
    (Sc : Time → F.Obj) (t τ : Time) (k L : Nat) (ε : ℚ) (hpos : 0 < k)
    (hkt : F.K (Sc t) = k) (hktau : F.K (Sc (t + τ)) = k)
    (hdrift : condStar F (Sc t) (Sc (t + τ)) ≤ L)
    (hε : ((L : ℚ) + (F.slack : ℚ)) ≤ ε * (k : ℚ)) :
    (1 : ℚ) - ε ≤ Pers F Sc t τ := by
  have hk : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hpos
  have hbound := meta_persistence F hsym Sc t τ k L hpos hkt hktau hdrift
  have hfrac : ((L : ℚ) + (F.slack : ℚ)) / (k : ℚ) ≤ ε := by rw [div_le_iff₀ hk]; exact hε
  linarith

end KTAIT
