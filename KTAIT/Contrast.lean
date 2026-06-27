/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic

/-!
# KTAIT.Contrast — the contrast-fiber posterior (WP0162 Q3, Eq. 26)

Conditioning on the contrast event `δ_N(W,R) ≥ Δ` ALONE (rather than on the specific ON
readout `x`) gives the universal posterior restricted to the contrast fiber,
`m(W,R | δ ≥ Δ) = 2^{−K(W,R)} 𝟙{δ≥Δ} / Σ_{δ≥Δ} 2^{−K}`. Unlike ART's Theorem 2, this carries
**no `2^{−Δ}` tilt**: within the fiber the posterior depends on the pair only through its joint
complexity `K(W,R)`, so it simply favors the shortest joint explanation.

We model the candidate explanations as a `Finset` with a complexity `K` and a contrast value
`δ`, and prove the qualitative content of Eq. (26): the fiber posterior ranks pairs by joint
simplicity.
-/

namespace KTAIT

open Finset

variable {E : Type}

/-- Universal weight of an explanation: `2^{−K(e)}`. -/
noncomputable def cweight (K : E → ℕ) (e : E) : ℝ := (2 : ℝ) ^ (-(K e : ℤ))

theorem cweight_pos (K : E → ℕ) (e : E) : 0 < cweight K e := by
  unfold cweight; positivity

/-- The contrast fiber `{e ∈ cand : δ e ≥ Δ}`. -/
def fiber (cand : Finset E) (δ : E → ℤ) (Δ : ℤ) : Finset E :=
  cand.filter (fun e => Δ ≤ δ e)

/-- The contrast-fiber posterior (Eq. 26): weight normalized over the fiber. -/
noncomputable def contrastPosterior (cand : Finset E) (K : E → ℕ) (δ : E → ℤ) (Δ : ℤ)
    (e : E) : ℝ :=
  cweight K e / ∑ e' ∈ fiber cand δ Δ, cweight K e'

/-- The normalizer is positive whenever the fiber is inhabited. -/
theorem contrast_Z_pos {cand : Finset E} {K : E → ℕ} {δ : E → ℤ} {Δ : ℤ} {e : E}
    (he : e ∈ fiber cand δ Δ) : 0 < ∑ e' ∈ fiber cand δ Δ, cweight K e' :=
  Finset.sum_pos (fun e' _ => cweight_pos K e') ⟨e, he⟩

/-- **WP0162 Q3 (Eq. 26).** Conditioning on the contrast alone ranks explanations by joint
    simplicity: within the fiber, a pair has *higher* posterior iff its joint complexity
    `K(W,R)` is *smaller* — there is no `2^{−Δ}` tilt. -/
theorem contrast_posterior_ranks_by_complexity
    {cand : Finset E} {K : E → ℕ} {δ : E → ℤ} {Δ : ℤ} {e₁ e₂ : E}
    (h₁ : e₁ ∈ fiber cand δ Δ) (_h₂ : e₂ ∈ fiber cand δ Δ) :
    contrastPosterior cand K δ Δ e₁ ≤ contrastPosterior cand K δ Δ e₂ ↔ K e₂ ≤ K e₁ := by
  have hZ : 0 < ∑ e' ∈ fiber cand δ Δ, cweight K e' := contrast_Z_pos h₁
  unfold contrastPosterior
  rw [div_le_div_iff_of_pos_right hZ]
  unfold cweight
  rw [zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)]
  omega

end KTAIT
