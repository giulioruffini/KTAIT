/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic
import KTAIT.Ontology

/-!
# KTAIT.SelfModel — Proposition 3: self-regulation requires a temporal self-model (M4)

This is the headline KT corollary (WP0162, Appendix K, Proposition 3 — the
`self_regulation_temporal_model` of the kickoff).

Setup (the temporal, NOT static, reading — this is why the ontology forces `SelfCode`
to be temporal): the regulated source is the self-code TRAJECTORY `S t → S (t+τ)`; the
regulator is the maintaining sub-pattern `E = A \ S`; `C` is the context. The
self-regulation gap is
  `Δ_self := K(O_{S,∅}) − K(O_{S,E})`
(the self-code's length-N readout under the unmaintained null vs. under `E`).

The proof chain is purely logical, hence `omega`-closable:

  Δ_self > 0  ──(ART for S:E)──▶  high conditional mutual information
              ──(symmetry of information: mutual info = complexity drop)──▶
  K(S(t+τ) | S t, E, C)  ≪  K(S(t+τ) | C).        (Eq. 44)

Per the M2 design rule, the AIT facts (ART, symmetry of information) enter as named
HYPOTHESES, so the corollary is a sound implication and `#print axioms` shows only
Lean core — strictly stronger than "rests on named AIT axioms".
-/

namespace KTAIT

/-- Self-regulation gap `Δ_self := K(O_{S,∅}) − K(O_{S,E})`. -/
def DeltaSelf (F : AITFrame) (Onull Oreg : F.Obj) : ℤ :=
  (F.K Onull : ℤ) - (F.K Oreg : ℤ)

/-- **Proposition 3 (Self-regulation requires a temporal self-model).**
    With `S : Time → Obj` the self-code trajectory, `E` the maintaining sub-pattern,
    `C` the context, and the present-organization bundle `⟨S t, E, C⟩`:

    if `Δ_self > 0`, then — given symmetry of information (`hSI`: the conditional-
    complexity drop is at least the conditional mutual information `cmi`, up to `slack`)
    and ART for the pair `S : E` (`hART`: a sustained gap forces `cmi ≥ Δ_self − slack`)
    — the future self-code is cheap given the present organization:
    `K(S(t+τ) | S t, E, C) ≤ K(S(t+τ) | C) − Δ_self + 2·slack`  (Eq. 44). -/
theorem self_regulation_temporal_model
    (F : AITFrame) (S : Time → F.Obj) (E C Onull Oreg : F.Obj) (t τ : Time)
    (cmi : ℤ)
    (hΔ : 0 < DeltaSelf F Onull Oreg)
    (hSI : (F.cond (S (t + τ)) C : ℤ)
              - (F.cond (S (t + τ)) (F.pair (S t) (F.pair E C)) : ℤ)
            ≥ cmi - (F.slack : ℤ))
    -- ART for the pair `S : E`: a POSITIVE self-regulation gap forces shared structure.
    (hART : 0 < DeltaSelf F Onull Oreg → cmi ≥ DeltaSelf F Onull Oreg - (F.slack : ℤ)) :
    (F.cond (S (t + τ)) (F.pair (S t) (F.pair E C)) : ℤ)
      ≤ (F.cond (S (t + τ)) C : ℤ) - DeltaSelf F Onull Oreg + 2 * (F.slack : ℤ) := by
  have hbound := hART hΔ   -- fire ART using the positive gap
  omega

end KTAIT
