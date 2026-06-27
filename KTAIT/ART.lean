/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic

/-!
# KTAIT.ART — the probabilistic Algorithmic Regulator Theorem (M2.5 / Level 1.5)

This is the FAITHFUL, probabilistic ART (Theorem 2 of the ART paper,
*An Algorithmic-Information-Theoretic Regulator Theorem*, Entropy 2026, 28, 257),
not the deterministic K-only shadow.

`AITProb` extends `AITFrame` with a **posterior** `post e x = P(e | x)`: a real-valued
Bayesian posterior over an explanation `e` given an observation `x`. The conditioning
on the left of Theorem 2 lives here, in `post`.

The two AIT facts the proof consumes are taken as HYPOTHESES (sound stand-ins for
axioms, per the M2 design rule):

* **Eq. (6) — wrapper bound.** `P((W,R) | x) ≤ C̃ · 2^{K(x) − K(W,R)}`. This is the
  probability→complexity *bridge*: a canonical constant-overhead code of length
  `K(W,R)+O(1)` plus the Coding Theorem turns the posterior into a `K`-expression.
* **Lemma 2 — OFF run lower-bounds the world.** `K(O_{W,∅}) ≤ K(W) + O(1)`, because a
  wrapper simulates the OFF dynamics with constant overhead.

From these we PROVE Theorem 2:  `P((W,R) | x, E) ≤ C · 2^{M(W:R)} · 2^{−Δ}`,
with `M(W:R) = IK` and `Δ = K(O_{W,∅}) − K(O_{W,R})`.
-/

namespace KTAIT

/-- A probabilistic AIT frame: an `AITFrame` plus a universal posterior
    `post e x = P(e | x)` over explanations `e` given an observation `x`. -/
structure AITProb extends AITFrame where
  /-- The Bayesian posterior `P(e | x)` over explanation `e` given observation `x`. -/
  post : Obj → Obj → ℝ

namespace AITProb

variable (F : AITProb)

/-- **Theorem 2 (Probabilistic Regulator Theorem).**
    With `x := O_{W,R}` the observed on-case readout and `xoff := O_{W,∅}` the off-case
    readout, gap `Δ := K(xoff) − K(x)`, and mutual algorithmic information
    `M(W:R) := IK W R`, the universal posterior on the explanation `(W,R)` obeys
    `P((W,R) | x, E) ≤ C · 2^{M(W:R)} · 2^{−Δ}`. -/
theorem probabilistic_regulator_theorem
    (W R xon xoff : F.Obj)
    -- Lemma 2 (OFF run lower-bounds the world): `K(O_{W,∅}) ≤ K(W) + c₀`.
    -- (`c₀ = O(1)` in the paper; the bound does not actually need its sign.)
    (c0 : ℤ)
    (hoff : (F.K xoff : ℤ) ≤ (F.K W : ℤ) + c0)
    -- Eq. (6) wrapper bound: posterior ≤ `C̃ · 2^{K(x) − K(W,R)}`.
    (Ctil : ℝ) (hCtil : 0 < Ctil)
    (hwrap : F.post (F.pair W R) xon
              ≤ Ctil * (2 : ℝ) ^ ((F.K xon : ℤ) - (F.K (F.pair W R) : ℤ))) :
    ∃ C : ℝ, 0 < C ∧
      F.post (F.pair W R) xon
        ≤ C * (2 : ℝ) ^ (IK F.toAITFrame W R)
            * (2 : ℝ) ^ (-((F.K xoff : ℤ) - (F.K xon : ℤ))) := by
  -- The constant: C := C̃ · 2^{c₀}.
  refine ⟨Ctil * (2 : ℝ) ^ c0, by positivity, ?_⟩
  -- Integer exponent inequality:  K(x) − K(W,R)  ≤  c₀ + M(W:R) − Δ.
  have hexp : (F.K xon : ℤ) - (F.K (F.pair W R) : ℤ)
      ≤ c0 + IK F.toAITFrame W R - ((F.K xoff : ℤ) - (F.K xon : ℤ)) := by
    simp only [IK]
    omega
  calc F.post (F.pair W R) xon
      ≤ Ctil * (2 : ℝ) ^ ((F.K xon : ℤ) - (F.K (F.pair W R) : ℤ)) := hwrap
    _ ≤ Ctil * (2 : ℝ) ^ (c0 + IK F.toAITFrame W R - ((F.K xoff : ℤ) - (F.K xon : ℤ))) := by
        gcongr
        norm_num
    _ = Ctil * (2 : ℝ) ^ c0 * (2 : ℝ) ^ (IK F.toAITFrame W R)
          * (2 : ℝ) ^ (-((F.K xoff : ℤ) - (F.K xon : ℤ))) := by
        rw [show c0 + IK F.toAITFrame W R - ((F.K xoff : ℤ) - (F.K xon : ℤ))
              = c0 + IK F.toAITFrame W R + (-((F.K xoff : ℤ) - (F.K xon : ℤ))) from by ring,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        ring

end AITProb

end KTAIT
