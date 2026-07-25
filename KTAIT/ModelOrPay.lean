/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic
import KTAIT.ART

/-!
# KTAIT.ModelOrPay — the gap ART leaves open (WP0203)

Formalization of the *checkable* content of WP0203, *The ART Tail Does Not Follow: A
Correction to the Concentration Corollary of the Algorithmic Regulator Theorem*.

**Provenance note (2026-07-26).** This module was written on 2026-07-16 against an earlier
draft of WP0203 titled *Model It or Pay For It*, whose headline was a conjecture ("model it
or pay for it"). That draft was recast the same night into the present correction note, and
the conjecture was demoted to an open question. The module name is kept because what it
formalizes is exactly the gap the final paper leaves open — "be big, or be hot" — but the
cross-references below have been re-mapped onto the published structure (Propositions 1–2,
Remarks 1–4). Where the earlier draft's structure has no counterpart, that is said.

## What can and cannot be formalized here

The paper's headline conjecture — a faithful regulator sustaining `Δ_N` either has
`MAI = Ω(Δ_N)` or dissipates `Ω(Δ_N)·kT ln 2` — is **not** stateable in this frame, and
that is itself a finding worth recording. `Q_diss` is a physical quantity; `AITFrame`
has no notion of a heat bath, a temperature, or a physical realization. Stating the
conjecture needs a formal model of physical realization (stochastic thermodynamics over
a defined coupling) that the paper does not supply. We therefore formalize the parts
that *are* mathematics:

* `simple_regulator_cannot_model` — the sharpening: since `MAI(W:R) ≤ K(R)` up to slack,
  the modelling disjunct **forces `K(R) = Ω(Δ)`**. A regulator simpler than the gap it
  opens cannot take that disjunct. "Model it or pay for it" is therefore
  **"be big, or be hot."**
* `perpair_does_not_lift` — a per-pair bound of `2^(-k)` places **no** useful bound on
  the sum over a fiber of size `2^k`. Witnessed, not asserted.
* `invertible_bound_insufficient` — the invertible-coupling inequality
  `MAI ≥ K(R) − K(ON)` is satisfiable with `MAI ≪ Δ`. Witnessed.

## Discipline

As in `Basic.lean`, the AIT facts are **hypotheses about a frame**, never global axioms.
`MAICapped` is the one AIT fact assumed here; the toy model of `ToyModel.lean` is the
kind of witness that keeps it non-vacuous.
-/

namespace KTAIT

namespace ModelOrPay

/-! ## 1. The AIT fact we assume -/

variable (F : AITFrame)

/-- **Assumed AIT fact.** Mutual algorithmic information is capped by either side's
complexity, up to the `O(log)` slack: `I(x:y) ≤ K(y) + O(log)`. (Standard: it follows
from `K(⟨x,y⟩) ≥ K(x) − O(log)`.) Stated as a hypothesis about a frame, not an axiom. -/
def MAICapped : Prop := ∀ x y : F.Obj, IK F x y ≤ (F.K y : Int) + (F.slack : Int)

/-! ## 2. The sharpening: "model it" means "be big"

The conjecture of the earlier draft offered a regulator two options: model the world's structure, or
dissipate it. The first option is not free of structural cost — it forces the regulator
to be at least as complex as the gap it opens. This is what makes the clamp interesting:
a clamp is *cheap*, and cheapness alone forecloses the modelling disjunct. -/

/-- **The modelling disjunct forces `K(R) = Ω(Δ)`.**

If the regulator's own complexity (plus slack) falls below the gap, then its mutual
algorithmic information with the world does too — so it *cannot* satisfy
`MAI(W:R) ≳ Δ`, whatever the world is. A regulator simpler than the gap it opens is
forced onto the dissipative horn.

This is the formal content of "a simple regulator cannot carry Δ bits of model." -/
theorem simple_regulator_cannot_model (hcap : MAICapped F) (W R : F.Obj) (Δ : Int)
    (hsimple : (F.K R : Int) + (F.slack : Int) < Δ) :
    IK F W R < Δ :=
  lt_of_le_of_lt (hcap W R) hsimple

/-- **Contrapositive, as the paper should state it.** If a pair does satisfy the
modelling disjunct `Δ ≤ MAI(W:R)`, then the regulator is at least as complex as the gap,
up to slack: `Δ ≤ K(R) + slack`. "Model it" ⇒ "be big." -/
theorem model_implies_big (hcap : MAICapped F) (W R : F.Obj) (Δ : Int)
    (hmodel : Δ ≤ IK F W R) :
    Δ ≤ (F.K R : Int) + (F.slack : Int) :=
  le_trans hmodel (hcap W R)

/-- The clamp, formally: a regulator of `O(1)` complexity has `O(1)` mutual algorithmic
information with **every** world. Nothing about the world can rescue it. So the
counterexample of WP0203 Prop. 2 (Refutation) needs no special pleading — its `MAI ≈ 0` is
forced by `K(R) = O(1)` alone. -/
theorem clamp_MAI_bounded_by_own_complexity (hcap : MAICapped F) (R : F.Obj) :
    ∀ W : F.Obj, IK F W R ≤ (F.K R : Int) + (F.slack : Int) :=
  fun W => hcap W R

/-! ## 3. Per-pair bounds do not lift to the fiber

WP0203 §4 ("What the honest summation gives"). The point is elementary and entirely about
summation: a bound on each
term says nothing useful about a sum with enough terms. We witness it rather than assert
it — `2^k` terms each `≤ 2^(-k)` can sum to `1`. -/

/-- **Per-pair bounds do not lift.** For every `k` there is a family of `2^k`
explanations, each carrying posterior support at most `2^(-k)` — the ART per-pair
penalty — whose **total** support is `1`. No tail bound follows from the per-pair bound.

This is the multiplicity objection, in its entirety. The `2^(-k)` per-pair penalty is
real and is exactly cancelled by a fiber of size `2^k`. -/
theorem perpair_does_not_lift (k : ℕ) :
    ∃ (M : ℕ) (f : Fin M → ℝ),
      0 < M ∧
      (∀ i, 0 ≤ f i ∧ f i ≤ (2 : ℝ) ^ (-(k : ℤ))) ∧
      ∑ i, f i = 1 := by
  refine ⟨2 ^ k, fun _ => (2 : ℝ) ^ (-(k : ℤ)), Nat.two_pow_pos k, ?_, ?_⟩
  · intro i
    exact ⟨by positivity, le_rfl⟩
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        zpow_neg, zpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
    field_simp

/-- The same statement in the form the paper uses: if the fiber has `2^k` members and
each is penalised by `2^(-k)`, the product is `1` — the penalty is exactly consumed by
the multiplicity. Summing the ART bound over the fiber therefore yields the trivial
bound. -/
theorem multiplicity_cancels_penalty (k : ℕ) :
    ((2 : ℝ) ^ k) * ((2 : ℝ) ^ (-(k : ℤ))) = 1 := by
  rw [zpow_neg, zpow_natCast]
  field_simp

/-! ## 4. The invertible-coupling bound does not reach Δ

the earlier draft's Remark 6, which has no counterpart in the published note (its Remarks
run 1–4). Invertible coupling yields `MAI(W:R) ≥ K(R) − K(ON) − O(log)`. That is
a bound in `K(R) − K(ON)`, **not** in `Δ = K(OFF) − K(ON)`. The two coincide only if
`K(R) ≥ K(OFF)`. We witness the gap. -/

/-- **Faithfulness alone does not deliver the strict bound.** There are values satisfying
the invertible-coupling inequality `K(R) − K(ON) ≤ MAI` for which `MAI` is nonetheless
far below the gap `Δ = K(OFF) − K(ON)`.

Witness: a regulator of complexity `1`, an ON readout of complexity `0`, an OFF readout
of complexity `100`. Invertible coupling demands only `MAI ≥ 1`; the gap is `100`. This
is the clamp's signature — tiny `K(R)`, huge `K(OFF)`. -/
theorem invertible_bound_insufficient :
    ∃ KR Kon Koff MAI : Int,
      0 ≤ KR ∧ 0 ≤ Kon ∧ 0 ≤ Koff ∧
      KR - Kon ≤ MAI ∧                    -- invertible coupling satisfied
      MAI < Koff - Kon ∧                  -- yet MAI is below the gap …
      MAI + 98 ≤ Koff - Kon := by         -- … indeed far below it
  exact ⟨1, 0, 100, 1, by norm_num, by norm_num, by norm_num,
         by norm_num, by norm_num, by norm_num⟩

/-- The two bounds coincide exactly when the regulator is at least as complex as the
unregulated readout — the hypothesis nothing supplies, and the one a clamp violates. -/
theorem invertible_reaches_gap_iff (KR Kon Koff : Int) :
    (Koff - Kon ≤ KR - Kon) ↔ (Koff ≤ KR) := by
  constructor <;> intro h <;> omega

/-! ## 5. What is *not* formalized, and why

`Q_diss = Ω(Δ_N)·kT ln 2` has no referent in `AITFrame`: there is no bath, no
temperature, no dynamics, no notion of a physical realization of `W` or `R`. The
conjecture as stated in the earlier draft is therefore **not a well-formed statement of this
theory** — it is a statement about physical realizations, and it needs a formalism
(stochastic thermodynamics over a specified coupling) that the paper does not supply.

That is not a defect of the conjecture; it is a specification of the work remaining.
Recording it here so the gap is visible rather than papered over:

* the escape dichotomy of the earlier draft (dropped from the published note) quantifies
  over "any physical realization";
* its saturation claim quantifies over sinks of "finite capacity `c` bits";
* neither notion exists in `AITFrame`.

The three theorems above are what survives translation into this frame. They are, in
compensation, unconditional given `MAICapped`. -/

end ModelOrPay

end KTAIT
