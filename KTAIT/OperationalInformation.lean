/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Kaiti / Codex)
-/
import Mathlib

/-!
# Operational information for reliable decisions (WP0251)

The effective search is actual partial-recursive search. The AIT consequences
use named hypotheses for conditional prefix coding and Meyer--Loveland.
These are NOT axioms, and no quantum or physical principle is asserted here.
The separate WP0215Hypercomputation project proves Meyer from a concrete
optimal-machine definition on Lean 4.35; this module retains KTAIT's 4.31
interface and does not claim to import that proof across toolchains.

`obs (a,n) t` is an effective finite-stage attempt to reconstruct the first
`n` answers using replacement description `a`. Soundness and termination are
premises justified by the paper's probability-threshold construction.
The scalar threshold bounds are proved here, but assembling that construction
into a block observer, quantum trace-distance contraction, state nets, and
tensor-product inequalities remain paper-level arguments.

`reliable_report_bound` separately checks a scalar consequence for a complete
reported string, assuming reference coding and a success-weighted surprisal
budget. It does not formalize the Gibbs/quantum argument supplying that budget.
The binary-relative-entropy lemmas prove the classical event inequality used
in that argument, including actual success probabilities zero and one. The
quantum data-processing and Gibbs steps remain named paper-level premises.
-/

namespace KTAIT.OperationalInformation

abbrev Code := List Bool

/-- The first `n` bits of the total task `f`. -/
def answers (f : ℕ → Bool) (n : ℕ) : Code := (List.range n).map f

/-- Search finite stages for the first recognized answer table. -/
def recover (obs : Code × ℕ → ℕ → Option Code) : Code × ℕ →. Code :=
  fun z => Nat.rfindOpt (obs z)

/-- The search uses no supplied bound on stopping time. -/
theorem recover_partrec (obs : Code × ℕ → ℕ → Option Code)
    (hobs : Computable₂ obs) : Partrec (recover obs) :=
  Partrec.rfindOpt hobs

/-- Every successful search returns the target if every report is sound. -/
theorem recover_correct (obs : Code × ℕ → ℕ → Option Code)
    (z : Code × ℕ) (target : Code)
    (halts : ∃ t value, value ∈ obs z t)
    (sound : ∀ t value, value ∈ obs z t → value = target) :
    target ∈ recover obs z := by
  have hdom : (Nat.rfindOpt (obs z)).Dom := Nat.rfindOpt_dom.mpr halts
  obtain ⟨value, hv⟩ := Part.dom_iff_mem.mp hdom
  obtain ⟨t, ht⟩ := Nat.rfindOpt_spec hv
  simpa only [recover, sound t value ht] using hv

/-- Standard conditional prefix coding under a partial computable map. -/
def DecoderCoding (CK : Code → ℕ → ℕ) : Prop :=
  ∀ g : Code × ℕ →. Code, Partrec g →
    ∃ c : ℕ, ∀ a n out, out ∈ g (a, n) → CK out n ≤ CK a n + c

/-- Standard Meyer--Loveland characterization, explicit at this interface. -/
def Meyer (CK : Code → ℕ → ℕ) : Prop :=
  ∀ f : ℕ → Bool, Computable f ↔ ∃ B : ℕ, ∀ n, CK (answers f n) n ≤ B

/-- A replacement family supplies sound, eventually recognized answer tables.
The family `a` need not be computable. -/
structure Adequate (obs : Code × ℕ → ℕ → Option Code)
    (a : ℕ → Code) (f : ℕ → Bool) : Prop where
  halts : ∀ n, ∃ t value, value ∈ obs (a n, n) t
  sound : ∀ n t value, value ∈ obs (a n, n) t → value = answers f n

/-- AIT replacement bound, with one constant for every adequate family and task.
The constant depends on the fixed observer and the coding interface. -/
theorem replacement_bound (CK : Code → ℕ → ℕ) (hcoding : DecoderCoding CK)
    (obs : Code × ℕ → ℕ → Option Code) (hobs : Computable₂ obs) :
    ∃ c : ℕ, ∀ a f, Adequate obs a f →
      ∀ n, CK (answers f n) n ≤ CK (a n) n + c := by
  obtain ⟨c, hc⟩ := hcoding (recover obs) (recover_partrec obs hobs)
  refine ⟨c, fun a f ha n => hc (a n) n (answers f n) ?_⟩
  exact recover_correct obs (a n, n) (answers f n) (ha.halts n) (ha.sound n)

/-- Bounded conditional replacement complexity implies a computable task,
without an effective selector for the replacement descriptions. -/
theorem computable_of_bounded_replacements (CK : Code → ℕ → ℕ)
    (hcoding : DecoderCoding CK) (hmeyer : Meyer CK)
    (obs : Code × ℕ → ℕ → Option Code) (hobs : Computable₂ obs)
    (a : ℕ → Code) (f : ℕ → Bool) (ha : Adequate obs a f)
    (bounded : ∃ B : ℕ, ∀ n, CK (a n) n ≤ B) : Computable f := by
  obtain ⟨c, hc⟩ := replacement_bound CK hcoding obs hobs
  obtain ⟨B, hB⟩ := bounded
  apply (hmeyer f).mpr
  exact ⟨B + c, fun n => (hc a f ha n).trans (Nat.add_le_add_right (hB n) c)⟩

/-- The contrapositive asserts unboundedness, not a linear rate or randomness. -/
theorem noncomputable_unbounded_replacements (CK : Code → ℕ → ℕ)
    (hcoding : DecoderCoding CK) (hmeyer : Meyer CK)
    (obs : Code × ℕ → ℕ → Option Code) (hobs : Computable₂ obs)
    (a : ℕ → Code) (f : ℕ → Bool) (ha : Adequate obs a f)
    (hnot : ¬ Computable f) : ∀ B : ℕ, ∃ n, B < CK (a n) n := by
  intro B
  by_contra h
  push Not at h
  exact hnot (computable_of_bounded_replacements CK hcoding hmeyer obs hobs a f ha ⟨B, h⟩)

/-- A physical description budget transfers to the answer family. The budget
itself is a premise: this theorem does not derive a quantum state net. -/
theorem budget_transfer (CK : Code → ℕ → ℕ) (hcoding : DecoderCoding CK)
    (obs : Code × ℕ → ℕ → Option Code) (hobs : Computable₂ obs) :
    ∃ c : ℕ, ∀ a f (budget : ℕ → ℕ), Adequate obs a f →
      (∀ n, CK (a n) n ≤ budget n) →
      ∀ n, CK (answers f n) n ≤ budget n + c := by
  obtain ⟨c, hc⟩ := replacement_bound CK hcoding obs hobs
  exact ⟨c, fun a f budget ha hb n =>
    (hc a f ha n).trans (Nat.add_le_add_right (hb n) c)⟩

/-- Wrong terminal events cannot cross the decision threshold after replacing
probabilities to error 1/12 and estimating the replacement to error 1/48. -/
theorem wrong_estimate_below_half (p q e : ℝ)
    (hwrong : p ≤ 1 / 3) (hreplace : |q - p| ≤ 1 / 12)
    (hestimate : |e - q| ≤ 1 / 48) : e < 1 / 2 := by
  have hq := (abs_le.mp hreplace).2
  have he := (abs_le.mp hestimate).2
  linarith

/-- Once actual correct-report probability exceeds 5/8, the estimated
replacement probability crosses 1/2. Eventual success at least 2/3 supplies
such a finite stage; deriving this from a probability process is paper-level. -/
theorem correct_estimate_above_half (p q e : ℝ)
    (hcorrect : 5 / 8 < p) (hreplace : |q - p| ≤ 1 / 12)
    (hestimate : |e - q| ≤ 1 / 48) : 1 / 2 < e := by
  have hq := (abs_le.mp hreplace).1
  have he := (abs_le.mp hestimate).1
  linarith

/-- A complete reported string inherits a budget from reference surprisal.
`surprisal` and `budget` are in bits; `margin` is a positive lower bound on
the unconditional probability of that particular complete string.
The prefix-coding bound and the physical inequality are named premises.
Quantum relative-entropy data processing, the Gibbs state, and effectiveness
of reference report probabilities are NOT formalized by this scalar result. -/
theorem reliable_report_bound (complexity : ℕ)
    (overhead surprisal budget success margin : ℝ)
    (hmargin : 0 < margin) (hreliable : margin ≤ success)
    (hsurprisal : 0 ≤ surprisal)
    (hcoding : (complexity : ℝ) ≤ surprisal + overhead)
    (hphysical : success * surprisal ≤ budget + 1) :
    (complexity : ℝ) ≤ (budget + 1) / margin + overhead := by
  have hweighted : margin * surprisal ≤ budget + 1 :=
    (mul_le_mul_of_nonneg_right hreliable hsurprisal).trans hphysical
  have hbound : surprisal ≤ (budget + 1) / margin := by
    apply (le_div_iff₀ hmargin).2
    simpa only [mul_comm] using hweighted
  linarith

/-- Binary relative entropy in natural-log units on `0 ≤ p ≤ 1`, `0 < q < 1`.
Outside that domain Lean's totalized logarithm and division need not agree
with extended-real relative entropy. In particular this definition is not
used to represent the infinite divergence at `q = 0` or `q = 1, p < 1`. -/
noncomputable def binaryRelativeEntropy (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/-- The binary divergence decomposes into cross-entropy minus binary entropy.
Both actual-probability endpoints are included with the convention `0 log 0 = 0`. -/
theorem binaryRelativeEntropy_eq_binEntropy (p q : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hq₀ : 0 < q) (hq₁ : q < 1) :
    binaryRelativeEntropy p q = -Real.binEntropy p +
      p * (-Real.log q) + (1 - p) * (-Real.log (1 - q)) := by
  rcases hp₀.eq_or_lt with hp | hp
  · subst p
    simp [binaryRelativeEntropy, Real.binEntropy, one_div]
  rcases hp₁.eq_or_lt with hp_one | hp_one
  · subst p
    simp [binaryRelativeEntropy, Real.binEntropy, one_div]
  unfold binaryRelativeEntropy Real.binEntropy
  rw [Real.log_div hp.ne' hq₀.ne',
    Real.log_div (sub_pos.mpr hp_one).ne' (sub_pos.mpr hq₁).ne',
    Real.log_inv, Real.log_inv]
  ring

/-- Success-weighted reference surprisal is bounded by binary divergence
plus the actual binary entropy. This is the classical event step in the
hypothesis-testing weak converse, not a new information-theoretic inequality. -/
theorem binary_surprisal_le (p q : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hq₀ : 0 < q) (hq₁ : q < 1) :
    p * (-Real.log q) ≤ binaryRelativeEntropy p q + Real.binEntropy p := by
  rw [binaryRelativeEntropy_eq_binEntropy p q hp₀ hp₁ hq₀ hq₁]
  have hlog : 0 ≤ -Real.log (1 - q) :=
    neg_nonneg.mpr (Real.log_nonpos (sub_pos.mpr hq₁).le (by linarith))
  have hrest := mul_nonneg (sub_nonneg.mpr hp₁) hlog
  linarith

/-- Replacing binary entropy by `log 2` gives the one-bit allowance used
in WP0251's original Gibbs-report derivation. All quantities here are in nats. -/
theorem binary_surprisal_le_add_log_two (p q : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hq₀ : 0 < q) (hq₁ : q < 1) :
    p * (-Real.log q) ≤ binaryRelativeEntropy p q + Real.log 2 :=
  (binary_surprisal_le p q hp₀ hp₁ hq₀ hq₁).trans
    (add_le_add le_rfl Real.binEntropy_le_log_two)

/-- A complete-report bound from conditional prefix coding and a binary
relative-entropy budget, with the classical event inequality proved here.
The coding premise has interpretation `K(z|n) ≤ -log₂ q + K(b|n) + c_M`.
Its uniform constant, the reference semimeasure, quantum data processing,
and the Gibbs budget are external obligations, not certified by this theorem.
`budget` is in nats; complexity and overhead are in bits. -/
theorem reliable_report_of_binary_budget (complexity : ℕ)
    (overhead budget p margin q : ℝ)
    (hmargin : 0 < margin) (hreliable : margin ≤ p) (hp₁ : p ≤ 1)
    (hq₀ : 0 < q) (hq₁ : q < 1)
    (hcoding : (complexity : ℝ) ≤ (-Real.log q) / Real.log 2 + overhead)
    (hphysical : binaryRelativeEntropy p q ≤ budget) :
    (complexity : ℝ) ≤ (budget + Real.log 2) / (margin * Real.log 2) + overhead := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsurprisal : 0 ≤ (-Real.log q) / Real.log 2 :=
    div_nonneg (neg_nonneg.mpr (Real.log_nonpos hq₀.le hq₁.le)) htwo.le
  have hbinary := binary_surprisal_le_add_log_two p q
    (hmargin.le.trans hreliable) hp₁ hq₀ hq₁
  have hweighted : p * ((-Real.log q) / Real.log 2) ≤ budget / Real.log 2 + 1 := by
    calc
      p * ((-Real.log q) / Real.log 2) = (p * (-Real.log q)) / Real.log 2 :=
        (mul_div_assoc _ _ _).symm
      _ ≤ (budget + Real.log 2) / Real.log 2 :=
        div_le_div_of_nonneg_right (hbinary.trans (add_le_add hphysical le_rfl)) htwo.le
      _ = budget / Real.log 2 + 1 := by rw [add_div, div_self htwo.ne']
  have hbound := reliable_report_bound complexity overhead
    ((-Real.log q) / Real.log 2) (budget / Real.log 2) p margin
    hmargin hreliable hsurprisal hcoding hweighted
  have hunits : (budget / Real.log 2 + 1) / margin =
      (budget + Real.log 2) / (margin * Real.log 2) := by
    field_simp
  rwa [hunits] at hbound

/-- Reference report probability one is handled by coding directly, without
using the real-valued binary-divergence definition at its excluded boundary.
Nonnegativity of the physical budget is a premise; a Gibbs application must
justify it even when the partition function is less than one. -/
theorem reliable_report_of_reference_one (complexity : ℕ)
    (overhead budget margin : ℝ) (hbudget : 0 ≤ budget) (hmargin : 0 < margin)
    (hcoding : (complexity : ℝ) ≤ (-Real.log 1) / Real.log 2 + overhead) :
    (complexity : ℝ) ≤ (budget + Real.log 2) / (margin * Real.log 2) + overhead := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsimple : (complexity : ℝ) ≤ overhead := by simpa using hcoding
  have hallowance : 0 ≤ (budget + Real.log 2) / (margin * Real.log 2) :=
    div_nonneg (add_nonneg hbudget htwo.le) (mul_pos hmargin htwo).le
  linarith

end KTAIT.OperationalInformation
