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

end KTAIT.OperationalInformation
