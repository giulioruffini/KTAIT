/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import KTAIT.CertifiedPrograms.Marking
import KTAIT.CertifiedPrograms.Encoding

/-!
# Binary candidate counts and the final integer arithmetic (WP0228)

The finite binary universe and the bit width of every marking event are proved here.
`combine_decoder_costs` is only the arithmetic combination of two separately supplied
decoder costs. It does not assert that those costs have been established for a universal
machine. In particular it is not a formalization of the paper's whole-function AIT theorem.
-/

namespace KTAIT.CertifiedPrograms

def wordsExact : Nat → Finset CodeBits
  | 0 => {[]}
  | n + 1 => ((wordsExact n).image (false :: ·)) ∪
      ((wordsExact n).image (true :: ·))

theorem words_exact_length (n : Nat) (s : CodeBits) (hs : s ∈ wordsExact n) :
    s.length = n := by
  induction n generalizing s with
  | zero => simpa [wordsExact] using hs
  | succ n ih =>
    simp only [wordsExact, Finset.mem_union, Finset.mem_image] at hs
    rcases hs with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ <;> simp [ih u hu]

theorem words_exact_complete (s : CodeBits) : s ∈ wordsExact s.length := by
  induction s with
  | nil => simp [wordsExact]
  | cons b s ih =>
    cases b <;> simp [wordsExact, ih]

theorem words_exact_card (n : Nat) : (wordsExact n).card = 2 ^ n := by
  induction n with
  | zero => simp [wordsExact]
  | succ n ih =>
    have hd : Disjoint ((wordsExact n).image (false :: ·))
        ((wordsExact n).image (true :: ·)) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp ha
      obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hb
      have := hx.trans hy.symm
      simp at this
    rw [wordsExact, Finset.card_union_of_disjoint hd]
    rw [Finset.card_image_of_injective _ (fun _ _ he => List.cons_injective he),
      Finset.card_image_of_injective _ (fun _ _ he => List.cons_injective he), ih]
    rw [pow_succ]
    omega

def wordsThrough : Nat → Finset CodeBits
  | 0 => wordsExact 0
  | L + 1 => wordsThrough L ∪ wordsExact (L + 1)

theorem words_through_length (L : Nat) (s : CodeBits) (hs : s ∈ wordsThrough L) :
    s.length ≤ L := by
  induction L with
  | zero => exact le_of_eq (words_exact_length 0 s hs)
  | succ L ih =>
    rcases Finset.mem_union.mp hs with hs | hs
    · exact (ih hs).trans (Nat.le_succ L)
    · exact le_of_eq (words_exact_length (L + 1) s hs)

theorem words_through_complete (L : Nat) (s : CodeBits) (hs : s.length ≤ L) :
    s ∈ wordsThrough L := by
  induction L with
  | zero =>
    have he : s.length = 0 := by omega
    simpa [wordsThrough, ← he] using words_exact_complete s
  | succ L ih =>
    by_cases h : s.length ≤ L
    · exact Finset.mem_union_left _ (ih h)
    · have he : s.length = L + 1 := by omega
      exact Finset.mem_union_right _ (he ▸ words_exact_complete s)

/-- Actual binary strings, including the empty string, have the claimed exact cardinality. -/
theorem bounded_binary_card (L : Nat) : (wordsThrough L).card + 1 = 2 ^ (L + 1) := by
  induction L with
  | zero => decide
  | succ L ih =>
    have hd : Disjoint (wordsThrough L) (wordsExact (L + 1)) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      have hlen := words_through_length L a ha
      have heq := words_exact_length (L + 1) a hb
      omega
    rw [wordsThrough, Finset.card_union_of_disjoint hd, words_exact_card]
    rw [pow_succ (n := L + 1)]
    omega

/-- The dyadic threshold exponent is within the length budget. -/
theorem class_log_range (L N : Nat) (hN : 0 < N)
    (hbound : N < 2 ^ (L + 1)) :
    2 ^ Nat.log 2 N ≤ N ∧ N < 2 ^ (Nat.log 2 N + 1) ∧ Nat.log 2 N ≤ L := by
  refine ⟨Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by decide) N, ?_⟩
  have := Nat.log_lt_of_lt_pow (by omega : N ≠ 0) hbound
  omega

/-- The charging budget gives a strict bound on the number of events, with no rounding loss. -/
theorem event_count_fits_width (L t J : Nat) (ht : t ≤ L)
    (hbudget : J * 2 ^ t < 2 ^ (L + 1)) : J < 2 ^ globalWidth L t := by
  have he : 2 ^ (L + 1) = 2 ^ globalWidth L t * 2 ^ t := by
    rw [← pow_add]
    congr 1
    unfold globalWidth
    omega
  rw [he] at hbudget
  exact Nat.lt_of_mul_lt_mul_right hbudget

/-- Every event produced by the executable marking scan fits the global index field. -/
theorem marking_rank_bound {m : Nat} (L t n : Nat) (ht : t ≤ L)
    (hUniverse : m + 1 < 2 ^ (L + 1))
    (R : Fin (m + 1) → Fin (m + 1) → Prop)
    (e : Nat → Option (Fin (m + 1) × Fin (m + 1)))
    (hes : ∀ j p a, e j = some (p, a) → R p a) :
    (markingRun e (2 ^ t) n).emitted.length < 2 ^ globalWidth L t := by
  apply event_count_fits_width L t _ ht
  exact (marking_event_budget R e hes (2 ^ t) n).trans_lt hUniverse

/-- Arithmetic only: the two decoder cost bounds must still be supplied and instantiated. -/
theorem combine_decoder_costs (E k L t cG cI : Nat) (ht : t ≤ L)
    (hG : k ≤ L + 1 - t + gammaLength L + gammaLength t + cG)
    (hI : E ≤ t + 1 + gammaLength L + gammaLength t + cI) :
    E + k ≤ L + 4 * gammaLength L + (cG + cI + 2) := by
  have hm := gamma_length_mono ht
  omega

/-- Arithmetic specialization to additive minimality excess. -/
theorem near_minimal_cost_corollary (E k L δ c : Nat)
    (h : E + k ≤ L + 4 * gammaLength L + c) (hL : L ≤ k + δ) :
    E ≤ δ + 4 * gammaLength (k + δ) + c := by
  have hm := gamma_length_mono hL
  omega

end KTAIT.CertifiedPrograms
