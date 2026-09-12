/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Infix
import Mathlib.Tactic

/-!
# Explicit self-delimiting descriptors (WP0228)

The natural-number code uses the Elias gamma header and a least-significant-bit-first
payload of the same length. Reversing the payload is a fixed effective coding convention;
the exact length is `2 * Nat.log 2 (a + 1) + 1`. The parsers are total Lean definitions;
the global and local formats execute using finite tests. This module proves their behavior
and prefix-freeness, but does not supply Mathlib `Computable` witnesses or an optimal machine.
-/

namespace KTAIT.CertifiedPrograms

abbrev CodeBits := List Bool

def fixedBits : Nat → Nat → CodeBits
  | 0, _ => []
  | w + 1, n => (n % 2 == 1) :: fixedBits w (n / 2)

def bitsValue : CodeBits → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * bitsValue bs

theorem fixed_bits_length (w n : Nat) : (fixedBits w n).length = w := by
  induction w generalizing n <;> simp [fixedBits, *]

theorem fixed_bits_value (w n : Nat) (hn : n < 2 ^ w) :
    bitsValue (fixedBits w n) = n := by
  induction w generalizing n with
  | zero =>
    have : n = 0 := by simpa using hn
    simp [fixedBits, bitsValue, this]
  | succ w ih =>
    have hdiv : n / 2 < 2 ^ w := by
      rw [pow_succ] at hn
      omega
    simp only [fixedBits, bitsValue, ih (n / 2) hdiv]
    have hm : n % 2 < 2 := Nat.mod_lt n (by decide)
    by_cases hr : n % 2 = 1
    · simp [hr]; omega
    · have hz : n % 2 = 0 := by omega
      simp [hz]; omega

def gammaLength (a : Nat) : Nat := 2 * Nat.log 2 (a + 1) + 1

def gammaCode (a : Nat) : CodeBits :=
  let d := Nat.log 2 (a + 1)
  List.replicate d false ++ true :: fixedBits d (a + 1 - 2 ^ d)

def parseUnary : CodeBits → Option (Nat × CodeBits)
  | [] => none
  | true :: bs => some (0, bs)
  | false :: bs => do
    let (d, rest) ← parseUnary bs
    pure (d + 1, rest)

def parseGamma (bs : CodeBits) : Option (Nat × CodeBits) := do
  let (d, rest) ← parseUnary bs
  if d ≤ rest.length then
    pure (2 ^ d + bitsValue (rest.take d) - 1, rest.drop d)
  else none

theorem gamma_code_length (a : Nat) : (gammaCode a).length = gammaLength a := by
  simp [gammaCode, gammaLength, fixed_bits_length]
  omega

theorem gamma_length_mono : Monotone gammaLength := by
  intro a b hab
  have := Nat.log_mono_right (Nat.add_le_add_right hab 1) (b := 2)
  unfold gammaLength
  omega

private theorem parse_unary_zeros (d : Nat) (bs : CodeBits) :
    parseUnary (List.replicate d false ++ true :: bs) = some (d, bs) := by
  induction d with
  | zero => simp [parseUnary]
  | succ d ih => simp [List.replicate_succ, parseUnary, ih]

/-- The parser recovers the exact number and leaves every following bit untouched. -/
theorem gamma_parse_append (a : Nat) (tail : CodeBits) :
    parseGamma (gammaCode a ++ tail) = some (a, tail) := by
  let d := Nat.log 2 (a + 1)
  have hp : 2 ^ d ≤ a + 1 := Nat.pow_log_le_self 2 (Nat.succ_ne_zero a)
  have hq : a + 1 < 2 ^ (d + 1) := Nat.lt_pow_succ_log_self (by decide) _
  have hoff : a + 1 - 2 ^ d < 2 ^ d := by rw [pow_succ] at hq; omega
  have hv := fixed_bits_value d (a + 1 - 2 ^ d) hoff
  have hl := fixed_bits_length d (a + 1 - 2 ^ d)
  unfold gammaCode
  change parseGamma ((List.replicate d false ++
    true :: fixedBits d (a + 1 - 2 ^ d)) ++ tail) = _
  rw [List.append_assoc, List.cons_append]
  unfold parseGamma
  rw [parse_unary_zeros]
  simp only [bind, Option.bind]
  have hlen : d ≤ (fixedBits d (a + 1 - 2 ^ d) ++ tail).length := by simp [hl]
  rw [if_pos hlen]
  have ht : (fixedBits d (a + 1 - 2 ^ d) ++ tail).take d =
      fixedBits d (a + 1 - 2 ^ d) := by
    have hx := (List.take_left :
      (fixedBits d (a + 1 - 2 ^ d) ++ tail).take
        (fixedBits d (a + 1 - 2 ^ d)).length = fixedBits d (a + 1 - 2 ^ d))
    simpa only [hl] using hx
  have hd : (fixedBits d (a + 1 - 2 ^ d) ++ tail).drop d = tail := by
    have hx := (List.drop_left :
      (fixedBits d (a + 1 - 2 ^ d) ++ tail).drop
        (fixedBits d (a + 1 - 2 ^ d)).length = tail)
    simpa only [hl] using hx
  have heq : 2 ^ d + (a + 1 - 2 ^ d) - 1 = a := by omega
  simp [ht, hd, hv, heq]

/-- Distinct natural numbers have prefix-incomparable gamma codes. -/
theorem gamma_prefix_free {a b : Nat} (h : gammaCode a <+: gammaCode b) : a = b := by
  obtain ⟨tail, ht⟩ := h
  have hp := gamma_parse_append a tail
  rw [ht] at hp
  have hq := gamma_parse_append b []
  simp only [List.append_nil] at hq
  rw [hq] at hp
  exact (Prod.mk.inj (Option.some.inj hp)).1.symm

def descriptor (width : Nat → Nat → Nat) (L t i : Nat) : CodeBits :=
  gammaCode L ++ gammaCode t ++ fixedBits (width L t) i

/-- The parser rejects t > L and reads exactly the declared index width. -/
def parseDescriptor (width : Nat → Nat → Nat) (bs : CodeBits) :
    Option ((Nat × Nat × Nat) × CodeBits) := do
  let (L, rest₁) ← parseGamma bs
  let (t, rest₂) ← parseGamma rest₁
  if t ≤ L ∧ width L t ≤ rest₂.length then
    pure ((L, t, bitsValue (rest₂.take (width L t))), rest₂.drop (width L t))
  else none

theorem descriptor_length (width : Nat → Nat → Nat) (L t i : Nat) :
    (descriptor width L t i).length = gammaLength L + gammaLength t + width L t := by
  simp [descriptor, gamma_code_length, fixed_bits_length, Nat.add_assoc]

theorem descriptor_parse_append (width : Nat → Nat → Nat) (L t i : Nat)
    (ht : t ≤ L) (hi : i < 2 ^ width L t) (tail : CodeBits) :
    parseDescriptor width (descriptor width L t i ++ tail) = some ((L, t, i), tail) := by
  unfold descriptor
  rw [List.append_assoc, List.append_assoc]
  unfold parseDescriptor
  rw [gamma_parse_append]
  simp only [bind, Option.bind]
  rw [gamma_parse_append]
  dsimp only
  have hl := fixed_bits_length (width L t) i
  have hlen : width L t ≤ (fixedBits (width L t) i ++ tail).length := by simp [hl]
  rw [if_pos ⟨ht, hlen⟩]
  have htake : (fixedBits (width L t) i ++ tail).take (width L t) =
      fixedBits (width L t) i := by
    have hx := (List.take_left :
      (fixedBits (width L t) i ++ tail).take (fixedBits (width L t) i).length =
        fixedBits (width L t) i)
    simpa only [hl] using hx
  have hdrop : (fixedBits (width L t) i ++ tail).drop (width L t) = tail := by
    have hx := (List.drop_left :
      (fixedBits (width L t) i ++ tail).drop (fixedBits (width L t) i).length = tail)
    simpa only [hl] using hx
  simp [htake, hdrop, fixed_bits_value _ _ hi]

/-- Valid two-header records of a fixed format are self-delimiting. -/
theorem descriptor_prefix_free (width : Nat → Nat → Nat) {L t i L' t' i' : Nat}
    (ht : t ≤ L) (hi : i < 2 ^ width L t)
    (ht' : t' ≤ L') (hi' : i' < 2 ^ width L' t')
    (hp : descriptor width L t i <+: descriptor width L' t' i') :
    (L, t, i) = (L', t', i') := by
  obtain ⟨tail, heq⟩ := hp
  have hleft := descriptor_parse_append width L t i ht hi tail
  rw [heq] at hleft
  have hright := descriptor_parse_append width L' t' i' ht' hi' []
  simp only [List.append_nil] at hright
  rw [hright] at hleft
  exact (Prod.mk.inj (Option.some.inj hleft)).1.symm

theorem descriptor_rejects_bad_header (width : Nat → Nat → Nat) (L t i : Nat)
    (ht : L < t) (tail : CodeBits) :
    parseDescriptor width (descriptor width L t i ++ tail) = none := by
  simp [descriptor, List.append_assoc, parseDescriptor, gamma_parse_append,
    bind, Option.bind, Nat.not_le.mpr ht]

def globalWidth (L t : Nat) := L + 1 - t
def localWidth (_L t : Nat) := t + 1

theorem global_descriptor_length (L t i : Nat) :
    (descriptor globalWidth L t i).length =
      L + 1 - t + gammaLength L + gammaLength t := by
  rw [descriptor_length]
  simp only [globalWidth]
  omega

theorem local_descriptor_length (L t i : Nat) :
    (descriptor localWidth L t i).length =
      t + 1 + gammaLength L + gammaLength t := by
  rw [descriptor_length]
  simp only [localWidth]
  omega

end KTAIT.CertifiedPrograms
