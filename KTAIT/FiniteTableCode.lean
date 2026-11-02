/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import KTAIT.CertifiedPrograms.Encoding
import KTAIT.SymmetryCompression

/-!
# Fixed-width table codes for WP0215

The encoder, parser, exact length, recovery and conditional prefix-freeness are
proved for literal tables. The complexity consequence consumes a named bound
for a fixed interpreter executing this parser. This is the standard description
principle; it is not a global axiom or a concrete optimal-machine construction.
The width and number of entries are supplied by the conditional presentation.
-/
namespace KTAIT.FiniteTableCode
open KTAIT.CertifiedPrograms

/-- Concatenate fixed-width binary entries. -/
def encode (width : Nat) : List Nat → CodeBits
  | [] => []
  | a :: xs => fixedBits width a ++ encode width xs

/-- Parse exactly `count` fixed-width entries, returning the unused suffix. -/
def parse (width : Nat) : Nat → CodeBits → Option (List Nat × CodeBits)
  | 0, bits => some ([], bits)
  | count + 1, bits =>
    if width ≤ bits.length then do
      let (xs, rest) ← parse width count (bits.drop width)
      pure (bitsValue (bits.take width) :: xs, rest)
    else none

theorem encode_length (width : Nat) (xs : List Nat) :
    (encode width xs).length = xs.length * width := by
  induction xs with
  | nil => simp [encode]
  | cons a xs ih => simp [encode, fixed_bits_length, ih, Nat.add_mul, Nat.add_comm]

theorem parse_encode_append (width : Nat) (xs : List Nat)
    (hxs : ∀ a ∈ xs, a < 2 ^ width) (tail : CodeBits) :
    parse width xs.length (encode width xs ++ tail) = some (xs, tail) := by
  induction xs with
  | nil => simp [encode, parse]
  | cons a xs ih =>
    have ha := hxs a (by simp)
    have hs : ∀ b ∈ xs, b < 2 ^ width := fun b hb => hxs b (by simp [hb])
    have hl := fixed_bits_length width a
    have ht : (fixedBits width a ++ (encode width xs ++ tail)).take width =
        fixedBits width a := by
      simpa only [hl] using
        (List.take_left (l₁ := fixedBits width a) (l₂ := encode width xs ++ tail))
    have hd : (fixedBits width a ++ (encode width xs ++ tail)).drop width =
        encode width xs ++ tail := by
      simpa only [hl] using
        (List.drop_left (l₁ := fixedBits width a) (l₂ := encode width xs ++ tail))
    have hw : width ≤ (fixedBits width a ++ (encode width xs ++ tail)).length := by simp [hl]
    simp only [List.length_cons, encode, List.append_assoc, parse, if_pos hw, hd, ht,
      ih hs, fixed_bits_value width a ha]
    rfl

/-- Given the entry count and width, every table code recovers its literal entries. -/
theorem parse_encode (width : Nat) (xs : List Nat)
    (hxs : ∀ a ∈ xs, a < 2 ^ width) :
    parse width xs.length (encode width xs) = some (xs, []) := by
  simpa using parse_encode_append width xs hxs []

/-- Equal-length valid tables have prefix-incomparable codes unless identical. -/
theorem encode_prefix_free (width : Nat) {xs ys : List Nat}
    (hx : ∀ a ∈ xs, a < 2 ^ width) (hy : ∀ a ∈ ys, a < 2 ^ width)
    (hlen : xs.length = ys.length) (hp : encode width xs <+: encode width ys) : xs = ys := by
  have hc : encode width xs = encode width ys := hp.eq_of_length (by simp [encode_length, hlen])
  have hs := parse_encode width xs hx
  rw [hc, hlen, parse_encode width ys hy] at hs
  exact (Prod.mk.inj (Option.some.inj hs)).1.symm

/-- Ceiling-log width suffices for every state index, including a singleton alphabet. -/
theorem state_index_fits (n a : Nat) (ha : a < n) : a < 2 ^ Nat.clog 2 n :=
  ha.trans_le (Nat.le_pow_clog (by decide) n)

/-- A fixed interpreter parses the supplied number and width and outputs the
encoded literal list. This named AIT law supplies only its uniform overhead. -/
def InterpreterBound (A : AITFrame) (encodeObject : List Nat → A.Obj)
    (context : A.Obj) (width count overhead : Nat) : Prop :=
  ∀ bits xs, parse width count bits = some (xs, []) →
    A.cond (encodeObject xs) context ≤ bits.length + overhead

/-- The concrete prefix code establishes k ceil(log₂ n) plus interpreter overhead. -/
theorem literal_table_complexity (A : AITFrame) (encodeObject : List Nat → A.Obj)
    (context : A.Obj) (n k overhead : Nat)
    (hInterpreter : InterpreterBound A encodeObject context (Nat.clog 2 n) k overhead)
    (xs : List Nat) (hlen : xs.length = k) (hxs : ∀ a ∈ xs, a < n) :
    A.cond (encodeObject xs) context ≤ k * Nat.clog 2 n + overhead := by
  have hfit : ∀ a ∈ xs, a < 2 ^ Nat.clog 2 n :=
    fun a ha => state_index_fits n a (hxs a ha)
  have hp := parse_encode (Nat.clog 2 n) xs hfit
  rw [hlen] at hp
  simpa [encode_length, hlen] using hInterpreter _ xs hp

/-- An explicit enumeration turns a finite function table into its literal indices. -/
def tableValues {X Q : Type*} {n k : Nat} (states : X ≃ Fin n)
    (rows : Fin k ≃ Q) (t : Q → X) : List Nat :=
  List.ofFn (fun i => (states (t (rows i))).val)

theorem table_values_length {X Q : Type*} {n k : Nat} (states : X ≃ Fin n)
    (rows : Fin k ≃ Q) (t : Q → X) :
    (tableValues states rows t).length = k := by simp [tableValues]

theorem table_values_lt {X Q : Type*} {n k : Nat} (states : X ≃ Fin n)
    (rows : Fin k ≃ Q) (t : Q → X) :
    ∀ a ∈ tableValues states rows t, a < n := by
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact (states (t (rows i))).isLt

/-- Literal table coding supplies the previously abstract table-coding premise. -/
theorem finite_table_coding_bound {X Q : Type*} [Fintype X] [Fintype Q]
    (A : AITFrame) (encodeObject : List Nat → A.Obj) (context : A.Obj)
    (states : X ≃ Fin (Fintype.card X)) (rows : Fin (Fintype.card Q) ≃ Q)
    (overhead : Nat)
    (hInterpreter : InterpreterBound A encodeObject context
      (Nat.clog 2 (Fintype.card X)) (Fintype.card Q) overhead) :
    SymmetryCompression.TableCodingBound A
      (fun t => encodeObject (tableValues states rows t)) context
      (Nat.clog 2 (Fintype.card X)) overhead := by
  intro t
  exact literal_table_complexity A encodeObject context _ _ overhead hInterpreter
    _ (table_values_length states rows t) (table_values_lt states rows t)

/-- The paper's orbit-code bound, with the literal table code proved above and
only the fixed-interpreter and fixed-orbit-decoder AIT laws supplied. -/
theorem equivariant_update_code_bound {G X Q : Type*} [Group G] [MulAction G X]
    [Fintype X] [Fintype Q] (P : SymmetryCompression.OrbitPresentation G X Q)
    (A : AITFrame) (encodeObject : List Nat → A.Obj)
    (encodeUpdate : (X → X) → A.Obj) (context : A.Obj)
    (states : X ≃ Fin (Fintype.card X)) (rows : Fin (Fintype.card Q) ≃ Q)
    (codingCost decoderCost : Nat)
    (hInterpreter : InterpreterBound A encodeObject context
      (Nat.clog 2 (Fintype.card X)) (Fintype.card Q) codingCost)
    (hDecoder : SymmetryCompression.OrbitDecoderBound P A
      (fun t => encodeObject (tableValues states rows t)) encodeUpdate context decoderCost)
    (f : X → X) (hf : SymmetryCompression.EquivariantUpdate (G := G) f) :
    A.cond (encodeUpdate f) context ≤
      Fintype.card Q * Nat.clog 2 (Fintype.card X) + codingCost + decoderCost := by
  exact SymmetryCompression.equivariant_update_complexity P A f hf _ _ _ _ _ _
    (finite_table_coding_bound A encodeObject context states rows codingCost hInterpreter)
    hDecoder

end KTAIT.FiniteTableCode
