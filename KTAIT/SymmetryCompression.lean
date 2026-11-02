/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import KTAIT.Basic

/-!
# Effective orbit tables and conditional description costs (WP0215)

An orbit presentation supplies representatives, class labels, and a group element
reconstructing each state from its representative. Equivariant updates are recovered
from their values on representatives, and induce closed updates on the classes.
For finite carriers this gives a cardinality bound on equivariant updates.

The final AIT bound uses named table-coding and decoder-cost hypotheses. The table
and reconstruction functions are explicit Lean definitions. This module does not
construct partial-recursive encodings of arbitrary group actions, an optimal prefix
machine, or a uniform procedure discovering a suitable symmetry.
-/

namespace KTAIT.SymmetryCompression

variable {G X Q : Type*} [Group G] [MulAction G X]

/-- Data for a represented orbit quotient. The reconstruction field supplies the
coordinate choice; no effective orbit selector is inferred from an abstract action. -/
structure OrbitPresentation (G X Q : Type*) [Group G] [MulAction G X] where
  label : X → Q
  representative : Q → X
  coordinate : X → G
  representative_label : ∀ q, label (representative q) = q
  label_invariant : ∀ (g : G) (x : X), label (g • x) = label x
  reconstruct : ∀ x, coordinate x • representative (label x) = x

/-- The update commutes with every supplied group action. -/
def EquivariantUpdate (f : X → X) : Prop := ∀ (g : G) (x : X), f (g • x) = g • f x

variable (P : OrbitPresentation G X Q)

/-- One image for each orbit representative. -/
def orbitTable (f : X → X) : Q → X := fun q => f (P.representative q)

/-- Extend representative images using the supplied orbit coordinates. -/
def decodeOrbitTable (t : Q → X) : X → X :=
  fun x => P.coordinate x • t (P.label x)

/-- Every equivariant update is reconstructed from its representative table. -/
theorem orbit_table_recovery (f : X → X) (hf : EquivariantUpdate (G := G) f) :
    decodeOrbitTable P (orbitTable P f) = f := by
  funext x
  dsimp [decodeOrbitTable, orbitTable]
  rw [← hf, P.reconstruct]

/-- Representative tables distinguish equivariant updates. -/
theorem orbit_table_injective :
    Function.Injective (fun f : { f : X → X // EquivariantUpdate (G := G) f } =>
      orbitTable P f.val) := by
  intro f g h
  apply Subtype.ext
  calc
    f.val = decodeOrbitTable P (orbitTable P f.val) :=
      (orbit_table_recovery P f.val f.property).symm
    _ = decodeOrbitTable P (orbitTable P g.val) := congrArg (decodeOrbitTable P) h
    _ = g.val := orbit_table_recovery P g.val g.property

include P in
/-- With n states and k represented orbits, there are at most n^k equivariant updates. -/
theorem equivariant_update_count [Fintype X] [Fintype Q] :
    Nat.card { f : X → X // EquivariantUpdate (G := G) f } ≤
      Fintype.card X ^ Fintype.card Q := by
  classical
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun] using Nat.card_le_card_of_injective
    (fun f : { f : X → X // EquivariantUpdate (G := G) f } => orbitTable P f.val)
    (orbit_table_injective P)

/-- The retained update takes the class of each representative's image. -/
def quotientUpdate (f : X → X) : Q → Q :=
  fun q => P.label (f (P.representative q))

/-- Equivariance gives exact closure of the represented orbit quotient. -/
theorem quotient_update_commutes (f : X → X) (hf : EquivariantUpdate (G := G) f)
    (x : X) : P.label (f x) = quotientUpdate P f (P.label x) := by
  unfold quotientUpdate
  calc
    P.label (f x) = P.label (f (P.coordinate x • P.representative (P.label x))) :=
      congrArg (fun y => P.label (f y)) (P.reconstruct x).symm
    _ = P.label (P.coordinate x • f (P.representative (P.label x))) := by rw [hf]
    _ = P.label (f (P.representative (P.label x))) := P.label_invariant _ _

/-- Closure iterates over an arbitrary ordinary finite horizon. -/
theorem quotient_update_iterates (f : X → X) (hf : EquivariantUpdate (G := G) f)
    (n : Nat) (x : X) : P.label ((f^[n]) x) = ((quotientUpdate P f)^[n]) (P.label x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      quotient_update_commutes P f hf, ih]

variable (A : AITFrame)

/-- Standard fixed-width table coding, conditional on the supplied presentation.
The width must be justified by the chosen finite encoding. -/
def TableCodingBound [Fintype Q] (encodeTable : (Q → X) → A.Obj) (context : A.Obj)
    (width codingCost : Nat) : Prop :=
  ∀ t, A.cond (encodeTable t) context ≤ Fintype.card Q * width + codingCost

/-- Standard conditional description bound for the fixed table decoder.
This requires an effective coded presentation; it is not asserted for arbitrary maps. -/
def OrbitDecoderBound (encodeTable : (Q → X) → A.Obj)
    (encodeUpdate : (X → X) → A.Obj) (context : A.Obj) (decoderCost : Nat) : Prop :=
  ∀ t, A.cond (encodeUpdate (decodeOrbitTable P t)) context ≤
    A.cond (encodeTable t) context + decoderCost

/-- The orbit-table reconstruction converts the named coding premises into a bound
on the complete equivariant update, including both coding and interpreter constants. -/
theorem equivariant_update_complexity [Fintype Q] (f : X → X)
    (hf : EquivariantUpdate (G := G) f)
    (encodeTable : (Q → X) → A.Obj) (encodeUpdate : (X → X) → A.Obj)
    (context : A.Obj) (width codingCost decoderCost : Nat)
    (hcode : TableCodingBound A encodeTable context width codingCost)
    (hdecode : OrbitDecoderBound P A encodeTable encodeUpdate context decoderCost) :
    A.cond (encodeUpdate f) context ≤ Fintype.card Q * width + codingCost + decoderCost := by
  have hd := hdecode (orbitTable P f)
  rw [orbit_table_recovery P f hf] at hd
  have hc := hcode (orbitTable P f)
  omega

end KTAIT.SymmetryCompression
