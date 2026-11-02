/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Kaiti/Codex)
-/
import KTAIT.CertifiedPrograms.Counting
import KTAIT.CertifiedPrograms.Certification
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Unrestricted total-function counts from bounded-width trees (WP0215)

The threshold tree is defined from finite prefixes produced by a fixed staged
source evaluator. Output framing, finite-stage parsing, search stability, and
decoder correctness are proved. Incompatible words have disjoint contributor sets, giving a
bound on every finite antichain, not merely on each level. Every framed prefix of
a total function enters the tree when its implementation family meets the threshold.

The standard effective bounded-width tree path-labeling theorem and uniform
compilation of its stream decoder remain explicit named Prop premises. Neither
the whole-function multiplicity bound nor a complexity bound is assumed. Source
stream computability and correctness are fields of the supplied evaluator model;
this module does not construct a universal evaluator or a Partrec witness for
the composed decoder. Its concrete finite-stage operations and their correctness
are checked separately from the compiler premise.
-/

namespace KTAIT.WholeFunctionTree
open KTAIT.CertifiedPrograms

/-- Nonempty self-delimiting encoding used in the manuscript. -/
def frame (y : CodeBits) : CodeBits := List.replicate y.length true ++ false :: y

/-- The stream after the first n completed outputs, in fixed input order. -/
def framedPrefix (f : Nat → CodeBits) : Nat → CodeBits
  | 0 => []
  | n + 1 => framedPrefix f n ++ frame (f n)

private theorem framed_prefix_step (f : Nat → CodeBits) (n : Nat) :
    framedPrefix f n <+: framedPrefix f (n + 1) := List.prefix_append _ _

/-- Framed output prefixes form an increasing chain. -/
theorem framed_prefix_mono (f : Nat → CodeBits) {n m : Nat} (hnm : n ≤ m) :
    framedPrefix f n <+: framedPrefix f m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction k with
  | zero => simp
  | succ k ih => exact ih.trans (framed_prefix_step f (n + k))

/-- Nonempty frames ensure that a total output sequence gives an infinite bit stream. -/
theorem framed_prefix_length (f : Nat → CodeBits) (n : Nat) :
    n ≤ (framedPrefix f n).length := by
  induction n with
  | zero => simp
  | succ n ih => simp only [framedPrefix, frame, List.length_append,
      List.length_replicate, List.length_cons]; omega

abbrev Evaluator := ProgramSemantics Nat CodeBits

def Computes (V : Evaluator) (p : CodeBits) (f : Nat → CodeBits) : Prop :=
  ∀ n, V p n = Part.some (f n)

/-- A fixed effective dovetailing convention, with sound prefixes and progress on total sources. -/
structure SourceStreams (V : Evaluator) where
  stage : CodeBits → Nat → CodeBits
  computable : Computable (fun pn : CodeBits × Nat => stage pn.1 pn.2)
  monotone : ∀ p n m, n ≤ m → stage p n <+: stage p m
  sound : ∀ p f, Computes V p f → ∀ s, ∃ n, stage p s <+: framedPrefix f n
  complete : ∀ p f, Computes V p f → ∀ n, ∃ s, framedPrefix f n <+: stage p s

/-- Contributors already visible at one finite stage. -/
def stageContributors {V : Evaluator} (S : SourceStreams V) (L n : Nat)
    (w : CodeBits) : Finset CodeBits :=
  (wordsThrough L).filter fun p => w <+: S.stage p n

/-- The c.e. threshold tree; no totality or equality test occurs in admission. -/
def Admitted {V : Evaluator} (S : SourceStreams V) (L t : Nat) (w : CodeBits) : Prop :=
  ∃ n, 2 ^ t ≤ (stageContributors S L n w).card

/-- All sources that eventually contribute a prefix, used only in the finite counting proof. -/
noncomputable def contributors {V : Evaluator} (S : SourceStreams V) (L : Nat)
    (w : CodeBits) : Finset CodeBits := by
  classical
  exact (wordsThrough L).filter fun p => ∃ n, w <+: S.stage p n

private theorem stage_subset_contributors {V : Evaluator} (S : SourceStreams V)
    (L n : Nat) (w : CodeBits) : stageContributors S L n w ⊆ contributors S L w := by
  classical
  intro p hp
  obtain ⟨hb, hw⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hb, n, hw⟩

/-- Admission is downward closed under binary prefixes. -/
theorem admitted_prefix_closed {V : Evaluator} (S : SourceStreams V) (L t : Nat)
    (u w : CodeBits) (huw : u <+: w) (hw : Admitted S L t w) : Admitted S L t u := by
  obtain ⟨n, hn⟩ := hw
  refine ⟨n, hn.trans (Finset.card_le_card ?_)⟩
  intro p hp
  obtain ⟨hb, hw⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hb, huw.trans hw⟩

/-- Mutually incomparable words in the prefix order. -/
def PrefixAntichain (A : Finset CodeBits) : Prop :=
  ∀ u ∈ A, ∀ w ∈ A, u ≠ w → ¬ u <+: w

/-- One source cannot contribute to incompatible prefixes, even at different stages. -/
theorem incompatible_contributors_disjoint {V : Evaluator} (S : SourceStreams V)
    (L : Nat) (u w : CodeBits) (huw : ¬ u <+: w) (hwu : ¬ w <+: u) :
    Disjoint (contributors S L u) (contributors S L w) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hpu hpw
  obtain ⟨_, n, hn⟩ := Finset.mem_filter.mp hpu
  obtain ⟨_, m, hm⟩ := Finset.mem_filter.mp hpw
  have hn' := hn.trans (S.monotone p n (max n m) (le_max_left _ _))
  have hm' := hm.trans (S.monotone p m (max n m) (le_max_right _ _))
  exact (List.prefix_or_prefix_of_prefix hn' hm').elim huw hwu

/-- Every finite antichain pays for its nodes with disjoint batches of bounded sources. -/
theorem antichain_source_budget {V : Evaluator} (S : SourceStreams V)
    (L t : Nat) (A : Finset CodeBits) (hA : PrefixAntichain A)
    (hadmitted : ∀ w ∈ A, Admitted S L t w) :
    A.card * 2 ^ t < 2 ^ (L + 1) := by
  classical
  have hd : (A : Set CodeBits).Pairwise (fun u w =>
      Disjoint (contributors S L u) (contributors S L w)) := by
    intro u hu w hw hne
    exact incompatible_contributors_disjoint S L u w
      (hA u hu w hw hne) (hA w hw u hu hne.symm)
  have hcard : A.card * 2 ^ t ≤ ∑ w ∈ A, (contributors S L w).card := by
    calc
      A.card * 2 ^ t = ∑ _w ∈ A, 2 ^ t := by simp
      _ ≤ ∑ w ∈ A, (contributors S L w).card := by
        apply Finset.sum_le_sum
        intro w hw
        obtain ⟨n, hn⟩ := hadmitted w hw
        exact hn.trans (Finset.card_le_card (stage_subset_contributors S L n w))
  have hb : A.biUnion (contributors S L) ⊆ wordsThrough L := by
    intro p hp
    obtain ⟨w, _, hpw⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp hpw).1
  have hu := Finset.card_le_card hb
  rw [Finset.card_biUnion hd] at hu
  have hc := bounded_binary_card L
  omega

/-- The strict global antichain-width bound used by the tree-labeling theorem. -/
theorem admitted_antichain_width {V : Evaluator} (S : SourceStreams V)
    (L t : Nat) (ht : t ≤ L) (A : Finset CodeBits) (hA : PrefixAntichain A)
    (hadmitted : ∀ w ∈ A, Admitted S L t w) :
    A.card < 2 ^ globalWidth L t :=
  event_count_fits_width L t A.card ht (antichain_source_budget S L t A hA hadmitted)

private theorem common_stage {V : Evaluator} (S : SourceStreams V)
    (A : Finset CodeBits) (w : CodeBits) (hA : ∀ p ∈ A, ∃ n, w <+: S.stage p n) :
    ∃ n, ∀ p ∈ A, w <+: S.stage p n := by
  induction A using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert p A hp ih =>
    obtain ⟨n, hn⟩ := hA p (by simp)
    obtain ⟨m, hm⟩ := ih (fun q hq => hA q (Finset.mem_insert_of_mem hq))
    refine ⟨max n m, ?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hn.trans (S.monotone q n (max n m) (le_max_left _ _))
    · exact (hm q hq).trans (S.monotone q m (max n m) (le_max_right _ _))

/-- Every prefix of the chosen total stream is admitted once its source family is large enough. -/
theorem target_prefix_admitted {V : Evaluator} (S : SourceStreams V)
    (L t : Nat) (A : Finset CodeBits) (f : Nat → CodeBits)
    (hA : ∀ p ∈ A, p.length ≤ L ∧ Computes V p f) (hsize : 2 ^ t ≤ A.card)
    (n : Nat) : Admitted S L t (framedPrefix f n) := by
  obtain ⟨s, hs⟩ := common_stage S A (framedPrefix f n)
    (fun p hp => S.complete p f (hA p hp).2 n)
  refine ⟨s, hsize.trans (Finset.card_le_card ?_)⟩
  intro p hp
  exact Finset.mem_filter.mpr
    ⟨words_through_complete L p (hA p hp).1, hs p hp⟩

/-- Read the unary length prefix of one output frame. -/
def readFrameLength : CodeBits → Option (Nat × CodeBits)
  | [] => none
  | false :: bs => some (0, bs)
  | true :: bs => do
    let (n, rest) ← readFrameLength bs
    pure (n + 1, rest)

private theorem read_frame_length_append (n : Nat) (bs : CodeBits) :
    readFrameLength (List.replicate n true ++ false :: bs) = some (n, bs) := by
  induction n with
  | zero => simp [readFrameLength]
  | succ n ih => simp [List.replicate_succ, readFrameLength, ih]

private theorem read_frame_length_sound (bs : CodeBits) (n : Nat) (rest : CodeBits)
    (h : readFrameLength bs = some (n, rest)) :
    bs = List.replicate n true ++ false :: rest := by
  induction bs generalizing n rest with
  | nil => simp [readFrameLength] at h
  | cons b bs ih =>
    cases b with
    | false =>
      simp only [readFrameLength, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
    | true =>
      cases hr : readFrameLength bs with
      | none => simp [readFrameLength, hr] at h
      | some pair =>
        rcases pair with ⟨m, tail⟩
        simp only [readFrameLength, hr, bind, Option.bind, pure,
          Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [ih m tail hr]
        simp [List.replicate_succ]

/-- Parse one complete output frame; an incomplete frame yields none. -/
def parseFrame (bs : CodeBits) : Option (CodeBits × CodeBits) := do
  let (n, rest) ← readFrameLength bs
  if n ≤ rest.length then pure (rest.take n, rest.drop n) else none

/-- Framing followed by parsing recovers the exact output and leaves the suffix. -/
theorem parse_frame_append (y tail : CodeBits) :
    parseFrame (frame y ++ tail) = some (y, tail) := by
  unfold frame
  rw [List.append_assoc, List.cons_append]
  simp only [parseFrame, read_frame_length_append, bind, Option.bind]
  simp

/-- A successful parse identifies the literal initial frame, not merely its length. -/
theorem parse_frame_sound (bs y tail : CodeBits)
    (h : parseFrame bs = some (y, tail)) : bs = frame y ++ tail := by
  unfold parseFrame at h
  cases hr : readFrameLength bs with
  | none => simp [hr] at h
  | some pair =>
    rcases pair with ⟨n, rest⟩
    simp only [hr, bind, Option.bind] at h
    split_ifs at h with hn
    · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [read_frame_length_sound bs n rest hr]
      unfold frame
      rw [List.length_take, Nat.min_eq_left hn]
      simp only [List.append_assoc, List.cons_append, List.take_append_drop]

private theorem parse_frame_append_stable (bs y rest tail : CodeBits)
    (h : parseFrame bs = some (y, rest)) :
    parseFrame (bs ++ tail) = some (y, rest ++ tail) := by
  rw [parse_frame_sound bs y rest h, List.append_assoc]
  exact parse_frame_append y (rest ++ tail)

/-- Decode the n-th completed output from a finite bit prefix. -/
def parseOutput : Nat → CodeBits → Option CodeBits
  | 0, bs => do
    let (y, _rest) ← parseFrame bs
    pure y
  | n + 1, bs => do
    let (_y, rest) ← parseFrame bs
    parseOutput n rest

/-- Once an output is decoded, appending bits cannot change it. -/
theorem parse_output_append_stable (n : Nat) (bs tail y : CodeBits)
    (h : parseOutput n bs = some y) : parseOutput n (bs ++ tail) = some y := by
  induction n generalizing bs with
  | zero =>
    cases hp : parseFrame bs with
    | none => simp [parseOutput, hp] at h
    | some pair =>
      rcases pair with ⟨z, rest⟩
      have he := parse_frame_append_stable bs z rest tail hp
      simpa [parseOutput, hp, he] using h
  | succ n ih =>
    cases hp : parseFrame bs with
    | none => simp [parseOutput, hp] at h
    | some pair =>
      rcases pair with ⟨z, rest⟩
      have he := parse_frame_append_stable bs z rest tail hp
      simp only [parseOutput, hp, bind, Option.bind] at h
      simpa [parseOutput, he] using ih rest h

private theorem framed_prefix_shift (f : Nat → CodeBits) (n : Nat) :
    framedPrefix f (n + 1) = frame (f 0) ++ framedPrefix (fun k => f (k + 1)) n := by
  induction n with
  | zero => simp [framedPrefix]
  | succ n ih =>
    change framedPrefix f (n + 1) ++ frame (f (n + 1)) =
      frame (f 0) ++ (framedPrefix (fun k => f (k + 1)) n ++ frame (f (n + 1)))
    rw [ih, List.append_assoc]

/-- A complete framed prefix yields the requested output, independently of trailing bits. -/
theorem parse_output_framed_prefix (f : Nat → CodeBits) (n : Nat) (tail : CodeBits) :
    parseOutput n (framedPrefix f (n + 1) ++ tail) = some (f n) := by
  induction n generalizing f with
  | zero => simp [framedPrefix, parseOutput, parse_frame_append]
  | succ n ih =>
    rw [framed_prefix_shift]
    rw [List.append_assoc]
    simp only [parseOutput, parse_frame_append, bind, Option.bind]
    exact ih (fun k => f (k + 1))

private theorem parse_output_prefix_stable (n : Nat) (bs more y : CodeBits)
    (hp : bs <+: more) (hy : parseOutput n bs = some y) : parseOutput n more = some y := by
  obtain ⟨tail, rfl⟩ := hp
  exact parse_output_append_stable n bs tail y hy

/-- Parsing any prefix of the target stream cannot return a different output. -/
theorem parse_output_stream_sound (f : Nat → CodeBits) (n m : Nat) (bs y : CodeBits)
    (hp : bs <+: framedPrefix f m) (hy : parseOutput n bs = some y) : y = f n := by
  have hm := framed_prefix_mono f (le_max_left m (n + 1))
  have hn := framed_prefix_mono f (le_max_right m (n + 1))
  have hy' := parse_output_prefix_stable n bs _ y (hp.trans hm) hy
  have hf : parseOutput n (framedPrefix f (n + 1)) = some (f n) := by
    simpa using parse_output_framed_prefix f n []
  have hf' := parse_output_prefix_stable n _ _ (f n) hn hf
  exact Option.some.inj (hy'.symm.trans hf')

/-- A uniform staged output process for each possible tree label. -/
structure LabelStreams where
  stage : Nat → Nat → Nat → Nat → CodeBits
  computable : Computable (fun p : Nat × Nat × Nat × Nat =>
    stage p.1 p.2.1 p.2.2.1 p.2.2.2)
  monotone : ∀ L t i n m, n ≤ m → stage L t i n <+: stage L t i m

/-- One label produces precisely the target's infinite framed stream. -/
def LabelProduces (D : LabelStreams) (L t i : Nat) (f : Nat → CodeBits) : Prop :=
  (∀ n, ∃ s, framedPrefix f n <+: D.stage L t i s) ∧
  (∀ s, ∃ n, D.stage L t i s <+: framedPrefix f n)

/-- Standard effective bounded-antichain-width tree labeling, supplied explicitly.
This is the decision-complexity tree principle cited in WP0215. It concerns all
finite antichains and supplies one persistent label for every infinite path. -/
def BoundedTreePathLabeling {V : Evaluator} (S : SourceStreams V)
    (D : LabelStreams) : Prop :=
  ∀ L t, t ≤ L →
    (∀ u w, u <+: w → Admitted S L t w → Admitted S L t u) →
    (∀ A, PrefixAntichain A → (∀ w ∈ A, Admitted S L t w) →
      A.card < 2 ^ globalWidth L t) →
    ∀ f : Nat → CodeBits, (∀ n, Admitted S L t (framedPrefix f n)) →
      ∃ i, i < 2 ^ globalWidth L t ∧ LabelProduces D L t i f

/-- One stage of the implemented decoder: parse the self-delimiting descriptor,
then read the requested completed frame from that label's current bit prefix. -/
def treeDecodeAt (D : LabelStreams) (code : CodeBits) (input stage : Nat) : Option CodeBits :=
  match parseDescriptor globalWidth code with
  | none => none
  | some ((L, t, i), tail) =>
    if tail = [] then parseOutput input (D.stage L t i stage) else none

private theorem tree_decode_at_code (D : LabelStreams) (L t i input stage : Nat)
    (ht : t ≤ L) (hi : i < 2 ^ globalWidth L t) :
    treeDecodeAt D (descriptor globalWidth L t i) input stage =
      parseOutput input (D.stage L t i stage) := by
  have hp := descriptor_parse_append globalWidth L t i ht hi []
  simp only [List.append_nil] at hp
  simp [treeDecodeAt, hp]

/-- The finite-stage search cannot revise an output after it has appeared. -/
theorem tree_decode_at_stable (D : LabelStreams) (code y : CodeBits)
    (input n m : Nat) (hnm : n ≤ m) (hn : treeDecodeAt D code input n = some y) :
    treeDecodeAt D code input m = some y := by
  unfold treeDecodeAt at hn ⊢
  cases hp : parseDescriptor globalWidth code with
  | none => simp [hp] at hn
  | some parsed =>
    rcases parsed with ⟨⟨L, t, i⟩, tail⟩
    simp only [hp] at hn ⊢
    by_cases he : tail = []
    · simp only [he, ↓reduceIte] at hn ⊢
      exact parse_output_prefix_stable input _ _ y (D.monotone L t i n m hnm) hn
    · simp [he] at hn

private theorem tree_decode_at_unique (D : LabelStreams) (code y z : CodeBits)
    (input n m : Nat) (hn : treeDecodeAt D code input n = some y)
    (hm : treeDecodeAt D code input m = some z) : y = z := by
  have hn' := tree_decode_at_stable D code y input n (max n m) (le_max_left _ _) hn
  have hm' := tree_decode_at_stable D code z input m (max n m) (le_max_right _ _) hm
  exact Option.some.inj (hn'.symm.trans hm')

/-- Partial semantics of searching finite stages for a completed output. The
executable work is treeDecodeAt; this Part value records its termination and result. -/
noncomputable def treeDecode (D : LabelStreams) (code : CodeBits) (input : Nat) :
    Part CodeBits where
  Dom := ∃ y, ∃ stage, treeDecodeAt D code input stage = some y
  get := fun h => Classical.choose h

/-- The partial decoder's values are exactly the results of its finite-stage search. -/
theorem tree_decode_mem_iff (D : LabelStreams) (code y : CodeBits) (input : Nat) :
    y ∈ treeDecode D code input ↔ ∃ stage, treeDecodeAt D code input stage = some y := by
  change (∃ h : (∃ z, ∃ stage, treeDecodeAt D code input stage = some z),
    Classical.choose h = y) ↔ _
  constructor
  · rintro ⟨h, hy⟩
    obtain ⟨stage, hs⟩ := Classical.choose_spec h
    exact ⟨stage, hy ▸ hs⟩
  · rintro ⟨stage, hs⟩
    let h : ∃ z, ∃ n, treeDecodeAt D code input n = some z := ⟨y, stage, hs⟩
    refine ⟨h, ?_⟩
    obtain ⟨n, hn⟩ := Classical.choose_spec h
    exact tree_decode_at_unique D code _ y input n stage hn hs

/-- A label emitting the target stream eventually yields every requested output. -/
theorem label_produces_decode_complete (D : LabelStreams) (L t i : Nat)
    (f : Nat → CodeBits) (ht : t ≤ L) (hi : i < 2 ^ globalWidth L t)
    (hprod : LabelProduces D L t i f) (n : Nat) :
    ∃ stage, treeDecodeAt D (descriptor globalWidth L t i) n stage = some (f n) := by
  obtain ⟨stage, hs⟩ := hprod.1 (n + 1)
  refine ⟨stage, ?_⟩
  rw [tree_decode_at_code D L t i n stage ht hi]
  apply parse_output_prefix_stable n (framedPrefix f (n + 1)) _ (f n) hs
  simpa using parse_output_framed_prefix f n []

/-- Successful decoding from a label for f cannot return a different output. -/
theorem label_produces_decode_sound (D : LabelStreams) (L t i : Nat)
    (f : Nat → CodeBits) (ht : t ≤ L) (hi : i < 2 ^ globalWidth L t)
    (hprod : LabelProduces D L t i f) (n stage : Nat) (y : CodeBits)
    (hy : treeDecodeAt D (descriptor globalWidth L t i) n stage = some y) : y = f n := by
  rw [tree_decode_at_code D L t i n stage ht hi] at hy
  obtain ⟨m, hm⟩ := hprod.2 stage
  exact parse_output_stream_sound f n m _ y hm hy

/-- Correctness of the implemented partial decoder is derived before compilation. -/
theorem label_produces_decoder_correct (D : LabelStreams) (L t i : Nat)
    (f : Nat → CodeBits) (ht : t ≤ L) (hi : i < 2 ^ globalWidth L t)
    (hprod : LabelProduces D L t i f) :
    ∀ n, treeDecode D (descriptor globalWidth L t i) n = Part.some (f n) := by
  intro n
  apply Part.eq_some_iff.mpr
  exact (tree_decode_mem_iff D _ (f n) n).mpr
    (label_produces_decode_complete D L t i f ht hi hprod n)

/-- Standard uniform simulation of the implemented partial decoder, with fixed
length overhead. It assumes neither target correctness nor a complexity bound. -/
def TreeStreamCompiler (V : Evaluator) (D : LabelStreams) (overhead : Nat) : Prop :=
  ∃ compile : CodeBits → CodeBits, ∀ code,
    V (compile code) = treeDecode D code ∧ (compile code).length ≤ code.length + overhead

/-- The full semantic implementation family inside the binary length cutoff. -/
noncomputable def functionFamily (V : Evaluator) (p : CodeBits) (L : Nat) : Finset CodeBits := by
  classical
  exact (wordsThrough L).filter fun q => V q = V p

private theorem mem_functionFamily (V : Evaluator) (p q : CodeBits) (L : Nat) :
    q ∈ functionFamily V p L ↔ q.length ≤ L ∧ V q = V p := by
  classical
  simp only [functionFamily, Finset.mem_filter]
  exact ⟨fun h => ⟨words_through_length L q h.1, h.2⟩,
    fun h => ⟨words_through_complete L q h.1, h.2⟩⟩

private theorem family_bound (V : Evaluator) (p : CodeBits) (L : Nat) :
    (functionFamily V p L).card < 2 ^ (L + 1) := by
  classical
  have hs : functionFamily V p L ⊆ wordsThrough L := Finset.filter_subset _ _
  have hcard := Finset.card_le_card hs
  have hc := bounded_binary_card L
  omega

private theorem family_positive (V : Evaluator) (p : CodeBits) (L : Nat)
    (hL : wholeFunctionComplexity V p ≤ L) : 0 < (functionFamily V p L).card := by
  obtain ⟨q, hq, hv⟩ := whole_function_minimum_exists V p
  exact Finset.card_pos.mpr ⟨q, (mem_functionFamily V p q L).mpr ⟨by omega, hv⟩⟩

/-- The checked tree construction supplies a short descriptor of every total
function with sufficiently many bounded implementations, using only the named
standard tree-labeling and compiler premises. -/
theorem total_tree_description_bound (V : Evaluator) (S : SourceStreams V)
    (D : LabelStreams) (c : Nat) (hlabel : BoundedTreePathLabeling S D)
    (hcompile : TreeStreamCompiler V D c) (p : CodeBits) (f : Nat → CodeBits)
    (hp : Computes V p f) (L : Nat) (hL : wholeFunctionComplexity V p ≤ L) :
    wholeFunctionComplexity V p ≤
      globalWidth L (Nat.log 2 (functionFamily V p L).card) + gammaLength L +
      gammaLength (Nat.log 2 (functionFamily V p L).card) + c := by
  let N := (functionFamily V p L).card
  let t := Nat.log 2 N
  obtain ⟨hthreshold, _, ht⟩ := class_log_range L N
    (family_positive V p L hL) (family_bound V p L)
  have hpath : ∀ n, Admitted S L t (framedPrefix f n) := by
    intro n
    apply target_prefix_admitted S L t (functionFamily V p L) f _ hthreshold n
    intro q hq
    obtain ⟨hqL, hsem⟩ := (mem_functionFamily V p q L).mp hq
    exact ⟨hqL, by intro x; rw [hsem]; exact hp x⟩
  obtain ⟨i, hi, hprod⟩ := hlabel L t ht
    (admitted_prefix_closed S L t)
    (fun A hA ha => admitted_antichain_width S L t ht A hA ha) f hpath
  obtain ⟨compile, hc⟩ := hcompile
  obtain ⟨hsem, hlen⟩ := hc (descriptor globalWidth L t i)
  have hdecoded := label_produces_decoder_correct D L t i f ht hi hprod
  have heq : V (compile (descriptor globalWidth L t i)) = V p := by
    rw [hsem]
    funext x
    exact (hdecoded x).trans (hp x).symm
  have hmin := whole_function_minimum_le V p (compile (descriptor globalWidth L t i)) heq
  have hdesc := global_descriptor_length L t i
  dsimp [globalWidth]
  change wholeFunctionComplexity V p ≤ L + 1 - t + gammaLength L + gammaLength t + c
  omega

/-- Exact integer form of the paper's logarithmic multiplicity bound. The
header cost is 2 gamma(k + delta), hence logarithmic in k + delta + 2. -/
theorem whole_function_log_count (V : Evaluator) (S : SourceStreams V)
    (D : LabelStreams) (c : Nat) (hlabel : BoundedTreePathLabeling S D)
    (hcompile : TreeStreamCompiler V D c) (p : CodeBits) (f : Nat → CodeBits)
    (hp : Computes V p f) (delta : Nat) :
    Nat.log 2 (functionFamily V p (wholeFunctionComplexity V p + delta)).card + 1 ≤
      delta + 2 * gammaLength (wholeFunctionComplexity V p + delta) + c + 2 := by
  let L := wholeFunctionComplexity V p + delta
  let N := (functionFamily V p L).card
  have hL : wholeFunctionComplexity V p ≤ L := Nat.le_add_right _ _
  obtain ⟨_, _, ht⟩ := class_log_range L N
    (family_positive V p L hL) (family_bound V p L)
  have hdesc := total_tree_description_bound V S D c hlabel hcompile p f hp L hL
  have hgamma := gamma_length_mono ht
  change wholeFunctionComplexity V p ≤
    L + 1 - Nat.log 2 N + gammaLength L + gammaLength (Nat.log 2 N) + c at hdesc
  change Nat.log 2 N + 1 ≤ delta + 2 * gammaLength L + c + 2
  have hLeq : L = wholeFunctionComplexity V p + delta := rfl
  omega

/-- A cardinality bound without floor-log notation, equivalent to the claimed
log2 multiplicity estimate up to its explicit uniform coding constant. -/
theorem whole_function_multiplicity_bound (V : Evaluator) (S : SourceStreams V)
    (D : LabelStreams) (c : Nat) (hlabel : BoundedTreePathLabeling S D)
    (hcompile : TreeStreamCompiler V D c) (p : CodeBits) (f : Nat → CodeBits)
    (hp : Computes V p f) (delta : Nat) :
    (functionFamily V p (wholeFunctionComplexity V p + delta)).card <
      2 ^ (delta + 4 * Nat.log 2 (wholeFunctionComplexity V p + delta + 1) + c + 4) := by
  have hlog := whole_function_log_count V S D c hlabel hcompile p f hp delta
  have hN := Nat.lt_pow_succ_log_self (by decide : 1 < 2)
    (functionFamily V p (wholeFunctionComplexity V p + delta)).card
  apply hN.trans_le
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  unfold gammaLength at hlog
  omega

/-- Real base-two logarithm form of Eq. wholeprogramcount, with an explicit
constant in place of the paper's logarithmic-order notation. -/
theorem whole_function_real_log_bound (V : Evaluator) (S : SourceStreams V)
    (D : LabelStreams) (c : Nat) (hlabel : BoundedTreePathLabeling S D)
    (hcompile : TreeStreamCompiler V D c) (p : CodeBits) (f : Nat → CodeBits)
    (hp : Computes V p f) (delta : Nat) :
    Real.logb 2 ((functionFamily V p (wholeFunctionComplexity V p + delta)).card : ℝ) <
      (delta + 4 * Nat.log 2 (wholeFunctionComplexity V p + delta + 1) + c + 4 : Nat) := by
  have hN := whole_function_multiplicity_bound V S D c hlabel hcompile p f hp delta
  have hpN := family_positive V p (wholeFunctionComplexity V p + delta) (Nat.le_add_right _ _)
  have hreal : ((functionFamily V p (wholeFunctionComplexity V p + delta)).card : ℝ) <
      (2 : ℝ) ^ (delta + 4 * Nat.log 2 (wholeFunctionComplexity V p + delta + 1) + c + 4) := by
    exact_mod_cast hN
  have hpos : (0 : ℝ) < (functionFamily V p (wholeFunctionComplexity V p + delta)).card := by
    exact_mod_cast hpN
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) hpos hreal
  simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
    using hlog

end KTAIT.WholeFunctionTree
