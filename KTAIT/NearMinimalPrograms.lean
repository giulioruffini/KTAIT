import KTAIT.CertifiedPrograms.Counting
import KTAIT.IS.CommonSemantics

/-!
# Near-minimal finite-output descriptions (WP0215)

The finite multiplicity bound uses the conditional coding theorem as a named
program-mass premise. Reconstruction is through a staged evaluator and an
explicit self-delimiting descriptor. Standard universal-machine simulation costs
are named premises, not global axioms. The conditional probability/coding theorem
and existence of an optimal prefix machine are not re-proved here. The staged
construction is executable relative to the supplied evaluator. Its partial
recursiveness and a concrete optimal-prefix-machine compiler are not instantiated;
`UniversalDecoderBound` is the explicit boundary for that standard simulation step.
-/

namespace KTAIT.NearMinimalPrograms
open KTAIT.CertifiedPrograms

abbrev Bits := List Bool

/-- A successful evaluation relation with a minimum conditional description length. -/
structure Machine (Output Context : Type*) where
  eval : Bits → Context → Output → Prop
  complexity : Output → Context → Nat
  eval_unique : ∀ p C F G, eval p C F → eval p C G → F = G
  minimum_le : ∀ p C F, eval p C F → complexity F C ≤ p.length

variable {Output Context : Type*}

/-- Program weights used by the conditional coding theorem. -/
noncomputable def weight (p : Bits) : ℝ := (2 : ℝ) ^ (-(p.length : ℤ))

/-- Standard conditional coding-theorem upper bound on every finite part of
an output's program mass; the constant is uniform in output and condition. -/
def CodingMassBound (M : Machine Output Context) (c : Nat) : Prop :=
  ∀ (F : Output) (C : Context) (A : Finset Bits),
    (∀ p ∈ A, M.eval p C F) →
    ∑ p ∈ A, weight p ≤ (2 : ℝ) ^ (-(M.complexity F C : ℤ) + c)

/-- The full bounded-length family, defined without deciding halting. -/
noncomputable def nearFamily (M : Machine Output Context) (F : Output) (C : Context)
    (δ : Nat) : Finset Bits := by
  classical
  exact (wordsThrough (M.complexity F C + δ)).filter (fun p => M.eval p C F)

theorem mem_nearFamily (M : Machine Output Context) (F : Output) (C : Context)
    (δ : Nat) (p : Bits) :
    p ∈ nearFamily M F C δ ↔ M.eval p C F ∧ p.length ≤ M.complexity F C + δ := by
  classical
  simp only [nearFamily, Finset.mem_filter]
  constructor
  · rintro ⟨h, he⟩
    exact ⟨he, words_through_length _ _ h⟩
  · rintro ⟨he, hl⟩
    exact ⟨words_through_complete _ _ hl, he⟩

/-- The multiplicity bound counts actual binary source strings. -/
theorem near_family_card (M : Machine Output Context) (c : Nat)
    (hMass : CodingMassBound M c) (F : Output) (C : Context) (δ : Nat) :
    (nearFamily M F C δ).card ≤ 2 ^ (δ + c) := by
  classical
  let A := nearFamily M F C δ
  have he : ∀ p ∈ A, M.eval p C F := by
    intro p hp
    exact ((mem_nearFamily M F C δ p).mp hp).1
  have hlow : (A.card : ℝ) * (2 : ℝ) ^ (-(M.complexity F C : ℤ) - δ) ≤
      ∑ p ∈ A, weight p := by
    calc
      (A.card : ℝ) * (2 : ℝ) ^ (-(M.complexity F C : ℤ) - δ) =
          ∑ _p ∈ A, (2 : ℝ) ^ (-(M.complexity F C : ℤ) - δ) := by simp
      _ ≤ ∑ p ∈ A, weight p := by
        apply Finset.sum_le_sum
        intro p hp
        unfold weight
        apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        have hl := ((mem_nearFamily M F C δ p).mp hp).2
        omega
  have hmass := hMass F C A he
  have hp : 0 < (2 : ℝ) ^ (-(M.complexity F C : ℤ) - δ) := by positivity
  have hsplit : (2 : ℝ) ^ (-(M.complexity F C : ℤ) + c) =
      (2 : ℝ) ^ (δ + c) * (2 : ℝ) ^ (-(M.complexity F C : ℤ) - δ) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    omega
  rw [hsplit] at hmass
  have hcard : (A.card : ℝ) ≤ (2 : ℝ) ^ (δ + c) :=
    (mul_le_mul_iff_left₀ hp).mp (hlow.trans hmass)
  exact_mod_cast hcard


/-- Canonical executable list of all binary strings of a fixed length. -/
def binaryWords : Nat → List Bits
  | 0 => [[]]
  | n + 1 => (binaryWords n).map (false :: ·) ++ (binaryWords n).map (true :: ·)

private theorem binaryWords_length (n : Nat) (p : Bits) (hp : p ∈ binaryWords n) :
    p.length = n := by
  induction n generalizing p with
  | zero => simpa [binaryWords] using hp
  | succ n ih =>
    simp only [binaryWords, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ <;> simp [ih q hq]

private theorem binaryWords_complete (p : Bits) : p ∈ binaryWords p.length := by
  induction p with
  | nil => simp [binaryWords]
  | cons b p ih => cases b <;> simp [binaryWords, ih]

private theorem binaryWords_nodup (n : Nat) : (binaryWords n).Nodup := by
  induction n with
  | zero => simp [binaryWords]
  | succ n ih =>
    rw [binaryWords, List.nodup_append]
    refine ⟨ih.map (fun _ _ h => List.cons_injective h),
      ih.map (fun _ _ h => List.cons_injective h), ?_⟩
    intro a ha b hb hab
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hb
    simp at hab

/-- Canonical executable bounded program universe. -/
def boundedWords : Nat → List Bits
  | 0 => binaryWords 0
  | L + 1 => boundedWords L ++ binaryWords (L + 1)

private theorem boundedWords_length (L : Nat) (p : Bits) (hp : p ∈ boundedWords L) :
    p.length ≤ L := by
  induction L with
  | zero => exact le_of_eq (binaryWords_length 0 p hp)
  | succ L ih =>
    rcases List.mem_append.mp hp with hp | hp
    · exact (ih hp).trans (Nat.le_succ L)
    · exact le_of_eq (binaryWords_length _ _ hp)

private theorem boundedWords_complete (L : Nat) (p : Bits) (hp : p.length ≤ L) :
    p ∈ boundedWords L := by
  induction L with
  | zero =>
    have he : p.length = 0 := by omega
    simpa [boundedWords, ← he] using binaryWords_complete p
  | succ L ih =>
    by_cases h : p.length ≤ L
    · exact List.mem_append_left _ (ih h)
    · have he : p.length = L + 1 := by omega
      exact List.mem_append_right _ (he ▸ binaryWords_complete p)

private theorem boundedWords_nodup (L : Nat) : (boundedWords L).Nodup := by
  induction L with
  | zero => exact binaryWords_nodup 0
  | succ L ih =>
    rw [boundedWords, List.nodup_append]
    refine ⟨ih, binaryWords_nodup _, ?_⟩
    intro a ha b hb hab
    have hla := boundedWords_length L a ha
    have hlb := binaryWords_length (L+1) b hb
    subst b
    omega

/-- A staged interpreter. Soundness and completeness concern actual halting
outputs, rather than a decidable total evaluation oracle. -/
structure StagedMachine (Output Context : Type*) extends Machine Output Context where
  run : Nat → Bits → Context → Option Output
  sound : ∀ t p C F, run t p C = some F → eval p C F
  complete : ∀ p C F, eval p C F → ∃ t, run t p C = some F
  stable : ∀ t n p C F, run t p C = some F → run (t+n) p C = some F

variable [DecidableEq Output]

/-- Append newly witnessed programs once, in a fixed order. -/
def discoveries (M : StagedMachine Output Context) (L : Nat) (F : Output) (C : Context) :
    Nat → List Bits
  | 0 => []
  | t + 1 =>
    let previous := discoveries M L F C t
    previous ++ (boundedWords L).filter (fun p =>
      decide (M.run t p C = some F ∧ p ∉ previous))

private theorem discoveries_nodup (M : StagedMachine Output Context)
    (L : Nat) (F : Output) (C : Context) (t : Nat) :
    (discoveries M L F C t).Nodup := by
  induction t with
  | zero => simp [discoveries]
  | succ t ih =>
    rw [discoveries, List.nodup_append]
    refine ⟨ih, (boundedWords_nodup L).filter _, ?_⟩
    intro a ha b hb hab
    have hh := List.mem_filter.mp hb
    simp only [decide_eq_true_eq] at hh
    exact hh.2.2 (hab ▸ ha)

private theorem discoveries_sound (M : StagedMachine Output Context)
    (L : Nat) (F : Output) (C : Context) (t : Nat) (p : Bits)
    (hp : p ∈ discoveries M L F C t) : M.eval p C F ∧ p.length ≤ L := by
  induction t with
  | zero => simp [discoveries] at hp
  | succ t ih =>
    rcases List.mem_append.mp hp with hp | hp
    · exact ih hp
    · have hh := List.mem_filter.mp hp
      simp only [decide_eq_true_eq] at hh
      exact ⟨M.sound t p C F hh.2.1, boundedWords_length L p hh.1⟩

private theorem discoveries_prefix (M : StagedMachine Output Context)
    (L : Nat) (F : Output) (C : Context) {t s : Nat} (ht : t ≤ s) :
    discoveries M L F C t <+: discoveries M L F C s := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
  clear ht
  induction n with
  | zero => simp
  | succ n ih =>
    exact ih.trans (List.prefix_append _ _)

private theorem discoveries_event (M : StagedMachine Output Context)
    (L : Nat) (F : Output) (C : Context) (t : Nat) (p : Bits)
    (hr : M.run t p C = some F) (hl : p.length ≤ L) :
    p ∈ discoveries M L F C (t+1) := by
  by_cases hp : p ∈ discoveries M L F C t
  · exact List.mem_append_left _ hp
  · apply List.mem_append_right
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨boundedWords_complete L p hl, hr, hp⟩

/-- Every program below the cutoff is eventually listed, without needing to know
when the list is complete. -/
theorem discoveries_complete (M : StagedMachine Output Context)
    (L : Nat) (F : Output) (C : Context) (p : Bits)
    (he : M.eval p C F) (hl : p.length ≤ L) :
    ∃ t, p ∈ discoveries M L F C t := by
  obtain ⟨t, ht⟩ := M.complete p C F he
  exact ⟨t+1, discoveries_event M L F C t p ht hl⟩

private theorem discoveries_length_bound (M : StagedMachine Output Context)
    (c : Nat) (hm : CodingMassBound M.toMachine c) (F : Output) (C : Context)
    (δ t : Nat) :
    (discoveries M (M.complexity F C + δ) F C t).length ≤ 2 ^ (δ+c) := by
  have hd := discoveries_nodup M (M.complexity F C + δ) F C t
  rw [← List.toFinset_card_of_nodup hd]
  apply (Finset.card_le_card ?_).trans (near_family_card M.toMachine c hm F C δ)
  intro p hp
  apply (mem_nearFamily M.toMachine F C δ p).mpr
  exact discoveries_sound M _ F C t p (List.mem_toFinset.mp hp)

/-- A two-header prefix format: excess, supplied deficit, then fixed-width index. -/
def nearWidth (c δ _d : Nat) := δ+c

def nearCode (c δ d i : Nat) : Bits := descriptor (nearWidth c) δ d i

theorem near_code_length (c δ d i : Nat) :
    (nearCode c δ d i).length = δ+c+gammaLength δ+gammaLength d := by
  simp only [nearCode, descriptor_length, nearWidth]
  omega

/-- Descriptor formats remain prefix-free even when their excesses differ. -/
theorem near_code_prefix_free (c δ d i δ' d' i' : Nat)
    (hd : d ≤ δ) (hi : i < 2 ^ (δ + c))
    (hd' : d' ≤ δ') (hi' : i' < 2 ^ (δ' + c))
    (hp : nearCode c δ d i <+: nearCode c δ' d' i') :
    (δ,d,i) = (δ',d',i') :=
  descriptor_prefix_free (nearWidth c) hd hi hd' hi' hp

/-- Stage t of the fixed decoder. The deficit is supplied, never computed. -/
def decodeAt (M : StagedMachine Output Context) (c : Nat)
    (code q : Bits) (C : Context) (t : Nat) : Option Bits :=
  match parseDescriptor (nearWidth c) code with
  | none => none
  | some ((δ, d, i), tail) =>
    if tail = [] then
      match M.run t q C with
      | none => none
      | some F => (discoveries M (q.length - d + δ) F C t)[i]?
    else none

private theorem decodeAt_code (M : StagedMachine Output Context) (c δ d i : Nat)
    (hd : d ≤ δ) (hi : i < 2 ^ (δ + c)) (q : Bits) (C : Context) (t : Nat) :
    decodeAt M c (nearCode c δ d i) q C t =
      (match M.run t q C with
      | none => none
      | some F => (discoveries M (q.length - d + δ) F C t)[i]?) := by
  have h := descriptor_parse_append (nearWidth c) δ d i hd hi []
  simp only [List.append_nil] at h
  simp [decodeAt, nearCode, h]

/-- An emitted source never changes at later stages of the decoder. Thus searching
for the first successful stage defines a single-valued partial decoder. -/
theorem decodeAt_stable (M : StagedMachine Output Context) (c : Nat)
    (code q p : Bits) (C : Context) {t s : Nat} (hts : t ≤ s)
    (ht : decodeAt M c code q C t = some p) :
    decodeAt M c code q C s = some p := by
  unfold decodeAt at ht ⊢
  cases hp : parseDescriptor (nearWidth c) code with
  | none => simp [hp] at ht
  | some parsed =>
    rcases parsed with ⟨⟨δ, d, i⟩, tail⟩
    simp only [hp] at ht ⊢
    by_cases he : tail = []
    · simp only [he, ↓reduceIte] at ht ⊢
      cases hr : M.run t q C with
      | none => simp [hr] at ht
      | some F =>
        simp only [hr] at ht
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hts
        rw [M.stable t n q C F hr]
        simp only
        have hprefix := discoveries_prefix M (q.length - d + δ) F C
          (Nat.le_add_right t n)
        have hi := (List.getElem?_eq_some_iff.mp ht).1
        obtain ⟨rest, hrest⟩ := hprefix
        rw [← hrest, List.getElem?_append_left hi]
        exact ht
    · simp [he] at ht

/-- A successful code has one output across all finite-stage observations. -/
theorem decodeAt_unique (M : StagedMachine Output Context) (c : Nat)
    (code q p p' : Bits) (C : Context) (t s : Nat)
    (ht : decodeAt M c code q C t = some p)
    (hs : decodeAt M c code q C s = some p') : p = p' := by
  have ht' := decodeAt_stable M c code q p C (le_max_left t s) ht
  have hs' := decodeAt_stable M c code q p' C (le_max_right t s) hs
  exact Option.some.inj (ht'.symm.trans hs')

/-- Successful decoding is derived from the interpreter and enumeration, not
assumed as an interface law. The index is bounded independently of the output. -/
theorem near_decoder_correct (M : StagedMachine Output Context) (c : Nat)
    (hm : CodingMassBound M.toMachine c) (F : Output) (C : Context)
    (δ : Nat) (p q : Bits)
    (hp : p ∈ nearFamily M.toMachine F C δ)
    (hq : q ∈ nearFamily M.toMachine F C δ) :
    ∃ d i t, d ≤ δ ∧ i < 2 ^ (δ + c) ∧
      decodeAt M c (nearCode c δ d i) q C t = some p := by
  obtain ⟨hep, hlp⟩ := (mem_nearFamily M.toMachine F C δ p).mp hp
  obtain ⟨heq, hlq⟩ := (mem_nearFamily M.toMachine F C δ q).mp hq
  let d := q.length - M.complexity F C
  have hmin := M.minimum_le q C F heq
  have hd : d ≤ δ := by dsimp [d]; omega
  have hcut : q.length-d+δ = M.complexity F C+δ := by dsimp [d]; omega
  obtain ⟨tp, htp⟩ := discoveries_complete M _ F C p hep hlp
  obtain ⟨tq, htq⟩ := M.complete q C F heq
  let t := tp+tq
  have hpref := discoveries_prefix M (M.complexity F C+δ) F C (by omega : tp ≤ t)
  have hpt : p ∈ discoveries M (M.complexity F C+δ) F C t :=
    hpref.sublist.subset htp
  let i := (discoveries M (M.complexity F C+δ) F C t).idxOf p
  have hiLen : i < (discoveries M (M.complexity F C+δ) F C t).length :=
    List.idxOf_lt_length_iff.mpr hpt
  have hi : i < 2 ^ (δ + c) := hiLen.trans_le (discoveries_length_bound M c hm F C δ t)
  refine ⟨d,i,t,hd,hi,?_⟩
  rw [decodeAt_code M c δ d i hd hi]
  have hqr : M.run t q C = some F := by
    simpa [t, Nat.add_comm] using M.stable tq tp q C F htq
  simp only [hqr, hcut]
  exact List.getElem?_idxOf hpt

/-- Standard universal prefix-decoder simulation bound for this fixed decoder.
The uniform constant concerns the machine and the fixed mass-bound code budget;
it does not depend on the output, source programs, condition, or excess. -/
def UniversalDecoderBound (M : StagedMachine Output Context) (c : Nat)
    (sourceK : Bits → Bits → Context → Nat) (overhead : Nat) : Prop :=
  ∀ code q C t p, decodeAt M c code q C t = some p →
    sourceK p q C ≤ code.length + overhead

/-- Explicit version of delta + O(log(delta+2)) source reconstruction.
The mass/coding theorem and uniform universal-decoder simulation are named AIT
premises. Both directions use the same fixed decoder and constant. -/
theorem near_minimal_reconstruction (M : StagedMachine Output Context)
    (c overhead : Nat) (hm : CodingMassBound M.toMachine c)
    (sourceK : Bits → Bits → Context → Nat)
    (hU : UniversalDecoderBound M c sourceK overhead)
    (F : Output) (C : Context) (δ : Nat) (p q : Bits)
    (hp : p ∈ nearFamily M.toMachine F C δ)
    (hq : q ∈ nearFamily M.toMachine F C δ) :
    max (sourceK p q C) (sourceK q p C) ≤
      δ + 4 * Nat.log 2 (δ+1) + (c+overhead+2) := by
  have one : ∀ p q, p ∈ nearFamily M.toMachine F C δ →
      q ∈ nearFamily M.toMachine F C δ →
      sourceK p q C ≤ δ + 4 * Nat.log 2 (δ+1) + (c+overhead+2) := by
    intro p q hp hq
    obtain ⟨d,i,t,hd,hi,hr⟩ := near_decoder_correct M c hm F C δ p q hp hq
    have hc := hU (nearCode c δ d i) q C t p hr
    rw [near_code_length] at hc
    have hmono := gamma_length_mono hd
    unfold gammaLength at hc hmono
    omega
  exact max_le (one p q hp hq) (one q p hq hp)

/-- The two claims of WP0215 Proposition S6, under the stated coding and
universal-simulation premises. No halting oracle is used. -/
theorem near_minimal_programs (M : StagedMachine Output Context)
    (c overhead : Nat) (hm : CodingMassBound M.toMachine c)
    (sourceK : Bits → Bits → Context → Nat)
    (hU : UniversalDecoderBound M c sourceK overhead)
    (F : Output) (C : Context) (δ : Nat) :
    (nearFamily M.toMachine F C δ).card ≤ 2 ^ (δ + c) ∧
    ∀ p ∈ nearFamily M.toMachine F C δ, ∀ q ∈ nearFamily M.toMachine F C δ,
      max (sourceK p q C) (sourceK q p C) ≤
        δ + 4 * Nat.log 2 (δ + 1) + (c + overhead + 2) := by
  refine ⟨near_family_card M.toMachine c hm F C δ, ?_⟩
  intro p hp q hq
  exact near_minimal_reconstruction M c overhead hm sourceK hU F C δ p q hp hq

/-- Explicit rational normalization of a nonnegative shared-information lower bound. -/
theorem normalized_overlap (shared lower kp kq upper : ℝ)
    (hlower : 0 ≤ lower) (hshared : lower ≤ shared)
    (hmin : 0 < min kp kq) (hp : kp ≤ upper) (hq : kq ≤ upper) :
    lower / upper ≤ shared / min kp kq := by
  have hm : min kp kq ≤ upper := by simpa using min_le_min hp hq
  exact div_le_div₀ (hlower.trans hshared) hshared hmin hm

/-- WP0215's normalized common-semantics consequence, with the same AIT-frame
premises as `common_semantics_bound` and the paper's minimum denominator. -/
theorem normalized_common_semantics (Fr : AITFrame)
    (hDP : IS.DataProcessingIK Fr) (hself : IS.SelfInfo Fr)
    (hpair : PairSymmetric Fr) (p q F : Fr.Obj) (c₁ c₂ δ : Nat)
    (h₁ : Fr.cond F (Fr.star p) ≤ c₁) (h₂ : Fr.cond F (Fr.star q) ≤ c₂)
    (hp : Fr.K p ≤ Fr.K F + δ) (hq : Fr.K q ≤ Fr.K F + δ)
    (hmin : 0 < min (Fr.K p) (Fr.K q))
    (hbudget : c₁ + c₂ + 4 * Fr.slack ≤ Fr.K F) :
    ((Fr.K F : ℝ) - c₁ - c₂ - 4 * Fr.slack) / (Fr.K F + δ) ≤
      (IK Fr p q : ℝ) / min (Fr.K p : ℝ) (Fr.K q : ℝ) := by
  have hshared := IS.common_semantics_bound Fr hDP hself hpair p q F c₁ c₂ h₁ h₂
  have hsharedR : (Fr.K F : ℝ) - c₁ - c₂ - 4 * Fr.slack ≤ (IK Fr p q : ℝ) := by
    exact_mod_cast hshared
  have hbudgetR : (c₁ : ℝ) + c₂ + 4 * Fr.slack ≤ Fr.K F := by
    exact_mod_cast hbudget
  apply normalized_overlap _ _ _ _ _ (by linarith) hsharedR
  · exact_mod_cast hmin
  · exact_mod_cast hp
  · exact_mod_cast hq

/-- Chain-rule consequence for the information fraction of an internal report.
`hchain` is the standard conditional prefix-chain-rule inequality with explicit slack. -/
theorem report_fraction_reconstruction (kr ik conditional slack ε : ℝ)
    (hkr : 0 < kr) (hfrac : 1 - ε ≤ ik / kr)
    (hchain : conditional ≤ kr - ik + slack) :
    conditional ≤ ε * kr + slack := by
  have hf := (le_div_iff₀ hkr).mp hfrac
  nlinarith

end KTAIT.NearMinimalPrograms
