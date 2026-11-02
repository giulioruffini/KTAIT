import KTAIT.CertifiedPrograms.Certification
import KTAIT.CertifiedPrograms.Counting
import KTAIT.NearMinimalPrograms

/-!
# Certified whole-function reconstruction (WP0215)

A computably enumerable sound equivalence relation supplies actual finite-stage
certificates. A permanent-marking scan produces global representatives; a second
stream lists the exact sources in a certified class. Descriptor parsing, coverage,
and index bounds are proved. Fixed compilation and universal source-complexity
simulation remain named standard AIT premises. This module does not instantiate
an optimal prefix interpreter or formalize unrestricted semantic equivalence.
-/

namespace KTAIT.WholeFunctionPrograms
open KTAIT.CertifiedPrograms
open KTAIT.NearMinimalPrograms (boundedWords binaryWords)

variable {Input Output : Type}

private theorem binary_length (n : Nat) (p : CodeBits) (hp : p ∈ binaryWords n) :
    p.length = n := by
  induction n generalizing p with
  | zero => simpa [binaryWords] using hp
  | succ n ih =>
    simp only [binaryWords, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ <;> simp [ih q hq]

private theorem binary_complete (p : CodeBits) : p ∈ binaryWords p.length := by
  induction p with
  | nil => simp [binaryWords]
  | cons b p ih => cases b <;> simp [binaryWords, ih]

private theorem bounded_complete (L : Nat) (p : CodeBits) (hp : p.length ≤ L) :
    p ∈ boundedWords L := by
  induction L with
  | zero =>
    have he : p.length = 0 := by omega
    simpa [boundedWords, ← he] using binary_complete p
  | succ L ih =>
    by_cases h : p.length ≤ L
    · exact List.mem_append_left _ (ih h)
    · have he : p.length = L + 1 := by omega
      exact List.mem_append_right _ (he ▸ binary_complete p)

private theorem bounded_length (L : Nat) (p : CodeBits) (hp : p ∈ boundedWords L) :
    p.length ≤ L := by
  induction L with
  | zero => exact le_of_eq (binary_length 0 p hp)
  | succ L ih =>
    rcases List.mem_append.mp hp with hp | hp
    · exact (ih hp).trans (Nat.le_succ L)
    · exact le_of_eq (binary_length _ _ hp)

private theorem bounded_pos (L : Nat) : 0 < (boundedWords L).length := by
  have h := bounded_complete L [] (by simp)
  exact List.length_pos_of_mem h

/-- Fixed round-robin schedule over the actual bounded binary sources. -/
def scanWord (L n : Nat) : CodeBits :=
  (boundedWords L)[n % (boundedWords L).length]'(Nat.mod_lt _ (bounded_pos L))

private theorem scanWord_bounded (L n : Nat) : (scanWord L n).length ≤ L :=
  bounded_length L _ (List.getElem_mem _)

private theorem scanWord_fair (L : Nat) (p : CodeBits) (hp : p.length ≤ L) (N : Nat) :
    ∃ n, N ≤ n ∧ scanWord L n = p := by
  have hmem := bounded_complete L p hp
  let k := (boundedWords L).idxOf p
  have hk : k < (boundedWords L).length := List.idxOf_lt_length_iff.mpr hmem
  let n := N * (boundedWords L).length + k
  have hn : N ≤ n := by
    have := bounded_pos L
    dsimp [n]
    nlinarith
  refine ⟨n, hn, ?_⟩
  have hmod : n % (boundedWords L).length = k := by
    simp [n, Nat.add_mod, Nat.mod_eq_of_lt hk]
  simp only [scanWord, hmod]
  exact List.getElem_idxOf hk

/-- Bounded certified neighbors witnessed in the finite stream prefix. -/
def seen {V : ProgramSemantics Input Output} (C : Certification V)
    (L n : Nat) (p : CodeBits) : Finset CodeBits :=
  (wordsThrough L).filter fun q => ∃ j ∈ Finset.range n, C.stream j = some (p, q)

private theorem seen_sound {V : ProgramSemantics Input Output} (C : Certification V)
    (L n : Nat) (p q : CodeBits) (hq : q ∈ seen C L n p) : C.related p q := by
  obtain ⟨_, j, _, hj⟩ := Finset.mem_filter.mp hq
  exact C.stream_sound j p q hj

private theorem seen_bounded {V : ProgramSemantics Input Output} (C : Certification V)
    (L n : Nat) (p : CodeBits) : seen C L n p ⊆ wordsThrough L :=
  Finset.filter_subset _ _

private theorem seen_mono {V : ProgramSemantics Input Output} (C : Certification V)
    (L : Nat) (p : CodeBits) {n m : Nat} (hnm : n ≤ m) :
    seen C L n p ⊆ seen C L m p := by
  intro q hq
  obtain ⟨hb, j, hj, he⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨hb, j, Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hj) hnm), he⟩

private theorem seen_eventual {V : ProgramSemantics Input Output} (C : Certification V)
    (L : Nat) (p : CodeBits) (A : Finset CodeBits)
    (hA : ∀ q ∈ A, C.related p q ∧ q.length ≤ L) :
    ∃ n, A ⊆ seen C L n p := by
  induction A using Finset.induction_on with
  | empty => exact ⟨0, Finset.empty_subset _⟩
  | @insert a A ha ih =>
    have haa := hA a (by simp)
    obtain ⟨j, hj⟩ := C.stream_complete p a haa.1
    obtain ⟨n, hn⟩ := ih (fun q hq => hA q (Finset.mem_insert_of_mem hq))
    refine ⟨max n (j + 1), ?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_filter.mpr ⟨words_through_complete L q haa.2,
        j, Finset.mem_range.mpr (by omega), hj⟩
    · exact seen_mono C L p (le_max_left _ _) (hn hq)

/-- The marking process visits every bounded source, without deciding the final relation. -/
def globalRun {V : ProgramSemantics Input Output} (C : Certification V)
    (L h : Nat) : Nat → MarkState CodeBits
  | 0 => emptyState
  | n + 1 => markStep h (scanWord L n) (seen C L n (scanWord L n)) (globalRun C L h n)

private theorem global_invariant {V : ProgramSemantics Input Output} (C : Certification V)
    (L h n : Nat) : MarkInvariant C.related h (globalRun C L h n) := by
  induction n with
  | zero => exact marking_empty_invariant _ _
  | succ n ih =>
    exact marking_step_invariant _ _ _ _ _ ih (fun q hq => seen_sound C L n _ q hq)

private theorem global_marks_bounded {V : ProgramSemantics Input Output} (C : Certification V)
    (L h n : Nat) : (globalRun C L h n).marked ⊆ wordsThrough L := by
  induction n with
  | zero => simp [globalRun, emptyState]
  | succ n ih =>
    unfold globalRun markStep
    split_ifs
    · intro q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · exact ih hq
      · exact seen_bounded C L n _ (Finset.mem_sdiff.mp hq).1
    · exact ih

/-- Every emitted representative consumes fresh bounded source strings. -/
theorem global_event_budget {V : ProgramSemantics Input Output} (C : Certification V)
    (L h n : Nat) :
    (globalRun C L h n).emitted.length * h < 2 ^ (L + 1) := by
  have hi := (global_invariant C L h n).1
  have hb := Finset.card_le_card (global_marks_bounded C L h n)
  have hc := bounded_binary_card L
  omega

/-- Every large certified class is reached by an actual emitted representative. -/
theorem global_coverage {V : ProgramSemantics Input Output} (C : Certification V)
    (L h : Nat) (p : CodeBits) (hp : p.length ≤ L) (A : Finset CodeBits)
    (hA : ∀ q ∈ A, C.related p q ∧ q.length ≤ L) (hlarge : h ≤ A.card) :
    ∃ n q, q ∈ (globalRun C L h n).emitted ∧ C.related p q := by
  obtain ⟨N, hN⟩ := seen_eventual C L p A hA
  obtain ⟨n, hNn, hscan⟩ := scanWord_fair L p hp N
  have hs : A ⊆ seen C L n (scanWord L n) := by
    rw [hscan]
    exact hN.trans (seen_mono C L p hNn)
  obtain ⟨q, hq, hr⟩ := marking_step_covers C.related C.equivalence h
    (scanWord L n) A _ _ (global_invariant C L h n)
    (fun q hq => by rw [hscan]; exact (hA q hq).1) hs hlarge
  exact ⟨n + 1, q, hq, by simpa [hscan] using hr⟩

/-- The full bounded certified class, defined without a decidability assumption on R. -/
noncomputable def classFamily {V : ProgramSemantics Input Output} (C : Certification V)
    (L : Nat) (p : CodeBits) : Finset CodeBits := by
  classical
  exact (wordsThrough L).filter (C.related p)

private theorem mem_class {V : ProgramSemantics Input Output} (C : Certification V)
    (L : Nat) (p q : CodeBits) :
    q ∈ classFamily C L p ↔ C.related p q ∧ q.length ≤ L := by
  classical
  simp only [classFamily, Finset.mem_filter]
  exact ⟨fun h => ⟨h.2, words_through_length L q h.1⟩,
    fun h => ⟨words_through_complete L q h.2, h.1⟩⟩

private theorem class_pos {V : ProgramSemantics Input Output} (C : Certification V)
    (L : Nat) (p : CodeBits) (hp : p.length ≤ L) : 0 < (classFamily C L p).card := by
  exact Finset.card_pos.mpr ⟨p, (mem_class C L p p).mpr ⟨C.equivalence.refl p, hp⟩⟩

private theorem class_bound {V : ProgramSemantics Input Output} (C : Certification V)
    (L : Nat) (p : CodeBits) : (classFamily C L p).card < 2 ^ (L + 1) := by
  classical
  have hsub : classFamily C L p ⊆ wordsThrough L := Finset.filter_subset _ _
  have hb := Finset.card_le_card hsub
  have hc := bounded_binary_card L
  omega

private theorem class_congr {V : ProgramSemantics Input Output} (C : Certification V)
    (L : Nat) (p q : CodeBits) (hpq : C.related p q) :
    classFamily C L p = classFamily C L q := by
  ext a
  rw [mem_class, mem_class]
  exact ⟨fun h => ⟨C.equivalence.trans (C.equivalence.symm hpq) h.1, h.2⟩,
    fun h => ⟨C.equivalence.trans hpq h.1, h.2⟩⟩

/-- Exact sources are appended on their first certificate, preserving their indices. -/
def localHistory {V : ProgramSemantics Input Output} (C : Certification V)
    (L : Nat) (p : CodeBits) : Nat → List CodeBits
  | 0 => []
  | n + 1 =>
    let previous := localHistory C L p n
    match C.stream n with
    | none => previous
    | some (a, q) =>
      if a = p ∧ q.length ≤ L ∧ q ∉ previous then previous ++ [q] else previous

private theorem local_prefix_step {V : ProgramSemantics Input Output} (C : Certification V)
    (L : Nat) (p : CodeBits) (n : Nat) :
    localHistory C L p n <+: localHistory C L p (n + 1) := by
  conv_rhs => rw [localHistory]
  split
  · exact ⟨[], by simp⟩
  · split_ifs
    · exact List.prefix_append _ _
    · exact ⟨[], by simp⟩

private theorem local_prefix {V : ProgramSemantics Input Output} (C : Certification V)
    (L : Nat) (p : CodeBits) {n m : Nat} (hnm : n ≤ m) :
    localHistory C L p n <+: localHistory C L p m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction k with
  | zero => simp
  | succ k ih => exact ih.trans (local_prefix_step C L p (n + k))

private theorem local_nodup {V : ProgramSemantics Input Output} (C : Certification V)
    (L : Nat) (p : CodeBits) (n : Nat) : (localHistory C L p n).Nodup := by
  induction n with
  | zero => simp [localHistory]
  | succ n ih =>
    rw [localHistory]
    split
    · exact ih
    · split_ifs with hc
      · simpa using ih.concat hc.2.2
      · exact ih

private theorem local_sound {V : ProgramSemantics Input Output} (C : Certification V)
    (L : Nat) (p : CodeBits) (n : Nat) (q : CodeBits)
    (hq : q ∈ localHistory C L p n) : C.related p q ∧ q.length ≤ L := by
  induction n with
  | zero => simp [localHistory] at hq
  | succ n ih =>
    rw [localHistory] at hq
    split at hq
    · exact ih hq
    · next a b he =>
        split_ifs at hq with hc
        · rcases List.mem_append.mp hq with hq | hq
          · exact ih hq
          · have hqb : q = b := List.mem_singleton.mp hq
            subst q
            exact ⟨hc.1 ▸ C.stream_sound n a b he, hc.2.1⟩
        · exact ih hq

/-- The local source decoder eventually sees every certified bounded alternative. -/
theorem local_complete {V : ProgramSemantics Input Output} (C : Certification V)
    (L : Nat) (p q : CodeBits) (hpq : C.related p q) (hq : q.length ≤ L) :
    ∃ n, q ∈ localHistory C L p n := by
  obtain ⟨n, hn⟩ := C.stream_complete p q hpq
  refine ⟨n + 1, ?_⟩
  by_cases hm : q ∈ localHistory C L p n
  · exact (local_prefix_step C L p n).sublist.subset hm
  · simp [localHistory, hn, hq, hm]

private theorem local_length_bound {V : ProgramSemantics Input Output} (C : Certification V)
    (L : Nat) (p : CodeBits) (n : Nat) :
    (localHistory C L p n).length ≤ (classFamily C L p).card := by
  rw [← List.toFinset_card_of_nodup (local_nodup C L p n)]
  apply Finset.card_le_card
  intro q hq
  exact (mem_class C L p q).mpr (local_sound C L p n q (List.mem_toFinset.mp hq))

/-- Chronological global indices do not shift when a new representative is emitted. -/
def globalHistory {V : ProgramSemantics Input Output} (C : Certification V)
    (L t n : Nat) : List CodeBits := (globalRun C L (2 ^ t) n).emitted.reverse

private theorem global_prefix_step {V : ProgramSemantics Input Output} (C : Certification V)
    (L t n : Nat) : globalHistory C L t n <+: globalHistory C L t (n + 1) := by
  change (globalRun C L (2 ^ t) n).emitted.reverse <+:
    (markStep (2 ^ t) (scanWord L n) (seen C L n (scanWord L n))
      (globalRun C L (2 ^ t) n)).emitted.reverse
  unfold markStep
  split_ifs
  · simp only [List.reverse_cons]
    exact List.prefix_append _ _
  · exact ⟨[], by simp⟩

private theorem global_prefix {V : ProgramSemantics Input Output} (C : Certification V)
    (L t : Nat) {n m : Nat} (hnm : n ≤ m) :
    globalHistory C L t n <+: globalHistory C L t m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction k with
  | zero => simp
  | succ k ih => exact ih.trans (global_prefix_step C L t (n + k))

/-- Stage of the unconditional source-selection decoder. Executing the selected
source on the external input is the fixed compiler's role. -/
def globalDecodeAt {V : ProgramSemantics Input Output} (C : Certification V)
    (code : CodeBits) (n : Nat) : Option CodeBits :=
  match parseDescriptor globalWidth code with
  | none => none
  | some ((L, t, i), tail) =>
    if tail = [] then (globalHistory C L t n)[i]? else none

/-- Stage of the conditional decoder, returning the exact selected source string. -/
def localDecodeAt {V : ProgramSemantics Input Output} (C : Certification V)
    (code p : CodeBits) (n : Nat) : Option CodeBits :=
  match parseDescriptor localWidth code with
  | none => none
  | some ((L, _t, i), tail) =>
    if tail = [] then (localHistory C L p n)[i]? else none

private theorem global_decode_code {V : ProgramSemantics Input Output} (C : Certification V)
    (L t i n : Nat) (ht : t ≤ L) (hi : i < 2 ^ globalWidth L t) :
    globalDecodeAt C (descriptor globalWidth L t i) n = (globalHistory C L t n)[i]? := by
  have h := descriptor_parse_append globalWidth L t i ht hi []
  simp only [List.append_nil] at h
  simp [globalDecodeAt, h]

private theorem local_decode_code {V : ProgramSemantics Input Output} (C : Certification V)
    (L t i n : Nat) (p : CodeBits) (ht : t ≤ L) (hi : i < 2 ^ localWidth L t) :
    localDecodeAt C (descriptor localWidth L t i) p n = (localHistory C L p n)[i]? := by
  have h := descriptor_parse_append localWidth L t i ht hi []
  simp only [List.append_nil] at h
  simp [localDecodeAt, h]

private theorem prefix_get_stable {α : Type} (a : α) (xs ys : List α) (i : Nat)
    (hp : xs <+: ys) (hx : xs[i]? = some a) : ys[i]? = some a := by
  have hi := (List.getElem?_eq_some_iff.mp hx).1
  obtain ⟨tail, ht⟩ := hp
  rw [← ht, List.getElem?_append_left hi]
  exact hx

/-- Global descriptor outputs persist, so compilation selects a well-defined source. -/
theorem global_decode_stable {V : ProgramSemantics Input Output} (C : Certification V)
    (code q : CodeBits) {n m : Nat} (hnm : n ≤ m)
    (hn : globalDecodeAt C code n = some q) : globalDecodeAt C code m = some q := by
  unfold globalDecodeAt at hn ⊢
  cases hp : parseDescriptor globalWidth code with
  | none => simp [hp] at hn
  | some parsed =>
    rcases parsed with ⟨⟨L, t, i⟩, tail⟩
    simp only [hp] at hn ⊢
    by_cases he : tail = []
    · simp only [he, ↓reduceIte] at hn ⊢
      exact prefix_get_stable q _ _ i (global_prefix C L t hnm) hn
    · simp [he] at hn

/-- Local descriptor outputs persist and return one exact source. -/
theorem local_decode_stable {V : ProgramSemantics Input Output} (C : Certification V)
    (code p q : CodeBits) {n m : Nat} (hnm : n ≤ m)
    (hn : localDecodeAt C code p n = some q) : localDecodeAt C code p m = some q := by
  unfold localDecodeAt at hn ⊢
  cases hp : parseDescriptor localWidth code with
  | none => simp [hp] at hn
  | some parsed =>
    rcases parsed with ⟨⟨L, t, i⟩, tail⟩
    simp only [hp] at hn ⊢
    by_cases he : tail = []
    · simp only [he, ↓reduceIte] at hn ⊢
      exact prefix_get_stable q _ _ i (local_prefix C L p hnm) hn
    · simp [he] at hn

/-- A global descriptor cannot select different sources at different stages. -/
theorem global_decode_unique {V : ProgramSemantics Input Output} (C : Certification V)
    (code p q : CodeBits) (n m : Nat)
    (hn : globalDecodeAt C code n = some p)
    (hm : globalDecodeAt C code m = some q) : p = q := by
  have hn' := global_decode_stable C code p (le_max_left n m) hn
  have hm' := global_decode_stable C code q (le_max_right n m) hm
  exact Option.some.inj (hn'.symm.trans hm')

/-- A local descriptor cannot reconstruct different source strings at different stages. -/
theorem local_decode_unique {V : ProgramSemantics Input Output} (C : Certification V)
    (code p q r : CodeBits) (n m : Nat)
    (hn : localDecodeAt C code p n = some q)
    (hm : localDecodeAt C code p m = some r) : q = r := by
  have hn' := local_decode_stable C code p q (le_max_left n m) hn
  have hm' := local_decode_stable C code p r (le_max_right n m) hm
  exact Option.some.inj (hn'.symm.trans hm')

/-- A fixed compiler selects the decoded source and runs it on the external input.
This standard compilation law is uniform in the descriptor and selected source. -/
def GlobalCompiler {V : ProgramSemantics Input Output} (C : Certification V)
    (overhead : Nat) : Prop :=
  ∃ compile : CodeBits → CodeBits, ∀ code n q,
    globalDecodeAt C code n = some q →
    V (compile code) = V q ∧ (compile code).length ≤ code.length + overhead

/-- Standard uniform conditional prefix-machine simulation of the explicit local decoder. -/
def LocalCompiler {V : ProgramSemantics Input Output} (C : Certification V)
    (sourceK : CodeBits → CodeBits → Nat) (overhead : Nat) : Prop :=
  ∀ code p n q, localDecodeAt C code p n = some q →
    sourceK q p ≤ code.length + overhead

/-- The global descriptor selects a representative from the requested class with
an index justified by the permanent-mark charging bound. -/
theorem global_decoder_correct {V : ProgramSemantics Input Output} (C : Certification V)
    (L t : Nat) (p : CodeBits) (hp : p.length ≤ L) (ht : t ≤ L)
    (hlarge : 2 ^ t ≤ (classFamily C L p).card) :
    ∃ i n q, i < 2 ^ globalWidth L t ∧ C.related p q ∧
      globalDecodeAt C (descriptor globalWidth L t i) n = some q := by
  obtain ⟨n, q, hq, hpq⟩ := global_coverage C L (2 ^ t) p hp (classFamily C L p)
    (fun r hr => (mem_class C L p r).mp hr) hlarge
  have hmem : q ∈ globalHistory C L t n := List.mem_reverse.mpr hq
  let i := (globalHistory C L t n).idxOf q
  have hi : i < (globalHistory C L t n).length := List.idxOf_lt_length_iff.mpr hmem
  have hbound : (globalHistory C L t n).length < 2 ^ globalWidth L t := by
    simpa [globalHistory] using event_count_fits_width L t _ ht (global_event_budget C L (2 ^ t) n)
  refine ⟨i, n, q, hi.trans hbound, hpq, ?_⟩
  rw [global_decode_code C L t i n ht (hi.trans hbound)]
  exact List.getElem?_idxOf hmem

/-- The local descriptor returns the exact selected related source; the class
cardinality bounds its index without an enumeration-completion test. -/
theorem local_decoder_correct {V : ProgramSemantics Input Output} (C : Certification V)
    (L t : Nat) (p q : CodeBits) (hpq : C.related p q) (hq : q.length ≤ L)
    (ht : t ≤ L) (hsmall : (classFamily C L p).card < 2 ^ (t + 1)) :
    ∃ i n, i < 2 ^ localWidth L t ∧
      localDecodeAt C (descriptor localWidth L t i) p n = some q := by
  obtain ⟨n, hn⟩ := local_complete C L p q hpq hq
  let i := (localHistory C L p n).idxOf q
  have hi : i < (localHistory C L p n).length := List.idxOf_lt_length_iff.mpr hn
  have hwidth : i < 2 ^ localWidth L t :=
    (hi.trans_le (local_length_bound C L p n)).trans hsmall
  refine ⟨i, n, hwidth, ?_⟩
  rw [local_decode_code C L t i n p ht hwidth]
  exact List.getElem?_idxOf hn

/-- Whole-function description cost is derived by compiling an actual global
selection event, then comparing with the unrestricted implementation minimum. -/
theorem global_cost_bound {V : ProgramSemantics Input Output} (C : Certification V)
    (cG : Nat) (hG : GlobalCompiler C cG) (L t : Nat) (p : CodeBits)
    (hp : p.length ≤ L) (ht : t ≤ L) (hlarge : 2 ^ t ≤ (classFamily C L p).card) :
    wholeFunctionComplexity V p ≤ L + 1 - t + gammaLength L + gammaLength t + cG := by
  obtain ⟨i, n, q, hi, hpq, hd⟩ := global_decoder_correct C L t p hp ht hlarge
  obtain ⟨compile, hc⟩ := hG
  obtain ⟨he, hl⟩ := hc (descriptor globalWidth L t i) n q hd
  have hm := whole_function_minimum_le V p (compile (descriptor globalWidth L t i))
    (he.trans (C.semantic_sound p q hpq).symm)
  rw [global_descriptor_length] at hl
  exact hm.trans hl

/-- Exact source reconstruction cost is derived from the local event and its code. -/
theorem local_cost_bound {V : ProgramSemantics Input Output} (C : Certification V)
    (sourceK : CodeBits → CodeBits → Nat) (cI : Nat) (hI : LocalCompiler C sourceK cI)
    (L t : Nat) (p q : CodeBits) (hpq : C.related p q) (hq : q.length ≤ L)
    (ht : t ≤ L) (hsmall : (classFamily C L p).card < 2 ^ (t + 1)) :
    sourceK q p ≤ t + 1 + gammaLength L + gammaLength t + cI := by
  obtain ⟨i, n, hi, hd⟩ := local_decoder_correct C L t p q hpq hq ht hsmall
  have hc := hI (descriptor localWidth L t i) p n q hd
  rw [local_descriptor_length] at hc
  exact hc

/-- WP0215's certified whole-function inequality. The class log is selected in
the proof; no oracle is asked to compute it. All description costs are derived
from concrete event decoders and the named fixed-compiler laws. -/
theorem certified_reconstruction {V : ProgramSemantics Input Output} (C : Certification V)
    (sourceK : CodeBits → CodeBits → Nat) (cG cI : Nat)
    (hG : GlobalCompiler C cG) (hI : LocalCompiler C sourceK cI)
    (L : Nat) (p q : CodeBits) (hpq : C.related p q)
    (hp : p.length ≤ L) (hq : q.length ≤ L) :
    max (sourceK p q) (sourceK q p) + wholeFunctionComplexity V p ≤
      L + 4 * gammaLength L + (cG + cI + 2) := by
  let N := (classFamily C L p).card
  let t := Nat.log 2 N
  obtain ⟨hlarge, hsmall, ht⟩ := class_log_range L N (class_pos C L p hp) (class_bound C L p)
  have hg := global_cost_bound C cG hG L t p hp ht hlarge
  have hiqp := local_cost_bound C sourceK cI hI L t p q hpq hq ht hsmall
  have hsmallq : (classFamily C L q).card < 2 ^ (t + 1) := by
    rw [← class_congr C L p q hpq]
    exact hsmall
  have hipq := local_cost_bound C sourceK cI hI L t q p (C.equivalence.symm hpq) hp ht hsmallq
  exact combine_decoder_costs _ _ L t cG cI ht hg (max_le hipq hiqp)

/-- Additive near-minimality gives the certified information-distance bound for
whole partial functions, with a uniform explicit logarithmic correction. -/
theorem certified_near_minimal {V : ProgramSemantics Input Output} (C : Certification V)
    (sourceK : CodeBits → CodeBits → Nat) (cG cI : Nat)
    (hG : GlobalCompiler C cG) (hI : LocalCompiler C sourceK cI)
    (δ : Nat) (p q : CodeBits) (hpq : C.related p q)
    (hp : p.length ≤ wholeFunctionComplexity V p + δ)
    (hq : q.length ≤ wholeFunctionComplexity V p + δ) :
    max (sourceK p q) (sourceK q p) ≤
      δ + 8 * Nat.log 2 (wholeFunctionComplexity V p + δ + 1) + (cG + cI + 6) := by
  have h := certified_reconstruction C sourceK cG cI hG hI
    (wholeFunctionComplexity V p + δ) p q hpq hp hq
  unfold gammaLength at h
  omega

end KTAIT.WholeFunctionPrograms
