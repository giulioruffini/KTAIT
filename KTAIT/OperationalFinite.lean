/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import KTAIT.OperationalAlgebra

/-!
# Finite operational examples (WP0004)

Finite certificates use kernel reduction. The enumeration is proved to equal
the generated transformation monoid when its closure certificate succeeds.
-/

namespace KTAIT.OperationalFinite

open KTAIT.OperationalAlgebra
open KTAIT.ComputationCores (run)

variable {X A : Type*} [Fintype X] [DecidableEq X] [Fintype A]

/-- Breadth-first enumeration of transformations of words of length at most `n`. -/
def wordStage (F : A → X → X) : ℕ → Finset (X → X)
  | 0 => {id}
  | n + 1 => wordStage F n ∪ Finset.univ.biUnion (fun a =>
      (wordStage F n).image (fun f => F a ∘ f))

private theorem stage_identity (F : A → X → X) (n : ℕ) : id ∈ wordStage F n := by
  induction n with
  | zero => simp [wordStage]
  | succ n ih => exact Finset.mem_union_left _ ih

private theorem stage_sound (F : A → X → X) (n : ℕ) :
    ∀ f ∈ wordStage F n, f ∈ generated F := by
  induction n with
  | zero =>
    intro f hf
    have hf' : f = id := by simpa [wordStage] using hf
    subst f
    exact (generated F).one_mem
  | succ n ih =>
    intro f hf
    rcases Finset.mem_union.mp hf with h | h
    · exact ih f h
    · obtain ⟨a, _, g, hg, rfl⟩ := by simpa only [Finset.mem_biUnion, Finset.mem_image] using h
      exact (generated F).mul_mem ⟨[a], rfl⟩ (ih g hg)

private theorem stable_stage_closed (F : A → X → X) (n : ℕ)
    (hs : wordStage F (n + 1) = wordStage F n) (a : A) (f : X → X)
    (hf : f ∈ wordStage F n) : F a ∘ f ∈ wordStage F n := by
  rw [← hs]
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  exact ⟨a, Finset.mem_univ a, Finset.mem_image.mpr ⟨f, hf, rfl⟩⟩

/-- A stable enumerated stage is exactly the realized transformation monoid. -/
theorem stable_stage_exact (F : A → X → X) (n : ℕ)
    (hs : wordStage F (n + 1) = wordStage F n) (f : X → X) :
    f ∈ wordStage F n ↔ f ∈ generated F := by
  constructor
  · exact stage_sound F n f
  · rintro ⟨w, rfl⟩
    induction w using List.reverseRecOn with
    | nil => exact stage_identity F n
    | append_singleton w a ih =>
      simpa only [run, List.foldl_append, List.foldl_cons, List.foldl_nil, Function.comp_def]
        using stable_stage_closed F n hs a (fun x => run F x w) ih

/-- Cardinalities of stable stages are cardinalities of the actual generated monoids. -/
theorem stable_stage_card (F : A → X → X) (n : ℕ)
    (hs : wordStage F (n + 1) = wordStage F n) :
    Nat.card (generated F) = (wordStage F n).card := by
  classical
  let e : generated F ≃ {f // f ∈ wordStage F n} :=
    { toFun := fun f => ⟨f.val, (stable_stage_exact F n hs f.val).mpr f.property⟩
      invFun := fun f => ⟨f.val, (stable_stage_exact F n hs f.val).mp f.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  exact Fintype.card_coe _

/-- Identity, negation, and the two writes on one bit. -/
def bitOperation (a : Fin 4) (q : Bool) : Bool :=
  if a = 0 then q else if a = 1 then !q else if a = 2 then false else true

set_option maxRecDepth 10000 in
theorem bit_monoid_card : Nat.card (generated bitOperation) = 4 := by
  rw [stable_stage_card bitOperation 1 (by decide)]
  decide

/-- Negation is invertible; writing obeys last-write-wins and is idempotent. -/
theorem bit_relations :
    (∀ q : Bool, !(!q) = q) ∧
    (∀ b q : Bool, (fun _ : Bool => b) ((fun _ : Bool => b) q) = b) ∧
    (∀ a b q : Bool, (fun _ : Bool => b) ((fun _ : Bool => a) q) = b) := by decide

/-- Exactly the identity and negation are bijections on the bit state space. -/
theorem bit_bijections : ∀ a : Fin 4, Function.Bijective (bitOperation a) ↔ a = 0 ∨ a = 1 := by
  decide

/-- The complete composition table, with the row applied after the column. -/
theorem bit_composition_table : ∀ a b : Fin 4,
    bitOperation a ∘ bitOperation b =
      bitOperation (![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 2, 2, 2], ![3, 3, 3, 3]] a b) := by
  decide

/-- The bit repertoire contains every map on the two-state space. -/
theorem bit_all_transformations : ∀ f : Bool → Bool, ∃ a, f = bitOperation a := by decide

/-- Record and receiver operations, with the receiver updated by Boolean XOR. -/
def recordOperation (a : Fin 4) (s : Bool × Bool) : Bool × Bool :=
  if a = 0 then (false, s.2) else if a = 1 then (true, s.2)
  else if a = 2 then (!s.1, s.2) else (s.1, xor s.2 s.1)

/-- An additional implementation bit flips at every operation. -/
def extendedOperation (a : Fin 4) (s : (Bool × Bool) × Bool) : (Bool × Bool) × Bool :=
  (recordOperation a s.1, !s.2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the finite closure certificate without a native-code axiom.
theorem record_monoid_card : Nat.card (generated recordOperation) = 16 := by
  rw [stable_stage_card recordOperation 6 (by decide)]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the finite closure certificate without a native-code axiom.
theorem extended_monoid_card : Nat.card (generated extendedOperation) = 24 := by
  rw [stable_stage_card extendedOperation 7 (by decide)]
  decide

/-- The extension preserves generators, hence their full generated action. -/
theorem extension_preserves_generators :
    ∀ a s, (extendedOperation a s).1 = recordOperation a s.1 := by
  intro a s; rfl

/-- The receiver projection fails closure, although the record projection closes. -/
theorem record_receiver_closure :
    (¬ ∃ G : Bool → Bool, ∀ s, (recordOperation 3 s).2 = G s.2) ∧
    (∀ a : Fin 4, ∃ G : Bool → Bool, ∀ s, (recordOperation a s).1 = G s.1) := by
  decide

/-- Use is reversible, whereas each write loses the previous record. -/
theorem receiver_reversibility :
    Function.Involutive (recordOperation 3) ∧
    ¬ Function.Injective (recordOperation 0) ∧
    ¬ Function.Injective (recordOperation 1) := by
  constructor
  · exact (by decide : ∀ s, recordOperation 3 (recordOperation 3 s) = s)
  · decide

/-- Equality of present and one-step receiver observations already separates all states. -/
theorem receiver_observations_separate :
    ∀ s t : Bool × Bool, s.2 = t.2 →
      (∀ a : Fin 4, (recordOperation a s).2 = (recordOperation a t).2) → s = t := by decide

/-- Consequently the coarsest receiver-preserving quotient retains all four states. -/
theorem receiver_future_eq :
    futureEquivalence recordOperation Prod.snd = ⊥ := by
  apply le_antisymm
  · intro s t h
    apply receiver_observations_separate s t (h [])
    intro a
    exact h [a]
  · exact bot_le

def bypassOperation (a : Fin 4) (s : Bool × Bool) : Bool × Bool :=
  if a = 3 then s else recordOperation a s

/-- Bypassing use leaves precisely the receiver kernel as the greatest quotient. -/
theorem bypass_future_eq :
    futureEquivalence bypassOperation Prod.snd = Setoid.ker Prod.snd := by
  apply le_antisymm (future_equivalence_content _ _)
  apply future_equivalence_greatest _ _ _ le_rfl
  exact (by decide : ∀ a s t, s.2 = t.2 →
    (bypassOperation a s).2 = (bypassOperation a t).2)

/-- Retaining only the record instead gives the record kernel. -/
theorem record_future_eq :
    futureEquivalence recordOperation Prod.fst = Setoid.ker Prod.fst := by
  apply le_antisymm (future_equivalence_content _ _)
  apply future_equivalence_greatest _ _ _ le_rfl
  exact (by decide : ∀ a s t, s.1 = t.1 →
    (recordOperation a s).1 = (recordOperation a t).1)

/-- A Boolean controlled update is an involution for every Boolean function. -/
theorem controlled_boolean_involution {Y : Type*} (f : Y → Bool) (x : Y) (y : Bool) :
    xor (xor y (f x)) (f x) = y := by cases y <;> cases f x <;> rfl

/-- Prepared readout recovers the selected Boolean function exactly. -/
theorem controlled_boolean_readout {Y : Type*} (f : Y → Bool) (x : Y) :
    xor false (f x) = f x := by cases f x <;> rfl

/-- A nonzero controlled update is nonidentity. -/
theorem controlled_boolean_nonidentity {Y : Type*} (f : Y → Bool)
    (hf : ∃ x, f x = true) : (fun s : Y × Bool => (s.1, xor s.2 (f s.1))) ≠ id := by
  obtain ⟨x, hx⟩ := hf
  intro h
  have := congrArg Prod.snd (congrFun h (x, false))
  simp [hx] at this

/-- Every nonzero Boolean embedding generates precisely two transformations. -/
theorem controlled_boolean_two_elements {Y : Type*} (f : Y → Bool)
    (hf : ∃ x, f x = true) :
    let U : Function.End (Y × Bool) := fun s => (s.1, xor s.2 (f s.1))
    U ≠ 1 ∧ ∀ m, m ∈ Submonoid.closure ({U} : Set _) ↔ m = 1 ∨ m = U := by
  dsimp
  constructor
  · exact controlled_boolean_nonidentity f hf
  · apply involution_generated_elements
    funext s
    exact Prod.ext rfl (controlled_boolean_involution f s.1 s.2)

/-- The nontrivial record/receiver recoding is bijective. -/
def recordRecoding : (Bool × Bool) ≃ (Bool × Bool) where
  toFun s := (s.2, xor s.1 s.2)
  invFun s := (xor s.2 s.1, s.1)
  left_inv := by decide
  right_inv := by decide

/-- The stated recoding changes the use operation. -/
theorem receiver_recoding_nontrivial :
    (recordRecoding : Bool × Bool → Bool × Bool) ≠ id ∧
    (fun s => recordRecoding (recordOperation 3 (recordRecoding.symm s))) ≠ recordOperation 3 := by
  decide

omit [Fintype A] in
/-- Conjugating every operation preserves every intermediate labeled step. -/
theorem operation_conjugacy {S T : Type*} (e : S ≃ T) (F : A → S → S) (a : A) (s : S) :
    e (F a s) = (fun t => e (F a (e.symm t))) (e s) := by simp

/-- The four-state counter projects onto parity and has a dependent carry. -/
theorem counter_parity_and_carry :
    (∀ q : Fin 4, ((q.val + 1) % 4) % 2 = (q.val % 2 + 1) % 2) ∧
    (∀ q : Fin 4, ((q.val + 1) % 4) / 2 = (q.val / 2 + q.val % 2) % 2) := by decide

/-- The counter and independent toggles have different orders. -/
theorem counter_and_independent_orders :
    (fun q : Fin 4 => q + 1)^[4] = id ∧
    (fun q : Fin 4 => q + 1)^[1] ≠ id ∧
    (fun q : Fin 4 => q + 1)^[2] ≠ id ∧
    (fun q : Fin 4 => q + 1)^[3] ≠ id ∧
    (fun s : Bool × Bool => (!s.1, !s.2))^[2] = id ∧
    (fun s : Bool × Bool => (!s.1, !s.2)) ≠ id := by decide

/-- The parity counter has exactly order two. -/
theorem parity_counter_order :
    (fun q : Fin 2 => q + 1)^[2] = id ∧ (fun q : Fin 2 => q + 1) ≠ id := by decide

/-- Two actions of the same order-two operation have different fixed-point behavior. -/
def flipFour (q : Fin 4) : Fin 4 := if q = 0 then 1 else if q = 1 then 0 else q

theorem distinct_order_two_actions :
    (∀ q : Bool, !(!q) = q) ∧ (¬ ∃ q : Bool, !q = q) ∧
    (∀ q : Fin 4, flipFour (flipFour q) = q) ∧
    (∀ q : Fin 4, flipFour q = q ↔ q = 2 ∨ q = 3) ∧ flipFour ≠ id := by decide

def gateA : Equiv.Perm (Fin 3) := Equiv.swap 0 1
def gateB : Equiv.Perm (Fin 3) := Equiv.swap 1 2

def gateProgram (x y : Bool) : Equiv.Perm (Fin 3) :=
  (if x then gateA else 1) * (if y then gateB else 1) *
    (if x then gateA⁻¹ else 1) * (if y then gateB⁻¹ else 1)

/-- The commutator truth table, including its exact nontrivial cycle. -/
theorem commutator_and :
    (∀ x y : Bool, gateProgram x y 0 ≠ 0 ↔ x = true ∧ y = true) ∧
    (∀ q : Fin 3, gateProgram true true q = ![2, 0, 1] q) ∧
    gateProgram false false = 1 ∧ gateProgram false true = 1 ∧ gateProgram true false = 1 := by
  decide

/-- A nonidentity permutation need not move a chosen observation state. -/
theorem nonidentity_can_fix_readout : gateA ≠ 1 ∧ gateA 2 = 2 := by decide

/-- In the regular action the identity state detects every nonidentity element. -/
theorem regular_action_detects {G : Type*} [Group G] (g : G) :
    g * 1 ≠ 1 ↔ g ≠ 1 := by simp

/-- Matrix of the deterministic pushforward on basis vectors. -/
def actionMatrix {S k : Type*} [DecidableEq S] [Zero k] [One k]
    (f : S → S) : Matrix S S k := fun i j => if i = f j then 1 else 0

/-- Matrix multiplication preserves ordinary transformation composition. -/
theorem action_matrix_composition {S k : Type*} [Fintype S] [DecidableEq S] [Semiring k]
    (f g : S → S) : actionMatrix (k := k) (f ∘ g) = actionMatrix f * actionMatrix g := by
  ext i j
  simp [actionMatrix, Matrix.mul_apply]

/-- Different transformations remain different matrices over a nontrivial coefficient ring. -/
theorem action_matrix_injective {S k : Type*} [DecidableEq S] [Semiring k] [Nontrivial k] :
    Function.Injective (actionMatrix (S := S) (k := k)) := by
  intro f g h
  funext j
  have hij := congrFun (congrFun h (f j)) j
  by_contra hn
  simp [actionMatrix, hn] at hij

/-- Deterministic pushforward is a monoid representation. -/
def actionMatrixHom {S k : Type*} [Fintype S] [DecidableEq S] [Semiring k] :
    Function.End S →* Matrix S S k where
  toFun := actionMatrix
  map_one' := by
    ext i j
    change (if i = j then 1 else 0) = (1 : Matrix S S k) i j
    simp [Matrix.one_apply]
  map_mul' f g := action_matrix_composition f g

/-- The action extends to its formal monoid algebra. -/
noncomputable def actionAlgebra {M S k : Type*} [Monoid M] [Fintype S] [DecidableEq S]
    [CommSemiring k] (α : M →* Function.End S) :
    MonoidAlgebra k M →ₐ[k] Matrix S S k :=
  MonoidAlgebra.lift k (Matrix S S k) M (actionMatrixHom.comp α)

/-- A formal basis element acts by its deterministic matrix. -/
theorem action_algebra_basis {M S k : Type*} [Monoid M] [Fintype S] [DecidableEq S]
    [CommSemiring k] (α : M →* Function.End S) (m : M) :
    actionAlgebra α (Finsupp.single m (1 : k)) = actionMatrix (α m) := by
  simp [actionAlgebra, MonoidAlgebra.lift_single, actionMatrixHom]

/-- The four deterministic bit matrices are linearly dependent. -/
theorem bit_matrix_dependence {k : Type*} [Semiring k] :
    actionMatrix (k := k) (bitOperation 0) + actionMatrix (bitOperation 1) =
      actionMatrix (bitOperation 2) + actionMatrix (bitOperation 3) := by
  ext i j
  cases i <;> cases j <;> simp [actionMatrix, bitOperation]

/-- Linear extension can identify distinct formal sums despite a faithful action. -/
theorem bit_algebra_not_injective {k : Type*} [CommSemiring k] [Nontrivial k] :
    ¬ Function.Injective (actionAlgebra (k := k) (MonoidHom.id (Function.End Bool))) := by
  classical
  intro hinj
  let basis (a : Fin 4) : MonoidAlgebra k (Function.End Bool) :=
    Finsupp.single (bitOperation a) 1
  have hm : actionAlgebra (k := k) (MonoidHom.id (Function.End Bool)) (basis 0 + basis 1) =
      actionAlgebra (k := k) (MonoidHom.id (Function.End Bool)) (basis 2 + basis 3) := by
    simp only [map_add, basis, action_algebra_basis, MonoidHom.id_apply]
    exact bit_matrix_dependence
  have h10 : bitOperation 1 ≠ bitOperation 0 := by decide
  have h20 : bitOperation 2 ≠ bitOperation 0 := by decide
  have h30 : bitOperation 3 ≠ bitOperation 0 := by decide
  have hs : (Finsupp.single (bitOperation 0) (1:k) + Finsupp.single (bitOperation 1) 1 :
      (Bool → Bool) →₀ k) = Finsupp.single (bitOperation 2) 1 +
        Finsupp.single (bitOperation 3) 1 := hinj hm
  have heq := DFunLike.congr_fun hs (bitOperation 0)
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne' h10, Finsupp.single_eq_of_ne' h20,
    Finsupp.single_eq_of_ne' h30, add_zero, zero_add] at heq
  exact one_ne_zero heq

/-- The displayed affine recoding conjugates bit negation to `c ↦ 16-c`. -/
theorem affine_bit_recoding (q : Bool) :
    (2 * ((!q).toNat : ℝ) + 7) = 16 - (2 * (q.toNat : ℝ) + 7) := by
  cases q <;> norm_num

/-- The affine code distinguishes both bits and transports every constant write. -/
theorem affine_bit_encoding :
    Function.Injective (fun q : Bool => 2 * (q.toNat : ℝ) + 7) ∧
    (∀ q : Bool, (2 * (q.toNat : ℝ) + 7) = 7 ∨ (2 * (q.toNat : ℝ) + 7) = 9) ∧
    (∀ b q : Bool, 2 * (((fun _ : Bool => b) q).toNat : ℝ) + 7 =
      (fun _ : ℝ => 2 * (b.toNat : ℝ) + 7) (2 * (q.toNat : ℝ) + 7)) := by
  constructor
  · intro a b h
    cases a <;> cases b
    · rfl
    · norm_num at h
    · norm_num at h
    · rfl
  constructor
  · intro q; cases q <;> norm_num
  · intro b q; rfl

end KTAIT.OperationalFinite
