/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import KTAIT.ClosureInvariance

/-!
# Finite stochastic closure and ordering content-preserving grains (WP0215)

For a finite Markov chain, equality of transition probabilities into every
retained class gives a unique quotient kernel. Its evolution commutes with
pushforward for every initial law, and hence for every number of steps. No
initial-law restriction is hidden in the lumpability condition.

The ordering results concern declared families of equivalence relations. The
finite and infinite witnesses below illustrate the abstract freedom of that
family; they do not establish physical admissibility of any representation.
-/

namespace KTAIT.ClosureExtensions

open scoped BigOperators

section Stochastic

variable {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]

/-- A finite transition matrix has nonnegative entries and unit row sums. -/
def Stochastic (P : X → X → ℝ) : Prop :=
  (∀ x z, 0 ≤ P x z) ∧ (∀ x, ∑ z, P x z = 1)

/-- Probability mass assigned to a retained state. -/
def pushforward (ρ : X → Q) (μ : X → ℝ) (q : Q) : ℝ :=
  ∑ x, if ρ x = q then μ x else 0

/-- One step of evolution for a finite signed mass, or a probability law. -/
def evolve (P : X → X → ℝ) (μ : X → ℝ) (z : X) : ℝ :=
  ∑ x, μ x * P x z

/-- Every microscopic representative gives the same next retained-state law. -/
def StrongLumpable (ρ : X → Q) (P : X → X → ℝ) : Prop :=
  ∀ x y, ρ x = ρ y → pushforward ρ (P x) = pushforward ρ (P y)

private theorem pushforward_sum (ρ : X → Q) (μ : X → ℝ) :
    ∑ q, pushforward ρ μ q = ∑ x, μ x := by
  classical
  simp only [pushforward]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

omit [Fintype Q] in
/-- Lumpability is equivalent to a unique factorization of the row laws. -/
theorem lumpable_iff_unique_quotient (ρ : X → Q) (hρ : Function.Surjective ρ)
    (P : X → X → ℝ) :
    StrongLumpable ρ P ↔ ∃! B : Q → Q → ℝ,
      ∀ x, pushforward ρ (P x) = B (ρ x) := by
  exact (ClosureInvariance.factor_iff_fiber_constant ρ hρ
    (fun x => pushforward ρ (P x))).symm

/-- The quotient of a stochastic kernel is stochastic, including its row sums. -/
theorem quotient_stochastic (ρ : X → Q) (hρ : Function.Surjective ρ)
    (P : X → X → ℝ) (hP : Stochastic P) (B : Q → Q → ℝ)
    (hB : ∀ x, pushforward ρ (P x) = B (ρ x)) : Stochastic B := by
  constructor
  · intro q q'
    obtain ⟨x, rfl⟩ := hρ q
    rw [← hB x]
    apply Finset.sum_nonneg
    intro z _
    split_ifs <;> simp_all only [hP.1, le_refl]
  · intro q
    obtain ⟨x, rfl⟩ := hρ q
    rw [← hB x, pushforward_sum]
    exact hP.2 x

/-- Strong lumpability constructs a unique stochastic quotient kernel. -/
theorem stochastic_quotient_exists_unique (ρ : X → Q) (hρ : Function.Surjective ρ)
    (P : X → X → ℝ) (hP : Stochastic P) (hl : StrongLumpable ρ P) :
    ∃! B : Q → Q → ℝ,
      Stochastic B ∧ ∀ x, pushforward ρ (P x) = B (ρ x) := by
  obtain ⟨B, hB, hu⟩ := (lumpable_iff_unique_quotient ρ hρ P).mp hl
  refine ⟨B, ⟨quotient_stochastic ρ hρ P hP B hB, hB⟩, ?_⟩
  intro C hC
  exact hu C hC.2

/-- Evolution commutes with projection for every initial mass, without a
restriction to one privileged initial distribution. -/
theorem pushforward_evolve (ρ : X → Q) (P : X → X → ℝ) (B : Q → Q → ℝ)
    (hB : ∀ x, pushforward ρ (P x) = B (ρ x)) (μ : X → ℝ) :
    pushforward ρ (evolve P μ) = evolve B (pushforward ρ μ) := by
  classical
  funext q'
  unfold pushforward evolve
  calc
    (∑ z, if ρ z = q' then ∑ x, μ x * P x z else 0) =
        ∑ z, ∑ x, if ρ z = q' then μ x * P x z else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases h : ρ z = q' <;> simp [h]
    _ = ∑ x, ∑ z, if ρ z = q' then μ x * P x z else 0 := Finset.sum_comm
    _ =
        ∑ x, μ x * B (ρ x) q' := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← congrFun (hB x) q']
      unfold pushforward
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      split_ifs <;> simp
    _ = ∑ q, (∑ x, if ρ x = q then μ x else 0) * B q q' := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp only [ite_mul, zero_mul]
      simp

/-- The same quotient law governs every natural-number time step. -/
theorem pushforward_evolve_iterates (ρ : X → Q) (P : X → X → ℝ)
    (B : Q → Q → ℝ) (hB : ∀ x, pushforward ρ (P x) = B (ρ x))
    (μ : X → ℝ) (n : ℕ) :
    pushforward ρ ((evolve P)^[n] μ) = (evolve B)^[n] (pushforward ρ μ) := by
  exact ClosureInvariance.reduced_iterates (pushforward ρ) (evolve P) (evolve B)
    (pushforward_evolve ρ P B hB) n μ

omit [Fintype Q] in
/-- Every convex mixture of two lumpable kernels remains lumpable for the
same partition. The algebraic equality actually permits any real weights. -/
theorem lumpable_linear_combination (ρ : X → Q) (P R : X → X → ℝ)
    (hP : StrongLumpable ρ P) (hR : StrongLumpable ρ R) (a b : ℝ) :
    StrongLumpable ρ (fun x z => a * P x z + b * R x z) := by
  intro x y hxy
  funext q
  have hp := congrFun (hP x y hxy) q
  have hr := congrFun (hR x y hxy) q
  have expand (v : X) :
      pushforward ρ (fun z => a * P v z + b * R v z) q =
        a * pushforward ρ (P v) q + b * pushforward ρ (R v) q := by
    simp only [pushforward, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    split_ifs <;> simp
  rw [expand x, expand y, hp, hr]

end Stochastic

section Ordering

variable {X V : Type*}

/-- The declared admissible equivalences that preserve selected content. -/
def contentPreservingFamily (A : Set (Setoid X)) (c : X → V) : Set (Setoid X) :=
  {R | R ∈ A ∧ R ≤ Setoid.ker c}

/-- Without an admissibility restriction, equality of content is the unique
coarsest equivalence preserving that content. -/
theorem content_kernel_is_greatest (c : X → V) :
    IsGreatest (contentPreservingFamily Set.univ c) (Setoid.ker c) := by
  exact ⟨⟨Set.mem_univ _, le_rfl⟩, fun _ h => h.2⟩

/-- A coarsest admissible equivalence, if one exists, is unique. -/
theorem greatest_content_equivalence_unique (A : Set (Setoid X)) (c : X → V)
    (R S : Setoid X) (hR : IsGreatest (contentPreservingFamily A c) R)
    (hS : IsGreatest (contentPreservingFamily A c) S) : R = S := by
  exact le_antisymm (hS.2 hR.1) (hR.2 hS.1)

/-- A finite illustration of the freedom in a declared family: the two
coordinate partitions preserve constant content but neither contains the other.
This is not a physical-admissibility claim. -/
theorem finite_family_without_coarsest :
    ∃ A : Set (Setoid (Bool × Bool)),
      A.Nonempty ∧ Set.Finite A ∧
      ¬ ∃ R, IsGreatest (contentPreservingFamily A (fun _ => ())) R := by
  let R : Setoid (Bool × Bool) := Setoid.ker Prod.fst
  let S : Setoid (Bool × Bool) := Setoid.ker Prod.snd
  have hrs : ¬ R ≤ S := by
    intro h
    have hh := h (x := (false, false)) (y := (false, true)) (show R _ _ from rfl)
    exact Bool.false_ne_true hh
  have hsr : ¬ S ≤ R := by
    intro h
    have hh := h (x := (false, false)) (y := (true, false)) (show S _ _ from rfl)
    exact Bool.false_ne_true hh
  have hR : R ∈ contentPreservingFamily {R, S} (fun _ => ()) :=
    ⟨by simp, fun _ _ _ => rfl⟩
  have hS : S ∈ contentPreservingFamily {R, S} (fun _ => ()) :=
    ⟨by simp, fun _ _ _ => rfl⟩
  refine ⟨{R, S}, ⟨R, by simp⟩, Set.toFinite _, ?_⟩
  rintro ⟨T, hT⟩
  have ht : T = R ∨ T = S := by simpa using hT.1.1
  rcases ht with rfl | rfl
  · exact hsr (hT.2 hS)
  · exact hrs (hT.2 hR)

/-- An unrestricted infinite declared family may lack even a maximal
content-preserving equivalence. The witness successively merges longer initial
segments of the natural numbers. No physical admissibility is asserted. -/
theorem infinite_family_without_maximal :
    ∃ A : Set (Setoid ℕ),
      (contentPreservingFamily A (fun _ => ())).Nonempty ∧
      ∀ R ∈ contentPreservingFamily A (fun _ => ()),
        ∃ S ∈ contentPreservingFamily A (fun _ => ()), R < S := by
  let E : ℕ → Setoid ℕ := fun n => Setoid.ker (fun k : ℕ => k - n)
  let A : Set (Setoid ℕ) := Set.range E
  have hm (n : ℕ) : E n ∈ contentPreservingFamily A (fun _ => ()) :=
    ⟨⟨n, rfl⟩, fun _ _ _ => rfl⟩
  refine ⟨A, ⟨E 0, hm 0⟩, ?_⟩
  intro R hR
  obtain ⟨n, rfl⟩ := hR.1
  refine ⟨E (n + 1), hm (n + 1), ?_⟩
  apply lt_of_le_not_ge
  · intro x y hxy
    change x - n = y - n at hxy
    change x - (n + 1) = y - (n + 1)
    omega
  · intro h
    have hh := h (x := 0) (y := n + 1)
      (show E (n + 1) 0 (n + 1) by change 0 - (n + 1) = (n + 1) - (n + 1); omega)
    change 0 - n = (n + 1) - n at hh
    omega

end Ordering

end KTAIT.ClosureExtensions
