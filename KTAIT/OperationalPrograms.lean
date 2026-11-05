/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import Mathlib

/-!
# Six multiplication programs (WP0004)

The source instructions retain mutable registers. Graph extraction versions each
write; graph isomorphism retains multiplicity, the input, and the output, but
does not retain the order in which the two operands are listed.
-/

namespace KTAIT.OperationalPrograms

abbrev Register := Fin 6
abbrev Instruction := Register × Register × Register
abbrev Edge := Fin 6 × Fin 6

/-- Destination, left operand, right operand; register zero is the input. -/
def programs : Fin 6 → List Instruction := ![
  [(1,0,0),(2,1,0),(3,2,2),(4,3,3),(5,4,2)],
  [(4,0,0),(3,4,0),(2,3,3),(1,2,2),(5,1,3)],
  [(1,0,0),(2,1,0),(1,2,2),(1,1,1),(5,1,2)],
  [(1,0,0),(2,1,1),(3,2,0),(4,3,3),(5,4,3)],
  [(4,0,0),(3,4,4),(2,3,0),(1,2,2),(5,1,2)],
  [(1,0,0),(1,1,1),(2,1,0),(1,2,2),(5,1,2)]]

def runRegisters : List Instruction → (Register → ℝ) → Register → ℝ
  | [], s => s
  | (d,l,r) :: rest, s => runRegisters rest (Function.update s d (s l * s r))

def denotation (i : Fin 6) (x : ℝ) : ℝ :=
  runRegisters (programs i) (fun r => if r = 0 then x else 0) 5

/-- All six mutable-register programs compute the same real polynomial. -/
theorem six_program_denotations (i : Fin 6) (x : ℝ) : denotation i x = x ^ 15 := by
  fin_cases i <;> simp [denotation, programs, runRegisters] <;> ring

/-- The chosen six source descriptions are pairwise different. -/
theorem six_distinct_programs : Function.Injective programs := by decide

/-- Every permutation of this universe preserves the polynomial denotation. -/
theorem all_permutations_preserve_function (σ : Equiv.Perm (Fin 6)) (i : Fin 6) (x : ℝ) :
    denotation (σ i) x = denotation i x := by simp [six_program_denotations]

def extractFrom : List Instruction → (Register → Fin 6) → Fin 6 →
    List Edge × (Register → Fin 6)
  | [], versions, _ => ([], versions)
  | (d,l,r) :: rest, versions, next =>
      let tail := extractFrom rest (Function.update versions d next) (next + 1)
      ((versions l, versions r) :: tail.1, tail.2)

def extracted (i : Fin 6) : List Edge × Fin 6 :=
  let result := extractFrom (programs i) (fun _ => 0) 1
  (result.1, result.2 5)

def graphA : List Edge := [(0,0),(1,0),(2,2),(3,3),(4,2)]
def graphB : List Edge := [(0,0),(1,1),(2,0),(3,3),(4,3)]

/-- Versioned extraction retains the actual two operation graphs through storage reuse. -/
theorem extracted_graphs : ∀ i : Fin 6,
    extracted i = (if i.val < 3 then graphA else graphB, 5) := by decide

/-- Number of operand incidences from vertex `i` into multiplication vertex `j`. -/
def incidence (edges : List Edge) (i j : Fin 6) : ℕ :=
  if j = 0 then 0 else
    let p := edges[j.val - 1]?.getD (0,0)
    (if i = p.1 then 1 else 0) + (if i = p.2 then 1 else 0)

def GraphIso (a b : List Edge × Fin 6) : Prop :=
  ∃ σ : Equiv.Perm (Fin 6), σ 0 = 0 ∧ σ a.2 = b.2 ∧
    ∀ i j, incidence a.1 i j = incidence b.1 (σ i) (σ j)

instance (a b : List Edge × Fin 6) : Decidable (GraphIso a b) := inferInstanceAs
  (Decidable (∃ σ : Equiv.Perm (Fin 6), σ 0 = 0 ∧ σ a.2 = b.2 ∧
    ∀ i j, incidence a.1 i j = incidence b.1 (σ i) (σ j)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel enumeration of the 720 vertex permutations checks the marked graphs themselves.
theorem distinct_multiplication_graphs : ¬ GraphIso (graphA,5) (graphB,5) := by decide

/-- Graph identity is always a marked graph isomorphism. -/
theorem graph_iso_refl (g : List Edge × Fin 6) : GraphIso g g :=
  ⟨1, rfl, rfl, fun _ _ => rfl⟩

/-- Reversing a graph isomorphism preserves the same incidence equations. -/
theorem graph_iso_symm (a b : List Edge × Fin 6) (h : GraphIso a b) : GraphIso b a := by
  obtain ⟨σ, h0, ho, he⟩ := h
  refine ⟨σ.symm, ?_, ?_, ?_⟩
  · exact σ.symm_apply_eq.mpr h0.symm
  · exact σ.symm_apply_eq.mpr ho.symm
  · intro i j
    simpa using (he (σ.symm i) (σ.symm j)).symm

/-- The exact isomorphism partition of the extracted graphs has two classes. -/
theorem graph_classification (i j : Fin 6) :
    GraphIso (extracted i) (extracted j) ↔ (i.val < 3 ↔ j.val < 3) := by
  rw [extracted_graphs i, extracted_graphs j]
  by_cases hi : i.val < 3 <;> by_cases hj : j.val < 3 <;> simp only [hi, hj, if_true, if_false]
  · exact iff_of_true (graph_iso_refl _) (by simp)
  · exact iff_of_false distinct_multiplication_graphs (by simp)
  · exact iff_of_false (fun h => distinct_multiplication_graphs (graph_iso_symm _ _ h)) (by simp)
  · exact iff_of_true (graph_iso_refl _) (by simp)

def renameInstruction (σ : Equiv.Perm Register) (i : Instruction) : Instruction :=
  (σ i.1, σ i.2.1, σ i.2.2)

/-- A storage comparison is a single bijective register renaming fixing the interface. -/
def StorageIso (i j : Fin 6) : Prop :=
  ∃ σ : Equiv.Perm Register, σ 0 = 0 ∧ σ 5 = 5 ∧
    (programs i).map (renameInstruction σ) = programs j

instance (i j : Fin 6) : Decidable (StorageIso i j) := inferInstanceAs
  (Decidable (∃ σ : Equiv.Perm Register, σ 0 = 0 ∧ σ 5 = 5 ∧
    (programs i).map (renameInstruction σ) = programs j))

def storageClass : Fin 6 → Fin 4 := ![0,0,1,2,2,3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Register permutations are checked against complete instruction lists, including overwrites.
theorem storage_classification : ∀ i j : Fin 6,
    StorageIso i j ↔ storageClass i = storageClass j := by decide

/-- The marked graph partition computed above. -/
def graphClass (i : Fin 6) : Fin 2 := if i.val < 3 then 0 else 1

/-- Class-preserving permutations act within each block, never exchanging blocks. -/
def classPreservers {C : Type*} [DecidableEq C] (c : Fin 6 → C) : Finset (Equiv.Perm (Fin 6)) :=
  Finset.univ.filter (fun σ => ∀ i, c (σ i) = c i)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- These are the exact cardinalities of the finite class-preserving permutation sets.
theorem hierarchy_group_orders :
    (classPreservers (fun i : Fin 6 => i)).card = 1 ∧
    (classPreservers storageClass).card = 4 ∧
    (classPreservers graphClass).card = 36 ∧
    (classPreservers (fun _ : Fin 6 => ())).card = 720 := by decide

end KTAIT.OperationalPrograms
