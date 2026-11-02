/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List

/-!
# Effective answer tables and their description bound (WP0215)

A fixed partial-recursive evaluator takes a finite model description and an
input index. Sequentially evaluating the first n inputs is itself
partial-recursive. A selected model that answers every input therefore produces
its complete answer prefix, without a supplied running-time bound.

The complexity bound uses the standard conditional description principle for
all partial-recursive maps, stated as a named Prop hypothesis. Its constant is
chosen for the fixed answer-table interpreter before the model, task, and prefix
length. No optimal prefix machine is constructed here. The module does not
formalize the finite-packing mechanism or its lattice interpretation.
-/

namespace KTAIT.AnswerTableCoding

abbrev Bits := List Bool

/-- The first n answers of a total binary task, in input order. -/
def answers (f : ℕ → Bool) (n : ℕ) : Bits := (List.range n).map f

/-- Sequentially collect the first n answers. Undefined evaluations remain
undefined; there is no default answer or finite runtime cutoff. -/
def collect (evaluate : Bits → ℕ →. Bool) (m : Bits) : ℕ →. Bits
  | 0 => Part.some []
  | n + 1 => (collect evaluate m n).bind fun xs =>
      (evaluate m n).map fun b => xs ++ [b]

/-- A selected model computes every answer of a task. Other model descriptions
may fail to halt. -/
def Realizes (evaluate : Bits → ℕ →. Bool) (m : Bits) (f : ℕ → Bool) : Prop :=
  ∀ n, f n ∈ evaluate m n

/-- The finite-prefix interpreter is genuinely partial-recursive whenever its
individual-answer evaluator is partial-recursive. -/
theorem collect_partrec (evaluate : Bits → ℕ →. Bool)
    (he : Partrec₂ evaluate) : Partrec₂ (collect evaluate) := by
  have step : Partrec₂ (fun (a : Bits × ℕ) (s : ℕ × Bits) =>
      (evaluate a.1 s.1).map fun b => s.2 ++ [b]) := by
    exact ((he.comp (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd)).map
      (Computable.list_concat.comp (Computable.snd.comp <| Computable.snd.comp Computable.fst)
        Computable.snd).to₂).to₂
  apply (Partrec.nat_rec Computable.snd (Partrec.const' (Part.some [])) step).of_eq
  intro a
  induction a.2 with
  | zero => rfl
  | succ n ih => simp only [ih, collect]

/-- Totality is needed only at the selected model. The computed list is exactly
the task's first n answers, not merely a list of the correct length. -/
theorem collect_correct (evaluate : Bits → ℕ →. Bool) (m : Bits)
    (f : ℕ → Bool) (hf : Realizes evaluate m f) (n : ℕ) :
    collect evaluate m n = Part.some (answers f n) := by
  induction n with
  | zero => simp [collect, answers]
  | succ n ih =>
    have he : evaluate m n = Part.some (f n) := Part.eq_some_iff.mpr (hf n)
    simp [collect, ih, he, answers, List.range_succ]

/-- Restricting the partial evaluator to a selected total model gives an
ordinary computable total task. -/
theorem realized_task_computable (evaluate : Bits → ℕ →. Bool)
    (he : Partrec₂ evaluate) (m : Bits) (f : ℕ → Bool)
    (hf : Realizes evaluate m f) : Computable f :=
  (he.comp (Computable.const m) Computable.id).of_eq_tot hf

/-- The output prefix contains precisely n answers. -/
theorem answers_length (f : ℕ → Bool) (n : ℕ) : (answers f n).length = n := by
  simp [answers]

/-- If the evaluator is total uniformly over all models, the resulting
model-and-length answer-table function is computable. -/
theorem answer_table_computable (evaluate : Bits → ℕ → Bool)
    (he : Computable₂ evaluate) : Computable₂ (fun m n => answers (evaluate m) n) := by
  apply (collect_partrec (fun m n => Part.some (evaluate m n)) he.partrec₂).of_eq_tot
  intro a
  have h := collect_correct (fun m n => Part.some (evaluate m n)) a.1 (evaluate a.1)
    (fun _ => Part.mem_some _) a.2
  rw [h]
  exact Part.mem_some _

/-- Standard conditional prefix coding for every partial-recursive binary-input
map. The auxiliary input n is supplied; the program supplies a shortest
unconditional description of m. The interpreter's overhead is uniform in m,n.
This is a named AIT principle, not an assumption about answer tables. -/
def UniformConditionalMapLaw (K : Bits → ℕ) (CK : Bits → ℕ → ℕ) : Prop :=
  ∀ g : Bits × ℕ →. Bits, Partrec g →
    ∃ c : ℕ, ∀ m n out, out ∈ g (m, n) → CK out n ≤ K m + c

/-- A fixed answer interpreter gives K(A_f restricted to n | n) ≤ K(m)+c.
The same constant works for all selected total models, tasks, and prefix lengths;
invalid or nonterminating model codes need not denote total computations. -/
theorem answer_prefix_complexity (K : Bits → ℕ) (CK : Bits → ℕ → ℕ)
    (hcoding : UniformConditionalMapLaw K CK)
    (evaluate : Bits → ℕ →. Bool) (he : Partrec₂ evaluate) :
    ∃ c : ℕ, ∀ m f, Realizes evaluate m f →
      ∀ n, CK (answers f n) n ≤ K m + c := by
  obtain ⟨c, hc⟩ := hcoding (fun a => collect evaluate a.1 a.2)
    (collect_partrec evaluate he)
  refine ⟨c, fun m f hf n => hc m n (answers f n) ?_⟩
  rw [collect_correct evaluate m f hf n]
  exact Part.mem_some _

/-- Specialization to a uniformly total evaluator retains the same uniform
constant over its entire model family. -/
theorem total_evaluator_complexity (K : Bits → ℕ) (CK : Bits → ℕ → ℕ)
    (hcoding : UniformConditionalMapLaw K CK)
    (evaluate : Bits → ℕ → Bool) (he : Computable₂ evaluate) :
    ∃ c : ℕ, ∀ m n, CK (answers (evaluate m) n) n ≤ K m + c := by
  obtain ⟨c, hc⟩ := answer_prefix_complexity K CK hcoding
    (fun m n => Part.some (evaluate m n)) he.partrec₂
  exact ⟨c, fun m n => hc m (evaluate m) (fun _ => Part.mem_some _) n⟩

end KTAIT.AnswerTableCoding
