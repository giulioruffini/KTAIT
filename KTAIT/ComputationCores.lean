/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import Mathlib.Data.List.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# Deterministic computation cores (WP0229)

Operation labels may include inputs and interventions. Whole finite-word behavior,
accessibility and observability yield a state conjugacy. Commuting atomic overwrites
then force its coordinate form. These are mathematical existence results, not an
algorithm deciding equality of arbitrary programs or a claim about physical access.
-/

namespace KTAIT.ComputationCores

variable {S R A Y : Type*}

/-- Operations are applied from left to right in the list. -/
def run (step : A → S → S) (s : S) (w : List A) : S :=
  w.foldl (fun x a => step a x) s

private theorem run_append (step : A → S → S) (s : S) (v w : List A) :
    run step s (v ++ w) = run step (run step s v) w := by
  simp [run, List.foldl_append]

/-- Intertwining each admitted operation intertwines every composite experiment. -/
theorem run_intertwines (step : A → S → S) (next : A → R → R) (h : S → R)
    (commute : ∀ a s, h (step a s) = next a (h s)) (s : S) (w : List A) :
    h (run step s w) = run next (h s) w := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => simpa [run, List.foldl_cons, commute] using ih (step a s)

/-- With matching readouts, composite experiments have matching outputs. -/
theorem experiment_outputs (step : A → S → S) (next : A → R → R) (h : S → R)
    (out : S → Y) (readout : R → Y)
    (commute : ∀ a s, h (step a s) = next a (h s))
    (observe : ∀ s, readout (h s) = out s) (s : S) (w : List A) :
    readout (run next (h s) w) = out (run step s w) := by
  rw [← run_intertwines step next h commute, observe]

def Accessible (step : A → S → S) (s₀ : S) : Prop :=
  ∀ s, ∃ w, run step s₀ w = s

def Observable (step : A → S → S) (out : S → Y) : Prop :=
  ∀ s t, (∀ w, out (run step s w) = out (run step t w)) → s = t

private theorem histories_match (step : A → S → S) (next : A → R → R)
    (out : S → Y) (readout : R → Y) (s₀ : S) (r₀ : R)
    (obs : Observable next readout)
    (same : ∀ w, out (run step s₀ w) = readout (run next r₀ w))
    (v w : List A) (eqStates : run step s₀ v = run step s₀ w) :
    run next r₀ v = run next r₀ w := by
  apply obs
  intro z
  rw [← run_append, ← run_append, ← same, ← same,
    run_append, run_append, eqStates]

/-- Equal complete behavior determines an accessible observable realization up to
state conjugacy. No state finiteness, effective minimization, component structure,
or intervention access is inferred from these hypotheses. -/
theorem observable_conjugacy (step : A → S → S) (next : A → R → R)
    (out : S → Y) (readout : R → Y) (s₀ : S) (r₀ : R)
    (reachS : Accessible step s₀) (reachR : Accessible next r₀)
    (obsS : Observable step out) (obsR : Observable next readout)
    (same : ∀ w, out (run step s₀ w) = readout (run next r₀ w)) :
    ∃ h : S ≃ R, h s₀ = r₀ ∧
      (∀ a s, h (step a s) = next a (h s)) ∧
      (∀ s, readout (h s) = out s) := by
  classical
  let word : S → List A := fun s => Classical.choose (reachS s)
  have reaches (s : S) : run step s₀ (word s) = s := Classical.choose_spec (reachS s)
  let h : S → R := fun s => run next r₀ (word s)
  have on_history (w : List A) : h (run step s₀ w) = run next r₀ w := by
    exact histories_match step next out readout s₀ r₀ obsR same
      (word (run step s₀ w)) w (reaches _)
  have injective : Function.Injective h := by
    intro s t eqh
    apply obsS
    intro z
    rw [← reaches s, ← reaches t, ← run_append, ← run_append,
      same, same, run_append, run_append]
    change readout (run next (h s) z) = readout (run next (h t) z)
    rw [eqh]
  have surjective : Function.Surjective h := by
    intro r
    obtain ⟨w, hw⟩ := reachR r
    exact ⟨run step s₀ w, (on_history w).trans hw⟩
  refine ⟨Equiv.ofBijective h ⟨injective, surjective⟩, ?_, ?_, ?_⟩
  · exact on_history []
  · intro a s
    change h (step a s) = next a (h s)
    have hw := on_history (word s ++ [a])
    rw [run_append, run_append] at hw
    change h (step a (run step s₀ (word s))) = next a (h s) at hw
    rwa [reaches] at hw
  · intro s
    change readout (run next r₀ (word s)) = out s
    rw [← same, reaches]

/-- On an accessible machine a transition-preserving initialized comparison is unique. -/
theorem initialized_intertwiner_unique (step : A → S → S) (next : A → R → R)
    (s₀ : S) (reach : Accessible step s₀) (h g : S → R)
    (start : h s₀ = g s₀)
    (hc : ∀ a s, h (step a s) = next a (h s))
    (gc : ∀ a s, g (step a s) = next a (g s)) : h = g := by
  funext s
  obtain ⟨w, rfl⟩ := reach s
  rw [run_intertwines step next h hc, run_intertwines step next g gc, start]

/-- Once every coordinate overwrite commutes, the state comparison has the
declared component form. A component permutation is absorbed by reindexing Z. -/
theorem overwrite_rigidity {I : Type*} [DecidableEq I] {X Z : I → Type*}
    (h : ((i : I) → X i) → ((i : I) → Z i)) (φ : (i : I) → X i → Z i)
    (commute : ∀ x i a, h (Function.update x i a) =
      Function.update (h x) i (φ i a)) :
    ∀ x i, h x i = φ i (x i) := by
  intro x i
  have hx := congrFun (commute x i (x i)) i
  simpa using hx

end KTAIT.ComputationCores
