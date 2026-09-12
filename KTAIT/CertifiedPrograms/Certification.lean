/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import KTAIT.CertifiedPrograms.Encoding
import Mathlib.Computability.Partrec
import Mathlib.Data.Nat.Find

/-!
# Whole-function semantics and a typed certification interface (WP0228)

`Part` equality records both domain and value. The minimum ranges over every source string,
not just certified alternatives. A certification object must carry a genuine `Computable`
proof for its optional-pair stream. The module does not instantiate an optimal prefix-coded
evaluator or claim soundness of any particular proof theory.
-/

namespace KTAIT.CertifiedPrograms

variable {Input Output : Type}

abbrev ProgramSemantics (Input Output : Type) := CodeBits → Input → Part Output

structure Certification (V : ProgramSemantics Input Output) where
  related : CodeBits → CodeBits → Prop
  equivalence : Equivalence related
  stream : Nat → Option (CodeBits × CodeBits)
  streamComputable : Computable stream
  stream_sound : ∀ j p q, stream j = some (p, q) → related p q
  stream_complete : ∀ p q, related p q → ∃ j, stream j = some (p, q)
  semantic_sound : ∀ p q, related p q → V p = V q

private theorem implementation_exists (V : ProgramSemantics Input Output) (p : CodeBits) :
    ∃ n, ∃ r : CodeBits, r.length = n ∧ V r = V p :=
  ⟨p.length, p, rfl, rfl⟩

/-- The unrestricted minimum for the whole partial function implemented by p. -/
noncomputable def wholeFunctionComplexity (V : ProgramSemantics Input Output)
    (p : CodeBits) : Nat := by
  classical
  exact Nat.find (implementation_exists V p)

theorem whole_function_minimum_exists (V : ProgramSemantics Input Output) (p : CodeBits) :
    ∃ r : CodeBits, r.length = wholeFunctionComplexity V p ∧ V r = V p := by
  classical
  exact Nat.find_spec (implementation_exists V p)

theorem whole_function_minimum_le (V : ProgramSemantics Input Output) (p r : CodeBits)
    (hr : V r = V p) : wholeFunctionComplexity V p ≤ r.length := by
  classical
  exact Nat.find_min' (implementation_exists V p) ⟨r, rfl, hr⟩

/-- Equality is equality of the whole partial function, including its domain. -/
theorem whole_function_minimum_congr (V : ProgramSemantics Input Output) (p q : CodeBits)
    (hpq : V p = V q) : wholeFunctionComplexity V p = wholeFunctionComplexity V q := by
  obtain ⟨rp, hlp, hsp⟩ := whole_function_minimum_exists V p
  obtain ⟨rq, hlq, hsq⟩ := whole_function_minimum_exists V q
  apply Nat.le_antisymm
  · rw [← hlq]
    exact whole_function_minimum_le V p rq (hsq.trans hpq.symm)
  · rw [← hlp]
    exact whole_function_minimum_le V q rp (hsp.trans hpq)

/-- Two certificates to the same reference implementation compose within the fixed relation. -/
theorem certificates_to_common_reference (V : ProgramSemantics Input Output)
    (C : Certification V) (p q r : CodeBits)
    (hp : C.related p r) (hq : C.related q r) : C.related p q :=
  C.equivalence.trans hp (C.equivalence.symm hq)

end KTAIT.CertifiedPrograms
