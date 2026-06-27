/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib

/-!
# KTAIT.CoarseGraining — regulatory coarse-graining is uncomputable (Phase 5)

WP0193 Theorem B / Corollary B. The optimal regulation-sufficient projection `π*` cannot be
computed by any algorithm. The argument is a REDUCTION: a correct *targeted* sufficient-
projection solver, specialized to `y := x`, would compute the ordinary Kolmogorov structure
function / minimal sufficient statistic — which Vereshchagin–Vitányi proves is uncomputable.

Computability is modeled abstractly: `CompT` / `CompS` are predicates "this solver is
computable" on the two solver shapes, and the reduction is captured by `ReductionClosure`
(specializing a computable targeted solver yields a computable structure-function solver).
Vereshchagin–Vitányi enters as the single named axiom `VV` (`¬ CompS sf₀`). This is the
honest Level-1 reading: the uncomputability *reduces* to V–V; we do not re-prove V–V.
-/

namespace KTAIT
namespace CoarseGraining

variable {S : Type}

/-- Specialize a targeted solver `T x y α` to the ordinary structure-function solver by
    setting the target equal to the object, `y := x`. -/
def specialize (T : S → S → ℕ → S) : S → ℕ → S := fun x α => T x x α

variable (CompT : (S → S → ℕ → S) → Prop) (CompS : (S → ℕ → S) → Prop)

/-- The reduction mechanism: specializing a *computable* targeted solver (`y := x`) yields a
    *computable* structure-function solver. -/
def ReductionClosure : Prop := ∀ T, CompT T → CompS (specialize T)

/-- **Vereshchagin–Vitányi** (the single axiom): the ordinary structure function / minimal
    sufficient statistic `sf₀` is not computable. -/
def VV (sf0 : S → ℕ → S) : Prop := ¬ CompS sf0

/-- **Theorem B (targeted sufficient projection is uncomputable).** Any *correct* targeted
    solver `T` (one whose `y := x` specialization is the structure function `sf₀`) is not
    computable — by reduction to Vereshchagin–Vitányi. -/
theorem theoremB {sf0 : S → ℕ → S}
    (hred : ReductionClosure CompT CompS) (hvv : VV CompS sf0)
    {T : S → S → ℕ → S} (hcorrect : specialize T = sf0) : ¬ CompT T := by
  intro hT
  have h1 : CompS (specialize T) := hred T hT
  rw [hcorrect] at h1
  exact hvv h1

/-- **Corollary B (regulatory coarse-graining is uncomputable).** The optimal regulation-
    sufficient projection `π` (a targeted sufficient projection from `Aₜ` to `Yₜ`, whose
    `Yₜ := Aₜ` specialization is the structure function) is not computable. -/
theorem corollaryB {sf0 : S → ℕ → S}
    (hred : ReductionClosure CompT CompS) (hvv : VV CompS sf0)
    {π : S → S → ℕ → S} (hcorrect : specialize π = sf0) : ¬ CompT π :=
  theoremB CompT CompS hred hvv hcorrect

/-- **Theorem A (selection uncomputability).** Selecting an optimal sufficient regulator is
    uncomputable — the same reduction to Vereshchagin–Vitányi as `theoremB` (a correct selection
    solver, specialized to `y := x`, computes the structure function). -/
theorem theoremA {sf0 : S → ℕ → S}
    (hred : ReductionClosure CompT CompS) (hvv : VV CompS sf0)
    {Sel : S → S → ℕ → S} (hcorrect : specialize Sel = sf0) : ¬ CompT Sel :=
  theoremB CompT CompS hred hvv hcorrect

/-- **WP0193 Proposition 1 (existence).** A persistent agent carrying a bounded,
    regulation-sufficient self-code witnesses a bounded regulation-sufficient projection — so the
    optimization of Definition 2 is over a non-empty set. -/
theorem existence {Proj : Type} {RegSuff : Proj → Prop} {cost : Proj → ℕ} {K0 : ℕ}
    (selfCode : Proj) (hsuff : RegSuff selfCode) (hbound : cost selfCode ≤ K0) :
    ∃ π, RegSuff π ∧ cost π ≤ K0 :=
  ⟨selfCode, hsuff, hbound⟩

end CoarseGraining
end KTAIT
