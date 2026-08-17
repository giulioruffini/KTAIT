/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic
import KTAIT.RegulationBalance

/-!
# KTAIT.GroundedRegulation — the repaired static-MAI corollary (WP0203 grounded exposition)

The withdrawn ART concentration corollary tried to read a large readout gap `Δ = K y − K x`
as forcing large static mutual algorithmic information `I_K(W:R)`. Two loopholes block the
inference: the readout can be simplified without simplifying the world variable it measures
(sensor hacking), and a simple intervention can drive the genuine reguland through a
many-to-one plant map (the blind clamp). This module formalizes the repair:

* a **grounding** condition ties the ART readouts `x, y` to a designated reguland's
  trajectories `z, z₀` up to tolerance `ε` (algorithmic information distance, both episodes);
* the **counterfactual residual** `L_Z = K(z₀ | ⟨z,R⟩)` is the exact obstruction;
* the **grounded regulator inequality** `Δ_Z ≤ I_K(z₀:R) + L_Z + slack
  ≤ I_K(W:R) + L_Z + slack`;
* the **repaired corollary** `I_K(W:R) ≥ Δ − L_Z − 2ε − slack` under grounding;
* the **ceiling** `I_K(W:R) ≤ K R + slack` turns the inequality around: a simple regulator
  opening an extensive grounded gap is *forced* to have an extensive residual
  (`L_Z ≥ Δ_Z − K R − slack`, the clamp regime);
* under the WP0203 closure, the residual **is** the completion term,
  `|L_Z − M(z₀:Q | ⟨z,R⟩)| ≤ slack` — so the repaired corollary and the regulation balance
  are two views of the same accounting.

The hypotheses are the same frame-level AIT facts as `KTAIT.RegulationBalance`
(`MutualChain`, `CondSubadd`, `CondMono`, `CondChain`, `InfoClosed`, `DataProcessing`), plus
plain subadditivity `Subadd`, the pair monotonicity `PairMono`, and the standard MAI ceiling
`IKCeiling`. As throughout KTAIT, they are named hypotheses about a frame, never global
axioms; everything below is `Int` arithmetic once they are supplied.

The asymptotic form `I_K(W:R) ≥ (1−o(1))Δ` and the `Θ(N)` reading are analysis on top of
the finite inequalities and are deliberately not formalized, as with the rate form of
`RegulationBalance`.
-/

namespace KTAIT
namespace GroundedRegulation

open RegulationBalance

variable (F : AITFrame)

/-! ## Grounding and the counterfactual residual -/

/-- **Plain subadditivity**: `K a ≤ K b + K(a|b) + slack`. -/
def Subadd (a b : F.Obj) : Prop :=
  (F.K a : Int) ≤ (F.K b : Int) + (F.cond a b : Int) + (F.slack : Int)

/-- **`ε`-grounded readout.** The scored ART outputs and the designated reguland
    trajectories determine one another up to `ε`, in both the ON episode (`x ↔ z`) and the
    OFF episode (`y ↔ z₀`). This is a small algorithmic information *distance*, not a large
    shared complexity — the right condition when successful regulation makes both `z` and
    `x` nearly constant. -/
def Grounded (x y z z0 : F.Obj) (eps : Int) : Prop :=
  (F.cond z x : Int) ≤ eps ∧ (F.cond x z : Int) ≤ eps ∧
  (F.cond z0 y : Int) ≤ eps ∧ (F.cond y z0 : Int) ≤ eps

/-- **Counterfactual residual** `L_Z = K(z₀ | ⟨z,R⟩)`: the bits still needed to specify the
    null-regulator reguland trajectory once the regulated trajectory and the regulator
    program are known. In the blind clamp, `L_Z = K(η | 0^N, R) = N − O(log N)`. -/
def residual (z z0 R : F.Obj) : Int := (F.cond z0 (F.pair z R) : Int)

/-! ## Gap transfer: grounding blocks the thermometer hack -/

/-- **Proposition (gap transfer).** Under grounding, the ART readout gap and the genuine
    reguland gap `Δ_Z = K z₀ − K z` agree up to `2ε + 2·slack`. A simple `x` cannot coexist
    with an algorithmically rich `z`. -/
theorem gap_transfer (x y z z0 : F.Obj) (eps : Int)
    (hg : Grounded F x y z z0 eps)
    (hzx : Subadd F z x) (hxz : Subadd F x z)
    (hz0y : Subadd F z0 y) (hyz0 : Subadd F y z0) :
    |gap F x y - gap F z z0| ≤ 2 * eps + 2 * (F.slack : Int) := by
  obtain ⟨h1, h2, h3, h4⟩ := hg
  simp only [Subadd] at hzx hxz hz0y hyz0
  simp only [gap]
  rw [abs_le]
  omega

/-! ## The grounded regulator inequality -/

/-- **Theorem (grounded regulator inequality), reguland form.**
    `Δ_Z ≤ I_K(z₀:R) + L_Z + 2·slack`. The same chain-rule spine as
    `RegulationBalance.balance_readout`, stopped at the residual instead of closed by `Q`. -/
theorem grounded_readout (z z0 R : F.Obj)
    (hmut : MutualChain F z0 R)
    (hsub : CondSubadd F z z0 R)
    (hmono : CondMono F z R) :
    gap F z z0 ≤ IK F z0 R + residual F z z0 R + 2 * (F.slack : Int) := by
  simp only [MutualChain, CondSubadd, CondMono] at hmut hsub hmono
  simp only [gap, residual]
  omega

/-- **Theorem (grounded regulator inequality), world form.**
    `Δ_Z ≤ I_K(W:R) + L_Z + 3·slack`, since `z₀` is computable from `W` at fixed horizon
    and fixed reguland projection (data processing). -/
theorem grounded_inequality (W z z0 R : F.Obj)
    (hmut : MutualChain F z0 R)
    (hsub : CondSubadd F z z0 R)
    (hmono : CondMono F z R)
    (hdp : DataProcessing F z0 W R) :
    gap F z z0 ≤ IK F W R + residual F z z0 R + 3 * (F.slack : Int) := by
  have h := grounded_readout F z z0 R hmut hsub hmono
  simp only [DataProcessing] at hdp
  omega

/-- **The repaired static-MAI corollary.** For an `ε`-grounded readout,
    `I_K(W:R) ≥ Δ − L_Z − 2ε − 5·slack`: the original Good-Regulator reading is recovered
    exactly when the readout is grounded and the counterfactual residual is small. -/
theorem repaired_corollary (W x y z z0 R : F.Obj) (eps : Int)
    (hg : Grounded F x y z z0 eps)
    (hzx : Subadd F z x) (hxz : Subadd F x z)
    (hz0y : Subadd F z0 y) (hyz0 : Subadd F y z0)
    (hmut : MutualChain F z0 R)
    (hsub : CondSubadd F z z0 R)
    (hmono : CondMono F z R)
    (hdp : DataProcessing F z0 W R) :
    IK F W R ≥ gap F x y - residual F z z0 R - 2 * eps - 5 * (F.slack : Int) := by
  have htr := gap_transfer F x y z z0 eps hg hzx hxz hz0y hyz0
  have hgi := grounded_inequality F W z z0 R hmut hsub hmono hdp
  rw [abs_le] at htr
  omega

/-- **Repaired Good-Regulator corollary.** Grounded and `λ`-non-collapsing
    (`L_Z ≤ λ`) regulation forces `I_K(W:R) ≥ Δ − λ − 2ε − 5·slack`. With
    `λ, ε = o(Δ)` this is the asymptotic `I_K(W:R) ≥ (1−o(1))Δ` of the exposition;
    the limit itself is analysis and is not formalized. -/
theorem repaired_good_regulator (W x y z z0 R : F.Obj) (eps lam : Int)
    (hg : Grounded F x y z z0 eps)
    (hzx : Subadd F z x) (hxz : Subadd F x z)
    (hz0y : Subadd F z0 y) (hyz0 : Subadd F y z0)
    (hmut : MutualChain F z0 R)
    (hsub : CondSubadd F z z0 R)
    (hmono : CondMono F z R)
    (hdp : DataProcessing F z0 W R)
    (hnc : residual F z z0 R ≤ lam) :
    IK F W R ≥ gap F x y - lam - 2 * eps - 5 * (F.slack : Int) := by
  have h := repaired_corollary F W x y z z0 R eps hg hzx hxz hz0y hyz0 hmut hsub hmono hdp
  omega

/-! ## Self-regulation: grounded self-regulation forces an implicit self-model

WP0203 v13, Corollary (implicit self-model from grounded self-regulation). The query is
role-relative: the focal agent pattern decomposes as `P = R ∪ H` with `R ∩ H = ∅`, the
reguland projection `ζ^P` tracks the self-side region `H`, and
`SM^imp_{P,N}(R) := M(ζ^P_∅ : R | C)` is the implicit task-relevant self-model content.
At the AIT-shadow level this is the same string inequality as the grounded regulator
inequality with `z := ζ^P_R`, `z₀ := ζ^P_∅`, and `IK z₀ R` read as `SM^imp`; the
decomposition of `P` and the word "self" are manuscript semantics and are deliberately not
encoded as new ontology. No new axiom, and no claim of explicit symbolic
self-representation. -/

/-- **Corollary (implicit self-model from grounded self-regulation), reguland form.**
    `SM^imp ≥ Δ_Z − L_Z − 2·slack`: reading `z, z₀` as the regulated and matched-null
    self-side reguland trajectories `ζ^P_R, ζ^P_∅`, successful self-regulation with a small
    counterfactual residual forces reusable information about the focal pattern's own
    counterfactual trajectory into the regulating organization. A rearrangement of
    `grounded_readout`; nothing here says the self-model is explicit, complete, or
    self-targeting. -/
theorem self_regulation_forces_self_model (z z0 R : F.Obj)
    (hmut : MutualChain F z0 R)
    (hsub : CondSubadd F z z0 R)
    (hmono : CondMono F z R) :
    IK F z0 R ≥ gap F z z0 - residual F z z0 R - 2 * (F.slack : Int) := by
  have h := grounded_readout F z z0 R hmut hsub hmono
  omega

/-- **Corollary, grounded form.** If the scored readout `x, y` is additionally `ε`-grounded
    in the self-side reguland `z, z₀`, the bound transfers to the scored gap:
    `SM^imp ≥ Δ − L_Z − 2ε − 4·slack`. Composition of
    `self_regulation_forces_self_model` with `gap_transfer`. -/
theorem self_regulation_forces_self_model_grounded (x y z z0 R : F.Obj) (eps : Int)
    (hg : Grounded F x y z z0 eps)
    (hzx : Subadd F z x) (hxz : Subadd F x z)
    (hz0y : Subadd F z0 y) (hyz0 : Subadd F y z0)
    (hmut : MutualChain F z0 R)
    (hsub : CondSubadd F z z0 R)
    (hmono : CondMono F z R) :
    IK F z0 R ≥ gap F x y - residual F z z0 R - 2 * eps - 4 * (F.slack : Int) := by
  have htr := gap_transfer F x y z z0 eps hg hzx hxz hz0y hyz0
  have h := grounded_readout F z z0 R hmut hsub hmono
  rw [abs_le] at htr
  omega

/-! ## The ceiling: a simple regulator is forced into an extensive residual -/

/-- **MAI ceiling**: `I_K(W:R) ≤ K R + slack`, since `K(⟨W,R⟩) ≥ K W − O(1)`.
    Standard; named hypothesis. -/
def IKCeiling (W R : F.Obj) : Prop := IK F W R ≤ (F.K R : Int) + (F.slack : Int)

/-- **Corollary (simple regulator forces counterfactual residual).**
    `L_Z ≥ Δ_Z − K R − 4·slack`. If `K R = O(1)` while `Δ_Z = Θ(N)`, then `L_Z = Θ(N)`:
    the blind clamp/AC regime classified. No horizon-uniform `I_K(W:R) ≍ Δ_N` can hold for
    a fixed finite regulator — static model content is reusable, cumulative regulation
    benefit is not. -/
theorem simple_regulator_forces_residual (W z z0 R : F.Obj)
    (hmut : MutualChain F z0 R)
    (hsub : CondSubadd F z z0 R)
    (hmono : CondMono F z R)
    (hdp : DataProcessing F z0 W R)
    (hceil : IKCeiling F W R) :
    residual F z z0 R ≥ gap F z z0 - (F.K R : Int) - 4 * (F.slack : Int) := by
  have h := grounded_inequality F W z z0 R hmut hsub hmono hdp
  simp only [IKCeiling] at hceil
  omega

/-! ## Closure holds by construction in abstract ART

WP0203 v10, Remark (automatic closure): in the deterministic Turing-pair idealization the
persistent world description is instantiated in the realized world-side record `S`, and the
null readout is computable from that description. An information-closing record therefore
exists by construction; closure becomes a substantive physical hypothesis only when ART is
instantiated with a chosen boundary that may omit an information-bearing degree. -/

/-- **Conditional composition**: `K(y|S) ≤ K(W|S) + K(y|W) + slack` — describe `W` from
    `S`, then `y` from `W`. Standard; named hypothesis. -/
def CondCompose (y W S : F.Obj) : Prop :=
  (F.cond y S : Int) ≤ (F.cond W S : Int) + (F.cond y W : Int) + (F.slack : Int)

/-- **Remark (closure by construction).** If the world description `W` is instantiated in
    the realized world-side record `S` (`K(W|S) ≤ slack`) and the null readout is computable
    from it (`K(y|W) ≤ slack`), then the record closes the accounting even after
    conditioning on the visible episode `C`: `K(y | ⟨S,C⟩) ≤ 3·slack`. Localization and
    minimality still govern which part of `S` may be charged as exhaust. -/
theorem closure_by_construction (y W S C : F.Obj)
    (hinst : (F.cond W S : Int) ≤ (F.slack : Int))
    (hcomp : (F.cond y W : Int) ≤ (F.slack : Int))
    (hchain : CondCompose F y W S)
    (hmono : CondMonoMore F y S C) :
    (F.cond y (F.pair S C) : Int) ≤ 3 * (F.slack : Int) := by
  simp only [CondCompose, CondMonoMore] at hchain hmono
  omega

/-! ## The residual is the WP0203 completion term -/

/-- **Pair monotonicity**: `K(B|C) ≤ K(⟨A,B⟩|C) + slack`, since `B` is computable from the
    pair. Named hypothesis. -/
def PairMono (A B C : F.Obj) : Prop :=
  (F.cond B C : Int) ≤ (F.cond (F.pair A B) C : Int) + (F.slack : Int)

/-- **The residual equals the completion term.** Under the reguland-level closure
    `K(z₀ | ⟨Q,⟨z,R⟩⟩) ≤ slack` with completion `Q = ⟨O_R, σ_R, Ξ⟩`,
    `|L_Z − M(z₀:Q | ⟨z,R⟩)| ≤ 2·slack`. The counterfactual residual is not a new sink: it
    is exactly the null-reguland information carried by the rest of the realized episode.
    The repaired corollary (when `L_Z` is small) and the WP0203 balance (where `L_Z` goes
    when it is not) are two views of the same decomposition. -/
theorem residual_is_completion (z z0 R Q : F.Obj)
    (hchain : CondChain F z0 Q (F.pair z R))
    (hclosed : InfoClosed F z0 Q (F.pair z R))
    (hpm : PairMono F z0 Q (F.pair z R)) :
    |residual F z z0 R - cIK F z0 Q (F.pair z R)| ≤ 2 * (F.slack : Int) := by
  have hupper := residual_in_completion F z0 Q (F.pair z R) hchain hclosed
  simp only [PairMono] at hpm
  simp only [residual, cIK] at *
  rw [abs_le]
  omega

/-- **Grounded balance.** Substituting the completion for the residual in the grounded
    inequality recovers the WP0203 balance at the reguland level:
    `Δ_Z ≤ I_K(W:R) + M(z₀:Q | ⟨z,R⟩) + 5·slack`. (This is
    `RegulationBalance.balance` with `x := z`, `y := z₀`; stated here to record that the
    grounded construction composes with the existing accounting.) -/
theorem grounded_balance (W z z0 R Q : F.Obj)
    (hmut : MutualChain F z0 R)
    (hsub : CondSubadd F z z0 R)
    (hmono : CondMono F z R)
    (hchain : CondChain F z0 Q (F.pair z R))
    (hclosed : InfoClosed F z0 Q (F.pair z R))
    (hdp : DataProcessing F z0 W R) :
    gap F z z0 ≤ IK F W R + cIK F z0 Q (F.pair z R) + 5 * (F.slack : Int) :=
  balance F W z z0 R Q hmut hsub hmono hchain hclosed hdp

/-! ## The exact counterfactual balance (WP0203 v16): the conservation seam

WP0203 v16 foregrounds the equality-level local ledger *before* the GART inequality: the
reguland gap is not merely bounded, it has a full local account,

  `Δ_N^ζ = M(ζ∅:R|C) + L_cf − M(ζR:R|C) − K(ζR|ζ∅,R,C) + O(log N)`,

with `L_cf = K(ζ∅|ζR,R,C)`. Algebraically this is finite-string chain-rule bookkeeping —
two applications of conditional symmetry of information plus the conditional chain-rule
exchange — and it deliberately carries **no reversibility premise**: WP0218's reversible
conservation/localization supplies the physical complete-ledger reading in the manuscripts,
not an algebraic hypothesis here. All quantities are conditioned on the declared common
frame `C`, so the earlier unconditional statements are the same identities read at a
trivial frame. The GART inequality is then re-derived as a *projection* of the equality
(drop the two regulated-branch correction terms, apply conditional data processing), so the
formal dependency graph matches the manuscript narrative: equality → projection →
inequality. -/

/-- **Conditional symmetry of information** (two-sided): `K(a|C)` splits into conditional
    mutual information with `R` plus the doubly-conditioned remainder,
    `|K(a|C) − M(a:R|C) − K(a|⟨R,C⟩)| ≤ slack`. Standard; named hypothesis. -/
def CondSI (a R C : F.Obj) : Prop :=
  |(F.cond a C : Int) - cIK F a R C - (F.cond a (F.pair R C) : Int)| ≤ (F.slack : Int)

/-- **Conditional chain-rule exchange** (two-sided): describing `a` then `b` given `D`
    accounts for the pair the same way as describing `b` then `a`,
    `|(K(a|D) − K(b|D)) − (K(a|⟨b,D⟩) − K(b|⟨a,D⟩))| ≤ slack`. Standard; named
    hypothesis (the "conditional chain-rule symmetry" step of the manuscript proof). -/
def CondExchange (a b D : F.Obj) : Prop :=
  |((F.cond a D : Int) - (F.cond b D : Int))
    - ((F.cond a (F.pair b D) : Int) - (F.cond b (F.pair a D) : Int))| ≤ (F.slack : Int)

/-- **Frame-conditional counterfactual residual** `L_cf = K(z₀|⟨z,⟨R,C⟩⟩)`:
    `GroundedRegulation.residual` with the common frame `C` carried explicitly.
    Definitionally `residual F z z0 (F.pair R C)`; the subtracted regulated-branch term
    `K(ζR|ζ∅,R,C)` of the manuscript is `residualC` with `z` and `z0` exchanged. -/
def residualC (z z0 R C : F.Obj) : Int := residual F z z0 (F.pair R C)

/-- **Proposition (exact counterfactual balance).** Up to ordinary finite-string
    chain-rule slack,

    `Δ_N^ζ = M(ζ∅:R|C) + L_cf − M(ζR:R|C) − K(ζR|ζ∅,R,C)`,

    with `Δ_N^ζ = K(ζ∅|C) − K(ζR|C)` read as `z := ζR`, `z0 := ζ∅`. The equality-level
    local ledger for the declared counterfactual query: nothing vanishes merely because
    the chosen reguland projection has become simpler. Two-sided finite-slack form; no
    reversibility premise. -/
theorem exact_counterfactual_balance (z z0 R C : F.Obj)
    (hz0 : CondSI F z0 R C)
    (hz : CondSI F z R C)
    (hex : CondExchange F z0 z (F.pair R C)) :
    |((F.cond z0 C : Int) - (F.cond z C : Int))
      - (cIK F z0 R C + residualC F z z0 R C
         - cIK F z R C - residualC F z0 z R C)| ≤ 3 * (F.slack : Int) := by
  simp only [CondSI, CondExchange, residualC, residual] at hz0 hz hex ⊢
  rw [abs_le] at hz0 hz hex ⊢
  omega

/-- **Conditional MAI nonnegativity**: `M(a:R|C) ≥ −slack`. Standard; named hypothesis. -/
def MutualNonnegC (a R C : F.Obj) : Prop := -(F.slack : Int) ≤ cIK F a R C

/-- **Conditional data processing**: `ζ∅` computable from `W` at fixed horizon and fixed
    reguland projection gives `M(ζ∅:R|C) ≤ M(W:R|C) + slack`. Standard; named hypothesis. -/
def DataProcessingC (y W R C : F.Obj) : Prop :=
  cIK F y R C ≤ cIK F W R C + (F.slack : Int)

/-- **GART, reguland form, as a projection of the exact balance.** Dropping the two
    regulated-branch correction terms (the residual `K(ζR|ζ∅,R,C) ≥ 0` and, up to slack,
    `M(ζR:R|C) ≥ −slack`) in `exact_counterfactual_balance` yields
    `Δ_N^ζ ≤ M(ζ∅:R|C) + L_cf + 4·slack`. -/
theorem gart_reguland_from_exact_balance (z z0 R C : F.Obj)
    (hz0 : CondSI F z0 R C)
    (hz : CondSI F z R C)
    (hex : CondExchange F z0 z (F.pair R C))
    (hnn : MutualNonnegC F z R C) :
    (F.cond z0 C : Int) - (F.cond z C : Int)
      ≤ cIK F z0 R C + residualC F z z0 R C + 4 * (F.slack : Int) := by
  have h := exact_counterfactual_balance F z z0 R C hz0 hz hex
  rw [abs_le] at h
  simp only [MutualNonnegC] at hnn
  simp only [residualC, residual] at h ⊢
  omega

/-- **GART, world form, as a projection of the exact balance.** Composing with
    conditional data processing for `ζ∅ = f(W)`:
    `Δ_N^ζ ≤ M(W:R|C) + L_cf + 5·slack`. This re-derives the grounded regulator
    inequality from the equality-level ledger, making the formal dependency path match
    the manuscript narrative (`grounded_inequality` remains the C-free statement). -/
theorem grounded_inequality_from_exact_balance (W z z0 R C : F.Obj)
    (hz0 : CondSI F z0 R C)
    (hz : CondSI F z R C)
    (hex : CondExchange F z0 z (F.pair R C))
    (hnn : MutualNonnegC F z R C)
    (hdp : DataProcessingC F z0 W R C) :
    (F.cond z0 C : Int) - (F.cond z C : Int)
      ≤ cIK F W R C + residualC F z z0 R C + 5 * (F.slack : Int) := by
  have h := gart_reguland_from_exact_balance F z z0 R C hz0 hz hex hnn
  simp only [DataProcessingC] at hdp
  omega

/-- **The closed exact ledger.** Substituting `residual_is_completion` (at conditioning
    base `⟨R,C⟩`) into the exact balance: under reguland-level closure with completion
    `Q`, up to `5·slack`,

    `Δ_N^ζ = M(ζ∅:R|C) + M(ζ∅:Q|⟨ζR,R,C⟩) − M(ζR:R|C) − K(ζR|ζ∅,R,C)`.

    The strongest checked expression of "the residual is not a sink": it is exactly the
    matched-null information localized in the complementary realized records. -/
theorem exact_counterfactual_balance_closed (z z0 R C Q : F.Obj)
    (hz0 : CondSI F z0 R C)
    (hz : CondSI F z R C)
    (hex : CondExchange F z0 z (F.pair R C))
    (hchain : CondChain F z0 Q (F.pair z (F.pair R C)))
    (hclosed : InfoClosed F z0 Q (F.pair z (F.pair R C)))
    (hpm : PairMono F z0 Q (F.pair z (F.pair R C))) :
    |((F.cond z0 C : Int) - (F.cond z C : Int))
      - (cIK F z0 R C + cIK F z0 Q (F.pair z (F.pair R C))
         - cIK F z R C - residualC F z0 z R C)| ≤ 5 * (F.slack : Int) := by
  have h1 := exact_counterfactual_balance F z z0 R C hz0 hz hex
  have h2 := residual_is_completion F z z0 (F.pair R C) Q hchain hclosed hpm
  rw [abs_le] at h1 h2 ⊢
  simp only [residualC, residual] at h1 h2 ⊢
  omega

end GroundedRegulation
end KTAIT
