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

end GroundedRegulation
end KTAIT
