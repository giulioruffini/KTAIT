/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini
-/
import KTAIT.RegulationBalance
import KTAIT.GroundedRegulation

/-!
# Intervention knowledge and descriptive power (WP0203 v34.3, Discussion 5.2)

WP0203's Discussion adds four paper-level statements about what small initial shared
information does and does not limit. This module checks them from named AIT facts.

* `key_bound`: a descriptor `m` recoverable by fixed maps from both `W` and `R` forces
  `I_K(W:R) ≥ K m − 3·slack`. Data processing in each argument, then self-information.
* `intervention_and_gap`: the descriptor bound and the residual bound hold together, so
  `I_K(W:R) ≥ max{K m, Δ − L} − 3·slack`; the two are not added.
* `readout_saving_upper`: for any world record `Z` computable from `W`, supplying `R` saves at
  most `I_K(W:R) + 2·slack` in describing `Z`.
* `descriptive_saving`: for the null output, the saving `K y₀ − K(y₀ | R)` is at least
  `Δ − L − slack` and at most `I_K(W:R) + 2·slack`.
* `shared_content_split`: `I_K(W:R) = I_K(y₀:R) + I_K(W:R | y₀) ± 3·slack` when `y₀` is
  computable from `W`, the chain-rule decomposition of shared information.

Conditioning on the frame is absorbed in `F`; the objects are the initial descriptions and
the records. The hypotheses are the module's own named facts or those of `RegulationBalance`
and `GroundedRegulation`; nothing is proved about a concrete machine.
-/

namespace KTAIT
namespace InterventionKnowledge

open RegulationBalance GroundedRegulation

variable (F : AITFrame)

/-- **Self-information**: `K m ≤ I_K(m:m) + slack`. Standard; named hypothesis. -/
def SelfInformation (m : F.Obj) : Prop := (F.K m : Int) ≤ IK F m m + (F.slack : Int)

/-- **Data processing in the second argument**: `m` computable from `R` gives
`I_K(m:m) ≤ I_K(m:R) + slack`. Standard; named hypothesis. -/
def DataProcessingSnd (m R : F.Obj) : Prop := IK F m m ≤ IK F m R + (F.slack : Int)

/-- **Chain rule through a computable output**: `y₀` computable from `a` gives
`K a = K y₀ + K(a | y₀) ± slack` (adjoining `y₀` to `a` costs only overhead). Standard;
named hypothesis. -/
def ChainThroughOutput (y0 a : F.Obj) : Prop :=
  |(F.K a : Int) - (F.K y0 : Int) - (F.cond a y0 : Int)| ≤ (F.slack : Int)

/-- **Two-sided chain rule**: `K⟨y₀,R⟩ = K y₀ + K(R | y₀) ± slack`. Standard; named hypothesis. -/
def ChainPair (y0 R : F.Obj) : Prop :=
  |(F.K (F.pair y0 R) : Int) - (F.K y0 : Int) - (F.cond R y0 : Int)| ≤ (F.slack : Int)

/-- **The descriptor bound.** A descriptor `m` recovered by fixed computable maps from `W` and
from `R` forces `I_K(W:R) ≥ K m − 3·slack`: data processing in the first argument
(`m` from `W`), data processing in the second (`m` from `R`), and self-information. -/
theorem key_bound (W R m : F.Obj)
    (hW : DataProcessing F m W R) (hR : DataProcessingSnd F m R)
    (hself : SelfInformation F m) :
    IK F W R ≥ (F.K m : Int) - 3 * (F.slack : Int) := by
  simp only [DataProcessing, DataProcessingSnd, SelfInformation] at *
  omega

/-- **Intervention knowledge and the gap together.** The descriptor bound and the residual
bound (`grounded_inequality`, read as a lower bound on shared information) hold at once, so
shared information dominates the larger of the two; they are not added, since they may
concern the same information. -/
theorem intervention_and_gap (W R m x y0 : F.Obj)
    (hW : DataProcessing F m W R) (hR : DataProcessingSnd F m R)
    (hself : SelfInformation F m)
    (hmut : MutualChain F y0 R) (hsub : CondSubadd F x y0 R)
    (hmono : CondMono F x R) (hdp : DataProcessing F y0 W R) :
    IK F W R ≥ max ((F.K m : Int) - 3 * (F.slack : Int))
      (gap F x y0 - residual F x y0 R - 3 * (F.slack : Int)) := by
  have h1 := key_bound F W R m hW hR hself
  have h2 := grounded_inequality F W x y0 R hmut hsub hmono hdp
  rw [ge_iff_le, max_le_iff]
  exact ⟨h1, by omega⟩

/-- **Description saving for any fixed world readout.** For `Z` computable from `W`,
supplying `R` shortens the description of `Z` by at most `I_K(W:R) + 2·slack`:
`K Z − K(Z | R) ≤ I_K(Z:R) + slack` by the mutual-information chain rule, then data
processing. -/
theorem readout_saving_upper (W R Z : F.Obj)
    (hmut : MutualChain F Z R) (hdp : DataProcessing F Z W R) :
    (F.K Z : Int) - (F.cond Z R : Int) ≤ IK F W R + 2 * (F.slack : Int) := by
  simp only [MutualChain, DataProcessing] at *
  omega

/-- **The descriptive saving on the null output is bracketed by the gap and the residual on
one side and by shared information on the other.** Lower bound: describe `y₀` given `R` by
producing `x` (at most `K x`, ignoring `R`) and then the residual program. Upper bound:
`readout_saving_upper` with `Z := y₀`. -/
theorem descriptive_saving (W R x y0 : F.Obj)
    (hmut : MutualChain F y0 R) (hsub : CondSubadd F x y0 R)
    (hmono : CondMono F x R) (hdp : DataProcessing F y0 W R) :
    gap F x y0 - residual F x y0 R - (F.slack : Int)
        ≤ (F.K y0 : Int) - (F.cond y0 R : Int) ∧
    (F.K y0 : Int) - (F.cond y0 R : Int) ≤ IK F W R + 2 * (F.slack : Int) := by
  refine ⟨?_, readout_saving_upper F W R y0 hmut hdp⟩
  simp only [RegulationBalance.gap, GroundedRegulation.residual, CondSubadd, CondMono] at *
  omega

/-- **Shared information splits into what concerns the null record and what lies beyond it.**
With `y₀` computable from `W`, `I_K(W:R) = I_K(y₀:R) + I_K(W:R | y₀) ± 3·slack`. The three
chain-rule facts adjoin `y₀` to `W`, to `⟨W,R⟩`, and pair it with `R`. -/
theorem shared_content_split (W R y0 : F.Obj)
    (hW : ChainThroughOutput F y0 W)
    (hWR : ChainThroughOutput F y0 (F.pair W R))
    (hR : ChainPair F y0 R) :
    |IK F W R - IK F y0 R - cIK F W R y0| ≤ 3 * (F.slack : Int) := by
  simp only [IK, cIK, ChainThroughOutput, ChainPair] at *
  have hW' := abs_le.mp hW
  have hWR' := abs_le.mp hWR
  have hR' := abs_le.mp hR
  exact abs_le.mpr ⟨by omega, by omega⟩

end InterventionKnowledge
end KTAIT
