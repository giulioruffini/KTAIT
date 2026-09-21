import KTAIT.RegulationBalance
import KTAIT.GroundedRegulation
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Reading GART across horizons (WP0203 v32.10, Remark "Reading the bound across horizons")

WP0203 states its balance at a fixed horizon `N`, and every complexity in it is
conditioned on the coding frame together with `N`. To compare the bound across horizons
one needs a horizon-free left side. The paper's Remark derives

  `I_K(W:R | C₀) ≥ I_K(W:R | C₀, N) − K(N | C₀) − c₀`

from prefix-program concatenation and the fact that supplying `N` cannot make either
marginal description longer, and then takes the supremum over a family of horizons of
the per-horizon initial-information bound. This module checks both steps.

The frame absorbs the background `C₀`; the horizon is an object `N`, and conditioning on
`C₀, N` is `F.cond · N`. The three AIT facts consumed are named hypotheses from the
existing modules: `RegulationBalance.CondMono` (supplying `N` does not lengthen a
description) and `GroundedRegulation.Subadd` (describe `N`, then the pair given `N`).
-/

namespace KTAIT
namespace HorizonConditioning

open RegulationBalance GroundedRegulation

variable (F : AITFrame)

/-- **Removing the horizon from the conditioning.**
`I_K(W:R) ≥ I_K(W:R | N) − K N − slack`. The `I_K(W:R | N)` is `cIK` with the horizon as the
conditioning object; `Subadd ⟨W,R⟩ N` is the concatenation bound
`K⟨W,R⟩ ≤ K N + K(⟨W,R⟩ | N) + slack`, and the two `CondMono` facts are
`K(W | N) ≤ K W`, `K(R | N) ≤ K R`. -/
theorem conditioning_on_horizon (W R N : F.Obj)
    (hW : CondMono F W N) (hR : CondMono F R N)
    (hpair : Subadd F (F.pair W R) N) :
    IK F W R ≥ cIK F W R N - (F.K N : Int) - (F.slack : Int) := by
  simp only [IK, cIK, CondMono, Subadd] at *
  omega

/-- **The initial-information bound read at every horizon.** If at each admitted horizon `N` the
initial-information bound `I_K(W:R | N) ≥ Δ_N − λ_N − h_N` holds, then the horizon-free
shared information satisfies `I_K(W:R) ≥ Δ_N − λ_N − h_N − K N − slack` for every such `N`.
The per-horizon premise is WP0203's initial-information corollary with the horizon made
explicit. -/
theorem horizon_bound_every {ι : Type*} (W R : F.Obj) (N : ι → F.Obj)
    (gap lam h : ι → Int)
    (hW : ∀ i, CondMono F W (N i)) (hR : ∀ i, CondMono F R (N i))
    (hpair : ∀ i, Subadd F (F.pair W R) (N i))
    (hcor : ∀ i, cIK F W R (N i) ≥ gap i - lam i - h i) (i : ι) :
    IK F W R ≥ gap i - lam i - h i - (F.K (N i) : Int) - (F.slack : Int) := by
  have := conditioning_on_horizon F W R (N i) (hW i) (hR i) (hpair i)
  have := hcor i
  omega

/-- **The supremum form over a finite family of horizons.** With the same premises, the
horizon-free shared information dominates the largest net gap over any nonempty finite set
`H` of admitted horizons, `I_K(W:R) ≥ max_{i ∈ H} [Δ_i − λ_i − h_i − K(N_i)] − slack`.
This is Equation (horizon-sup) of WP0203 with `c₀ := slack`. -/
theorem horizon_bound_sup {ι : Type*} (W R : F.Obj) (N : ι → F.Obj)
    (gap lam h : ι → Int)
    (hW : ∀ i, CondMono F W (N i)) (hR : ∀ i, CondMono F R (N i))
    (hpair : ∀ i, Subadd F (F.pair W R) (N i))
    (hcor : ∀ i, cIK F W R (N i) ≥ gap i - lam i - h i)
    (H : Finset ι) (hne : H.Nonempty) :
    IK F W R ≥
      H.sup' hne (fun i => gap i - lam i - h i - (F.K (N i) : Int)) - (F.slack : Int) := by
  have key : H.sup' hne (fun i => gap i - lam i - h i - (F.K (N i) : Int))
      ≤ IK F W R + (F.slack : Int) := by
    rw [Finset.sup'_le_iff]
    intro i _
    have := horizon_bound_every F W R N gap lam h hW hR hpair hcor i
    omega
  omega

end HorizonConditioning
end KTAIT
