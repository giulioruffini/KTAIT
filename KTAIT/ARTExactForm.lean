/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic
import KTAIT.ART
import KTAIT.RegulationBalance

/-!
# KTAIT.ARTExactForm — the specified-code posterior as three additive costs

WP0203 (the appendix on probabilistic regulator bounds, "Algorithmic Regulator Theorem: exact
form"). For a specified explanation `e = (W, R)` of the regulated output `x`, with null output
`y₀` computable from `W` and `x` computable from `(W, R)`, a compatible selected
program of length `K(W,R)+delta`, with matching output evidence, has posterior

  `log₂ P(e | x) = −K(R | x) − L − H − delta ± O(log N)`,

where `L = K(y₀ | x, R)` is the counterfactual residual and `H = K(W | x, R, y₀)` is the
world beyond what its two outputs and the regulator determine. The gap and the shared
information do not appear separately: the posterior ranks explanations by the cost of the
regulator given the output plus the residual, and charges the residual bit for bit. The clamp
family has `K(R₀ | x) = O(1)`, `L ≈ N`, hence weight `2^{−N}` each, and `2^N` members: the
residual cost is exactly offset by the multiplicity of worlds sharing that residual, which is
why the aggregate tail of the original article fails and why conditioning on the residual
(`ResidualTransfer`) repairs it.

`shared_information_exponent` restores the term `K(W | y₀)` dropped from ART's gap bound.
`bridge_identity` equates the exponent forms using complexity differences, within `5*slack`.
`bridge_symmetric_information` converts those differences to symmetric mutual information,
charging `7*slack` plus the three explicit pair and context conversion costs.

Hypotheses are the usual named facts: two-sided chain rules (unconditioned and conditional),
computability of both outputs from the pair, and the coding theorem already carried by
`AITProb`. The older declarations bound its abstract `post` weight;
`art_with_residual_specified` retains a selected program's length offset.
`bridge_symmetric_information` charges pair and context conversions separately.
Nothing is proved about a universal machine.
-/

namespace KTAIT
namespace ARTExactForm

open AITProb

variable (F : AITFrame)

/-- **Two-sided chain rule, unconditioned**: `K⟨a,b⟩ = K a + K(b | a) ± slack`. -/
def Chain (a b : F.Obj) : Prop :=
  |(F.K (F.pair a b) : ℤ) - (F.K a : ℤ) - (F.cond b a : ℤ)| ≤ (F.slack : ℤ)

/-- **Two-sided chain rule, conditional**: `K(⟨b,c⟩ | D) = K(b | D) + K(c | ⟨D,b⟩) ± slack`. -/
def CondChain (b c D : F.Obj) : Prop :=
  |(F.cond (F.pair b c) D : ℤ) - (F.cond b D : ℤ) - (F.cond c (F.pair D b) : ℤ)| ≤ (F.slack : ℤ)

/-- **Both outputs are computable from the pair**: the pair and the quadruple
    `⟨x, ⟨R, ⟨y₀, W⟩⟩⟩` have the same complexity up to slack. -/
def OutputsComputable (W R x y0 : F.Obj) : Prop :=
  |(F.K (F.pair W R) : ℤ) - (F.K (F.pair x (F.pair R (F.pair y0 W))) : ℤ)| ≤ (F.slack : ℤ)

/-- The residual `L = K(y₀ | ⟨x, R⟩)` and the hidden-world term `H = K(W | ⟨⟨x,R⟩, y₀⟩)`. -/
def residual (x y0 R : F.Obj) : ℤ := (F.cond y0 (F.pair x R) : ℤ)
def hidden (W x y0 R : F.Obj) : ℤ := (F.cond W (F.pair (F.pair x R) y0) : ℤ)

/-- **Exact-form exponent.** `K x − K⟨W,R⟩ = −(K(R | x) + L + H) ± 4·slack`. -/
theorem exact_exponent (W R x y0 : F.Obj)
    (hcomp : OutputsComputable F W R x y0)
    (h1 : Chain F x (F.pair R (F.pair y0 W)))
    (h2 : CondChain F R (F.pair y0 W) x)
    (h3 : CondChain F y0 W (F.pair x R)) :
    |((F.K x : ℤ) - (F.K (F.pair W R) : ℤ))
      + ((F.cond R x : ℤ) + residual F x y0 R + hidden F W x y0 R)| ≤ 4 * (F.slack : ℤ) := by
  simp only [OutputsComputable, Chain, CondChain, residual, hidden] at *
  have := abs_le.mp hcomp; have := abs_le.mp h1; have := abs_le.mp h2; have := abs_le.mp h3
  exact abs_le.mpr ⟨by omega, by omega⟩

/-- **Exact form of the abstract complexity weight (two-sided).** With the coding theorem,
    `(1/c₂)·2^{−(K(R|x)+L+H)−4s} ≤ post (W,R) x ≤ (1/c₁)·2^{−(K(R|x)+L+H)+4s}`. -/
theorem art_exact_form (F : AITProb) {c1 c2 : ℝ}
    (hLB : F.CodingLB c1) (hUB : F.CodingUB c2) (W R x y0 : F.Obj)
    (hcomp : OutputsComputable F.toAITFrame W R x y0)
    (h1 : Chain F.toAITFrame x (F.pair R (F.pair y0 W)))
    (h2 : CondChain F.toAITFrame R (F.pair y0 W) x)
    (h3 : CondChain F.toAITFrame y0 W (F.pair x R)) :
    (1 / c2) * (2 : ℝ) ^ (-((F.cond R x : ℤ) + residual F.toAITFrame x y0 R
        + hidden F.toAITFrame W x y0 R) - 4 * (F.slack : ℤ))
      ≤ F.post (F.pair W R) x ∧
    F.post (F.pair W R) x
      ≤ (1 / c1) * (2 : ℝ) ^ (-((F.cond R x : ℤ) + residual F.toAITFrame x y0 R
        + hidden F.toAITFrame W x y0 R) + 4 * (F.slack : ℤ)) := by
  have hexp := exact_exponent F.toAITFrame W R x y0 hcomp h1 h2 h3
  have htilt := F.theorem1_posterior_tilt hLB hUB W R x
  have hc1 : 0 < c1 := hLB.1
  have hc2 : 0 < c2 := hUB.1
  -- rewrite the tilt exponent K x − K W − K R + IK as K x − K⟨W,R⟩
  have hIK : (F.K x : ℤ) - (F.K W : ℤ) - (F.K R : ℤ) + IK F.toAITFrame W R
      = (F.K x : ℤ) - (F.K (F.pair W R) : ℤ) := by simp only [IK]; ring
  rw [hIK] at htilt
  set A : ℤ := (F.cond R x : ℤ) + residual F.toAITFrame x y0 R + hidden F.toAITFrame W x y0 R
  have hlo : -A - 4 * (F.slack : ℤ) ≤ (F.K x : ℤ) - (F.K (F.pair W R) : ℤ) := by
    have := abs_le.mp hexp; omega
  have hhi : (F.K x : ℤ) - (F.K (F.pair W R) : ℤ) ≤ -A + 4 * (F.slack : ℤ) := by
    have := abs_le.mp hexp; omega
  constructor
  · calc (1 / c2) * (2 : ℝ) ^ (-A - 4 * (F.slack : ℤ))
        ≤ (1 / c2) * (2 : ℝ) ^ ((F.K x : ℤ) - (F.K (F.pair W R) : ℤ)) := by
          gcongr
          · norm_num
      _ ≤ F.post (F.pair W R) x := htilt.1
  · calc F.post (F.pair W R) x
        ≤ (1 / c1) * (2 : ℝ) ^ ((F.K x : ℤ) - (F.K (F.pair W R) : ℤ)) := htilt.2
      _ ≤ (1 / c1) * (2 : ℝ) ^ (-A + 4 * (F.slack : ℤ)) := by
          gcongr
          · norm_num

/-- **Upper half without the hidden-world term**: since `H ≥ 0`,
    `post (W,R) x ≤ (1/c₁)·2^{−(K(R|x)+L)+4s}`. -/
theorem art_exact_upper (F : AITProb) {c1 c2 : ℝ}
    (hLB : F.CodingLB c1) (hUB : F.CodingUB c2) (W R x y0 : F.Obj)
    (hcomp : OutputsComputable F.toAITFrame W R x y0)
    (h1 : Chain F.toAITFrame x (F.pair R (F.pair y0 W)))
    (h2 : CondChain F.toAITFrame R (F.pair y0 W) x)
    (h3 : CondChain F.toAITFrame y0 W (F.pair x R)) :
    F.post (F.pair W R) x
      ≤ (1 / c1) * (2 : ℝ) ^ (-((F.cond R x : ℤ) + residual F.toAITFrame x y0 R)
        + 4 * (F.slack : ℤ)) := by
  have h := (art_exact_form F hLB hUB W R x y0 hcomp h1 h2 h3).2
  have hc1 : 0 < c1 := hLB.1
  have hH : 0 ≤ hidden F.toAITFrame W x y0 R := by simp [hidden]
  have hL : 0 ≤ residual F.toAITFrame x y0 R := by simp [residual]
  have hexp : -((F.cond R x : ℤ) + residual F.toAITFrame x y0 R + hidden F.toAITFrame W x y0 R)
      + 4 * (F.slack : ℤ) ≤ -((F.cond R x : ℤ) + residual F.toAITFrame x y0 R)
      + 4 * (F.slack : ℤ) := by omega
  calc F.post (F.pair W R) x ≤ _ := h
    _ ≤ (1 / c1) * (2 : ℝ) ^ (-((F.cond R x : ℤ) + residual F.toAITFrame x y0 R)
        + 4 * (F.slack : ℤ)) := by
        gcongr
        · norm_num

/-- **Comparison with the gap form.** In the other chain-rule order, with `y₀` computable
    from `W`, `K(R | x) + L ≥ Δ + K(R | W) − 7·slack`, so the upper half of the exact form
    implies the second line of the original ART bound. Hypotheses: chain rule for `⟨W,R⟩`,
    chain rule `K W = K y₀ + K(W | y₀) ± slack` (computability of `y₀` from `W` folded in),
    and monotonicity `K(W | y₀) ≥ K(W | ⟨⟨x,R⟩,y₀⟩) − slack`. -/
theorem residual_dominates_gap (W R x y0 : F.Obj)
    (hcomp : OutputsComputable F W R x y0)
    (h1 : Chain F x (F.pair R (F.pair y0 W)))
    (h2 : CondChain F R (F.pair y0 W) x)
    (h3 : CondChain F y0 W (F.pair x R))
    (h4 : Chain F W R)
    (h5 : |(F.K W : ℤ) - (F.K y0 : ℤ) - (F.cond W y0 : ℤ)| ≤ (F.slack : ℤ))
    (h6 : (F.cond W (F.pair (F.pair x R) y0) : ℤ) ≤ (F.cond W y0 : ℤ) + (F.slack : ℤ)) :
    (F.cond R x : ℤ) + residual F x y0 R
      ≥ ((F.K y0 : ℤ) - (F.K x : ℤ)) + (F.cond R W : ℤ) - 7 * (F.slack : ℤ) := by
  simp only [OutputsComputable, Chain, CondChain, residual] at *
  have := abs_le.mp hcomp; have := abs_le.mp h1; have := abs_le.mp h2
  have := abs_le.mp h3; have := abs_le.mp h4; have := abs_le.mp h5
  omega

/-! ## The shared-information form and the bridge identity -/

/-- **Exponent in shared-information form.** With `K W = K y₀ + K(W | y₀) ± slack` (`y₀`
    computable from `W`) and the definition of `IK`,
    `K x − K⟨W,R⟩ = IK W R − K R − (K y₀ − K x) − K(W | y₀) ± slack`.
    ART's gap form drops the nonnegative last term. -/
theorem shared_information_exponent (W R x y0 : F.Obj)
    (h5 : |(F.K W : ℤ) - (F.K y0 : ℤ) - (F.cond W y0 : ℤ)| ≤ (F.slack : ℤ)) :
    |((F.K x : ℤ) - (F.K (F.pair W R) : ℤ))
      - (IK F W R - (F.K R : ℤ) - ((F.K y0 : ℤ) - (F.K x : ℤ)) - (F.cond W y0 : ℤ))|
      ≤ (F.slack : ℤ) := by
  simp only [IK]
  have := abs_le.mp h5
  exact abs_le.mpr ⟨by omega, by omega⟩

/-- **Bridge identity: GART with its slack identified.**
    `IK W R = Δ − L + (K R − K(R | x)) + (K(W | y₀) − K(W | ⟨⟨x,R⟩,y₀⟩)) ± 5·slack`,
    where `Δ = K y₀ − K x` and `L` is the residual. The two bracketed terms are the information
    the regulated output carries about the regulator and the information the output and the
    regulator carry about the world beyond its null output; both are nonnegative up to slack,
    so `IK W R ≥ Δ − L − O(slack)` is GART, and the identity says what the gap in GART is. -/
theorem bridge_identity (W R x y0 : F.Obj)
    (hcomp : OutputsComputable F W R x y0)
    (h1 : Chain F x (F.pair R (F.pair y0 W)))
    (h2 : CondChain F R (F.pair y0 W) x)
    (h3 : CondChain F y0 W (F.pair x R))
    (h5 : |(F.K W : ℤ) - (F.K y0 : ℤ) - (F.cond W y0 : ℤ)| ≤ (F.slack : ℤ)) :
    |IK F W R - (((F.K y0 : ℤ) - (F.K x : ℤ)) - residual F x y0 R
        + ((F.K R : ℤ) - (F.cond R x : ℤ))
        + ((F.cond W y0 : ℤ) - hidden F W x y0 R))| ≤ 5 * (F.slack : ℤ) := by
  have hA := exact_exponent F W R x y0 hcomp h1 h2 h3
  have hB := shared_information_exponent F W R x y0 h5
  simp only [residual, hidden] at *
  have := abs_le.mp hA; have := abs_le.mp hB
  exact abs_le.mpr ⟨by omega, by omega⟩

/-- **Four-term form.** `K x − K⟨W,R⟩ = −K R − L − K(W | y₀) + (IK W R − (Δ − L)) ± slack`:
    the posterior charges the regulator's length, the residual and the null-world beyond its
    output, and rewards shared information only in excess of GART's minimum `Δ − L`. This is
    ART's exponent `IK − K R − Δ` with the residual made explicit. -/
theorem four_term_exponent (W R x y0 : F.Obj)
    (h5 : |(F.K W : ℤ) - (F.K y0 : ℤ) - (F.cond W y0 : ℤ)| ≤ (F.slack : ℤ)) :
    |((F.K x : ℤ) - (F.K (F.pair W R) : ℤ))
      - (-(F.K R : ℤ) - residual F x y0 R - (F.cond W y0 : ℤ)
          + (IK F W R - (((F.K y0 : ℤ) - (F.K x : ℤ)) - residual F x y0 R)))|
      ≤ (F.slack : ℤ) := by
  have h := shared_information_exponent F W R x y0 h5
  simp only [residual] at *
  have := abs_le.mp h
  exact abs_le.mpr ⟨by omega, by omega⟩

/-- The bridge identity bounds the excess `IK W R - (gap - residual)` below by
`-7*slack`. Both ignore-input instances carry their additive allowance. -/
theorem excess_nonneg (F : AITFrame) (W R x y0 : F.Obj)
    (hcomp : OutputsComputable F W R x y0)
    (h1 : Chain F x (F.pair R (F.pair y0 W)))
    (h2 : CondChain F R (F.pair y0 W) x)
    (h3 : CondChain F y0 W (F.pair x R))
    (h5 : |(F.K W : Int) - (F.K y0 : Int) - (F.cond W y0 : Int)| ≤ (F.slack : Int))
    (hmono : RegulationBalance.CondMono F R x)
    (h6 : (F.cond W (F.pair (F.pair x R) y0) : Int)
      ≤ (F.cond W y0 : Int) + (F.slack : Int)) :
    IK F W R - (((F.K y0 : Int) - (F.K x : Int)) - residual F x y0 R)
      ≥ -7 * (F.slack : Int) := by
  have hb := bridge_identity F W R x y0 hcomp h1 h2 h3 h5
  have hb' := abs_le.mp hb
  simp only [ARTExactForm.hidden] at hb'
  simp only [RegulationBalance.CondMono] at hmono
  omega

/-- Two-sided residual bounds for the abstract complexity weight `F.post`.
The lower exponent is `-K R-L-K(W|y0)-8s`; the upper is `IK-K R-gap+s`.
Their difference is the excess `IK-(gap-L)` plus `K(W|y0)+9s`; the coding
constants remain separate. Program-posterior interpretation requires
`AITProb.compatible_program_factor` and the selected length offset. -/
theorem art_with_residual (F : AITProb) {c1 c2 : Real}
    (hLB : F.CodingLB c1) (hUB : F.CodingUB c2) (W R x y0 : F.Obj)
    (hcomp : OutputsComputable F.toAITFrame W R x y0)
    (h1 : Chain F.toAITFrame x (F.pair R (F.pair y0 W)))
    (h2 : CondChain F.toAITFrame R (F.pair y0 W) x)
    (h3 : CondChain F.toAITFrame y0 W (F.pair x R))
    (h5 : |(F.K W : Int) - (F.K y0 : Int) - (F.cond W y0 : Int)| ≤ (F.slack : Int))
    (hmono : RegulationBalance.CondMono F.toAITFrame R x)
    (h6 : (F.cond W (F.pair (F.pair x R) y0) : Int)
      ≤ (F.cond W y0 : Int) + (F.slack : Int)) :
    (1 / c2) * (2 : Real) ^ (-(F.K R : Int) - residual F.toAITFrame x y0 R
      - (F.cond W y0 : Int) - 8 * (F.slack : Int)) ≤ F.post (F.pair W R) x ∧
    F.post (F.pair W R) x ≤ (1 / c1) * (2 : Real) ^ (IK F.toAITFrame W R
      - (F.K R : Int) - ((F.K y0 : Int) - (F.K x : Int)) + (F.slack : Int)) := by
  have htilt := F.theorem1_posterior_tilt hLB hUB W R x
  have hIK : (F.K x : ℤ) - (F.K W : ℤ) - (F.K R : ℤ) + IK F.toAITFrame W R
      = (F.K x : ℤ) - (F.K (F.pair W R) : ℤ) := by simp only [IK]; ring
  rw [hIK] at htilt
  have hsh := shared_information_exponent F.toAITFrame W R x y0 h5
  have hex := excess_nonneg F.toAITFrame W R x y0 hcomp h1 h2 h3 h5 hmono h6
  have hc1 : 0 < c1 := hLB.1
  have hc2 : 0 < c2 := hUB.1
  have hs := abs_le.mp hsh
  have hcw : (0 : ℤ) ≤ (F.cond W y0 : ℤ) := by positivity
  constructor
  · have hlo : -(F.K R : ℤ) - residual F.toAITFrame x y0 R - (F.cond W y0 : ℤ) - 8 * (F.slack : ℤ)
        ≤ (F.K x : ℤ) - (F.K (F.pair W R) : ℤ) := by
      simp only [ARTExactForm.residual] at *; omega
    calc (1 / c2) * (2 : ℝ) ^ (-(F.K R : ℤ) - residual F.toAITFrame x y0 R - (F.cond W y0 : ℤ)
          - 8 * (F.slack : ℤ))
        ≤ (1 / c2) * (2 : ℝ) ^ ((F.K x : ℤ) - (F.K (F.pair W R) : ℤ)) := by
          gcongr
          · norm_num
      _ ≤ F.post (F.pair W R) x := htilt.1
  · have hhi : (F.K x : ℤ) - (F.K (F.pair W R) : ℤ)
        ≤ IK F.toAITFrame W R - (F.K R : ℤ) - ((F.K y0 : ℤ) - (F.K x : ℤ)) + (F.slack : ℤ) := by
      omega
    calc F.post (F.pair W R) x
        ≤ (1 / c1) * (2 : ℝ) ^ ((F.K x : ℤ) - (F.K (F.pair W R) : ℤ)) := htilt.2
      _ ≤ (1 / c1) * (2 : ℝ) ^ (IK F.toAITFrame W R - (F.K R : ℤ)
            - ((F.K y0 : ℤ) - (F.K x : ℤ)) + (F.slack : ℤ)) := by
          gcongr
          · norm_num


/-! ## Specified-code and symmetric-information bridges -/

/-- the chain-rule slack remains in the exponent. -/
theorem conditional_art_specified (F : AITProb) {c1 : Real}
    (hLB : F.CodingLB c1) (W R x y0 : F.Obj)
    (c0 delta : Int) (n : Nat)
    (hoff : (F.K y0 : Int) ≤ (F.K W : Int) + c0)
    (hlen : (n : Int) = (F.K (F.pair W R) : Int) + delta)
    (hchain : Chain F.toAITFrame W R) :
    specifiedWeight F n x ≤ ((1 / c1) * (2 : Real) ^ (c0 - delta)) *
      (2 : Real) ^ (-(F.cond R W : Int)
        - ((F.K y0 : Int) - (F.K x : Int)) + (F.slack : Int)) := by
  have hs := sharp_art_specified F hLB W R x y0 c0 delta n hoff hlen
  have hc1 := hLB.1
  have hc := abs_le.mp hchain
  have hexp : IK F.toAITFrame W R - (F.K R : Int)
        - ((F.K y0 : Int) - (F.K x : Int))
      ≤ -(F.cond R W : Int) - ((F.K y0 : Int) - (F.K x : Int)) + (F.slack : Int) := by
    simp only [IK]
    omega
  refine hs.trans ?_
  gcongr
  norm_num

/-- the pair-order conversion has its own fixed cost. -/
theorem information_difference (F : AITFrame) (A B : F.Obj) (cPair : Nat)
    (hchain : Chain F B A)
    (hswap : |(F.K (F.pair A B) : Int) - (F.K (F.pair B A) : Int)|
      ≤ (cPair : Int)) :
    |IK F A B - ((F.K A : Int) - (F.cond A B : Int))|
      ≤ (F.slack : Int) + (cPair : Int) := by
  have hc := abs_le.mp hchain
  have hp := abs_le.mp hswap
  simp only [IK]
  exact abs_le.mpr ⟨by omega, by omega⟩

/-- distinguish pair reversal from reversal of the supplied context. -/
theorem conditional_information_difference (F : AITFrame) (A B C : F.Obj)
    (cPair cContext : Nat) (hchain : CondChain F B A C)
    (hswap : |(F.cond (F.pair A B) C : Int) - (F.cond (F.pair B A) C : Int)|
      ≤ (cPair : Int))
    (hcontext : |(F.cond A (F.pair C B) : Int) - (F.cond A (F.pair B C) : Int)|
      ≤ (cContext : Int)) :
    |RegulationBalance.cIK F A B C
      - ((F.cond A C : Int) - (F.cond A (F.pair B C) : Int))|
      ≤ (F.slack : Int) + (cPair : Int) + (cContext : Int) := by
  have hc := abs_le.mp hchain
  have hp := abs_le.mp hswap
  have hx := abs_le.mp hcontext
  simp only [RegulationBalance.cIK]
  exact abs_le.mpr ⟨by omega, by omega⟩

/-- the paper's symmetric-information form of the bridge identity.
With each fixed re-encoding cost at most s, the displayed tolerance is at most 10s. -/
theorem bridge_symmetric_information (F : AITFrame) (W R x y0 : F.Obj)
    (hcomp : OutputsComputable F W R x y0)
    (h1 : Chain F x (F.pair R (F.pair y0 W)))
    (h2 : CondChain F R (F.pair y0 W) x)
    (h3 : CondChain F y0 W (F.pair x R))
    (h5 : |(F.K W : Int) - (F.K y0 : Int) - (F.cond W y0 : Int)| ≤ (F.slack : Int))
    (cPair cCondPair cContext : Nat)
    (hreg : Chain F x R)
    (hswap : |(F.K (F.pair R x) : Int) - (F.K (F.pair x R) : Int)| ≤ (cPair : Int))
    (hworld : CondChain F (F.pair x R) W y0)
    (hcondSwap : |(F.cond (F.pair W (F.pair x R)) y0 : Int)
      - (F.cond (F.pair (F.pair x R) W) y0 : Int)| ≤ (cCondPair : Int))
    (hcontext : |(F.cond W (F.pair y0 (F.pair x R)) : Int)
      - (F.cond W (F.pair (F.pair x R) y0) : Int)| ≤ (cContext : Int)) :
    |(IK F W R - (((F.K y0 : Int) - (F.K x : Int)) - residual F x y0 R))
      - (IK F R x + RegulationBalance.cIK F W (F.pair x R) y0)|
      ≤ 7 * (F.slack : Int) + (cPair : Int) + (cCondPair : Int) + (cContext : Int) := by
  have hb := bridge_identity F W R x y0 hcomp h1 h2 h3 h5
  have hr := information_difference F R x cPair hreg hswap
  have hw := conditional_information_difference F W (F.pair x R) y0
    cCondPair cContext hworld hcondSwap hcontext
  have hb' := abs_le.mp hb
  have hr' := abs_le.mp hr
  have hw' := abs_le.mp hw
  simp only [ARTExactForm.hidden] at hb'
  exact abs_le.mpr ⟨by omega, by omega⟩

/-- The selected program length shifts both residual-bound exponents by
`-delta`. Compatibility and matching evidence are supplied separately by
`AITProb.compatible_program_factor`; the exponent separation is unchanged. -/
theorem art_with_residual_specified (F : AITProb) {c1 c2 : Real}
    (hLB : F.CodingLB c1) (hUB : F.CodingUB c2) (W R x y0 : F.Obj)
    (n : Nat) (delta : Int)
    (hlen : (n : Int) = (F.K (F.pair W R) : Int) + delta)
    (hcomp : OutputsComputable F.toAITFrame W R x y0)
    (h1 : Chain F.toAITFrame x (F.pair R (F.pair y0 W)))
    (h2 : CondChain F.toAITFrame R (F.pair y0 W) x)
    (h3 : CondChain F.toAITFrame y0 W (F.pair x R))
    (h5 : |(F.K W : Int) - (F.K y0 : Int) - (F.cond W y0 : Int)| ≤ (F.slack : Int))
    (hmono : RegulationBalance.CondMono F.toAITFrame R x)
    (h6 : (F.cond W (F.pair (F.pair x R) y0) : Int)
      ≤ (F.cond W y0 : Int) + (F.slack : Int)) :
    (1 / c2) * (2 : Real) ^ (-(F.K R : Int) - residual F.toAITFrame x y0 R
      - (F.cond W y0 : Int) - 8 * (F.slack : Int) - delta) ≤ specifiedWeight F n x ∧
    specifiedWeight F n x ≤ (1 / c1) * (2 : Real) ^ (IK F.toAITFrame W R
      - (F.K R : Int) - ((F.K y0 : Int) - (F.K x : Int)) + (F.slack : Int) - delta) := by
  have hb := art_with_residual F hLB hUB W R x y0 hcomp h1 h2 h3 h5 hmono h6
  have hf : specifiedWeight F n x = (2 : Real) ^ (-delta) * F.post (F.pair W R) x := by
    unfold specifiedWeight AITProb.post
    rw [hlen, neg_add, zpow_add₀ (by norm_num : (2 : Real) ≠ 0)]
    ring
  have hexp : ∀ (c : Real) (a : Int),
      (2 : Real) ^ (-delta) * (c * (2 : Real) ^ a) = c * (2 : Real) ^ (a - delta) := by
    intro c a
    rw [show a - delta = -delta + a by ring, zpow_add₀ (by norm_num : (2 : Real) ≠ 0)]
    ring
  constructor
  · have h := mul_le_mul_of_nonneg_left hb.1 (by positivity : 0 ≤ (2 : Real) ^ (-delta))
    rw [hexp, ← hf] at h
    exact h
  · have h := mul_le_mul_of_nonneg_left hb.2 (by positivity : 0 ≤ (2 : Real) ^ (-delta))
    rw [hexp, ← hf] at h
    exact h

/-- logarithms preserve the coding constants explicitly. -/
theorem log2_sandwich (weight c1 c2 : Real) (lo hi : Int)
    (hweight : 0 < weight) (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hlo : (1 / c2) * (2 : Real) ^ lo ≤ weight)
    (hhi : weight ≤ (1 / c1) * (2 : Real) ^ hi) :
    (lo : Real) - Real.logb 2 c2 ≤ Real.logb 2 weight ∧
    Real.logb 2 weight ≤ (hi : Real) - Real.logb 2 c1 := by
  have heval : ∀ (c : Real), 0 < c → ∀ n : Int,
      Real.logb 2 ((1 / c) * (2 : Real) ^ n) = (n : Real) - Real.logb 2 c := by
    intro c hc n
    rw [Real.logb_mul (by positivity) (by positivity), one_div, Real.logb_inv,
      ← Real.rpow_intCast (2 : Real) n,
      Real.logb_rpow (by norm_num : (0 : Real) < 2) (by norm_num : (2 : Real) ≠ 1)]
    ring
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : Real) < 2)
    (by positivity : 0 < (1 / c2) * (2 : Real) ^ lo) hlo
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : Real) < 2) hweight hhi
  rw [heval c2 hc2 lo] at hl
  rw [heval c1 hc1 hi] at hh
  exact ⟨hl, hh⟩


end ARTExactForm
end KTAIT
