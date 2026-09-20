/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic
import KTAIT.ART

/-!
# KTAIT.ARTExactForm — the specified-code posterior as three additive costs

WP0203 (the appendix on probabilistic regulator bounds, "Algorithmic Regulator Theorem: exact
form"). For a specified explanation `e = (W, R)` of the regulated output `x`, with null output
`y₀` computable from `W` and `x` computable from `(W, R)`, the canonical-code posterior obeys

  `log₂ P(e | x) = −K(R | x) − L − H ± O(log N)`,

where `L = K(y₀ | x, R)` is the counterfactual residual and `H = K(W | x, R, y₀)` is the
world beyond what its two outputs and the regulator determine. The gap and the shared
information do not appear separately: the posterior ranks explanations by the cost of the
regulator given the output plus the residual, and charges the residual bit for bit. The clamp
family has `K(R₀ | x) = O(1)`, `L ≈ N`, hence weight `2^{−N}` each, and `2^N` members: the
residual cost is exactly offset by the multiplicity of worlds sharing that residual, which is
why the aggregate tail of the original article fails and why conditioning on the residual
(`ResidualTransfer`) repairs it.

Two further declarations restore the shared information: `shared_information_exponent` is ART's
gap form made exact (the dropped term is `K(W | y₀)`), and `bridge_identity` equates the two
exact forms: `IK W R = Δ − L + I(R:x) + I(W:(x,R)|y₀) ± slack`, GART with its slack identified.

Hypotheses are the usual named facts: two-sided chain rules (unconditioned and conditional),
computability of both outputs from the pair, and the coding theorem already carried by
`AITProb`. Nothing is proved about a universal machine.
-/

namespace KTAIT
namespace ARTExactForm

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

/-- **Exact form of the specified-code posterior (two-sided).** With the coding theorem,
    `(1/c₂)·2^{−(K(R|x)+L+H)−4s} ≤ P(⟨W,R⟩ | x) ≤ (1/c₁)·2^{−(K(R|x)+L+H)+4s}`. -/
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
    `P(⟨W,R⟩ | x) ≤ (1/c₁)·2^{−(K(R|x)+L)+4s}`. -/
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
    from `W`, `K(R | x) + L ≥ Δ + K(R | W) − 3·slack`, so the upper half of the exact form
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

/-- **The excess is nonnegative up to slack.** With `K(R | x) ≤ K R` and
    `K(W | ⟨⟨x,R⟩,y₀⟩) ≤ K(W | y₀) + slack`, the bridge gives `IK W R − (Δ − L) ≥ −6·slack`:
    GART, read off the identity. -/
theorem excess_nonneg (W R x y0 : F.Obj)
    (hcomp : OutputsComputable F W R x y0)
    (h1 : Chain F x (F.pair R (F.pair y0 W)))
    (h2 : CondChain F R (F.pair y0 W) x)
    (h3 : CondChain F y0 W (F.pair x R))
    (h5 : |(F.K W : ℤ) - (F.K y0 : ℤ) - (F.cond W y0 : ℤ)| ≤ (F.slack : ℤ))
    (hmono : (F.cond R x : ℤ) ≤ (F.K R : ℤ))
    (h6 : (F.cond W (F.pair (F.pair x R) y0) : ℤ) ≤ (F.cond W y0 : ℤ) + (F.slack : ℤ)) :
    IK F W R - (((F.K y0 : ℤ) - (F.K x : ℤ)) - residual F x y0 R) ≥ -6 * (F.slack : ℤ) := by
  have hb := bridge_identity F W R x y0 hcomp h1 h2 h3 h5
  simp only [residual, hidden] at *
  have := abs_le.mp hb
  omega

end ARTExactForm
end KTAIT
