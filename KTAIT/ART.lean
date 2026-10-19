/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic
import KTAIT.Probability

/-!
# KTAIT.ART — the probabilistic Algorithmic Regulator Theorem (M2.5 + Phase 1)

The algebraic probabilistic bounds associated with *An Algorithmic-Information-Theoretic
Regulator Theorem*, Entropy 2026, 28, 257.

`AITProb` adds a positive real weight `m` to the abstract complexity frame. Its
`post e x := 2^(-K e)/m x` is an abstract complexity weight. The structure alone
neither assigns a compatible program to each explanation nor normalizes a law
over explanations. `compatible_program_factor` connects a selected program of
length `K e + delta` to this weight when its evidence denominator agrees:
its program posterior is `2^(-delta) * post e x`.

`CodingLB` and `CodingUB` are the two standard coding-theorem bounds, as named
hypotheses. They give the wrapper bound and two-sided pair-weight estimate.
The sharp ART bound also assumes the null-simulator cost. Its explicit-constant
form and uniform wrapper-offset form retain the cost of the regulator. The
chain-rule conversion is `ARTExactForm.conditional_art_specified`; it retains
the possibly horizon-dependent `slack` in the exponent.

-/

namespace KTAIT

/-- A probabilistic AIT interface: an `AITFrame` plus positive output weights `m`. -/
structure AITProb extends AITFrame where
  /-- Positive output weights; interpreted as a universal semimeasure in AIT applications. -/
  m : Obj → ℝ
  /-- Positivity of the semimeasure. -/
  m_pos : ∀ x, 0 < m x

namespace AITProb

variable (F : AITProb)

/-- Abstract complexity weight `2^(-K e)/m x`, with evidence denominator `m x`.
A conditional probability over specified programs additionally requires compatible
programs, their actual lengths, and the same evidence denominator; see
`compatible_program_factor`. A coding context such as `(C,N)` may be absorbed
into the frame, but that interpretation is separate from this definition.
A null-output or gap hypothesis does not itself condition this weight. -/
noncomputable def post (e x : F.Obj) : ℝ := (2 : ℝ) ^ (-(F.K e : ℤ)) / F.m x

/-- Coding Theorem, lower bound: `c₁·2^{−K x} ≤ m x` (with `c₁ > 0`). -/
def CodingLB (c1 : ℝ) : Prop := 0 < c1 ∧ ∀ x, c1 * (2 : ℝ) ^ (-(F.K x : ℤ)) ≤ F.m x

/-- Coding Theorem, upper bound: `m x ≤ c₂·2^{−K x}` (with `c₂ > 0`). -/
def CodingUB (c2 : ℝ) : Prop := 0 < c2 ∧ ∀ x, F.m x ≤ c2 * (2 : ℝ) ^ (-(F.K x : ℤ))

/-- Helper: the complexity weight factors as `(2^{−K x}/m x)·2^{K x − K e}`. -/
private theorem post_factor (e x : F.Obj) :
    F.post e x = ((2 : ℝ) ^ (-(F.K x : ℤ)) / F.m x) * (2 : ℝ) ^ ((F.K x : ℤ) - (F.K e : ℤ)) := by
  unfold AITProb.post
  rw [show (-(F.K e : ℤ)) = (-(F.K x : ℤ)) + ((F.K x : ℤ) - (F.K e : ℤ)) from by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), mul_div_right_comm]

/-- **Wrapper bound — Eq. (6).** Derived from the coding theorem (lower bound):
    `post e x ≤ (1/c₁)·2^{K(x) − K(e)}`. -/
theorem wrapper_bound {c1 : ℝ} (hLB : F.CodingLB c1) (e x : F.Obj) :
    F.post e x ≤ (1 / c1) * (2 : ℝ) ^ ((F.K x : ℤ) - (F.K e : ℤ)) := by
  obtain ⟨hc1, hlb⟩ := hLB
  have hm : 0 < F.m x := F.m_pos x
  have h2e : (0 : ℝ) < (2 : ℝ) ^ ((F.K x : ℤ) - (F.K e : ℤ)) := by positivity
  have hratio : (2 : ℝ) ^ (-(F.K x : ℤ)) / F.m x ≤ 1 / c1 := by
    rw [div_le_div_iff₀ hm hc1, one_mul]
    linarith [hlb x, mul_comm c1 ((2 : ℝ) ^ (-(F.K x : ℤ)))]
  rw [post_factor]
  exact mul_le_mul_of_nonneg_right hratio h2e.le

/-- **Coupled-pair complexity-weight bound.** With `M(W:R) = IK W R`, the weight is
    sandwiched: `(1/c₂)·2^{K(x)−K(W)−K(R)+M} ≤ post (W,R) x ≤ (1/c₁)·2^{K(x)−K(W)−K(R)+M}`. -/
theorem theorem1_posterior_tilt {c1 c2 : ℝ}
    (hLB : F.CodingLB c1) (hUB : F.CodingUB c2) (W R x : F.Obj) :
    (1 / c2) * (2 : ℝ) ^ ((F.K x : ℤ) - (F.K W : ℤ) - (F.K R : ℤ) + IK F.toAITFrame W R)
        ≤ F.post (F.pair W R) x ∧
    F.post (F.pair W R) x
        ≤ (1 / c1) * (2 : ℝ) ^ ((F.K x : ℤ) - (F.K W : ℤ) - (F.K R : ℤ) + IK F.toAITFrame W R) := by
  have hexp_eq : ((F.K x : ℤ) - (F.K W : ℤ) - (F.K R : ℤ) + IK F.toAITFrame W R)
      = (F.K x : ℤ) - (F.K (F.pair W R) : ℤ) := by simp only [IK]; ring
  rw [hexp_eq]
  refine ⟨?_, wrapper_bound F hLB _ _⟩
  -- lower bound from the upper coding bound
  obtain ⟨hc2, hub⟩ := hUB
  have hm : 0 < F.m x := F.m_pos x
  have h2e : (0 : ℝ) < (2 : ℝ) ^ ((F.K x : ℤ) - (F.K (F.pair W R) : ℤ)) := by positivity
  have hratio : 1 / c2 ≤ (2 : ℝ) ^ (-(F.K x : ℤ)) / F.m x := by
    rw [div_le_div_iff₀ hc2 hm, one_mul]
    linarith [hub x, mul_comm c2 ((2 : ℝ) ^ (-(F.K x : ℤ)))]
  rw [post_factor]
  exact mul_le_mul_of_nonneg_right hratio h2e.le

/-- **Theorem 2 (Probabilistic Regulator Theorem).** Now resting on the coding theorem
    (`hLB`) and Lemma 2 (`hoff`) — the wrapper bound is derived, not assumed:
    `post (W,R) x ≤ C · 2^{M(W:R)} · 2^{−Δ}` with `Δ = K(O_{W,∅}) − K(O_{W,R})`. -/
theorem probabilistic_regulator_theorem
    (W R xon xoff : F.Obj)
    (c0 : ℤ) (hoff : (F.K xoff : ℤ) ≤ (F.K W : ℤ) + c0)
    {c1 : ℝ} (hLB : F.CodingLB c1) :
    ∃ C : ℝ, 0 < C ∧
      F.post (F.pair W R) xon
        ≤ C * (2 : ℝ) ^ (IK F.toAITFrame W R)
            * (2 : ℝ) ^ (-((F.K xoff : ℤ) - (F.K xon : ℤ))) := by
  have hc1 := hLB.1
  refine ⟨(1 / c1) * (2 : ℝ) ^ c0, by positivity, ?_⟩
  have hexp : (F.K xon : ℤ) - (F.K (F.pair W R) : ℤ)
      ≤ c0 + IK F.toAITFrame W R - ((F.K xoff : ℤ) - (F.K xon : ℤ)) := by
    simp only [IK]; omega
  calc F.post (F.pair W R) xon
      ≤ (1 / c1) * (2 : ℝ) ^ ((F.K xon : ℤ) - (F.K (F.pair W R) : ℤ)) :=
        wrapper_bound F hLB _ _
    _ ≤ (1 / c1) * (2 : ℝ) ^ (c0 + IK F.toAITFrame W R - ((F.K xoff : ℤ) - (F.K xon : ℤ))) := by
        gcongr
        norm_num
    _ = (1 / c1) * (2 : ℝ) ^ c0 * (2 : ℝ) ^ (IK F.toAITFrame W R)
          * (2 : ℝ) ^ (-((F.K xoff : ℤ) - (F.K xon : ℤ))) := by
        rw [show c0 + IK F.toAITFrame W R - ((F.K xoff : ℤ) - (F.K xon : ℤ))
              = c0 + IK F.toAITFrame W R + (-((F.K xoff : ℤ) - (F.K xon : ℤ))) from by ring,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        ring

/-- **Theorem 2 (sharp form), retaining the regulator cost `2^{−K(R)}`.**
    This is clarification (ii) of the ART paper / WP0162 Eq. (22): before dropping
    `2^{−K(R)}≤1`. No extra hypothesis is needed — the exponent identity is exact
    (the `K(R)` term carried through, not bounded away):
    `post (W,R) x ≤ C · 2^{M(W:R)} · 2^{−Δ} · 2^{−K(R)}`.
    The conditional-complexity form `≤ C' · 2^{−K(R∣W)} · 2^{−Δ}` used by WP0203
    (Eq. art, second line) follows from the two-sided chain rule
    `K(W,R) = K(W) + K(R∣W) ± O(log)`, a standard AIT fact that is **not** among this
    theorem's hypotheses; `ARTExactForm.conditional_art_specified` supplies that bridge, and
    the resulting factor `2^s` must stay visible in `C'` rather than be presented as a
    horizon-independent constant when `s = O(log N)` (WP0203 Round 1 fidelity audit, record
    A03). -/
theorem probabilistic_regulator_theorem_sharp
    (W R xon xoff : F.Obj)
    (c0 : ℤ) (hoff : (F.K xoff : ℤ) ≤ (F.K W : ℤ) + c0)
    {c1 : ℝ} (hLB : F.CodingLB c1) :
    ∃ C : ℝ, 0 < C ∧
      F.post (F.pair W R) xon
        ≤ C * (2 : ℝ) ^ (IK F.toAITFrame W R)
            * (2 : ℝ) ^ (-((F.K xoff : ℤ) - (F.K xon : ℤ)))
            * (2 : ℝ) ^ (-(F.K R : ℤ)) := by
  have hc1 := hLB.1
  refine ⟨(1 / c1) * (2 : ℝ) ^ c0, by positivity, ?_⟩
  -- exact exponent identity (K(R) retained, not dropped):
  have hexp : (F.K xon : ℤ) - (F.K (F.pair W R) : ℤ)
      ≤ c0 + IK F.toAITFrame W R - ((F.K xoff : ℤ) - (F.K xon : ℤ)) - (F.K R : ℤ) := by
    simp only [IK]; omega
  calc F.post (F.pair W R) xon
      ≤ (1 / c1) * (2 : ℝ) ^ ((F.K xon : ℤ) - (F.K (F.pair W R) : ℤ)) :=
        wrapper_bound F hLB _ _
    _ ≤ (1 / c1) * (2 : ℝ) ^ (c0 + IK F.toAITFrame W R
            - ((F.K xoff : ℤ) - (F.K xon : ℤ)) - (F.K R : ℤ)) := by
        gcongr
        norm_num
    _ = (1 / c1) * (2 : ℝ) ^ c0 * (2 : ℝ) ^ (IK F.toAITFrame W R)
          * (2 : ℝ) ^ (-((F.K xoff : ℤ) - (F.K xon : ℤ))) * (2 : ℝ) ^ (-(F.K R : ℤ)) := by
        rw [show c0 + IK F.toAITFrame W R - ((F.K xoff : ℤ) - (F.K xon : ℤ)) - (F.K R : ℤ)
              = c0 + IK F.toAITFrame W R + (-((F.K xoff : ℤ) - (F.K xon : ℤ)))
                  + (-(F.K R : ℤ)) from by ring,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        ring

/-- The published headline (Theorem 2) follows from the sharp form by `2^{−K(R)} ≤ 1`. -/
theorem probabilistic_regulator_theorem_of_sharp
    (W R xon xoff : F.Obj)
    (c0 : ℤ) (hoff : (F.K xoff : ℤ) ≤ (F.K W : ℤ) + c0)
    {c1 : ℝ} (hLB : F.CodingLB c1) :
    ∃ C : ℝ, 0 < C ∧
      F.post (F.pair W R) xon
        ≤ C * (2 : ℝ) ^ (IK F.toAITFrame W R)
            * (2 : ℝ) ^ (-((F.K xoff : ℤ) - (F.K xon : ℤ))) := by
  obtain ⟨C, hC, hsharp⟩ := probabilistic_regulator_theorem_sharp F W R xon xoff c0 hoff hLB
  refine ⟨C, hC, ?_⟩
  have hKR : (2 : ℝ) ^ (-(F.K R : ℤ)) ≤ 1 := by
    apply zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  calc F.post (F.pair W R) xon
      ≤ C * (2 : ℝ) ^ (IK F.toAITFrame W R)
          * (2 : ℝ) ^ (-((F.K xoff : ℤ) - (F.K xon : ℤ))) * (2 : ℝ) ^ (-(F.K R : ℤ)) := hsharp
    _ ≤ C * (2 : ℝ) ^ (IK F.toAITFrame W R)
          * (2 : ℝ) ^ (-((F.K xoff : ℤ) - (F.K xon : ℤ))) * 1 := by gcongr
    _ = C * (2 : ℝ) ^ (IK F.toAITFrame W R)
          * (2 : ℝ) ^ (-((F.K xoff : ℤ) - (F.K xon : ℤ))) := by ring

/-- **Theorem 3 (On/Off evidence equals the complexity gap).** The ON/OFF evidence ratio
    is `2^Δ` up to the coding constants, `Δ = K(O_{W,∅}) − K(O_{W,R})`:
    `(c₁/c₂)·2^{Δ} ≤ m(x_on)/m(x_off) ≤ (c₂/c₁)·2^{Δ}`.
    (Multiplicative form; taking `log₂` gives `log₂(m_on/m_off) = Δ ± log₂(c₂/c₁)`.) -/
theorem theorem3_onoff_evidence {c1 c2 : ℝ}
    (hLB : F.CodingLB c1) (hUB : F.CodingUB c2) (xon xoff : F.Obj) :
    (c1 / c2) * (2 : ℝ) ^ ((F.K xoff : ℤ) - (F.K xon : ℤ)) ≤ F.m xon / F.m xoff ∧
    F.m xon / F.m xoff ≤ (c2 / c1) * (2 : ℝ) ^ ((F.K xoff : ℤ) - (F.K xon : ℤ)) := by
  obtain ⟨hc1, hlb⟩ := hLB
  obtain ⟨hc2, hub⟩ := hUB
  have hmon := F.m_pos xon
  have hmof := F.m_pos xoff
  -- algebra:  (a·2^{-K xon}) / (b·2^{-K xoff})  =  (a/b)·2^{K xoff − K xon}
  have ealg : ∀ a b : ℝ,
      (a * (2 : ℝ) ^ (-(F.K xon : ℤ))) / (b * (2 : ℝ) ^ (-(F.K xoff : ℤ)))
        = (a / b) * (2 : ℝ) ^ ((F.K xoff : ℤ) - (F.K xon : ℤ)) := by
    intro a b
    have hh : ((F.K xoff : ℤ) - (F.K xon : ℤ)) = (-(F.K xon : ℤ)) - (-(F.K xoff : ℤ)) := by ring
    rw [mul_div_mul_comm, hh, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  refine ⟨?_, ?_⟩
  · rw [← ealg c1 c2]
    exact div_le_div₀ hmon.le (hlb xon) hmof (hub xoff)
  · rw [← ealg c2 c1]
    exact div_le_div₀ (by positivity) (hub xon) (by positivity) (hlb xoff)

/-! ## Specified programs and explicit constants -/

/-- Weight of a selected program of length `n`, using the full output evidence.
Compatibility and agreement with a prefix machine are separate hypotheses. -/
noncomputable def specifiedWeight (F : AITProb) (n : Nat) (x : F.Obj) : Real :=
  (2 : Real) ^ (-(n : Int)) / F.m x

/-- identify a compatible program's weight, retaining its signed
length offset delta relative to the chosen explanation's complexity. -/
theorem compatible_program_factor (F : AITProb) (M : PrefixMachine)
    (readout : M.Out → F.Obj) (p : M.Prog) (e x : F.Obj) (delta : Int)
    (_hcompat : readout (M.U p) = x)
    (hevidence : M.m (M.U p) = F.m x)
    (hlen : (M.len p : Int) = (F.K e : Int) + delta) :
    M.posterior p = specifiedWeight F (M.len p) x ∧
    M.posterior p = (2 : Real) ^ (-delta) * F.post e x := by
  have hweight : M.posterior p = specifiedWeight F (M.len p) x := by
    simp only [PrefixMachine.posterior, PrefixMachine.prior, specifiedWeight, hevidence]
  refine ⟨hweight, ?_⟩
  rw [hweight]
  unfold specifiedWeight AITProb.post
  rw [hlen, neg_add, zpow_add₀ (by norm_num : (2 : Real) ≠ 0)]
  ring

/-- coding sandwich for the actual specified length. -/
theorem specified_weight_coding_bounds (F : AITProb) {c1 c2 : Real}
    (hLB : F.CodingLB c1) (hUB : F.CodingUB c2)
    (e x : F.Obj) (n : Nat) (delta : Int)
    (hlen : (n : Int) = (F.K e : Int) + delta) :
    (1 / c2) * (2 : Real) ^ ((F.K x : Int) - (F.K e : Int) - delta)
      ≤ specifiedWeight F n x ∧
    specifiedWeight F n x
      ≤ (1 / c1) * (2 : Real) ^ ((F.K x : Int) - (F.K e : Int) - delta) := by
  have hc1 := hLB.1
  have hc2 := hUB.1
  have hm := F.m_pos x
  have hlo : 1 / c2 ≤ (2 : Real) ^ (-(F.K x : Int)) / F.m x := by
    rw [div_le_div_iff₀ hc2 hm, one_mul]
    nlinarith [hUB.2 x]
  have hhi : (2 : Real) ^ (-(F.K x : Int)) / F.m x ≤ 1 / c1 := by
    rw [div_le_div_iff₀ hm hc1, one_mul]
    nlinarith [hLB.2 x]
  have hfactor : specifiedWeight F n x =
      ((2 : Real) ^ (-(F.K x : Int)) / F.m x) *
        (2 : Real) ^ ((F.K x : Int) - (F.K e : Int) - delta) := by
    unfold specifiedWeight
    have hn : -(n : Int) = -(F.K x : Int) +
        ((F.K x : Int) - (F.K e : Int) - delta) := by omega
    rw [hn, zpow_add₀ (by norm_num : (2 : Real) ≠ 0), mul_div_right_comm]
  rw [hfactor]
  exact ⟨mul_le_mul_of_nonneg_right hlo (by positivity),
    mul_le_mul_of_nonneg_right hhi (by positivity)⟩

/-- Sharp ART with explicit coding, simulator, and wrapper costs. Uniform
interpretation requires fixed `c1,c0` and a uniformly bounded length offset;
the prefactor may vary with that offset while remaining uniformly bounded. -/
theorem sharp_art_specified (F : AITProb) {c1 : Real}
    (hLB : F.CodingLB c1) (W R x y0 : F.Obj)
    (c0 delta : Int) (n : Nat)
    (hoff : (F.K y0 : Int) ≤ (F.K W : Int) + c0)
    (hlen : (n : Int) = (F.K (F.pair W R) : Int) + delta) :
    specifiedWeight F n x ≤ ((1 / c1) * (2 : Real) ^ (c0 - delta)) *
      (2 : Real) ^ (IK F.toAITFrame W R - (F.K R : Int)
        - ((F.K y0 : Int) - (F.K x : Int))) := by
  have hc1 := hLB.1
  have hfactor : specifiedWeight F n x = (2 : Real) ^ (-delta) * F.post (F.pair W R) x := by
    unfold specifiedWeight AITProb.post
    rw [hlen, neg_add, zpow_add₀ (by norm_num : (2 : Real) ≠ 0)]
    ring
  have hexp : (F.K x : Int) - (F.K (F.pair W R) : Int)
      ≤ c0 + (IK F.toAITFrame W R - (F.K R : Int)
        - ((F.K y0 : Int) - (F.K x : Int))) := by
    simp only [IK]
    omega
  rw [hfactor]
  calc
    _ ≤ (2 : Real) ^ (-delta) * ((1 / c1) *
        (2 : Real) ^ ((F.K x : Int) - (F.K (F.pair W R) : Int))) :=
      mul_le_mul_of_nonneg_left (F.wrapper_bound hLB _ _) (by positivity)
    _ ≤ (2 : Real) ^ (-delta) * ((1 / c1) *
        (2 : Real) ^ (c0 + (IK F.toAITFrame W R - (F.K R : Int)
          - ((F.K y0 : Int) - (F.K x : Int))))) := by
      gcongr
      norm_num
    _ = _ := by
      rw [zpow_add₀ (by norm_num : (2 : Real) ≠ 0),
        show c0 - delta = -delta + c0 by ring,
        zpow_add₀ (by norm_num : (2 : Real) ≠ 0)]
      ring

/-- the constant is fixed before quantifying over candidates.
A family over horizons must supply the same c1, c0 and deltaMin. -/
theorem sharp_art_uniform (F : AITProb) (c1 : Real) (c0 deltaMin : Int)
    (hLB : F.CodingLB c1) :
    0 < (1 / c1) * (2 : Real) ^ (c0 - deltaMin) ∧
    ∀ (W R x y0 : F.Obj) (n : Nat),
      (F.K y0 : Int) ≤ (F.K W : Int) + c0 →
      (F.K (F.pair W R) : Int) + deltaMin ≤ (n : Int) →
      specifiedWeight F n x ≤ ((1 / c1) * (2 : Real) ^ (c0 - deltaMin)) *
        (2 : Real) ^ (IK F.toAITFrame W R - (F.K R : Int)
          - ((F.K y0 : Int) - (F.K x : Int))) := by
  have hc1 := hLB.1
  refine ⟨by positivity, ?_⟩
  intro W R x y0 n hoff hlen
  have hs := sharp_art_specified F hLB W R x y0 c0
    ((n : Int) - (F.K (F.pair W R) : Int)) n hoff (by omega)
  refine hs.trans ?_
  have hd : deltaMin ≤ (n : Int) - (F.K (F.pair W R) : Int) := by omega
  gcongr
  norm_num

end AITProb

/-! ## ART Theorem A4 — low-complexity output ⇒ strict (tiny) shrinkage -/

/-- **ART Theorem A4 (single-episode identifiability).** If observing the low-complexity event
    confines the world to a strict subset of the `m`-bit programs, the multiplicity-compression
    bound (Lemma A1) gives an index cost `idx` for `K(W | R, E_a)` strictly below the
    unconditioned `K(W)` — so a single low-complexity readout strictly lowers the world's
    complexity. (The counting bound `hcount` and `idx < K(W)` are the assumed AIT facts; the
    conclusion `K(W | R, E_a) < K(W)` is their consequence.) -/
theorem low_complexity_shrinkage {KcondE Kw idx : ℕ}
    (hcount : KcondE ≤ idx) (hidx : idx < Kw) : KcondE < Kw := by omega

end KTAIT
