/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic

/-!
# KTAIT.WriteBack — WP0058: bandwidth of the write-back channel

Companion to `KTAIT.Decoder`, which settles the *computability* half of WP0058
Proposition 1 (no total, domain-recognizing inverse compiler). Here we do the
*algorithmic-information* half, and Proposition 2.

Setting: a lineage transmits a heritable program `H`; the agent acquires structure `a`
during life; the descendant program is `H'`. The **write-back bandwidth** is the acquired
information that reaches the descendant beyond what the parent already carried,
`λ_B := I(a : H' | H)` (WP0058 Definition 3), a rate in bits per generation.

Scope. WP0058 indexes the write-back parameters by architectural layer *and* channel
property, `λ_{ℓc}` with `ℓ ∈ {A, M, Π, O}` and `c ∈ {B, F, P}`. That object is a *profile* —
a point in `∏_ℓ (ℝ≥0 × [0,1] × ℝ>0)` — and neither a matrix nor a vector: nothing acts,
nothing composes, and the three entries of a row carry different units. (The transmission
operator `T` *is* an operator, being a Markov kernel; the write-back map `C` is a partial
map. Three objects, three kinds.) What follows formalizes a *single coordinate* of the
profile: the bandwidth `λ_B`, for one unnamed layer. Fidelity, persistence, and the layer
index play no role in these bounds, which is itself informative — they hold coordinate by
coordinate.

The results all descend from one lemma, `bandwidth_le_cond`: bandwidth is capped by
`K(H' | H)`, the novelty of the descendant program given the parent. Whatever channel
produces `H'` therefore fixes the cap:

* **Darwinian** (`darwinian_bandwidth_le_selection`): acquired information reaches `H'` only
  through a scalar selection signal `σ` (variation is undirected), so by data processing
  `λ_B ≤ I(a:σ|H) ≤ K(σ)`. Zeroth-order search — no matter how much the agent learned, only
  the selection signal crosses. The bound is on the *mutual information*, not on `K(H'|H)`:
  undirected mutation makes `K(H'|H)` large but carries nothing about `a`.
* **Lamarckian** (`lamarckian_bandwidth_le_decoder_image`): acquired information reaches `H'`
  only through the decoder output `C(a)`, so `λ_B ≤ I(a:C(a)|H) ≤ K(C(a) | H)`. First-order
  search — the cap is the decoder image, and `trivial_decoder_transmits_nothing` shows it
  binds: a decoder with nothing to say transmits nothing, however much was acquired.

Separately, `decoder_charged` is the second half of Proposition 1: a decoder recoverable
from the heritable program costs no more than that program, `K(C) ≤ K(H) + O(1)`. Together
with `Decoder.no_universal_decoder` this is the paper's Corollary 1 — the write-back
channel is bounded by prior structure, so it cannot bootstrap novelty.

Per the project methodology, the two AIT facts used (`JointGeMarginal`, `SubadditivityCond`)
are named `Prop`s about a frame, never global axioms. `ToyWB` witnesses that they are
satisfiable *and* that the bounds are attained (`toyWB_selection_bound_tight`), so the
corollaries are not vacuous.
-/

namespace KTAIT
namespace WriteBack

variable (F : AITFrame)

/-! ### Definitions -/

/-- Conditional mutual algorithmic information `I(x : y | z) = K(x|z) + K(y|z) − K(⟨x,y⟩|z)`.
An `Int`, since it can be negative before the `O(log)` correction. -/
def condIK (x y z : F.Obj) : Int :=
  (F.cond x z : Int) + (F.cond y z : Int) - (F.cond (F.pair x y) z : Int)

/-- **Total acquired information reaching the descendant**, `I(a : H' | H)`. This is *not* the
write-back bandwidth: in a strictly Darwinian lineage it is nonzero, because acquired structure
influences *who reproduces* and hence which program is transmitted. It is bounded by `K(σ)`
(`darwinian_bandwidth_le_selection`), not by zero. WP0058 calls it `λ_sel + λ_B`. -/
def bandwidth (a H' H : F.Obj) : Int := condIK F a H' H

/-- **Write-back bandwidth** `λ_B := I(w : H' | H, σ)` (WP0058 Definition 3, revised).

`w = C(a)` is the *write-back message*: the designated channel variable through which acquired
structure — and nothing else — may enter the descendant program. Defining `λ_B` on `w` rather
than on `a` attaches the quantity to the channel instead of inferring it from all residual
dependence of `a`, and conditioning on `σ` blocks the selection path `a → σ → H'`.

Two honesty notes. (1) Conditional mutual information still does not *identify* a causal path;
it isolates the write-back channel only under the stipulated factorization
`H' ~ T(H, σ, C(a), ξ)` with `ξ` independent of `a`, and with no other `a`-dependent path. That
premise is architectural and is carried by `Darwinian`/`Lamarckian`, not derived here.
(2) There is deliberately no `λ_sel := I(a:H'|H) − λ_B`: conditional mutual information is not
additively decomposable, the difference can be negative under synergy or suppression, and it
need not equal information carried through selection. The two channels are reported separately. -/
def writeBack (w H' H σ : F.Obj) : Int := condIK F H' w (F.pair H σ)

/-! ### The AIT facts, as named hypotheses -/

/-- **Joint dominates marginal.** A pair is no simpler than its first component, up to the
`O(log)` slack: `K(x|z) ≤ K(⟨x,y⟩|z) + O(log)`. -/
def JointGeMarginal (F : AITFrame) : Prop :=
  ∀ x y z : F.Obj, (F.cond x z : Int) ≤ (F.cond (F.pair x y) z : Int) + F.slack

/-- **Conditional subadditivity.** Describe `y`, then describe `x` given `y`:
`K(x) ≤ K(x|y) + K(y) + O(log)`. -/
def SubadditivityCond (F : AITFrame) : Prop :=
  ∀ x y : F.Obj, F.K x ≤ F.cond x y + F.K y + F.slack

/-- **Conditioning does not increase complexity.** Extra context can only help:
`K(x|y) ≤ K(x) + O(log)`. -/
def CondLeUncond (F : AITFrame) : Prop :=
  ∀ x y : F.Obj, (F.cond x y : Int) ≤ (F.K x : Int) + F.slack

/-! ### The channel bound -/

/-- **The master bound.** Write-back bandwidth is capped by the novelty of the descendant
program given the parent, `λ_B ≤ K(H'|H) + O(log)`. Nothing about `a` appears on the right:
however much is acquired, only what makes `H'` differ from `H` can carry it. -/
theorem bandwidth_le_cond (hJ : JointGeMarginal F) (a H' H : F.Obj) :
    bandwidth F a H' H ≤ (F.cond H' H : Int) + F.slack := by
  have h := hJ a H' H
  unfold bandwidth condIK
  omega

/-- **Mutual information is bounded by the description length of either side.**
`I(a : z | H) ≤ K(z | H) + O(log)`. This is the data-processing tool: whatever channel
variable `z` the acquired state must pass through, the information it can carry is capped by
the complexity of that channel — not by how much was acquired. -/
theorem condIK_le_condRight (hJ : JointGeMarginal F) (a z H : F.Obj) :
    condIK F a z H ≤ (F.cond z H : Int) + F.slack := by
  have h := hJ a z H
  unfold condIK
  omega

/-! ### Darwinian and Lamarckian regimes -/

/-- The **Darwinian** transmission regime (WP0058 Definition 1): variation is *undirected*.
The descendant `H'` is produced from the parent `H`, a scalar selection signal `σ`, and
variation randomness that carries no information about the acquired state `a`. So the only
channel from `a` into `H'` is the selection signal, giving the data-processing bound
`I(a : H' | H) ≤ I(a : σ | H)`. Note what is **not** claimed: `K(H'|H)` may be large —
undirected mutation is incompressible — but none of that novelty is correlated with what was
learned, so it does not enter the bandwidth. (The earlier `K(H'|H) ≤ K(σ)` form was false in
exactly this regime, since it charged the mutation randomness to the scalar signal.) -/
structure Darwinian (a H' H σ : F.Obj) : Prop where
  /-- Data processing: acquired information reaches `H'` only through the selection signal.
  This bounds the *total* information, which is nonzero in general. -/
  undirected : bandwidth F a H' H ≤ condIK F a σ H + F.slack

/-- **WP0058 Proposition 2, Darwinian half (the substantive part).** The *total* acquired
information reaching the descendant passes only through the scalar selection signal, so it is
bounded by `K(σ)` — however much the agent learned. This is the zeroth-order search bound, and
it is a genuine theorem. -/
theorem darwinian_bandwidth_le_selection (hJ : JointGeMarginal F) (hC : CondLeUncond F)
    {a H' H σ : F.Obj} (hD : Darwinian F a H' H σ) :
    bandwidth F a H' H ≤ (F.K σ : Int) + 3 * F.slack := by
  have h₁ := hD.undirected
  have h₂ := condIK_le_condRight F hJ a σ H
  have h₃ := hC σ H
  omega

/-- **WP0058 Proposition 2, Lamarckian half.** The write-back bandwidth is bounded by the
description length of the write-back message itself: `λ_B ≤ K(w | H, σ) + O(log)`. Because `λ_B`
is *defined* on `w`, this needs no data-processing hypothesis — it is immediate. The channel can
be wide, but only as wide as the message. -/
theorem lamarckian_bandwidth_le_decoder_image (hJ : JointGeMarginal F) (w H' H σ : F.Obj) :
    writeBack F w H' H σ ≤ (F.cond w (F.pair H σ) : Int) + F.slack :=
  condIK_le_condRight F hJ H' w (F.pair H σ)

/-- **Darwinian: no write-back message, hence no write-back.** If there is no message to send —
`K(w | H, σ) = O(log)`, the degenerate `w` of a lineage with no decoder — then `λ_B = O(log)`.

The regime premise is the *absence of the message*, which is architectural and posited: an
information measure cannot certify that a causal path is missing. -/
theorem no_message_no_write_back (hJ : JointGeMarginal F) {w H' H σ : F.Obj}
    (hw : (F.cond w (F.pair H σ) : Int) ≤ F.slack) :
    writeBack F w H' H σ ≤ 2 * F.slack := by
  have h := lamarckian_bandwidth_le_decoder_image F hJ w H' H σ
  omega

/-- **The bite of Corollary 1.** A write-back message that is trivial given the parent program
and the selection signal transmits nothing — the bound never mentions the acquired state `a` at
all. Write-back is capped by the message its decoder can form, not by how much was learned.

This is the whole of what is proved. It does **not** say the decoder's representational axes were
found by prior Darwinian search, nor that write-back cannot produce novelty. -/
theorem trivial_decoder_transmits_nothing (hJ : JointGeMarginal F) {w H' H σ : F.Obj}
    (hw : (F.cond w (F.pair H σ) : Int) ≤ F.slack) :
    writeBack F w H' H σ ≤ 2 * F.slack :=
  no_message_no_write_back F hJ hw

/-! ### The decoder is charged to the heritable program -/

/-- The decoder is **recoverable from** the heritable program: given `H`, describing the
decoder costs only the `O(log)` slack. This is what it means for the write-back machinery to
be specified by structure the lineage transmits. -/
def RecoverableFrom (F : AITFrame) (Cprog H : F.Obj) : Prop := F.cond Cprog H ≤ F.slack

/-- **WP0058 Proposition 1, AIT half.** A decoder recoverable from the heritable program is
charged to it: `K(C) ≤ K(H) + O(log)`. Combined with `Decoder.no_universal_decoder` — which
forces the decoder to be a partial map with a domain fixed in advance — this is the paper's
Corollary 1: Lamarckian write-back is bounded by prior structure, hence parasitic on the
Darwinian search that produced it, and cannot bootstrap novelty. -/
theorem decoder_charged (hS : SubadditivityCond F) {Cprog H : F.Obj}
    (h : RecoverableFrom F Cprog H) :
    F.K Cprog ≤ F.K H + 2 * F.slack := by
  have h₁ := hS Cprog H
  unfold RecoverableFrom at h
  omega

/-! ### Satisfiability witness

A frame in which both AIT hypotheses hold, the bandwidth is genuinely positive, and the
Darwinian bound is attained — so none of the above is vacuously true. -/

/-- Witness frame: `K := id`, `K(x|y) := x − y` (truncated), `⟨x,y⟩ := max x y`, no slack. -/
def ToyWB : AITFrame where
  Obj := Nat
  K := id
  pair := fun x y => max x y
  cond := fun x y => x - y
  star := id
  slack := 0

theorem toyWB_jointGeMarginal : JointGeMarginal ToyWB := by
  intro x y z; simp only [ToyWB]; omega

theorem toyWB_subadditivityCond : SubadditivityCond ToyWB := by
  intro x y; simp only [ToyWB, id]; omega

theorem toyWB_condLeUncond : CondLeUncond ToyWB := by
  intro x y; simp only [ToyWB, id]; omega

/-- The bandwidth is genuinely positive here: acquiring `a = 10` from a parent `H = 1`
transmits `3` bits into `H' = 4`. The interface is not degenerate. -/
theorem toyWB_bandwidth_pos :
    bandwidth ToyWB (10 : Nat) (4 : Nat) (1 : Nat) = 3 := by
  simp only [bandwidth, condIK, ToyWB]
  norm_num

/-- The Darwinian selection bound is **attained**: with `a = 5`, `H' = 3`, empty parent `H = 0`
and selection signal `σ = 3`, the cap `total ≤ K(σ)` is met with equality. Not vacuous. -/
theorem toyWB_selection_bound_tight :
    Darwinian ToyWB (5 : Nat) (3 : Nat) (0 : Nat) (3 : Nat) ∧
      bandwidth ToyWB (5 : Nat) (3 : Nat) (0 : Nat) = ((3 : Nat) : Int) := by
  refine ⟨⟨?_⟩, ?_⟩
  · simp only [bandwidth, condIK, ToyWB]; norm_num
  · simp only [bandwidth, condIK, ToyWB]; norm_num

/-- **The separation, machine-checked.** A Darwinian lineage has no write-back message (`w = 0`,
trivial), so `λ_B = 0` — while the *total* acquired information reaching the descendant is `3 ≠ 0`,
because acquired structure influenced who reproduced. The two quantities genuinely differ, which is
exactly why Definition 3 is stated on the message `w` and conditioned on `σ`. Defining `λ_B` as
`I(a : H' | H)` would have made the "Darwinian edge λ_B = 0" false. -/
theorem toyWB_writeback_zero_but_total_positive :
    writeBack ToyWB (0 : Nat) (3 : Nat) (0 : Nat) (3 : Nat) = 0 ∧
      bandwidth ToyWB (5 : Nat) (3 : Nat) (0 : Nat) = ((3 : Nat) : Int) := by
  constructor
  · simp only [writeBack, condIK, ToyWB]; norm_num
  · simp only [bandwidth, condIK, ToyWB]; norm_num

/-- The Lamarckian write-back bound is attained: message `w = 3` delivers exactly `3` bits. -/
theorem toyWB_lamarckian_bound_tight :
    writeBack ToyWB (3 : Nat) (3 : Nat) (0 : Nat) (0 : Nat) = ((3 : Nat) : Int) ∧
      (ToyWB.cond (3 : Nat) (ToyWB.pair (0 : Nat) (0 : Nat)) : Int) = ((3 : Nat) : Int) := by
  constructor
  · simp only [writeBack, condIK, ToyWB]; norm_num
  · simp only [ToyWB]; norm_num

end WriteBack
end KTAIT
