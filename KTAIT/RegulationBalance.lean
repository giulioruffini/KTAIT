/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic

/-!
# KTAIT.RegulationBalance — the algorithmic regulation balance (WP0203 v2)

The positive replacement for the withdrawn ART concentration corollary. Where
`KTAIT.ModelOrPay` records what ART *cannot* deliver (a per-pair bound does not lift to a
tail bound), this module records what *does* hold once the omitted degrees of freedom are
put back on the books.

## The statement

Fix the ART horizon. Write `x` for the ON readout `O^(N)_{W,R}`, `y` for the OFF readout
`O^(N)_{W,∅}`, and `Δ = K y − K x` for the regulator gap. Let `Q` bundle the realized
regulator output transcript, the regulator's retained private state, and the *world
exhaust* — the minimal hidden world record needed, alongside the visible record, to recover
`y`. Then

  `Δ ≤ IK(y : R) + cIK(y : Q | ⟨x,R⟩) + slack`,   and by data processing
  `Δ ≤ IK(W : R) + cIK(y : Q | ⟨x,R⟩) + slack`.

Equivalently, in deficit form,

  `cIK(y : Q | ⟨x,R⟩) ≥ Δ − IK(W : R) − slack`:

the null-world information missing from the regulated readout must be present somewhere in
the rest of the realized episode. A regulator may open a gap by already carrying structure
of the world, by routing the missing information through its action stream, or by leaving
the removed distinctions in the world. It may not open one for free.

## What this is, and what it is not

The first inequality is an accounting identity: it is the chain rule plus the closure
condition that *defines* the exhaust as whatever recovers `y`. Its content is not
mathematical depth but **localization** — the residual is forced into three named places
rather than being allowed to vanish. The clamp family of `KTAIT.ModelOrPay` is not a
counterexample to it; it is the instance that saturates the exhaust term.

The substantive consequence is the rate form: with a regulator of fixed finite description
and bounded private memory, a *sustained extensive* gap needs an extensive world-specific
flow through action or exhaust. `balance_rate_finite` below is its finite-horizon core; the
limiting statement is analysis on top of it and is not formalized here.

## Discipline

As throughout KTAIT, the AIT facts are **hypotheses about a frame**, never global axioms.
Everything below is arithmetic over `Int` once those hypotheses are supplied.
-/

namespace KTAIT
namespace RegulationBalance

variable (F : AITFrame)

/-! ## Conditional mutual algorithmic information -/

/-- **Conditional mutual algorithmic information** `M(A : B | C)`, defined as
    `K(A|C) + K(B|C) − K(⟨A,B⟩|C)`. An `Int`, since it may be negative before the
    `O(log)` correction. -/
def cIK (A B C : F.Obj) : Int :=
  (F.cond A C : Int) + (F.cond B C : Int) - (F.cond (F.pair A B) C : Int)

/-- The **regulator gap** `Δ = K(y) − K(x)`, with `y` the OFF readout and `x` the ON
    readout. Matches `Δ` of the ART papers. -/
def gap (x y : F.Obj) : Int := (F.K y : Int) - (F.K x : Int)

/-! ## The AIT facts used, as named hypotheses -/

/-- **Mutual-information chain rule**, in the form the balance consumes:
    `K(y) ≤ M(y : R) + K(y | R) + slack`. (An equality up to `O(log)`; only `≤` is used.) -/
def MutualChain (y R : F.Obj) : Prop :=
  (F.K y : Int) ≤ IK F y R + (F.cond y R : Int) + (F.slack : Int)

/-- **Subadditivity through an intermediate**: `K(y | R) ≤ K(x | R) + K(y | ⟨x,R⟩) + slack`.
    Describe `x` given `R`, then `y` given both. -/
def CondSubadd (x y R : F.Obj) : Prop :=
  (F.cond y R : Int) ≤ (F.cond x R : Int) + (F.cond y (F.pair x R) : Int) + (F.slack : Int)

/-- **Monotonicity of conditioning**: `K(x | R) ≤ K(x)`. -/
def CondMono (x R : F.Obj) : Prop := (F.cond x R : Int) ≤ (F.K x : Int)

/-- **Conditional chain rule**: `K(⟨y,Q⟩ | C) ≤ K(Q | C) + K(y | ⟨Q,C⟩) + slack`. -/
def CondChain (y Q C : F.Obj) : Prop :=
  (F.cond (F.pair y Q) C : Int)
    ≤ (F.cond Q C : Int) + (F.cond y (F.pair Q C) : Int) + (F.slack : Int)

/-- **Information closure** of the realized episode: given the visible record `C = ⟨x,R⟩`
    and the completion `Q`, the null readout is determined up to `slack`,
    `K(y | ⟨Q,C⟩) ≤ slack`. This is what makes `Q` an admissible completion; it is the
    formal content of "the exhaust is whatever, with the visible record, recovers `y`". -/
def InfoClosed (y Q C : F.Obj) : Prop :=
  (F.cond y (F.pair Q C) : Int) ≤ (F.slack : Int)

/-- **Algorithmic data processing**: `y` is computable from `W` at the fixed horizon, so
    `M(y : R) ≤ M(W : R) + slack`. -/
def DataProcessing (y W R : F.Obj) : Prop :=
  IK F y R ≤ IK F W R + (F.slack : Int)

/-! ## The residual lemma -/

/-- **The residual is mutual information with the completion.** Under the conditional chain
    rule and information closure, the conditional complexity of the null readout given the
    visible record is bounded by its conditional mutual information with `Q`:
    `K(y | C) ≤ M(y : Q | C) + 2·slack`.

    This is the step that converts "there is a residual" into "the residual sits in `Q`". -/
theorem residual_in_completion (y Q C : F.Obj)
    (hchain : CondChain F y Q C) (hclosed : InfoClosed F y Q C) :
    (F.cond y C : Int) ≤ cIK F y Q C + 2 * (F.slack : Int) := by
  simp only [CondChain, InfoClosed] at hchain hclosed
  simp only [cIK]
  omega

/-! ## The balance -/

/-- **Theorem (algorithmic regulation balance), model-content form.**
    `Δ ≤ M(y : R) + M(y : Q | ⟨x,R⟩) + 4·slack`.

    The gap a regulator opens is bounded by what it shares with the null readout plus the
    world-relevant information carried by the rest of the episode. -/
theorem balance_readout (x y R Q : F.Obj)
    (hmut : MutualChain F y R)
    (hsub : CondSubadd F x y R)
    (hmono : CondMono F x R)
    (hchain : CondChain F y Q (F.pair x R))
    (hclosed : InfoClosed F y Q (F.pair x R)) :
    gap F x y ≤ IK F y R + cIK F y Q (F.pair x R) + 4 * (F.slack : Int) := by
  have hres := residual_in_completion F y Q (F.pair x R) hchain hclosed
  simp only [MutualChain, CondSubadd, CondMono] at hmut hsub hmono
  simp only [gap]
  omega

/-- **Theorem (algorithmic regulation balance), ART form.**
    `Δ ≤ M(W : R) + M(y : Q | ⟨x,R⟩) + 5·slack`.

    This is the inequality quoted in the paper: static model content plus episode flow. -/
theorem balance (W x y R Q : F.Obj)
    (hmut : MutualChain F y R)
    (hsub : CondSubadd F x y R)
    (hmono : CondMono F x R)
    (hchain : CondChain F y Q (F.pair x R))
    (hclosed : InfoClosed F y Q (F.pair x R))
    (hdp : DataProcessing F y W R) :
    gap F x y ≤ IK F W R + cIK F y Q (F.pair x R) + 5 * (F.slack : Int) := by
  have h := balance_readout F x y R Q hmut hsub hmono hchain hclosed
  simp only [DataProcessing] at hdp
  omega

/-- **Deficit form.** The information missing from the regulated readout must be somewhere:
    `M(y : Q | ⟨x,R⟩) ≥ Δ − M(W : R) − 5·slack`.

    A regulator with little model content that nonetheless opens a large gap is *forced* to
    have routed the difference through its actions, its memory, or the world. -/
theorem deficit (W x y R Q : F.Obj)
    (hmut : MutualChain F y R)
    (hsub : CondSubadd F x y R)
    (hmono : CondMono F x R)
    (hchain : CondChain F y Q (F.pair x R))
    (hclosed : InfoClosed F y Q (F.pair x R))
    (hdp : DataProcessing F y W R) :
    cIK F y Q (F.pair x R) ≥ gap F x y - IK F W R - 5 * (F.slack : Int) := by
  have h := balance F W x y R Q hmut hsub hmono hchain hclosed hdp
  omega

/-- **Finite-horizon core of the rate form.** If the static model content is at most `m`
    and the episode flow at most `f`, the gap cannot exceed `m + f + 5·slack`.

    Taking a family of horizons with `m = o(N)` and dividing by `N` gives the rate
    statement of the paper: a sustained extensive gap needs an extensive flow. That limiting
    step is analysis and is deliberately left outside the formalization. -/
theorem balance_rate_finite (W x y R Q : F.Obj) (m f : Int)
    (hmut : MutualChain F y R)
    (hsub : CondSubadd F x y R)
    (hmono : CondMono F x R)
    (hchain : CondChain F y Q (F.pair x R))
    (hclosed : InfoClosed F y Q (F.pair x R))
    (hdp : DataProcessing F y W R)
    (hm : IK F W R ≤ m)
    (hf : cIK F y Q (F.pair x R) ≤ f) :
    gap F x y ≤ m + f + 5 * (F.slack : Int) := by
  have h := balance F W x y R Q hmut hsub hmono hchain hclosed hdp
  omega

/-! ## The trichotomy

By the conditional chain rule for mutual algorithmic information, the episode flow splits
into the contributions of the action transcript, the retained private state, and the world
exhaust. We record the split as a named hypothesis rather than re-deriving the chain rule,
and note its consequence: when two of the three vanish, the third carries the whole
deficit. -/

/-- **Three-way split of the episode flow** (conditional chain rule), with
    `Q = ⟨Oact, ⟨Sreg, Exh⟩⟩` the completion and `C` the visible record:

    `M(y : Q | C) ≤ M(y : Oact | C) + M(y : Sreg | ⟨Oact,C⟩)
                    + M(y : Exh | ⟨Sreg,⟨Oact,C⟩⟩) + slack`. -/
def FlowSplit (y Oact Sreg Exh Q C : F.Obj) : Prop :=
  cIK F y Q C
    ≤ cIK F y Oact C
      + cIK F y Sreg (F.pair Oact C)
      + cIK F y Exh (F.pair Sreg (F.pair Oact C))
      + (F.slack : Int)

/-- **Model it, transmit it, or leave it in the world.** A regulator carrying no model
    content, whose action transcript says nothing about the null readout and whose private
    state retains nothing, cannot open a gap beyond what its world exhaust accounts for.

    This is the clamp regime: the counterexample of `KTAIT.ModelOrPay` does not violate the
    balance, it saturates the exhaust term. -/
theorem gap_forces_exhaust (W x y R Q Oact Sreg Exh : F.Obj)
    (hmut : MutualChain F y R)
    (hsub : CondSubadd F x y R)
    (hmono : CondMono F x R)
    (hchain : CondChain F y Q (F.pair x R))
    (hclosed : InfoClosed F y Q (F.pair x R))
    (hdp : DataProcessing F y W R)
    (hsplit : FlowSplit F y Oact Sreg Exh Q (F.pair x R))
    (hmodel : IK F W R ≤ 0)
    (hact : cIK F y Oact (F.pair x R) ≤ 0)
    (hstate : cIK F y Sreg (F.pair Oact (F.pair x R)) ≤ 0) :
    gap F x y ≤ cIK F y Exh (F.pair Sreg (F.pair Oact (F.pair x R))) + 6 * (F.slack : Int) := by
  have h := balance F W x y R Q hmut hsub hmono hchain hclosed hdp
  simp only [FlowSplit] at hsplit
  omega

/-! ## Localization: what stops the accounting closing by fiat

WP0203 v4 adds the load-bearing hypothesis. If the exhaust were an arbitrary auxiliary
string, the choice `Ξ := y` would satisfy closure trivially and the balance would be
vacuous. v4 forbids that by requiring `Ξ = π_Ξ(S)`, a fixed projection of the realized
world-side record `S`, chosen independently of the null readout.

The physical-state structure (what a "world-side record" is, and that the projection is
fixed independently of `y`) is not expressible in an `AITFrame` and is not formalized. What
*is* formalizable is the anti-vacuity content: a localized exhaust cannot manufacture
recovery that the world record does not already support. -/

/-- **Localization**, at frame level: the exhaust is recoverable from the realized
    world-side record `S`, i.e. `K(Ξ | S) ≤ slack`. This is the frame-level shadow of
    `Ξ = π_Ξ(S)`; it does not capture that the projection is fixed independently of `y`. -/
def Localized (Exh S : F.Obj) : Prop := (F.cond Exh S : Int) ≤ (F.slack : Int)

/-- Monotonicity of conditioning in the second argument, as a named hypothesis:
    conditioning on more cannot cost more. -/
def CondMonoMore (A B C : F.Obj) : Prop :=
  (F.cond A (F.pair B C) : Int) ≤ (F.cond A B : Int)

/-- Subadditivity through the exhaust: `K(y | ⟨S,C⟩) ≤ K(Ξ | ⟨S,C⟩) + K(y | ⟨Ξ,C⟩) + slack`. -/
def SubaddVia (y Exh S C : F.Obj) : Prop :=
  (F.cond y (F.pair S C) : Int)
    ≤ (F.cond Exh (F.pair S C) : Int) + (F.cond y (F.pair Exh C) : Int) + (F.slack : Int)

/-- **A localized exhaust cannot close the accounting by fiat.** If `Ξ` is a projection of
    the world-side record `S`, and `Ξ` together with the visible episode `C` recovers `y`,
    then `S` together with `C` already recovered `y`:

    `K(y | ⟨S,C⟩) ≤ 3·slack`.

    This is the formal content of v4's localization clause. Its contrapositive is the one
    that bites, and is stated next. -/
theorem localized_closure_needs_world_record (y Exh S C : F.Obj)
    (hloc : Localized F Exh S)
    (hmono : CondMonoMore F Exh S C)
    (hsub : SubaddVia F y Exh S C)
    (hclosed : (F.cond y (F.pair Exh C) : Int) ≤ (F.slack : Int)) :
    (F.cond y (F.pair S C) : Int) ≤ 3 * (F.slack : Int) := by
  simp only [Localized, CondMonoMore, SubaddVia] at hloc hmono hsub
  omega

/-- **Anti-vacuity.** If the realized world-side record, together with the visible episode,
    does *not* determine the null readout, then no localized exhaust satisfies closure — so
    the realization is not information-closed and the balance does not apply to it.

    This is what rules out `Ξ := y` unless that information is genuinely instantiated in the
    realized world. -/
theorem no_localized_exhaust_of_world_record_insufficient (y Exh S C : F.Obj)
    (hmono : CondMonoMore F Exh S C)
    (hsub : SubaddVia F y Exh S C)
    (hbad : 3 * (F.slack : Int) < (F.cond y (F.pair S C) : Int)) :
    ¬ (Localized F Exh S ∧ (F.cond y (F.pair Exh C) : Int) ≤ (F.slack : Int)) := by
  rintro ⟨hloc, hclosed⟩
  have := localized_closure_needs_world_record F y Exh S C hloc hmono hsub hclosed
  omega

/-! ## The cyclic form

WP0203 v4, Corollary (cyclic form): a regulator returning its private state to a standard
state drops the memory channel, leaving the three-way statement of the title. -/

/-- The private state is (nearly) determined by the visible episode: `K(σ | C) ≤ slack`. -/
def CyclicMemory (Sreg C : F.Obj) : Prop := (F.cond Sreg C : Int) ≤ (F.slack : Int)

/-- `M(y : B | C) ≤ K(B | C)`, since `y` is computable from `⟨y,B⟩`. Named hypothesis. -/
def MutualBelowCond (y B C : F.Obj) : Prop :=
  cIK F y B C ≤ (F.cond B C : Int)

/-- **Cyclic form.** With a cyclic regulator the private-memory channel contributes only
    `slack`, so the deficit is carried by model content, action, and exhaust alone —
    *model it, transmit it, or leave it in the world*. -/
theorem cyclic_form (W x y R Q Oact Sreg Exh : F.Obj)
    (hmut : MutualChain F y R)
    (hsub : CondSubadd F x y R)
    (hmono : CondMono F x R)
    (hchain : CondChain F y Q (F.pair x R))
    (hclosed : InfoClosed F y Q (F.pair x R))
    (hdp : DataProcessing F y W R)
    (hsplit : FlowSplit F y Oact Sreg Exh Q (F.pair x R))
    (hcyc : CyclicMemory F Sreg (F.pair Oact (F.pair x R)))
    (hbound : MutualBelowCond F y Sreg (F.pair Oact (F.pair x R))) :
    gap F x y
      ≤ IK F W R
        + cIK F y Oact (F.pair x R)
        + cIK F y Exh (F.pair Sreg (F.pair Oact (F.pair x R)))
        + 7 * (F.slack : Int) := by
  have h := balance F W x y R Q hmut hsub hmono hchain hclosed hdp
  simp only [FlowSplit] at hsplit
  simp only [CyclicMemory] at hcyc
  simp only [MutualBelowCond] at hbound
  omega

end RegulationBalance
end KTAIT
