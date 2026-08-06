/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic
import KTAIT.ShiftInvariance

/-!
# KTAIT.IS.CommonSemantics — WP0215: what a shared semantics forces two descriptions to share

Formalization of the common-semantics lower bound of BCOM WP0215, *The Simulation Is
Phenomenally Itself*. Two descriptions `p` and `q` from which the same finite semantic object
`Fo` (a truth table, an intervention-response table, a finite trace) can be recovered cheaply
must share at least `K(Fo)` bits of algorithmic information.

Three points about the encoding.

**The `O(log n)` is explicit.** The paper writes `I_K(p:q) ≥ K(Fo) − O(log n)`. Inside Lean the
correction is the frame's `slack` field, and the bound comes out as `K(Fo) − c₁ − c₂ − 4·slack`,
with `c₁, c₂` the stated recovery costs and the coefficient `4` counting the four inequalities
chained below. Nothing asymptotic is hidden in the kernel: read `slack` as the `O(log n)` term
and the coefficient as the constant the chain actually pays.

**Recovery costs are conditioned on `p*`, not on `p`.** `Fr.cond Fo (Fr.star p)` is `K(Fo | p*)`.
The raw-`y` form is the error `BadStatements.rawy_form_fails` machine-checks as wrong, so the
hypotheses here are stated on `condStar`'s underlying `cond … (star …)` and never on `cond … p`.

**The bound is about information, not organization.** `common_semantics_does_not_give_structure`
exhibits a frame in which the bound is attained exactly while `K(p | q*)` is as large as one
likes: `p` and `q` share their semantics and nothing else. Near-minimality — which the paper
adds separately, and which is not assumed here — is what would force them to share almost all of
their information; even then it forces shared *information*, never shared causal form.

As everywhere in this development, the AIT facts (`DataProcessingIK`, `SelfInfo`, and
`PairSymmetric` from `KTAIT.ShiftInvariance`) are named `Prop`s about a frame, consumed as
hypotheses, never global `axiom`s. `ToyIS` witnesses that the three hold simultaneously.
-/

namespace KTAIT
namespace IS

/-! ### The AIT facts, as named hypotheses -/

/-- **Data processing for algorithmic mutual information.** Computing `z` from `x` cannot create
information about `y`: whatever `z` shares with `y` is bounded by what `x` shares with `y`, plus
the cost `K(z | x*)` of the transformation, plus the `O(log)` slack.

  `I_K(z : y) ≤ I_K(x : y) + K(z | x*) + O(log)`.

The conditioning is on the shortest program `x*`, as symmetry of information requires. -/
def DataProcessingIK (Fr : AITFrame) : Prop :=
  ∀ x y z : Fr.Obj,
    IK Fr z y ≤ IK Fr x y + (Fr.cond z (Fr.star x) : Int) + (Fr.slack : Int)

/-- **An object carries its own information.** `K(x) ≤ I_K(x : x) + O(log)`, since `K(⟨x,x⟩)`
exceeds `K(x)` only by the cost of duplication. -/
def SelfInfo (Fr : AITFrame) : Prop :=
  ∀ x : Fr.Obj, (Fr.K x : Int) - (Fr.slack : Int) ≤ IK Fr x x

/-! ### The bound -/

/-- **The common-semantics lower bound** (WP0215, the algorithmic-information proposition of
its equivalence-hierarchy section).

If a finite semantic object `Fo` is recoverable from `p` at cost `c₁` and from `q` at cost `c₂`
— both costs measured against the shortest programs `p*`, `q*` — then

  `I_K(p : q) ≥ K(Fo) − c₁ − c₂ − 4·slack`.

Two descriptions of the same finite semantics cannot be algorithmically independent: their
shared information contains the information specifying that semantics, net of the recovery costs
and the `O(log)` corrections.

The chain is four inequalities, one per slack term: `K(Fo)` is carried by `I_K(Fo : Fo)`
(`SelfInfo`); routing the first argument through `q` costs `c₂` (`DataProcessingIK`); swapping
the arguments costs a swap program (`PairSymmetric`); routing the second argument through `p`
costs `c₁` (`DataProcessingIK` again). -/
theorem common_semantics_bound (Fr : AITFrame)
    (hDP : DataProcessingIK Fr) (hself : SelfInfo Fr) (hpair : PairSymmetric Fr)
    (p q Fo : Fr.Obj) (c₁ c₂ : ℕ)
    (h₁ : Fr.cond Fo (Fr.star p) ≤ c₁) (h₂ : Fr.cond Fo (Fr.star q) ≤ c₂) :
    (Fr.K Fo : Int) - c₁ - c₂ - 4 * (Fr.slack : Int) ≤ IK Fr p q := by
  -- K(Fo) ≤ I(Fo : Fo) + slack
  have hA := hself Fo
  -- I(Fo : Fo) ≤ I(q : Fo) + K(Fo | q*) + slack ≤ I(q : Fo) + c₂ + slack
  have hB := hDP q Fo Fo
  -- I(q : Fo) ≤ I(Fo : q) + slack  (pairing is symmetric up to a swap program)
  have hC := hpair q Fo
  -- I(Fo : q) ≤ I(p : q) + K(Fo | p*) + slack ≤ I(p : q) + c₁ + slack
  have hD := hDP p q Fo
  simp only [IK] at hA hB hC hD ⊢
  omega

/-- **The bound with the costs left in place.** The same statement with the recovery costs as the
frame's own conditional complexities rather than as stipulated budgets `c₁, c₂`.

Instantiating `Fo` at a finite intervention-response table `T_D(f)` gives the reading the paper
wants — the common structure an experiment establishes grows with the repertoire `D`, because
`K(Fo)` does. What is *not* formalized here is the paper's `D`-conditioned inequality
`I_K(p : q | D) ≥ K(T_D(f) | D) − O(log n)`: conditional mutual algorithmic information lives in
`WriteBack.condIK`, and the conditional analogues of `DataProcessingIK` and `SelfInfo` would have
to be stated and witnessed before that form could be proved. The bound below is unconditional. -/
theorem common_semantics_bound_raw (Fr : AITFrame)
    (hDP : DataProcessingIK Fr) (hself : SelfInfo Fr) (hpair : PairSymmetric Fr)
    (p q Fo : Fr.Obj) :
    (Fr.K Fo : Int) - (Fr.cond Fo (Fr.star p) : Int) - (Fr.cond Fo (Fr.star q) : Int)
        - 4 * (Fr.slack : Int)
      ≤ IK Fr p q :=
  common_semantics_bound Fr hDP hself hpair p q Fo _ _ le_rfl le_rfl

/-! ### Satisfiability: a frame meeting all three hypotheses at once

A theorem whose hypotheses no frame satisfies is worthless. Read `Obj := ℕ` as "a description of
complexity `n`"; the frame is the `min`/`max` arithmetic of `ShiftInvariance.ShiftFrame`, here
with the two extra laws checked as well. -/

/-- Witness frame: `K := id`, `⟨x,y⟩ := max x y` (so `I_K(x:y) = min x y`),
`K(x|y) := x − y` truncated, `x* := x`, no slack. -/
def ToyIS : AITFrame where
  Obj := Nat
  K := id
  pair := fun x y => max x y
  cond := fun x y => x - y
  star := id
  slack := 0

instance instOfNatToyISObj (n : Nat) : OfNat ToyIS.Obj n := ⟨(n : Nat)⟩

theorem toyIS_dataProcessing : DataProcessingIK ToyIS := by
  intro x y z; simp only [IK, ToyIS, id_eq]; omega

theorem toyIS_selfInfo : SelfInfo ToyIS := by
  intro x; simp only [IK, ToyIS, id_eq]; omega

theorem toyIS_pairSymmetric : PairSymmetric ToyIS := by
  intro x y; simp only [ToyIS, id_eq]; omega

/-- The bound is **attained**, and not at zero: with a semantic object of complexity `3`
recoverable from both descriptions at cost `0`, the two descriptions share exactly `3` bits.
So `common_semantics_bound` is not vacuous in this frame. -/
theorem toyIS_bound_tight :
    ToyIS.cond (3 : Nat) (ToyIS.star (100 : Nat)) = 0 ∧
      ToyIS.cond (3 : Nat) (ToyIS.star (3 : Nat)) = 0 ∧
      IK ToyIS (100 : Nat) (3 : Nat) = (ToyIS.K (3 : Nat) : Int) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [ToyIS, id_eq]
  · simp only [ToyIS, id_eq]
  · simp only [IK, ToyIS, id_eq]; omega

/-! ### The guard: a shared semantics is not a shared organization -/

/-- **What the bound does not say.** Without near-minimality it constrains only the *quantity*
of information two descriptions share, and that quantity can be exactly the semantic content and
no more.

Witness, in `ToyIS`: a semantic object `Fo = 3` recoverable from `p = 100` and from `q = 3` at
zero cost, so the hypotheses of `common_semantics_bound` hold with `c₁ = c₂ = 0` and the bound
reads `I_K(p:q) ≥ 3`. It is met with equality — and yet `K(p | q*) = 97`. Ninety-seven of `p`'s
hundred bits are unrecoverable from `q`; the normalized mutual information is `3/100`.

Nothing about shared organization, mechanism, or causal form may be read out of the bound. The
paper's `K(p), K(q) ≤ K(Fo) + δ` near-minimality clause is a *separate* hypothesis, and even
with it what follows is shared information, not shared structure. -/
theorem common_semantics_does_not_give_structure :
    ToyIS.cond (3 : Nat) (ToyIS.star (100 : Nat)) = 0 ∧
      ToyIS.cond (3 : Nat) (ToyIS.star (3 : Nat)) = 0 ∧
      IK ToyIS (100 : Nat) (3 : Nat) = (ToyIS.K (3 : Nat) : Int) ∧
      ToyIS.cond (100 : Nat) (ToyIS.star (3 : Nat)) = 97 ∧
      NMAI ToyIS (100 : Nat) (3 : Nat) = 3 / 100 := by
  obtain ⟨ha, hb, hc⟩ := toyIS_bound_tight
  refine ⟨ha, hb, hc, ?_, ?_⟩
  · simp only [ToyIS, id_eq]
  · simp only [NMAI, IK, ToyIS, id_eq]
    norm_num

/-! ### A second guard: equal complexity is not a hypothesis of the bound

The recovery costs `c₁, c₂` are what the bound consumes. Equality of description *lengths* is a
different condition and implies nothing — the paper's "independent random strings can have the
same complexity". A frame satisfying all three AIT laws witnesses it. -/

/-- Witness frame for algorithmic independence at equal complexity. Complexity ignores the last
bit (`K n = 2⌊n/2⌋`), pairing is concatenation except on the diagonal (`⟨x,x⟩` costs what `x`
costs), and conditioning helps only on the diagonal. The `slack` is `2`, the rounding loss. -/
def ToyIndep : AITFrame where
  Obj := Nat
  K := fun n => 2 * (n / 2)
  pair := fun x y => if x = y then x else x + y
  cond := fun x y => if x = y then 0 else 2 * (x / 2)
  star := id
  slack := 2

instance instOfNatToyIndepObj (n : Nat) : OfNat ToyIndep.Obj n := ⟨(n : Nat)⟩

theorem toyIndep_dataProcessing : DataProcessingIK ToyIndep := by
  intro x y z; simp only [IK, ToyIndep, id_eq]; split_ifs <;> omega

theorem toyIndep_selfInfo : SelfInfo ToyIndep := by
  intro x; simp only [IK, ToyIndep]; split_ifs <;> omega

theorem toyIndep_pairSymmetric : PairSymmetric ToyIndep := by
  intro x y; simp only [ToyIndep]; split_ifs <;> omega

/-- **Equal complexity carries no shared information.** In `ToyIndep` — a frame satisfying
`DataProcessingIK`, `SelfInfo` and `PairSymmetric` — the descriptions `100` and `101` have the
same complexity `100` and mutual algorithmic information `0`.

So `K(p) ≃ K(q)` is not a weak form of the common-semantics hypothesis: it is unrelated to it.
What drives the bound is cheap recovery of a common semantic object, and nothing else. -/
theorem equal_complexity_is_not_shared_information :
    ToyIndep.K (100 : Nat) = ToyIndep.K (101 : Nat) ∧
      (100 : Nat) ≠ (101 : Nat) ∧
      IK ToyIndep (100 : Nat) (101 : Nat) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [ToyIndep]
  · omega
  · simp only [IK, ToyIndep]; norm_num

#check @common_semantics_bound
#check @common_semantics_bound_raw
#check @common_semantics_does_not_give_structure
#check @equal_complexity_is_not_shared_information

end IS
end KTAIT
