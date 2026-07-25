/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic
import KTAIT.ART

/-!
# KTAIT.PushPull — the push–pull motif (WP0186)

Formalization of WP0186, *Push–Pull Motifs as Minimal Units of Banded Regulation*.

## What is proved vs. what is assumed

Following the project rule (AIT facts are *hypotheses*, KT corollaries are *proved*), and
its dynamical analogue:

* **Assumed (classical, cited):** Nagumo's theorem — that an inward-pointing field on the
  boundary of a closed band is equivalent to forward invariance of that band. This is the
  control-theory counterpart of "we do not re-prove the coding theorem". It is stated as
  the predicate `NagumoBridge` and never used to *derive* the sign conditions.
* **Proved (no `sorry`):** the entire content of Theorems 1–2 and Corollary 1, which is
  *arithmetic on the boundary sign conditions* — no ODE theory is needed, because the
  paper's own proofs only ever evaluate the field at `x₋` and `x₊`.

This split is itself a finding: WP0186's Theorems 1–2 are **not** dynamical theorems.
They are statements about the reachable set of `u` at two points. The dynamics enter only
through Nagumo, which is classical.

## Notation fix forced by Lean

The paper defines the authorities `G` and `H` as **numbers** (a `sup` over engagements at
the single points `x₋`, `x₊`), but Theorem 2's proof then writes `H(x)` and `G(x)` at other
points, under a "neighborhood hypothesis". Lean will not let those be the same object.
Here `G H : ℝ → ℝ` are **functions**, and the paper's numbers are their edge values
`G x₋` and `H x₊`. See `KTAIT/PushPull.lean` docstrings and WP0186 §2.
-/

namespace KTAIT

namespace PushPull

/-! ## 1. The setting: sign-constrained flows against a two-sided disturbance -/

/-- A scalar push–pull plant, `ẋ = D(t) + u(t)`.

`G x` is the total **push** authority available at state `x` (the sup over engagements
`πₖ ∈ [0,1]` of `∑ₖ πₖ gₖ(x)`), and `H x` the total **pull** authority. Both are
non-negative: that non-negativity *is* the sign constraint. -/
structure Plant where
  /-- Lower edge of the target band. -/
  xminus : ℝ
  /-- Upper edge of the target band. -/
  xplus : ℝ
  /-- The band is non-degenerate. -/
  band : xminus < xplus
  /-- Least (most negative) admissible disturbance value. -/
  Dlo : ℝ
  /-- Greatest admissible disturbance value. -/
  Dhi : ℝ
  /-- Push authority as a function of state. -/
  G : ℝ → ℝ
  /-- Pull authority as a function of state. -/
  H : ℝ → ℝ
  /-- Sign constraint: every push flow contributes `≥ 0` to `ẋ`. -/
  G_nonneg : ∀ x, 0 ≤ G x
  /-- Sign constraint: every pull flow contributes `≤ 0` to `ẋ` (magnitude `H ≥ 0`). -/
  H_nonneg : ∀ x, 0 ≤ H x

variable (P : Plant)

/-- The disturbance is **two-sided**: it can genuinely push `x` both up and down. -/
def TwoSided : Prop := P.Dlo < 0 ∧ 0 < P.Dhi

/-- An **admissible control** is any state-feedback `u` whose value at each state lies in
the reachable interval `[-H x, G x]` carved out by the sign-constrained flows.

This interval is exactly the content of Eq. (1) of WP0186: engaging pushes at `πₖ ∈ [0,1]`
and pulls at `ρⱼ ∈ [0,1]` reaches every net flow between full pull and full push. -/
def Admissible (u : ℝ → ℝ) : Prop := ∀ x, -P.H x ≤ u x ∧ u x ≤ P.G x

/-- The field points **inward on the boundary** of the band, for *every* admissible
disturbance realization. This is the hypothesis of Nagumo's theorem, and it is all that
WP0186's proofs of Theorems 1–2 actually use. -/
def InwardOnBoundary (u : ℝ → ℝ) : Prop :=
  (∀ D, P.Dlo ≤ D → D ≤ P.Dhi → D + u P.xplus ≤ 0) ∧
  (∀ D, P.Dlo ≤ D → D ≤ P.Dhi → 0 ≤ D + u P.xminus)

/-- **The Nagumo bridge (assumed, classical).** For a locally Lipschitz field on a closed
interval, inward-pointing on the boundary ⟺ forward invariance. We take `ForwardInvariant`
as an opaque predicate and Nagumo as a hypothesis relating it to `InwardOnBoundary`;
nothing below derives the sign conditions *from* it. -/
def NagumoBridge (ForwardInvariant : (ℝ → ℝ) → Prop) : Prop :=
  ∀ u, ForwardInvariant u ↔ InwardOnBoundary P u

/-! ### The boundary conditions, extracted

The `∀ D` quantifier collapses to its worst case. This little lemma is where the paper's
"because the disturbance is free, it may realize `D = D̄` while `x = x₊`" step lives. -/

/-- Inward-on-boundary is equivalent to the two worst-case inequalities. -/
theorem inward_iff (u : ℝ → ℝ) (h2 : TwoSided P) :
    InwardOnBoundary P u ↔ (P.Dhi + u P.xplus ≤ 0 ∧ 0 ≤ P.Dlo + u P.xminus) := by
  constructor
  · rintro ⟨hup, hlo⟩
    exact ⟨hup P.Dhi (le_of_lt (lt_trans h2.1 h2.2)) le_rfl,
           hlo P.Dlo le_rfl (le_of_lt (lt_trans h2.1 h2.2))⟩
  · rintro ⟨hup, hlo⟩
    refine ⟨fun D _ hD => ?_, fun D hD _ => ?_⟩
    · linarith
    · linarith

/-! ## 2. Theorem 1 — necessity of opposed flows -/

/-- **Theorem 1 (Necessity of opposed flows), WP0186.**

If the band is rendered forward-invariant against a free two-sided disturbance by an
admissible control, then the plant must have pull authority at the upper edge at least the
disturbance's upward reach, *and* push authority at the lower edge at least its downward
reach:
`H x₊ ≥ D̄ > 0` and `G x₋ ≥ −D_ > 0`.

Note the authorities are evaluated **at the edges** — the paper's `H` and `G`. -/
theorem theorem1_necessity (u : ℝ → ℝ)
    (hadm : Admissible P u) (h2 : TwoSided P) (hinw : InwardOnBoundary P u) :
    P.Dhi ≤ P.H P.xplus ∧ -P.Dlo ≤ P.G P.xminus := by
  rw [inward_iff P u h2] at hinw
  obtain ⟨hup, hlo⟩ := hinw
  constructor
  · -- u x₊ ≤ −D̄, and −H x₊ ≤ u x₊, hence −H x₊ ≤ −D̄, i.e. D̄ ≤ H x₊
    have h1 : -P.H P.xplus ≤ u P.xplus := (hadm P.xplus).1
    linarith
  · -- 0 ≤ D_ + u x₋ gives u x₋ ≥ −D_, and u x₋ ≤ G x₋
    have h1 : u P.xminus ≤ P.G P.xminus := (hadm P.xminus).2
    linarith

/-- A **single-signed** controller has no pull authority at the upper edge, or no push
authority at the lower edge. -/
def SingleSigned : Prop := P.H P.xplus = 0 ∨ P.G P.xminus = 0

/-- **Theorem 1, contrapositive form.** A single-signed controller cannot render the band
invariant against a two-sided disturbance. This is the paper's headline necessity claim. -/
theorem single_signed_cannot_regulate (u : ℝ → ℝ)
    (hadm : Admissible P u) (h2 : TwoSided P) (hss : SingleSigned P) :
    ¬ InwardOnBoundary P u := by
  intro hinw
  obtain ⟨hH, hG⟩ := theorem1_necessity P u hadm h2 hinw
  rcases hss with h | h
  · -- H x₊ = 0 forces D̄ ≤ 0, contradicting two-sidedness
    rw [h] at hH; exact absurd hH (not_le.mpr h2.2)
  · -- G x₋ = 0 forces −D_ ≤ 0, i.e. D_ ≥ 0, contradicting two-sidedness
    rw [h] at hG; linarith [h2.1]

/-! ## 3. Theorem 2 — sufficiency

The paper's engagement rule, restricted to what the boundary argument needs: saturate the
pull at the upper edge and the push at the lower edge. -/

/-- The **saturating engagement rule** at the edges: full pull at `x₊`, full push at `x₋`.
(Between the edges any admissible interpolation will do — the boundary argument does not
see it. The paper's proportional rule is one such choice.) -/
def saturatingRule (u : ℝ → ℝ) : Prop :=
  u P.xplus = -P.H P.xplus ∧ u P.xminus = P.G P.xminus

/-- **Theorem 2 (Sufficiency), WP0186.**

If the edge authorities meet the disturbance (`H x₊ ≥ D̄`, `G x₋ ≥ −D_`), then the
saturating rule renders the band forward-invariant: the field points inward on `∂B` for
every admissible disturbance. Flows of both signs therefore *suffice*. -/
theorem theorem2_sufficiency (u : ℝ → ℝ)
    (h2 : TwoSided P) (hsat : saturatingRule P u)
    (hH : P.Dhi ≤ P.H P.xplus) (hG : -P.Dlo ≤ P.G P.xminus) :
    InwardOnBoundary P u := by
  rw [inward_iff P u h2]
  obtain ⟨hp, hm⟩ := hsat
  constructor
  · rw [hp]; linarith
  · rw [hm]; linarith

/-- **Theorems 1 + 2 combined: the edge conditions are exactly right.** Under the
saturating rule, invariance holds *if and only if* both authorities meet the disturbance.
This is the sharp statement the paper gestures at but never assembles. -/
theorem regulation_iff (u : ℝ → ℝ)
    (hadm : Admissible P u) (h2 : TwoSided P) (hsat : saturatingRule P u) :
    InwardOnBoundary P u ↔ (P.Dhi ≤ P.H P.xplus ∧ -P.Dlo ≤ P.G P.xminus) := by
  constructor
  · exact theorem1_necessity P u hadm h2
  · rintro ⟨hH, hG⟩; exact theorem2_sufficiency P u h2 hsat hH hG

/-! ### 3a. Attraction needs a strict margin — WP0186's Theorem 2 is defective here

The paper's Definition 1 demands not just invariance but **ultimate boundedness**: every
trajectory enters `B` in *finite time*, for every admissible disturbance. Theorem 2 tries to
get this from the *non-strict* hypothesis `H x ≥ D̄` off the band, with the escape clause
"with strict inequality whenever `D < D̄`".

That clause is vacuous: `D ≡ D̄` is itself admissible. Below, `nonstrict_fails_attraction`
exhibits a plant satisfying *every* hypothesis of Theorem 2 in which the closed-loop field
**vanishes identically** at a point outside the band under `D ≡ D̄` — the constant trajectory
sits there forever and never enters `B`. Invariance survives; attraction fails.

`margin_gives_uniform_decrease` shows the repair: a strict margin `ε > 0` off the band gives
`ẋ ≤ −ε`, hence entry in time `≤ (x₀ − x₊)/ε`. Note the honest asymmetry this exposes —
Theorem 1's *necessary* condition is tight and non-strict; the *sufficient* condition for
attraction needs one `ε` of slack. -/

/-- Off-band authority with a strict margin `ε > 0`. -/
def AttractionMargin (ε : ℝ) : Prop :=
  0 < ε ∧ (∀ x, P.xplus < x → P.Dhi + ε ≤ P.H x) ∧ (∀ x, x < P.xminus → -P.Dlo + ε ≤ P.G x)

/-- **The repair of Theorem 2's attraction half.** With a strict margin and the saturating
rule off the band, the field is bounded away from zero: `ẋ ≤ −ε` above the band, for every
admissible disturbance. Finite-time entry follows (in time `≤ (x₀ − x₊)/ε`). -/
theorem margin_gives_uniform_decrease {ε : ℝ} (u : ℝ → ℝ)
    (hmarg : AttractionMargin P ε)
    (hsatOff : ∀ x, P.xplus < x → u x = -P.H x) :
    ∀ x, P.xplus < x → ∀ D, P.Dlo ≤ D → D ≤ P.Dhi → D + u x ≤ -ε := by
  obtain ⟨hε, hup, _⟩ := hmarg
  intro x hx D _ hD
  rw [hsatOff x hx]
  have := hup x hx
  linarith

/-- **The defect, as a concrete witness.** A plant meeting every hypothesis of WP0186's
Theorem 2 — band `[-1,1]`, disturbance range `[-1,1]`, constant unit authorities `G ≡ H ≡ 1`
(so `H x ≥ D̄` and `G x ≥ −D_` hold *globally*, non-strictly, and `G, H` are trivially
non-decreasing away from the band) — under the saturating rule. The control is admissible and
the band is invariant, yet at `x = 5` the field vanishes under `D ≡ D̄ = 1`.

So `x(t) ≡ 5` solves the closed loop and never enters `B`: ultimate boundedness fails. -/
theorem nonstrict_fails_attraction :
    ∃ (P : Plant) (u : ℝ → ℝ),
      TwoSided P ∧ Admissible P u ∧ saturatingRule P u ∧ InwardOnBoundary P u ∧
      (∀ x, P.Dhi ≤ P.H x) ∧ (∀ x, -P.Dlo ≤ P.G x) ∧
      ∃ x, P.xplus < x ∧ P.Dhi + u x = 0 := by
  refine ⟨{ xminus := -1, xplus := 1, band := by norm_num,
            Dlo := -1, Dhi := 1,
            G := fun _ => 1, H := fun _ => 1,
            G_nonneg := fun _ => by norm_num, H_nonneg := fun _ => by norm_num },
          fun x => if 0 ≤ x then -1 else 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by norm_num, by norm_num⟩
  · intro x; dsimp only; split <;> norm_num
  · exact ⟨by norm_num, by norm_num⟩
  · refine ⟨fun D _ hD => ?_, fun D hD _ => ?_⟩ <;> · dsimp only; norm_num; linarith
  · intro _; norm_num
  · intro _; norm_num
  · exact ⟨5, by norm_num, by norm_num⟩

/-! ## 4. Minimality — the cardinality claim

The paper says the minimal regulating set has cardinality two, but the theorems bound
**signs**, not counts. Lean forces the distinction into the open: what is proved is that a
regulating set must contain at least one flow of each sign, whence `card ≥ 2`. Two pushes
do not regulate no matter how many there are. -/

/-- The sign of an elementary sign-constrained flow. -/
inductive FlowSign
  | push
  | pull
  deriving DecidableEq, Fintype

/-- An elementary flow: a sign together with a non-negative capacity profile. -/
structure Flow where
  /-- Which direction this flow can move `x`. -/
  sign : FlowSign
  /-- Capacity as a function of state (non-negative: the sign constraint). -/
  cap : ℝ → ℝ
  /-- The sign constraint. -/
  cap_nonneg : ∀ x, 0 ≤ cap x

/-- Equality of flows is not decidable (the capacity is a real-valued function), so we
work classically. This is only needed to form `Finset Flow`. -/
noncomputable instance : DecidableEq Flow := Classical.decEq _

/-- A flow set is **sign-diverse** if it contains at least one flow of each sign — the
architectural conclusion of Theorem 1. -/
def SignDiverse (S : Finset Flow) : Prop :=
  (∃ f ∈ S, f.sign = FlowSign.push) ∧ (∃ f ∈ S, f.sign = FlowSign.pull)

/-- **Minimality (the honest form).** A sign-diverse flow set has at least two elements.
The bound is on *signs*; the count follows because a push and a pull are distinct flows. -/
theorem sign_diverse_card_ge_two (S : Finset Flow) (h : SignDiverse S) : 2 ≤ S.card := by
  obtain ⟨⟨f, hfS, hf⟩, ⟨g, hgS, hg⟩⟩ := h
  have hne : f ≠ g := by
    intro heq
    rw [heq, hg] at hf
    exact FlowSign.noConfusion hf
  exact Finset.one_lt_card.mpr ⟨f, hfS, g, hgS, hne⟩

/-- **Minimality is achieved:** two flows, one of each sign, form a sign-diverse set of
cardinality exactly two. So the bound of `sign_diverse_card_ge_two` is tight — the minimal
sign-diverse set has cardinality two. This is the push–pull motif. -/
theorem minimal_is_two (fpush fpull : Flow)
    (hp : fpush.sign = FlowSign.push) (hq : fpull.sign = FlowSign.pull) :
    SignDiverse {fpush, fpull} ∧ ({fpush, fpull} : Finset Flow).card = 2 := by
  have hne : fpush ≠ fpull := by
    intro heq
    rw [heq, hq] at hp
    exact FlowSign.noConfusion hp
  refine ⟨⟨⟨fpush, by simp, hp⟩, ⟨fpull, by simp, hq⟩⟩, ?_⟩
  rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

/-! ## 5. Corollary 1 — the "restoring force" is already push–pull

The paper claims a single-term restoring law `ẋ = −κ(x − x⋆) + D` is not a counterexample,
because `−κ(x − x⋆)` is a *two-signed* flow. Lean makes the real content visible: the
restoring term takes a strictly positive value below `x⋆` and a strictly negative value
above it, hence it is **not** realizable by any single sign-constrained flow. -/

/-- The restoring field of a leaky integrator. -/
def restoring (κ xstar : ℝ) : ℝ → ℝ := fun x => -κ * (x - xstar)

/-- A field is realizable by a single push flow if it is everywhere `≥ 0`; by a single pull
flow if everywhere `≤ 0`. (This is the sign constraint applied to *one* device.) -/
def SingleSignedField (F : ℝ → ℝ) : Prop := (∀ x, 0 ≤ F x) ∨ (∀ x, F x ≤ 0)

/-- **Corollary 1, WP0186.** For `κ > 0`, the restoring field is genuinely two-signed: it
is not realizable by any single sign-constrained flow. Hence the leaky integrator
*presupposes* the opposed pair — it is a push–pull motif in collapsed notation. -/
theorem restoring_not_single_signed {κ xstar : ℝ} (hκ : 0 < κ) :
    ¬ SingleSignedField (restoring κ xstar) := by
  rintro (hpos | hneg)
  · -- above x⋆ the field is strictly negative
    have := hpos (xstar + 1)
    simp only [restoring] at this
    nlinarith
  · -- below x⋆ the field is strictly positive
    have := hneg (xstar - 1)
    simp only [restoring] at this
    nlinarith

/-- **Corollary 1, constructive half.** The restoring field decomposes into a push flow
active below `x⋆` and a pull flow active above it, each non-negative in magnitude — the
opposed pair Theorem 1 requires. -/
theorem restoring_decomposition (κ xstar : ℝ) (hκ : 0 < κ) :
    ∃ g h : ℝ → ℝ, (∀ x, 0 ≤ g x) ∧ (∀ x, 0 ≤ h x) ∧
      (∀ x, restoring κ xstar x = g x - h x) ∧
      (∀ x, x < xstar → 0 < g x ∧ h x = 0) ∧
      (∀ x, xstar < x → g x = 0 ∧ 0 < h x) := by
  refine ⟨fun x => max (-κ * (x - xstar)) 0, fun x => max (κ * (x - xstar)) 0,
          fun x => le_max_right _ _, fun x => le_max_right _ _, ?_, ?_, ?_⟩
  · intro x
    simp only [restoring]
    by_cases h : x ≤ xstar
    · rw [max_eq_left (by nlinarith), max_eq_right (by nlinarith)]; ring
    · push_neg at h
      rw [max_eq_right (by nlinarith), max_eq_left (by nlinarith)]; ring
  · intro x hx
    dsimp only
    exact ⟨by rw [max_eq_left (by nlinarith)]; nlinarith, by rw [max_eq_right (by nlinarith)]⟩
  · intro x hx
    dsimp only
    exact ⟨by rw [max_eq_right (by nlinarith)], by rw [max_eq_left (by nlinarith)]; nlinarith⟩

/-! ## 6. The GAR gap (Lemma 1) — axiom-backed, against the `AITFrame` interface

Per the kickoff rule, `K` stays opaque and the AIT facts stay hypotheses. What we check is
the **dependency structure**: does `Δ = S ± O(log N)` follow from (A1)–(A4)?

The answer Lean gives is instructive, and belongs in the paper. Assumptions (A2)+(A3) say
`K(x_OFF) = K(D_pred) + K(η) ± slack`; (A4) says `K(x_ON) = K(η) ± slack`. The conclusion
is then *pure arithmetic* — subtraction. The regulator's dynamics play **no role at all**.
That is a real finding: the assumptions, not the mechanism, carry Lemma 1. -/

variable (F : AITFrame)

/-- **(A2)+(A3) combined.** The OFF readout is inter-computable with the pair
`(D_pred, η)`, which by algorithmic independence costs `K(D_pred) + K(η)`, all within the
`O(log N)` slack. -/
def OffSplit (Dpred eta xoff : F.Obj) : Prop :=
  ((F.K xoff : Int) - ((F.K Dpred : Int) + (F.K eta : Int))).natAbs ≤ F.slack

/-- **(A4), faithful residual.** The ON readout is inter-computable with the residual `η`
within the slack. This is what excludes a readout pinned to a constant. -/
def OnResidual (eta xon : F.Obj) : Prop :=
  ((F.K xon : Int) - (F.K eta : Int)).natAbs ≤ F.slack

/-- **Lemma 1 (Complexity-gap identity), WP0186.**

`Δ := K(x_OFF) − K(x_ON) = S ± O(log N)`, where `S := K(D_pred)`.

Proved from `OffSplit` and `OnResidual` with the slack terms composing additively: the
error is at most `2·slack`, i.e. still `O(log N)`. The residual `K(η)` — possibly `Θ(N)` —
cancels. -/
theorem lemma1_gap_identity (Dpred eta xoff xon : F.Obj)
    (hoff : OffSplit F Dpred eta xoff) (hon : OnResidual F eta xon) :
    ((((F.K xoff : Int) - (F.K xon : Int)) - (F.K Dpred : Int))).natAbs ≤ 2 * F.slack := by
  unfold OffSplit at hoff
  unfold OnResidual at hon
  -- the two slack bounds compose by the triangle inequality
  omega

/-- **Lemma 1, existential form:** the gap *is* `S` up to a `2·slack` error term.

**A retraction is recorded here.** An earlier draft of WP0186 chained this into the ART
bound to conclude that a sustained gap `Δ` *forces* model content `M(W:R) ≳ Δ` in the
push–pull regulator. That inference is **not** licensed, and the paper no longer makes
it. `ART.probabilistic_regulator_theorem` bounds the *posterior support of a single
explanation pair* — it is not a statement about the distribution of `M(W:R)`, and the
corresponding forward event-tail bound is explicitly declined in WP0162 (the contrast
fiber can carry large mass, since many worlds with complex OFF output admit a simple
clamp that trivializes the ON output).

Note the type-level tell: `M(W:R)` (`IK`) does not appear in this statement at all, and
no amount of arithmetic on `OffSplit`/`OnResidual` will introduce it. WP0186's
Proposition 1 is now a *selection* claim under the universal conditional prior —
`argmax_{R ∈ S_Δ(W)} [IK W R − K R]` — which belongs with `RegulatorSelection.lean`,
not here. -/
theorem lemma1_gap_is_S_existential (Dpred eta xoff xon : F.Obj)
    (hoff : OffSplit F Dpred eta xoff) (hon : OnResidual F eta xon) :
    ∃ err : Int, err.natAbs ≤ 2 * F.slack ∧
      ((F.K xoff : Int) - (F.K xon : Int)) = (F.K Dpred : Int) + err := by
  refine ⟨((F.K xoff : Int) - (F.K xon : Int)) - (F.K Dpred : Int), ?_, by ring⟩
  exact lemma1_gap_identity F Dpred eta xoff xon hoff hon

/-! ### The degenerate cases (Remark 7), made formal

Two sanity checks the paper asserts in prose. Lean confirms both are consequences of the
same arithmetic — which is reassuring, but again shows the assumptions do the work. -/

/-- **Pure noise gives no gap.** If `D_pred` is trivial (`K(D_pred) = 0`), the gap vanishes
up to slack: a regulator can cap the amplitude of unpredictable disturbance but cannot
compress it, and claims no model content. -/
theorem no_structure_no_gap (Dpred eta xoff xon : F.Obj)
    (hoff : OffSplit F Dpred eta xoff) (hon : OnResidual F eta xon)
    (hS : F.K Dpred = 0) :
    ((F.K xoff : Int) - (F.K xon : Int)).natAbs ≤ 2 * F.slack := by
  have h := lemma1_gap_identity F Dpred eta xoff xon hoff hon
  rw [hS] at h
  omega

end PushPull

end KTAIT
