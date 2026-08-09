/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.PatternPersist

/-!
# KTAIT.Agentoptosis — bearer, target, and beneficiary kept apart (WP0207 v0.8)

WP0207 defines agentoptosis as the event in which a constituent's own action-selection
and execution machinery produces the irreversible transition that terminates it. This
module formalizes the *ontology and elementary logic* of that definition — nothing
biological or evolutionary. The design constraint, from the v0.8 review, is that three
things the definition deliberately does NOT fix must stay underivable:

* the persistence **target** of the operative objective,
* the actual **beneficiary** of the event,
* the agenthood of anything other than the constituent itself.

Accordingly `AgentoptoticEvent` requires agenthood of the constituent and internal
selection of the terminal action, and carries no target or beneficiary field. The
guards below witness, in `PatternPersist`'s toy frame `F0`, that the deliberately
absent implications really are absent:

* `other_target_not_telehomeostatic` — a general, definitional fact: an objective
  whose target differs from the bearer is not telehomeostatic for the bearer.
* `event_agent_not_telehomeostatic` — an agentoptotic event whose objective targets
  the class leaves the constituent a genuine agent with an other-directed objective
  (`PP.agentoptosis_gap` is the underlying conjunction).
* `targeted_class_not_agent` — being a persistence target does not make the class an
  agent (`PP.class_not_agent_here` supplies the witness).
* `composition_does_not_imply_agenthood` — a collective whose constituent is a
  genuine agent can itself fail the agent criterion.
* `CollectiveTelehomeostasis` — higher-scale telehomeostasis is by definition the
  conjunction of collective agenthood and a self-targeting collective objective;
  the two projection lemmas make each requirement citable on its own.
* `terminal_action_underdetermines_target` — the same terminal action is selected
  under objectives with distinct targets, so self-termination alone cannot identify
  the persistence target.

The decision algebra of WP0207's boxed rule is proved over `ℚ`:
`deletion_threshold` states `0 < p·C_FN − (1−p)·C_FP ↔ C_FP/(C_FP+C_FN) < p`
for positive costs. The biological quantities (Ψ, ΔJ, χ, the filter operator, release,
enforceability) are deliberately NOT formalized — they are empirical claims, not
consequences of the ontology.
-/

namespace KTAIT.PP

/-! ## 1. Bearer/target separation (general, definitional) -/

/-- An objective borne against pattern `S` but targeting a pattern with a different
trajectory is not telehomeostatic for `S`. Definitional: telehomeostasis is exactly
target–bearer coincidence. -/
theorem other_target_not_telehomeostatic {F : PPFrame} {Act : Type}
    (S : Pattern F) (O : Objective F Act) (h : O.target.traj ≠ S.traj) :
    ¬ IsTelehomeostatic S O :=
  fun hEq => h hEq

/-! ## 2. The event -/

/-- An AGENTOPTOTIC EVENT for constituent `S`: the constituent is an agent, and the
terminal action is selected by the objective implemented in its own regulatory loop.

Deliberately absent, per WP0207 v0.8: no `beneficiary` field, no constraint tying
`O.target` to any particular pattern, and no agenthood assertion about the target. -/
structure AgentoptoticEvent (F : PPFrame) (Act : Type) (S : Pattern F) where
  /-- The constituent's regulatory situation. -/
  R : Regulation F S
  /-- The operative objective or proxy implemented in the constituent's loop. -/
  O : Objective F Act
  /-- The constituent is a genuine agent. -/
  agent : IsAgent R
  /-- The terminal action. -/
  terminal : Act
  /-- The terminal action is selected inside the constituent's own loop. -/
  selected : ∃ m, O.app.choose m = terminal

/-! ## 3. Witnesses in the toy frame -/

/-- The canonical toy event: the token terminates under an objective targeting its
constituent class. -/
def toyEvent : AgentoptoticEvent F0 Unit a_i :=
  ⟨reg a_i, obj T, token_is_agent, (), ⟨0, rfl⟩⟩

/-- Agenthood survives an other-directed objective: the event's bearer is an agent
and its objective is not telehomeostatic for it. -/
theorem event_agent_not_telehomeostatic :
    IsAgent toyEvent.R ∧ ¬ IsTelehomeostatic a_i toyEvent.O :=
  ⟨token_is_agent, token_not_telehomeostatic⟩

/-- Being the persistence target promotes nothing: the class targeted by the toy
event's objective is, under its regulation, no agent. -/
theorem targeted_class_not_agent : ¬ IsAgent (inertReg T) :=
  class_not_agent_here

/-- Composition does not imply a meta-agent: in the very frame in which the token is
a genuine agent, the collective fails the agent criterion under its regulation. -/
theorem composition_does_not_imply_agenthood :
    IsAgent (reg a_i) ∧ ¬ IsAgent (inertReg M) :=
  ⟨token_is_agent, collective_not_agent_here⟩

/-! ## 4. Higher-scale telehomeostasis is conditional -/

/-- COLLECTIVE TELEHOMEOSTASIS at pattern `S`: the collective independently satisfies
the agent criterion AND its objective targets `S` itself. Both conjuncts are required
by definition; neither follows from the other or from properties of the parts. -/
def CollectiveTelehomeostasis {F : PPFrame} {Act : Type}
    (S : Pattern F) (R : Regulation F S) (O : Objective F Act) : Prop :=
  IsAgent R ∧ IsTelehomeostatic S O

theorem collective_telehomeostasis_requires_agent {F : PPFrame} {Act : Type}
    {S : Pattern F} {R : Regulation F S} {O : Objective F Act}
    (h : CollectiveTelehomeostasis S R O) : IsAgent R :=
  h.1

theorem collective_telehomeostasis_requires_self_target {F : PPFrame} {Act : Type}
    {S : Pattern F} {R : Regulation F S} {O : Objective F Act}
    (h : CollectiveTelehomeostasis S R O) : IsTelehomeostatic S O :=
  h.2

/-! ## 5. Self-termination does not identify the target -/

/-- The toy apparatus selects the same action under objectives targeting the class
and the kind, whose trajectories differ: observing the terminal action alone cannot
determine the persistence target. -/
theorem terminal_action_underdetermines_target :
    (obj T).app.choose = (obj L).app.choose ∧ (obj T).target.traj ≠ (obj L).target.traj :=
  ⟨rfl, fun hEq => (by decide : (20 : Nat) ≠ 40) (congrFun hEq 0)⟩

/-! ## 6. State dependence: the exception, not the rule

WP0207's nested-mutualism reading: the constituent and the larger pattern are ordinarily
mutualists, and agentoptosis is a state-dependent sign reversal, not standing hostility.
That baseline is architectural and evolutionary, so no generic mutual-benefit theorem is
stated or provable here; what CAN be witnessed is that a single other-directed objective
is compatible with bearer-preserving action in ordinary states and bearer-terminating
action in an exceptional one. -/

/-- A state-dependent apparatus over the toy frame. Actions are `Bool`, `true` meaning
terminate; the chosen action flips only when the state crosses `100`. -/
def stateApp : Apparatus F0 Bool where
  ME := fun m _ => m
  predict := fun m a => if a = decide (100 ≤ m) then 1 else 0
  OF := fun x => (x : Int)
  choose := fun m => decide (100 ≤ m)
  isArgmax := fun m a => by by_cases h : a = decide (100 ≤ m) <;> simp [h]
  nontrivial := ⟨0, 1, by decide⟩

/-- One objective, targeting the constituent class throughout. -/
def stateObj : Objective F0 Bool := ⟨stateApp, T⟩

/-- Under a single class-targeting objective, the ordinary state retains the bearer and
the exceptional state terminates it. Higher-scale targeting is compatible with keeping
the constituent alive almost everywhere; agentoptosis is the reversal region. -/
theorem ordinary_retains_exceptional_terminates :
    stateObj.app.choose 10 = false ∧ stateObj.app.choose 200 = true := by
  constructor <;> decide

/-! ## 7. The decision algebra of the boxed rule -/

/-- **WP0207 deletion threshold.** For positive misclassification costs, the expected
event-level effect `p·C_FN − (1−p)·C_FP` is positive exactly when the evidence `p`
clears the threshold `ϑ = C_FP/(C_FP+C_FN)`. Elementary algebra over `ℚ`, proved so
the boxed rule's symbols cannot drift from its inequality. -/
theorem deletion_threshold (p CFP CFN : ℚ) (hFP : 0 < CFP) (hFN : 0 < CFN) :
    0 < p * CFN - (1 - p) * CFP ↔ CFP / (CFP + CFN) < p := by
  rw [div_lt_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

end KTAIT.PP
