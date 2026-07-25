/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic
import KTAIT.Ontology
import KTAIT.Persistence
import KTAIT.SelfModel

/-!
# KTAIT.PatternPersist — the WP0162 ontology as types (M6)

The observer-relative ontology of *Pattern, Persist!* (WP0162 §4–§5), typed so the
structural errors the theory attracts cannot compile.

**Built on the existing machinery, not beside it.** `PPFrame` *extends* `AITFrame`
(the pattern `AITProb` already uses), so `IK` and `NMAI` come from `Basic`,
persistence from `Persistence.Pers`, and the self-regulation gap from
`SelfModel.DeltaSelf`. An earlier draft carried its own opaque `mai` with three
bolted-on laws and its own unnormalized persistence; both are gone. What remains
frame-specific is exactly the two relations WP0162 needs and AIT does not supply:
which descriptions are *submodels* of which, and which are *useful*.

**The single carrier.** WP0162: "the agent A is a pattern on the internal tape —
there is nothing else, no agent over and above the pattern", and "the persistent
patterns strictly *contain* the agents." So `Pattern` is the one carrier and
agenthood is a *predicate*, `IsAgent`. This is what lets the four cells of WP0207
(token, constituent class, collective, collective kind) all be agents.

**Agenthood has content now.** `IsAgent` is a positive self-regulation gap
`Δ_self = K(O_∅) − K(O_reg) > 0` — the paper's own quantity — not a hand-set tag.
Proposition 3 (`self_regulation_temporal_model`) therefore applies to any agent,
and `agent_has_temporal_self_model` below inherits it rather than restating it.

**Namespace note.** `KTAIT.Ontology` already defines a `Pattern` (a bare carrier
wrapper, parent of `SelfCode`). The `Pattern` here is a different object — a
*useful submodel trajectory inside an observer's world-model* — so it lives in
`KTAIT.PP`. Unifying them is deliberate future work.
-/

namespace KTAIT.PP

open KTAIT

/-! ## 1. The frame

`AITFrame` supplies `Obj`, `K`, `pair`, `cond`, `star`, `slack`, and hence `IK`/`NMAI`.
WP0162 needs two more relations that algorithmic information theory does not fix. -/

/-- An `AITFrame` together with WP0162's two observer-relative relations. -/
structure PPFrame extends AITFrame where
  /-- `sub s m`: description `s` is a submodel of description `m`. -/
  sub       : Obj → Obj → Prop
  /-- Usefulness: predicts, explains, regulates, or supports action (WP0162 §4). -/
  usefulFor : Obj → Prop

namespace PPFrame
variable (F : PPFrame)

/-- The observer's world-model trajectory `ℳ_t`. -/
abbrev WorldModel := Time → F.Obj

end PPFrame

/-! ## 2. Patterns

A pattern is a *trajectory* `S^α : Time → Obj` of useful submodels of the observer's
world-model. Time-indexed because WP0162's persistence compares `S^α_t` with
`S^α_{t+τ}`, which live in different world-models. -/

/-- A PATTERN: a useful submodel trajectory inside a world-model trajectory. -/
structure Pattern (F : PPFrame) where
  traj   : Time → F.Obj
  host   : Time → F.Obj
  isSub  : ∀ t, F.sub (traj t) (host t)
  useful : ∀ t, F.usefulFor (traj t)

/-! ## 3. Question 1 — persistence, inherited from `KTAIT.Persistence` -/

/-- Persistence of a pattern at `(t, τ)` against threshold `θ`. This is
    `Persistence.Persistent` on the pattern's trajectory: normalized, rational-valued,
    and lag-indexed. -/
def Persists (F : PPFrame) (S : Pattern F) (t τ : Time) (θ : ℚ) : Prop :=
  Persistent F.toAITFrame S.traj t τ θ

/-- Unfolding lemma: persistence really is WP0162's `NMAI(S_t, S_{t+τ})`. -/
theorem persists_iff_nmai (F : PPFrame) (S : Pattern F) (t τ : Time) (θ : ℚ) :
    Persists F S t τ θ ↔ θ ≤ NMAI F.toAITFrame (S.traj t) (S.traj (t + τ)) := Iff.rfl

/-! ## 4. Questions 2 and 3 — regulation, agenthood, telehomeostasis -/

/-- A regulatory situation for a pattern: the two readouts ART contrasts, with the
    maintaining sub-pattern `E` ablated (`onull`) or running (`oreg`). -/
structure Regulation (F : PPFrame) (_S : Pattern F) where
  onull : F.Obj
  oreg  : F.Obj
  /-- The maintaining sub-pattern itself, needed to state the self-model corollary. -/
  E     : F.Obj

/-- The self-regulation gap `Δ_self`, from `KTAIT.SelfModel`. -/
def selfGap {F : PPFrame} {S : Pattern F} (R : Regulation F S) : ℤ :=
  DeltaSelf F.toAITFrame R.onull R.oreg

/-- AGENTHOOD is a PREDICATE on patterns: the regulatory work is localized within,
    measured by a positive self-regulation gap. WP0162 §5. -/
def IsAgent {F : PPFrame} {S : Pattern F} (R : Regulation F S) : Prop :=
  0 < selfGap R

/-- ME / OF / PE. The Planning Engine is the argmax of the objective over predicted
    model states (WP0162 Box 1), not a free-standing map. -/
structure Apparatus (F : PPFrame) (Act : Type) where
  ME         : F.Obj → F.Obj → F.Obj
  predict    : F.Obj → Act → F.Obj
  OF         : F.Obj → Int
  choose     : F.Obj → Act
  isArgmax   : ∀ m a, OF (predict m a) ≤ OF (predict m (choose m))
  nontrivial : ∃ x y, OF x ≠ OF y

/-- An objective proxies the persistence of some named pattern. -/
structure Objective (F : PPFrame) (Act : Type) where
  app    : Apparatus F Act
  target : Pattern F

/-- TELEHOMEOSTATIC: fixed by the OBJECTIVE ALONE (WP0162 §3, "telehomeostatic exactly
    when its OF is its own persistence"). Locus attaches to agenthood, not to this. -/
def IsTelehomeostatic {F : PPFrame} {Act : Type}
    (S : Pattern F) (O : Objective F Act) : Prop :=
  O.target.traj = S.traj

/-! ## 5. What agenthood now buys: Proposition 3, inherited

Because `IsAgent` is a positive `DeltaSelf`, `SelfModel.self_regulation_temporal_model`
applies verbatim. An agent's future self-code is cheap given its present organization. -/

/-- **Any agent has a temporal self-model.** Proposition 3 of WP0162, specialized to a
    pattern that is an agent in the sense above. Nothing is re-proved: the hypotheses are
    the same named ones (`hSI`, `hART`) that Proposition 3 consumes. -/
theorem agent_has_temporal_self_model
    {F : PPFrame} {S : Pattern F} (R : Regulation F S) (C : F.Obj) (t τ : Time)
    (cmi : ℤ) (hagent : IsAgent R)
    (hSI : (F.cond (S.traj (t + τ)) C : ℤ)
              - (F.cond (S.traj (t + τ)) (F.pair (S.traj t) (F.pair R.E C)) : ℤ)
            ≥ cmi - (F.slack : ℤ))
    (hART : 0 < DeltaSelf F.toAITFrame R.onull R.oreg →
              cmi ≥ DeltaSelf F.toAITFrame R.onull R.oreg - (F.slack : ℤ)) :
    (F.cond (S.traj (t + τ)) (F.pair (S.traj t) (F.pair R.E C)) : ℤ)
      ≤ (F.cond (S.traj (t + τ)) C : ℤ)
          - DeltaSelf F.toAITFrame R.onull R.oreg + 2 * (F.slack : ℤ) :=
  self_regulation_temporal_model F.toAITFrame S.traj R.E C R.onull R.oreg t τ cmi
    hagent hSI hART

/-! ## 6. Witness: the four cells of WP0207

A toy frame in which the four cells are distinct trajectories, each self-regulating. -/

@[reducible] def F0 : PPFrame where
  Obj := Nat
  K := id
  pair := fun x y => max x y
  cond := fun x _ => x
  star := id
  slack := 0
  sub := fun s m => s ≤ m
  usefulFor := fun _ => True

/-- Constant trajectories, one per cell; the tag distinguishes them. -/
def cell (n : Nat) (h : n ≤ 1000) : Pattern F0 :=
  { traj := fun _ => n, host := fun _ => 1000
  , isSub := fun _ => h
  , useful := fun _ => trivial }

def a_i : Pattern F0 := cell 10 (by decide)   -- the token
def T   : Pattern F0 := cell 20 (by decide)   -- the constituent class
def M   : Pattern F0 := cell 30 (by decide)   -- this collective
def L   : Pattern F0 := cell 40 (by decide)   -- the collective kind

/-- Every cell is self-regulating here: ablating its maintainer costs 5 bits. -/
def reg (S : Pattern F0) : Regulation F0 S := ⟨7, 2, 1⟩

def app0 : Apparatus F0 Unit where
  ME := fun m _ => m
  predict := fun m _ => m
  OF := fun x => (x : Int)
  choose := fun _ => ()
  isArgmax := fun m a => by cases a; exact le_refl _
  nontrivial := ⟨0, 1, by decide⟩

def obj (target : Pattern F0) : Objective F0 Unit := ⟨app0, target⟩

/-! ### All four cells are agents -/

theorem token_is_agent      : IsAgent (reg a_i) := by
  simp [IsAgent, selfGap, DeltaSelf, reg]
theorem class_is_agent      : IsAgent (reg T)   := by
  simp [IsAgent, selfGap, DeltaSelf, reg]
theorem collective_is_agent : IsAgent (reg M)   := by
  simp [IsAgent, selfGap, DeltaSelf, reg]
theorem kind_is_agent       : IsAgent (reg L)   := by
  simp [IsAgent, selfGap, DeltaSelf, reg]

/-! ### Telehomeostasis splits by column -/

private theorem traj_ne {m n : Nat} {hm : m ≤ 1000} {hn : n ≤ 1000} (h : m ≠ n) :
    (cell m hm).traj ≠ (cell n hn).traj :=
  fun hEq => h (congrFun hEq 0)

/-- In agentoptosis the token's objective proxies its CLASS, not itself. -/
theorem token_not_telehomeostatic : ¬ IsTelehomeostatic a_i (obj T) :=
  traj_ne (by decide)

theorem class_is_telehomeostatic : IsTelehomeostatic T (obj T) := rfl

/-- Snowflake yeast: the collective instance's objective proxies its LINEAGE. -/
theorem collective_not_telehomeostatic : ¬ IsTelehomeostatic M (obj L) :=
  traj_ne (by decide)

theorem kind_is_telehomeostatic : IsTelehomeostatic L (obj L) := rfl

/-- The payoff: a token can be a genuine agent AND not telehomeostatic. -/
theorem agentoptosis_gap :
    IsAgent (reg a_i) ∧ ¬ IsTelehomeostatic a_i (obj T) :=
  ⟨token_is_agent, token_not_telehomeostatic⟩

/-- Normally the objective targets the token itself, and then it IS telehomeostatic.
    The divergence is the exception, not the rule. -/
theorem token_usually_telehomeostatic : IsTelehomeostatic a_i (obj a_i) := rfl

/-! ## 7. Guards -/

/-- A pattern with no self-regulation gap is not an agent, however it is described. -/
def inertReg (S : Pattern F0) : Regulation F0 S := ⟨2, 7, 1⟩

theorem externally_regulated_not_agent : ¬ IsAgent (inertReg a_i) := by
  simp [IsAgent, selfGap, DeltaSelf, inertReg]

end KTAIT.PP
