/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
/-!
# KTAIT.PatternPersist — the WP0162 ontology as types (M6)

The observer-relative ontology of *Pattern, Persist!* (WP0162 §4–§5), typed so the
structural errors the theory attracts cannot compile.

**Namespace note.** `KTAIT.Ontology` already defines a `Pattern` (a bare carrier
wrapper, parent of `SelfCode`). The `Pattern` here is a different object — a
*useful submodel of an observer's world-model* — so it lives in `KTAIT.PP` and the
two never meet. Unifying them is deliberate future work, not an oversight.

**The single carrier.** WP0162: "the agent A is a pattern on the internal tape —
there is nothing else, no agent over and above the pattern." So `Pattern` is the
one carrier and agenthood is a *predicate*, `IsAgent`, not a rival structure. This
is what lets the four cells of WP0207 (token, constituent class, collective,
collective kind) all be agents, which is the point of `token_is_agent` &c. below.

**The three questions WP0162 keeps apart** (§5): whether a pattern persists
(`Persists`), where its regulator sits (`locusOf`, derived from a directional
ablation pair), and whether the regulator's objective is the pattern's own
continuation (`IsTelehomeostatic`, fixed by the objective *alone*, per §3).

Design points, each the repair of a real defect found by adversarial audit:
  * K and DL are separate: K is the (uncomputable) ideal, DL the computable
    proxy, related by an explicit slack.
  * `mai` carries its laws: symmetry and mai <= min{K,K}.
  * Persistence is NORMALIZED and CROSS-TIME: it relates submodels of two
    different world-models, at strictly increasing time, comparing
    NMAI >= num/den without division.
  * Admissibility excludes CONSTANT MAPS, which v2's DL-monotone condition
    wrongly admitted -- the paper's named exclusion.
  * Locus is DERIVED from a directional ablation pair, with all four outcomes
    including `decoupled`.
  * PE is the ARGMAX of OF over predicted model states (Box 1), not a bare map.
  * Telehomeostasis is fixed by the OBJECTIVE ALONE (WP0162 l.277:
    "telehomeostatic exactly when its OF is its own persistence").
-/
namespace KTAIT.PP

abbrev Time := Nat

/-- Description frame `C = (O, B_0)`. `K` is the ideal complexity, `DL` the
    computable description length an observer actually runs. -/
structure Frame where
  Desc      : Type
  K         : Desc → Nat
  DL        : Desc → Nat
  slack     : Nat
  sub       : Desc → Desc → Prop
  mai       : Desc → Desc → Nat
  usefulFor : Desc → Prop
  mai_symm  : ∀ x y, mai x y = mai y x
  mai_le_l  : ∀ x y, mai x y ≤ K x
  mai_le_r  : ∀ x y, mai x y ≤ K y
  proxy     : ∀ x, K x ≤ DL x + slack

/-- Substrate with dynamics: `X_t`, indexed by time. -/
structure Substrate (F : Frame) where
  state : Time → F.Desc

/-- Coarse-graining. Admissibility here excludes the constant maps WP0162 names. -/
structure Projection (F : Frame) where
  rho      : F.Desc → F.Desc
  nonconst : ∃ x y, rho x ≠ rho y

/-- The observer's world-model at a time: `M_t = ME(P^rho_{<=t})`. -/
structure WorldModel (F : Frame) where
  time  : Time
  model : F.Desc

/-- A PATTERN: a useful submodel of a world-model. THE single carrier. -/
structure Pattern (F : Frame) where
  code   : F.Desc
  host   : WorldModel F
  isSub  : F.sub code host.model
  useful : F.usefulFor code

/-- QUESTION 1. Normalized, cross-time persistence: NMAI >= num/den, stated
    without division, and requiring the later pattern to be strictly later. -/
def Persists (F : Frame) (num den : Nat) (S S' : Pattern F) : Prop :=
  S.host.time < S'.host.time ∧
  num * (max (F.K S.code) (F.K S'.code)) ≤ den * F.mai S.code S'.code

/-- What a directional ablation does to the pattern. -/
inductive Effect | dissolves | raisesDL (n : Nat) | noEffect
  deriving DecidableEq

def Effect.matters : Effect → Bool
  | .noEffect => false
  | _         => true

/-- QUESTION 2. The four outcomes of WP0162 section 5. -/
inductive Locus | selfRegulating | externallyRegulated | coRegulated | decoupled
  deriving DecidableEq

/-- The directional ablation PAIR: null each channel in turn. -/
structure Regulation (F : Frame) (_S : Pattern F) where
  cutInternal : Effect
  cutExternal : Effect

/-- Locus is COMPUTED from the ablation pair, never asserted. -/
def locusOf {F : Frame} {S : Pattern F} (R : Regulation F S) : Locus :=
  match R.cutInternal.matters, R.cutExternal.matters with
  | true,  false => .selfRegulating
  | false, true  => .externallyRegulated
  | true,  true  => .coRegulated
  | false, false => .decoupled

/-- ME / OF / PE. PE is the argmax of OF over predicted model states (Box 1). -/
structure Apparatus (F : Frame) (Act : Type) where
  ME         : F.Desc → F.Desc → F.Desc
  predict    : F.Desc → Act → F.Desc
  OF         : F.Desc → Int
  choose     : F.Desc → Act
  isArgmax   : ∀ m a, OF (predict m a) ≤ OF (predict m (choose m))
  nontrivial : ∃ x y, OF x ≠ OF y

/-- An agent's objective proxies the persistence of some named pattern. -/
structure Objective (F : Frame) (Act : Type) where
  app    : Apparatus F Act
  target : Pattern F

/-- AGENTHOOD is a PREDICATE on patterns: regulatory work localized within
    (self- or co-regulation), plus the apparatus. -/
def IsAgent {F : Frame} {Act : Type} {S : Pattern F}
    (R : Regulation F S) (_O : Objective F Act) : Prop :=
  locusOf R = Locus.selfRegulating ∨ locusOf R = Locus.coRegulated

/-- TELEHOMEOSTATIC: fixed by the OBJECTIVE ALONE. -/
def IsTelehomeostatic {F : Frame} {Act : Type}
    (S : Pattern F) (O : Objective F Act) : Prop :=
  O.target.code = S.code

/-! ### Witness frame -/

@[reducible] def F0 : Frame where
  Desc := Nat
  K := id
  DL := id
  slack := 0
  sub := fun s m => s ≤ m
  mai := fun x y => min x y
  usefulFor := fun _ => True
  mai_symm := Nat.min_comm
  mai_le_l := fun x y => Nat.min_le_left x y
  mai_le_r := fun x y => Nat.min_le_right x y
  proxy := fun x => by simp

def W0 : WorldModel F0 := ⟨0, 1000⟩

/-! ### The four cells of WP0207, ALL patterns -/

def a_i : Pattern F0 := ⟨10, W0, by decide, trivial⟩   -- the token
def T   : Pattern F0 := ⟨20, W0, by decide, trivial⟩   -- the constituent class
def M   : Pattern F0 := ⟨30, W0, by decide, trivial⟩   -- this collective
def L   : Pattern F0 := ⟨40, W0, by decide, trivial⟩   -- the collective kind

/-- A minimal apparatus; every cell carries one, so every cell can be an agent. -/
def app0 : Apparatus F0 Unit where
  ME := fun m _ => m
  predict := fun m _ => m
  OF := fun x => (x : Int)
  choose := fun _ => ()
  isArgmax := fun m a => by cases a; exact le_refl _
  nontrivial := ⟨0, 1, by decide⟩

def obj (target : Pattern F0) : Objective F0 Unit := ⟨app0, target⟩

/-- All four are self-regulating: cutting the internal channel dissolves them. -/
def selfReg (S : Pattern F0) : Regulation F0 S := ⟨Effect.dissolves, Effect.noEffect⟩

/-! ### The claim: all four cells are agents -/

theorem token_is_agent      : IsAgent (selfReg a_i) (obj T) := Or.inl rfl
theorem class_is_agent      : IsAgent (selfReg T)   (obj T) := Or.inl rfl
theorem collective_is_agent : IsAgent (selfReg M)   (obj L) := Or.inl rfl
theorem kind_is_agent       : IsAgent (selfReg L)   (obj L) := Or.inl rfl

/-! ### Who is telehomeostatic: the objective decides, and it splits by column -/

/-- In agentoptosis the token's objective proxies its CLASS, not itself. -/
theorem token_not_telehomeostatic : ¬ IsTelehomeostatic a_i (obj T) := by
  simp [IsTelehomeostatic, obj, a_i, T]

/-- The class's objective is its own persistence. -/
theorem class_is_telehomeostatic : IsTelehomeostatic T (obj T) := rfl

/-- Snowflake yeast: the collective instance's objective proxies its LINEAGE. -/
theorem collective_not_telehomeostatic : ¬ IsTelehomeostatic M (obj L) := by
  simp [IsTelehomeostatic, obj, M, L]

/-- The collective kind's objective is its own persistence. -/
theorem kind_is_telehomeostatic : IsTelehomeostatic L (obj L) := rfl

/-- The payoff: a token can be a genuine agent AND not telehomeostatic. That is
    exactly the room agentoptosis occupies. -/
theorem agentoptosis_gap :
    IsAgent (selfReg a_i) (obj T) ∧ ¬ IsTelehomeostatic a_i (obj T) :=
  ⟨token_is_agent, token_not_telehomeostatic⟩

/-- Normally the proxy coincides with the token itself, and then it IS
    telehomeostatic. Agentoptosis is the divergence, not the rule. -/
theorem token_usually_telehomeostatic : IsTelehomeostatic a_i (obj a_i) := rfl

/-- Neither ablation matters: the pattern is decoupled. -/
def decoupledReg (S : Pattern F0) : Regulation F0 S := ⟨Effect.noEffect, Effect.noEffect⟩

/-- The thermostat room: only the EXTERNAL cut dissolves it. -/
def roomReg (S : Pattern F0) : Regulation F0 S := ⟨Effect.noEffect, Effect.dissolves⟩

end KTAIT.PP
