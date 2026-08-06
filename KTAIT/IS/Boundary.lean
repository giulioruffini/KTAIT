/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib

/-!
# KTAIT.IS.Boundary — WP0215: equal boundary behavior, different internal organization

The negative half of BCOM WP0215, *The Simulation Is Phenomenally Itself*: sameness of the
exposed input–output map does not fix the internal structure. Here that is a theorem and a
counterexample rather than an intuition.

**The boundary is declared, not assumed.** A `Machine` exposes an output at every prefix of a
finite input word (`trace`), and `boundary` is that map from the start state. Choosing a coarser
boundary — the final output only — would make more machines agree; choosing a richer one, with
interventions on internal state, would make fewer. The counterexample below survives the *finest*
boundary of this family, the full output trace.

**Internal isomorphism is restricted to reachable states.** Otherwise the counterexample would be
cheap: pad a machine with unreachable states and it stops being isomorphic to anything. The
`parity4`/`parity2` pair does not use that trick — every state of the four-state machine is
reachable (`parity4_all_reachable`), and it still fails to be isomorphic to the two-state machine
with the same boundary. The obstruction is the count of reachable states, which no relabelling
can change.

One direction holds and the other does not, which is the whole point:

* `boundary_eq_of_iso` — internal isomorphism implies boundary equality;
* `parity4_boundary_eq_parity2` together with `parity4_not_internal_iso` — the converse fails.

Mathlib only; no AIT interface is involved and no axioms beyond Lean core are used.
-/

namespace KTAIT
namespace IS

variable {S I O S₁ S₂ : Type}

/-! ### Finite deterministic machines and their boundary -/

/-- A deterministic machine: a start state, a state transition driven by an input symbol, and an
output readout. Finiteness of `S` is not part of the structure; the counterexamples instantiate
it at `Fin 4` and `Fin 2`. -/
structure Machine (S I O : Type) where
  /-- The initial state. -/
  start : S
  /-- The transition function. -/
  step : S → I → S
  /-- The readout exposed at the boundary. -/
  out : S → O

namespace Machine

/-- The state reached from `s` after consuming the input word `w`. -/
def run (M : Machine S I O) (s : S) : List I → S
  | [] => s
  | i :: is => M.run (M.step s i) is

/-- The output trace from `s` on the input word `w`: the readout at every prefix, so a word of
length `n` produces `n + 1` outputs. -/
def trace (M : Machine S I O) (s : S) : List I → List O
  | [] => [M.out s]
  | i :: is => M.out s :: M.trace (M.step s i) is

/-- **The boundary map**: the output trace from the start state. This is the exposed interface —
everything an external observer restricted to input words and outputs can see. -/
def boundary (M : Machine S I O) (w : List I) : List O := M.trace M.start w

/-- A state is **reachable** when some input word leads to it from the start state. -/
def Reach (M : Machine S I O) (s : S) : Prop := ∃ w : List I, M.run M.start w = s

theorem run_append (M : Machine S I O) (s : S) (w v : List I) :
    M.run s (w ++ v) = M.run (M.run s w) v := by
  induction w generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, run, ih]

/-- Reachability is closed under one transition. -/
theorem reach_step (M : Machine S I O) {s : S} (h : M.Reach s) (i : I) :
    M.Reach (M.step s i) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w ++ [i], by rw [run_append, hw]; rfl⟩

/-- The start state is reachable. -/
theorem reach_start (M : Machine S I O) : M.Reach M.start := ⟨[], rfl⟩

end Machine

/-! ### Internal isomorphism, restricted to the reachable part -/

/-- An **internal isomorphism** between two machines over the same interface: a bijection between
their *reachable* state sets that carries start to start, commutes with the transition function,
and preserves the readout.

The restriction to reachable states is deliberate: unreachable states are not part of the
system's organization, and a counterexample built out of them would be about dead code rather
than about structure. Stated with an explicit inverse `g` rather than an `Equiv` so that the
reachability side-conditions stay visible in every field. -/
structure InternalIso (M₁ : Machine S₁ I O) (M₂ : Machine S₂ I O) where
  /-- The forward map on states. -/
  f : S₁ → S₂
  /-- The backward map on states. -/
  g : S₂ → S₁
  /-- `g` inverts `f` on the reachable part of `M₁`. -/
  left_inv : ∀ s, M₁.Reach s → g (f s) = s
  /-- `f` inverts `g` on the reachable part of `M₂`. -/
  right_inv : ∀ s, M₂.Reach s → f (g s) = s
  /-- Start states correspond. -/
  map_start : f M₁.start = M₂.start
  /-- The correspondence commutes with the dynamics on the reachable part. -/
  map_step : ∀ s, M₁.Reach s → ∀ i, f (M₁.step s i) = M₂.step (f s) i
  /-- The correspondence preserves the readout on the reachable part. -/
  map_out : ∀ s, M₁.Reach s → M₁.out s = M₂.out (f s)

/-! ### Internal isomorphism implies boundary equality -/

/-- Traces agree from corresponding reachable states. -/
theorem trace_eq_of_iso {M₁ : Machine S₁ I O} {M₂ : Machine S₂ I O} (Φ : InternalIso M₁ M₂)
    (w : List I) : ∀ s, M₁.Reach s → M₁.trace s w = M₂.trace (Φ.f s) w := by
  induction w with
  | nil => intro s hs; simp only [Machine.trace, Φ.map_out s hs]
  | cons i is ih =>
      intro s hs
      simp only [Machine.trace, Φ.map_out s hs, ← Φ.map_step s hs i,
        ih (M₁.step s i) (Machine.reach_step M₁ hs i)]

/-- **Internal isomorphism implies boundary equality.** The organization determines the exposed
behavior; this is the direction that does hold. -/
theorem boundary_eq_of_iso {M₁ : Machine S₁ I O} {M₂ : Machine S₂ I O} (Φ : InternalIso M₁ M₂) :
    ∀ w, M₁.boundary w = M₂.boundary w := by
  intro w
  simp only [Machine.boundary, trace_eq_of_iso Φ w M₁.start (Machine.reach_start M₁),
    Φ.map_start]

/-! ### The converse fails: parity by a four-state counter and by a two-state counter

Both machines consume clock ticks (`I := Unit`) and report the parity of the number of ticks so
far. `parity4` counts modulo four, `parity2` modulo two. They expose the same boundary, all four
states of `parity4` are reachable, and no internal isomorphism exists — for the plainest of
reasons, that four reachable states cannot be put in bijection with two. -/

/-- Parity computed by a counter modulo four. -/
def parity4 : Machine (Fin 4) Unit Bool where
  start := 0
  step := fun s _ => s + 1
  out := fun s => decide (s.val % 2 = 1)

/-- Parity computed by a counter modulo two. -/
def parity2 : Machine (Fin 2) Unit Bool where
  start := 0
  step := fun s _ => s + 1
  out := fun s => decide (s.val % 2 = 1)

/-- The reduction modulo two, the only candidate correspondence. -/
def red (s : Fin 4) : Fin 2 := ⟨s.val % 2, by omega⟩

theorem red_out : ∀ s : Fin 4, parity4.out s = parity2.out (red s) := by decide

theorem red_step : ∀ (s : Fin 4) (i : Unit), red (parity4.step s i) = parity2.step (red s) i := by
  decide

/-- **Every state of the four-state machine is reachable.** The counterexample therefore does not
rest on dead code: nothing here could be removed by pruning unreachable states. -/
theorem parity4_all_reachable : ∀ s : Fin 4, parity4.Reach s := by
  intro s
  fin_cases s
  · exact ⟨[], rfl⟩
  · exact ⟨[()], rfl⟩
  · exact ⟨[(), ()], rfl⟩
  · exact ⟨[(), (), ()], rfl⟩

theorem parity_trace_eq (w : List Unit) :
    ∀ s : Fin 4, parity4.trace s w = parity2.trace (red s) w := by
  induction w with
  | nil => intro s; simp only [Machine.trace, red_out s]
  | cons i is ih =>
      intro s
      simp only [Machine.trace, red_out s, ← red_step s i, ih (parity4.step s i)]

/-- **Same boundary.** On every input word the two machines emit the same output trace, so no
observation confined to the declared boundary can tell them apart. -/
theorem parity4_boundary_eq_parity2 : ∀ w, parity4.boundary w = parity2.boundary w := by
  intro w
  simp only [Machine.boundary, parity_trace_eq w parity4.start]
  rfl

/-- **Different organization.** There is no internal isomorphism between them. The four reachable
states of `parity4` would have to inject into the two states of `parity2`, and they cannot.

With `boundary_eq_of_iso` this settles the converse: boundary equality does not imply internal
isomorphism, and it does so without any appeal to unreachable states. The paper's use of this is
that extensional agreement at a declared interface underdetermines implemented structure. -/
theorem parity4_not_internal_iso : ¬ Nonempty (InternalIso parity4 parity2) := by
  rintro ⟨Φ⟩
  have hinj : Function.Injective Φ.f := by
    intro a b hab
    have ha := Φ.left_inv a (parity4_all_reachable a)
    have hb := Φ.left_inv b (parity4_all_reachable b)
    rw [← ha, ← hb, hab]
  have hcard := Fintype.card_le_of_injective Φ.f hinj
  simp only [Fintype.card_fin] at hcard
  omega

#check @boundary_eq_of_iso
#check @parity4_boundary_eq_parity2
#check @parity4_not_internal_iso

end IS
end KTAIT
