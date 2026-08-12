/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic
import KTAIT.RegulationBalance

/-!
# KTAIT.PersistenceFlow — the Algorithmic Persistence Balance suite (APB)

The persistence theorem suite of the KT Persistence Theorem Roadmap v2 (2026-08-12),
superseding the earlier `PersistenceAccounting` module (APAT is renamed APB; the pigeonhole
corollary is reorganized per the roadmap's module plan).

Reading of the objects (roadmap notation):

* `iota` — the fixed identity-relevant incoming interface record `ι_{P,N}` for focal
  pattern `P` over horizon `N`, a computable projection declared before any comparison.
* `Ctx` — the initial conditioning context `Ctx_{P,t} = ⟨C, Z_t, 𝒲_t⟩`: frame, current
  self-code, current reusable model. `K(ι | Ctx)` is then the *residual identity-relevant
  novelty* `ν_{P,N}`: what the present organization fails to predict about its own inflow.
* `Znext, Mnext, sigma, action, exhaust` — later self-code `Z⁺`, later reusable model
  `𝒲⁺`, retained state `σ_N`, action/interface transcript `a_N`, and an admissible
  complementary world record `Ξ_N`. As in `KTAIT.RegulationBalance`, a complete reversible
  realization always supplies a closure witness; minimality and physical localization of
  `Ξ` are additional modelling hypotheses (see that module's Localization section).

The suite:

1. `FlowSplit5` — the named five-way ordered conditional-flow split (house style).
2. `algorithmic_persistence_balance` (APB) — identity-relevant novelty is recoverable from
   self-code change, model update, retained state, action, or world complement.
3. `bounded_persistence_forces_flow` — bounded internal channels force interface/world flow.
4. `flow_pigeonhole` — finite max-form: one of the two flow channels carries half the load.
5. `self_code_overload` — recoverable novelty forces self-code update.
6. `bounded_self_code_capacity` — a budgeted self-code stores at most `K₀ + δ + slack` of
   independent novelty.
7. `persistence_does_not_imply_gap` — explicit witness: perfect persistence with a strictly
   negative raw readout gap. Kills any universal persistence-to-positive-gap bridge; the
   universal statement is APB's accounting, not a gap claim.

Counterfactual input suppression (acting so that less novelty arrives) is not re-proved
here: it is the existing grounded machinery of `KTAIT.GroundedRegulation` instantiated with
an identity-relevant input reguland; the hard part is the modelling (fixed projection,
matched null), not new algebra.

## Discipline

All AIT facts consumed (`CondChain`, `InfoClosed`, `CondSubadd`, `CondMono`, the split, the
conditional-MAI ceiling) are named `Prop` hypotheses about a frame, never axioms. The
counterexample is a hand-built frame witness, in the style of `ModelOrPay`.
-/

namespace KTAIT
namespace PersistenceFlow

open RegulationBalance

variable (F : AITFrame)

/-! ## The completion tuple and the named AIT facts -/

/-- The APB completion tuple `Q = ⟨Z⁺, ⟨𝒲⁺, ⟨σ, ⟨a, Ξ⟩⟩⟩⟩`. -/
def flowTuple (Znext Mnext sigma action exhaust : F.Obj) : F.Obj :=
  F.pair Znext (F.pair Mnext (F.pair sigma (F.pair action exhaust)))

/-- **Five-way ordered split of the persistence flow** (conditional chain rule), with
    `Q = flowTuple` the completion and `Ctx` the initial conditioning context:

    `M(ι : Q | Ctx) ≤ M(ι : Z⁺ | Ctx) + M(ι : 𝒲⁺ | ⟨Z⁺,Ctx⟩) + M(ι : σ | ⟨𝒲⁺,⟨Z⁺,Ctx⟩⟩)`
    `              + M(ι : a | ⟨σ,…⟩) + M(ι : Ξ | ⟨a,…⟩) + slack`.

    The order (self-code, model, state, action, world record) is fixed for interpretation;
    only the joint total is order-invariant up to slack. -/
def FlowSplit5 (iota Znext Mnext sigma action exhaust Ctx : F.Obj) : Prop :=
  cIK F iota (flowTuple F Znext Mnext sigma action exhaust) Ctx
    ≤ cIK F iota Znext Ctx
      + cIK F iota Mnext (F.pair Znext Ctx)
      + cIK F iota sigma (F.pair Mnext (F.pair Znext Ctx))
      + cIK F iota action (F.pair sigma (F.pair Mnext (F.pair Znext Ctx)))
      + cIK F iota exhaust (F.pair action (F.pair sigma (F.pair Mnext (F.pair Znext Ctx))))
      + (F.slack : Int)

/-- **Conditional-MAI ceiling**: `M(A : B | C) ≤ K(B | C) + slack`. Shared information
    with `B` given `C` cannot exceed `B`'s own conditional description. The conditional
    analogue of `ModelOrPay.MAICapped` / `GroundedRegulation.IKCeiling`. -/
def CIKCeiling (A B C : F.Obj) : Prop :=
  cIK F A B C ≤ (F.cond B C : Int) + (F.slack : Int)

/-! ## The Algorithmic Persistence Balance -/

/-- **Algorithmic Persistence Balance (APB).** Under information closure of the episode
    and the declared five-way split, the residual identity-relevant novelty `K(ι | Ctx)`
    is bounded by what the later self-code, later model, retained state, action
    transcript, and complementary world record each carry about the inflow record:

    `K(ι|Ctx) ≤ M(ι:Z⁺|Ctx) + M(ι:𝒲⁺|…) + M(ι:σ|…) + M(ι:a|…) + M(ι:Ξ|…) + 3·slack`.

    Identity-relevant novelty is never unaccounted for: it is predicted-away, kept,
    consolidated, acted out, or left in the world. The proof is
    `residual_in_completion` plus the declared split. -/
theorem algorithmic_persistence_balance
    (iota Ctx Znext Mnext sigma action exhaust : F.Obj)
    (hchain : CondChain F iota (flowTuple F Znext Mnext sigma action exhaust) Ctx)
    (hclosed : InfoClosed F iota (flowTuple F Znext Mnext sigma action exhaust) Ctx)
    (hsplit : FlowSplit5 F iota Znext Mnext sigma action exhaust Ctx) :
    (F.cond iota Ctx : Int)
      ≤ cIK F iota Znext Ctx
        + cIK F iota Mnext (F.pair Znext Ctx)
        + cIK F iota sigma (F.pair Mnext (F.pair Znext Ctx))
        + cIK F iota action (F.pair sigma (F.pair Mnext (F.pair Znext Ctx)))
        + cIK F iota exhaust (F.pair action (F.pair sigma (F.pair Mnext (F.pair Znext Ctx))))
        + 3 * (F.slack : Int) := by
  have hres :=
    residual_in_completion F iota (flowTuple F Znext Mnext sigma action exhaust) Ctx
      hchain hclosed
  simp only [FlowSplit5] at hsplit
  omega

/-! ## Bounded persistence forces flow -/

/-- **Bounded persistence forces flow.** Cap the three internal channels by their
    conditional descriptions (`d_Z = K(Z⁺|Ctx)`, `d_M = K(𝒲⁺|⟨Z⁺,Ctx⟩)`,
    `d_σ = K(σ|⟨𝒲⁺,⟨Z⁺,Ctx⟩⟩)`, via the conditional-MAI ceiling). Then the two flow
    channels carry the rest of the residual novelty:

    `J_a + J_Ξ ≥ K(ι|Ctx) − d_Z − d_M − d_σ − 6·slack`.

    If self-code change, model growth, and retained state are bounded, remaining
    identity-relevant novelty must be carried through the interface or remain in
    complementary world degrees. (Prevention — acting so the novelty never arrives — is
    the separate grounded-regulation route.) -/
theorem bounded_persistence_forces_flow
    (iota Ctx Znext Mnext sigma action exhaust : F.Obj)
    (hchain : CondChain F iota (flowTuple F Znext Mnext sigma action exhaust) Ctx)
    (hclosed : InfoClosed F iota (flowTuple F Znext Mnext sigma action exhaust) Ctx)
    (hsplit : FlowSplit5 F iota Znext Mnext sigma action exhaust Ctx)
    (hcZ : CIKCeiling F iota Znext Ctx)
    (hcM : CIKCeiling F iota Mnext (F.pair Znext Ctx))
    (hcS : CIKCeiling F iota sigma (F.pair Mnext (F.pair Znext Ctx))) :
    cIK F iota action (F.pair sigma (F.pair Mnext (F.pair Znext Ctx)))
      + cIK F iota exhaust (F.pair action (F.pair sigma (F.pair Mnext (F.pair Znext Ctx))))
      ≥ (F.cond iota Ctx : Int)
        - (F.cond Znext Ctx : Int)
        - (F.cond Mnext (F.pair Znext Ctx) : Int)
        - (F.cond sigma (F.pair Mnext (F.pair Znext Ctx)) : Int)
        - 6 * (F.slack : Int) := by
  have h :=
    algorithmic_persistence_balance F iota Ctx Znext Mnext sigma action exhaust
      hchain hclosed hsplit
  simp only [CIKCeiling] at hcZ hcM hcS
  omega

/-- **Finite flow pigeonhole (max form).** Under the same hypotheses, twice the larger
    flow channel dominates the unaccounted residual:

    `2 · max{J_a, J_Ξ} ≥ K(ι|Ctx) − d_Z − d_M − d_σ − 6·slack`.

    One of interface flow and world complement carries at least half the load. Finite
    only; asymptotic rate forms are analysis on top of this and are deliberately not
    formalized. -/
theorem flow_pigeonhole
    (iota Ctx Znext Mnext sigma action exhaust : F.Obj)
    (hchain : CondChain F iota (flowTuple F Znext Mnext sigma action exhaust) Ctx)
    (hclosed : InfoClosed F iota (flowTuple F Znext Mnext sigma action exhaust) Ctx)
    (hsplit : FlowSplit5 F iota Znext Mnext sigma action exhaust Ctx)
    (hcZ : CIKCeiling F iota Znext Ctx)
    (hcM : CIKCeiling F iota Mnext (F.pair Znext Ctx))
    (hcS : CIKCeiling F iota sigma (F.pair Mnext (F.pair Znext Ctx))) :
    2 * max (cIK F iota action (F.pair sigma (F.pair Mnext (F.pair Znext Ctx))))
            (cIK F iota exhaust (F.pair action (F.pair sigma (F.pair Mnext (F.pair Znext Ctx)))))
      ≥ (F.cond iota Ctx : Int)
        - (F.cond Znext Ctx : Int)
        - (F.cond Mnext (F.pair Znext Ctx) : Int)
        - (F.cond sigma (F.pair Mnext (F.pair Znext Ctx)) : Int)
        - 6 * (F.slack : Int) := by
  have h :=
    bounded_persistence_forces_flow F iota Ctx Znext Mnext sigma action exhaust
      hchain hclosed hsplit hcZ hcM hcS
  rcases le_total
      (cIK F iota action (F.pair sigma (F.pair Mnext (F.pair Znext Ctx))))
      (cIK F iota exhaust (F.pair action (F.pair sigma (F.pair Mnext (F.pair Znext Ctx))))) with
    hle | hle
  · rw [max_eq_right hle]; omega
  · rw [max_eq_left hle]; omega

/-! ## Self-code overload -/

/-- **Self-code overload.** If the identity-relevant novelty is recoverable from the later
    self-code — `K(ι | ⟨Z₁, ⟨Z₀,C⟩⟩) ≤ δ` — then the self-code update must be at least as
    large as the novelty:

    `K(Z₁ | ⟨Z₀,C⟩) ≥ K(ι | ⟨Z₀,C⟩) − δ − slack`.

    Writing unpredicted novelty into the identity core forces the identity description to
    change by that much. The proof is subadditivity through the intermediate `Z₁`. -/
theorem self_code_overload
    (iota Z0 Z1 Cf : F.Obj) (δ : Int)
    (hsub : CondSubadd F Z1 iota (F.pair Z0 Cf))
    (hrec : (F.cond iota (F.pair Z1 (F.pair Z0 Cf)) : Int) ≤ δ) :
    (F.cond Z1 (F.pair Z0 Cf) : Int)
      ≥ (F.cond iota (F.pair Z0 Cf) : Int) - δ - (F.slack : Int) := by
  simp only [CondSubadd] at hsub
  omega

/-- **Bounded self-code capacity.** If additionally the later self-code obeys a uniform
    budget `K(Z₁) ≤ K₀` (and conditioning only shrinks description length), then the
    novelty storable uniquely in the self-code is capped:

    `K(ι | ⟨Z₀,C⟩) ≤ K₀ + δ + 2·slack`.

    A bounded identity cannot be an indefinitely growing memory: novelty beyond the budget
    must be compressed, consolidated outside the identity core, routed out, or forgotten. -/
theorem bounded_self_code_capacity
    (iota Z0 Z1 Cf : F.Obj) (δ K0 : Int)
    (hsub : CondSubadd F Z1 iota (F.pair Z0 Cf))
    (hrec : (F.cond iota (F.pair Z1 (F.pair Z0 Cf)) : Int) ≤ δ)
    (hmono : CondMono F Z1 (F.pair Z0 Cf))
    (hbudget : (F.K Z1 : Int) ≤ K0) :
    (F.cond iota (F.pair Z0 Cf) : Int) ≤ K0 + δ + (F.slack : Int) := by
  have h := self_code_overload F iota Z0 Z1 Cf δ hsub hrec
  simp only [CondMono] at hmono
  omega

/-! ## Persistence does not imply a positive gap -/

/-- The witness frame: an incompressible identity `z` (code 2, `K = 100`) and its
    annihilated continuation `0^n` (code 3, `K = 7`). Pairing is `Nat.pair`; `K` on the
    relevant pairs makes `z` self-redundant (`K⟨z,z⟩ = 100`) and `z, 0^n` independent
    (`K⟨z,0^n⟩ = 107`). Conditional structure is irrelevant to the claim and set to 0. -/
def noGapFrame : AITFrame where
  Obj := ℕ
  K := fun m =>
    if m = 2 then 100 else if m = 3 then 7
    else if m = Nat.pair 2 2 then 100 else if m = Nat.pair 2 3 then 107 else 0
  pair := Nat.pair
  cond := fun _ _ => 0
  star := id
  slack := 0

/-- **Persistence does not imply a positive gap** (explicit witness). There is a frame
    and a pair of readouts — regulated continuation `z` and unregulated annihilation
    `0^n` — with perfect persistence of the regulated identity, zero persistence of the
    annihilated one, and a *strictly negative* raw readout gap:

    `NMAI(z,z) = 1`, `NMAI(z,0^n) = 0`, yet `Δ = K(0^n) − K(z) < 0`.

    Simple destruction is simpler than survival, so no universal theorem can take a
    persistence advantage to a positive ART/GART gap. The universal statement is APB's
    accounting; GART remains the counterfactual refinement *when* a scientifically
    meaningful positive gap exists. -/
theorem persistence_does_not_imply_gap :
    ∃ (F : AITFrame) (zOn zOff : F.Obj),
      NMAI F zOn zOn = 1 ∧ NMAI F zOn zOff = 0 ∧ gap F zOn zOff < 0 := by
  refine ⟨noGapFrame, (2 : ℕ), (3 : ℕ), ?_, ?_, ?_⟩
  · simp [NMAI, IK, noGapFrame, Nat.pair]
  · simp [NMAI, IK, noGapFrame, Nat.pair]
  · simp [gap, noGapFrame]

end PersistenceFlow
end KTAIT
