/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import KTAIT.GroundedRegulation
import KTAIT.ReversibleReconstruction

/-!
# Lossless generative-model regulation for WP0203 v22

A retained model generates the null output. Additive compensation has an explicit
inverse and makes an exactly predicted output zero. The algebra below does not
assume that an actuator can implement it in a particular physical system.

At the AIT-frame level, fixed computable maps have explicit description-cost
hypotheses. They give conservation under a supplied inverse, reconstruction from
an available model, and the initial-information bound. The context and horizon
are absorbed into the frame; model parameters remain part of the supplied model.
No shortest-model discovery procedure or new AIT axiom is introduced.
-/

namespace KTAIT.GenerativeRegulation

section Compensation

variable {Model Value : Type} [AddGroup Value]

/-- Apply the predicted correction while retaining the model. -/
def compensate (generate : Model → Value) (state : Value × Model) : Value × Model :=
  (state.1 - generate state.2, state.2)

/-- Add the prediction back, using the model retained in the joint state. -/
def restore (generate : Model → Value) (state : Value × Model) : Value × Model :=
  (state.1 + generate state.2, state.2)

/-- Compensation loses no distinction in the joint output/model state. -/
theorem compensation_reversible (generate : Model → Value) :
    Function.LeftInverse (restore generate) (compensate generate) := by
  rintro ⟨value, model⟩
  simp [compensate, restore]

/-- An exactly generated disturbance is canceled; the model remains available. -/
theorem model_cancellation (generate : Model → Value) (model : Model) :
    compensate generate (generate model, model) = (0, model) := by
  simp [compensate]

end Compensation

open GroundedRegulation RegulationBalance ReversibleReconstruction

variable (F : AITFrame)

/-- Standard description-cost bound for a supplied fixed computable map.
It is a hypothesis about the map, not a claim for arbitrary functions. -/
def DescriptionMapBound (f : F.Obj → F.Obj) (cost : Nat) : Prop :=
  ∀ state, F.K (f state) ≤ F.K state + cost

/-- Forward and inverse description bounds preserve the complete-state complexity
to their shared overhead. The encoded state may be the output/model pair. -/
theorem joint_complexity_preserved
    (forward backward : F.Obj → F.Obj)
    (hinverse : Function.LeftInverse backward forward) (cost : Nat)
    (hforward : DescriptionMapBound F forward cost)
    (hbackward : DescriptionMapBound F backward cost) (state : F.Obj) :
    |(F.K (forward state) : Int) - (F.K state : Int)| ≤ (cost : Int) := by
  have hf := hforward state
  have hb := hbackward (forward state)
  rw [hinverse state] at hb
  rw [abs_le]
  omega

/-- Reading an available model and executing its generator bounds the residual,
independently of the observed output gap. The model includes parameter data. -/
theorem model_residual
    (generate : F.Obj → F.Obj) (model output regulator : F.Obj)
    (readCost generateCost : Nat)
    (hmodel : F.cond model (F.pair output regulator) ≤ readCost)
    (hgenerate : ConditionalMapBound F generate generateCost) :
    residual F output (generate model) regulator ≤ (readCost + generateCost : Nat) := by
  have hg := hgenerate model (F.pair output regulator)
  simp only [GroundedRegulation.residual]
  omega

/-- A model that already reconstructs the null output supplies the small-residual
premise of the existing initial-information inference. -/
theorem model_initial_information
    (generate : F.Obj → F.Obj) (world model output regulator : F.Obj)
    (readCost generateCost : Nat)
    (hmodel : F.cond model (F.pair output regulator) ≤ readCost)
    (hgenerate : ConditionalMapBound F generate generateCost)
    (hmut : MutualChain F (generate model) regulator)
    (hsub : CondSubadd F output (generate model) regulator)
    (hmono : CondMono F output regulator)
    (hdp : DataProcessing F (generate model) world regulator) :
    IK F world regulator ≥ gap F output (generate model) -
      (readCost + generateCost : Nat) - 3 * (F.slack : Int) := by
  have hr := model_residual F generate model output regulator readCost generateCost
    hmodel hgenerate
  have hb := grounded_inequality F world output (generate model) regulator
    hmut hsub hmono hdp
  omega

end KTAIT.GenerativeRegulation
