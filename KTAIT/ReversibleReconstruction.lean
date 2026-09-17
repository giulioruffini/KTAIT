/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import KTAIT.Basic

/-!
# Reversible reconstruction for WP0203 v20

Complete regulated-episode records recover the final joint state. A left inverse of the
joint evolution recovers the initial state, a world decoder extracts the initial world,
and a specified null protocol produces the uncontrolled output.

This module checks the composition with the inverse law explicitly present. The standard
AIT description-cost bound for applying each fixed computable map is a named hypothesis;
computability and universal-machine coding are not constructed at this frame level. The
context (including the law and horizon) is absorbed into the conditioned frame. Records
must cover the joint state, including regulator memory; a world-only projection is not
assumed complete. All costs below are explicit natural numbers.
-/

namespace KTAIT.ReversibleReconstruction

variable (F : AITFrame)

/-- Description-cost bound for applying a fixed computable map, with supplied context.
It is a hypothesis about the map and frame, not an axiom for arbitrary functions. -/
def ConditionalMapBound (f : F.Obj → F.Obj) (cost : Nat) : Prop :=
  ∀ x context, F.cond (f x) context ≤ F.cond x context + cost

/-- Recover the initial state from any records that recover the final state, using the
left inverse of the joint evolution. No world-only recovery is inferred. -/
theorem initial_from_complete_records
    (forward backward : F.Obj → F.Obj)
    (hinverse : Function.LeftInverse backward forward)
    (s₀ records : F.Obj) (recordCost inverseCost : Nat)
    (hrecords : F.cond (forward s₀) records ≤ recordCost)
    (hbackward : ConditionalMapBound F backward inverseCost) :
    F.cond s₀ records ≤ recordCost + inverseCost := by
  have h := hbackward (forward s₀) records
  rw [hinverse s₀] at h
  omega

/-- Complete final records, inverse joint dynamics, the initial-world decoder, and a
specified null protocol together reconstruct the uncontrolled output. The four costs
sum; there is no assumption that the resulting residual before records are supplied is
small. This is the frame-level counterpart of WP0203's reconstruction proposition. -/
theorem null_from_complete_records
    (forward backward world nullOutput : F.Obj → F.Obj)
    (hinverse : Function.LeftInverse backward forward)
    (s₀ records : F.Obj) (recordCost inverseCost worldCost nullCost : Nat)
    (hrecords : F.cond (forward s₀) records ≤ recordCost)
    (hbackward : ConditionalMapBound F backward inverseCost)
    (hworld : ConditionalMapBound F world worldCost)
    (hnull : ConditionalMapBound F nullOutput nullCost) :
    F.cond (nullOutput (world s₀)) records ≤
      recordCost + inverseCost + worldCost + nullCost := by
  have hi := initial_from_complete_records F forward backward hinverse
    s₀ records recordCost inverseCost hrecords hbackward
  have hw := hworld s₀ records
  have hn := hnull (world s₀) records
  omega

end KTAIT.ReversibleReconstruction
