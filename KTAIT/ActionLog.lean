/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code and Codex)
-/
import Mathlib
import KTAIT.Basic
import KTAIT.RegulationBalance
import KTAIT.GroundedRegulation

/-!
# KTAIT.ActionLog — the thermostat with an action log (WP0203 Round 1 worked case)

WP0203's Round 1 revision adds a worked case: a room's temperature deviation changes by a
disturbance and by the heater's action, `x_{n+1} = x_n + d_n + u_n` from `x_0 = 0`, and the
null episode runs the same disturbance with `u = 0`. If the heater keeps a log of its
actions, subtracting the accumulated actions from the regulated record rebuilds the null
record exactly (`reconstruct_null`, the integer identity, by Kaiti). The frame-level
statements then read that decoder as a description-cost bound and derive the example's
inferences: the residual is at most the log's description cost plus the decoder
(`residual_from_action_log`); with the first `N − m` disturbances stored in the initial
regulator the log costs `m` bits plus framing (`residual_with_preload`); a complex
disturbance recovered from the null record gives the gap (`gap_from_disturbance`); and GART
turns these into a certified lower bound on initial shared information
(`preload_certifies_initial_information`). The numerical premises `hdec`, `hlog`, `hrec`,
`hreg` are named hypotheses here; the finite-record bridges that derive them from the
decoder, the stored prefix and the first-difference inverse are stated in the paper's review
notes and follow once approved.
-/

namespace KTAIT
namespace ActionLog

open RegulationBalance GroundedRegulation

/-- The trajectory `x_{n+1} = x_n + d_n + u_n` from `x_0 = 0`, for a disturbance `d` and an
action sequence `u` (exact integers). The null trajectory is the same with `u = 0`. -/
def trajectory (disturbance action : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => trajectory disturbance action n + disturbance n + action n

/-- **The decoder identity.** Subtracting the accumulated actions from the regulated
trajectory gives the null trajectory, at every step. -/
theorem reconstruct_null (disturbance action : ℕ → ℤ) (n : ℕ) :
    trajectory disturbance (fun _ => 0) n =
      trajectory disturbance action n - trajectory (fun _ => 0) action n := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih =>
    simp only [trajectory]
    rw [ih]
    ring

variable (F : AITFrame)

/-- **Online case.** The residual is at most the description cost of the action log `U`
given the regulated record `yR` and the initial regulator `R`, plus the fixed decoder `b`
(`hdec`: given the log and the regulated record, the null record costs at most `b`) and one
composition overhead (`CondSubadd`). -/
theorem residual_from_action_log (yR ynull U R : F.Obj) (b : Nat)
    (hdec : (F.cond ynull (F.pair U (F.pair yR R)) : Int) ≤ b)
    (hsub : CondSubadd F U ynull (F.pair yR R)) :
    residual F yR ynull R ≤ (F.cond U (F.pair yR R) : Int) + b + (F.slack : Int) := by
  simp only [CondSubadd] at hsub
  simp only [GroundedRegulation.residual]
  omega

/-- **Preload case.** The first `N − m` binary disturbance values are stored in `R`, so the
log costs at most `m + b₁` given the regulated record and `R` (`hlog`); the residual is at
most `m + b` with `b := b₁ + bdec + slack`, as the paper collects it. -/
theorem residual_with_preload (yR ynull U R : F.Obj) (bdec b₁ m : Nat)
    (hdec : (F.cond ynull (F.pair U (F.pair yR R)) : Int) ≤ bdec)
    (hsub : CondSubadd F U ynull (F.pair yR R))
    (hlog : (F.cond U (F.pair yR R) : Int) ≤ m + b₁) :
    residual F yR ynull R ≤ m + (b₁ + bdec + (F.slack : Int)) := by
  have h := residual_from_action_log F yR ynull U R bdec hdec hsub
  omega

/-- **The gap.** A complex disturbance (`K d ≥ N − r`) recovered from the null record by a
fixed program (`K d ≤ K y∅ + c₁`) and a regulated record of bounded complexity
(`K yR ≤ c₂`) give `Δ ≥ N − r − (c₁ + c₂)`. -/
theorem gap_from_disturbance (yR ynull d : F.Obj) (N r c₁ c₂ : Int)
    (hd : (F.K d : Int) ≥ N - r)
    (hrec : (F.K d : Int) ≤ (F.K ynull : Int) + c₁)
    (hreg : (F.K yR : Int) ≤ c₂) :
    gap F yR ynull ≥ N - r - (c₁ + c₂) := by
  simp only [gap]
  omega

/-- **The certified inference.** GART in its world form with allowance `h` (an instance of
`grounded_inequality`, `h := 4·slack`), the preload residual bound and the gap bound give
`I ≥ N − m − s` with `s := r + b + c + h`. -/
theorem preload_certifies_initial_information (W yR ynull R : F.Obj) (N r c m b h : Int)
    (hgart : gap F yR ynull ≤ IK F W R + residual F yR ynull R + h)
    (hres : residual F yR ynull R ≤ m + b)
    (hgap : gap F yR ynull ≥ N - r - c) :
    IK F W R ≥ N - m - (r + b + c + h) := by
  omega

end ActionLog
end KTAIT
