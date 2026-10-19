/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic
import KTAIT.RegulationBalance
import KTAIT.GroundedRegulation
import KTAIT.ReversibleReconstruction
import KTAIT.GenerativeRegulation

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
(`preload_certifies_initial_information`). Those four helpers take the numerical premises
`hdec`, `hlog`, `hrec`, `hreg` as hypotheses. The finite-record section then identifies the
maps that produce the records (the decoder, the reactive rule, the stored prefix with the
supplied suffix, first differences and cumulative sums), proves that they do, and derives
those premises from named fixed-map costs (`ConditionalMapBound`, `DescriptionMapBound`),
with encodings of finite records into frame objects as explicit functions. The reactive case
gets two-sided bounds comparing the residual and the gap with the disturbance's complexity,
and a two-sided bound on the initial shared information of a short controller. Every
constant is named; the standard `slack` is the frame's uniform tolerance (`O(log N)` under
the paper's size convention), while the fixed-map costs of this example are `O(1)` in the
paper's interpretation.
-/

namespace KTAIT
namespace ActionLog

open RegulationBalance GroundedRegulation ReversibleReconstruction GenerativeRegulation

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

/-! ## Finite records: the maps behind the premises -/

section Finite

/-- With zero disturbance, the trajectory is the accumulated action, `∑_{j<n} u_j`. -/
theorem trajectory_zero_disturbance (u : ℕ → ℤ) (n : ℕ) :
    trajectory (fun _ => 0) u n = ∑ j ∈ Finset.range n, u j := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih => simp [trajectory, Finset.sum_range_succ, ih]

/-- With zero action, the trajectory is the accumulated disturbance, `∑_{j<n} d_j`. -/
theorem trajectory_zero_action (d : ℕ → ℤ) (n : ℕ) :
    trajectory d (fun _ => 0) n = ∑ j ∈ Finset.range n, d j := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih => simp [trajectory, Finset.sum_range_succ, ih]

/-- A sum over `Fin N` truncated at `t ≤ N` is the sum over `range t`. -/
theorem sum_fin_truncate (N t : ℕ) (ht : t ≤ N) (f : ℕ → ℤ) :
    (∑ j : Fin N, if (j : ℕ) < t then f j else 0) = ∑ j ∈ Finset.range t, f j := by
  have h := Fin.sum_univ_eq_sum_range (fun i => if i < t then f i else 0) N
  rw [h, ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- The null record and the regulated record over horizon `N`: samples `x_0, …, x_N`. -/
def nullRecord (d : ℕ → ℤ) (N : ℕ) : Fin (N + 1) → ℤ := fun t => trajectory d (fun _ => 0) t
def regulatedRecord (d u : ℕ → ℤ) (N : ℕ) : Fin (N + 1) → ℤ := fun t => trajectory d u t
/-- The action log over horizon `N`: actions `u_0, …, u_{N-1}`. -/
def actionLog (u : ℕ → ℤ) (N : ℕ) : Fin N → ℤ := fun j => u j
/-- The finite decoder: subtract the accumulated logged actions from the regulated record. -/
def decode (N : ℕ) (x : Fin (N + 1) → ℤ) (u : Fin N → ℤ) : Fin (N + 1) → ℤ :=
  fun t => x t - ∑ j : Fin N, if (j : ℕ) < (t : ℕ) then u j else 0

/-- **The decoder on finite records.** Applied to the regulated record and the log, the
decoder returns the null record of the same disturbance and initial state. -/
theorem decode_regulated_eq_null (d u : ℕ → ℤ) (N : ℕ) :
    decode N (regulatedRecord d u N) (actionLog u N) = nullRecord d N := by
  funext t
  have ht := t.isLt
  simp only [decode, regulatedRecord, actionLog, nullRecord]
  rw [sum_fin_truncate N t (by omega) u, ← trajectory_zero_disturbance, reconstruct_null d u t]

/-- **The decoder supplies `hdec`.** `encRec` and `encLog` encode records and logs as frame
objects; `decObj` is the decoder on encoded pairs and agrees with `decode` on encodings
(`hdecObj`); it has fixed-map cost `bdec` (`ConditionalMapBound`); the pair `⟨yR, U⟩`
projects from a context containing both at one `slack` (`hproj`). Then
`K(y∅ | U, yR, R) ≤ bdec + slack`, the `hdec` of `residual_from_action_log`. -/
theorem hdec_from_decoder (N : ℕ) (d u : ℕ → ℤ)
    (encRec : (Fin (N + 1) → ℤ) → F.Obj) (encLog : (Fin N → ℤ) → F.Obj)
    (decObj : F.Obj → F.Obj) (bdec : ℕ) (R : F.Obj)
    (hdecObj : ∀ x v, decObj (F.pair (encRec x) (encLog v)) = encRec (decode N x v))
    (hcost : ConditionalMapBound F decObj bdec)
    (hproj : (F.cond (F.pair (encRec (regulatedRecord d u N)) (encLog (actionLog u N)))
        (F.pair (encLog (actionLog u N)) (F.pair (encRec (regulatedRecord d u N)) R)) : Int)
        ≤ (F.slack : Int)) :
    (F.cond (encRec (nullRecord d N))
        (F.pair (encLog (actionLog u N)) (F.pair (encRec (regulatedRecord d u N)) R)) : Int)
      ≤ (bdec : Int) + (F.slack : Int) := by
  have h := hcost (F.pair (encRec (regulatedRecord d u N)) (encLog (actionLog u N)))
    (F.pair (encLog (actionLog u N)) (F.pair (encRec (regulatedRecord d u N)) R))
  rw [hdecObj, decode_regulated_eq_null] at h
  omega

/-- The reactive rule: cancel the observed pre-action deviation. Along the regulated
trajectory that deviation equals the disturbance (`reactive_observes_disturbance`), so the
log is `−d`. -/
def reactiveLog (d : ℕ → ℤ) : ℕ → ℤ := fun n => -d n

/-- Under the reactive log the regulated record is identically zero. -/
theorem reactive_regulated_zero (d : ℕ → ℤ) (n : ℕ) :
    trajectory d (reactiveLog d) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [trajectory, reactiveLog, ih]

/-- The pre-action deviation `x_n + d_n` along the reactive trajectory equals `d_n`: the rule
is realized from the measurement, not from a stored disturbance sequence. -/
theorem reactive_observes_disturbance (d : ℕ → ℤ) (n : ℕ) :
    trajectory d (reactiveLog d) n + d n = d n := by
  rw [reactive_regulated_zero]; ring

/-- A length-`N` record assembled from a stored prefix of length `N − m` and a supplied
suffix of length `m`. -/
def assemble (N m : ℕ) (hm : m ≤ N) (pre : Fin (N - m) → ℤ) (suf : Fin m → ℤ) : Fin N → ℤ :=
  fun t => if h : (t : ℕ) < N - m then pre ⟨t, h⟩
    else suf ⟨(t : ℕ) - (N - m), by have := t.isLt; omega⟩

/-- The stored prefix and the supplied suffix of the disturbance. -/
def prefixOf (d : ℕ → ℤ) (N m : ℕ) : Fin (N - m) → ℤ := fun t => d t
def suffixOf (d : ℕ → ℤ) (N m : ℕ) : Fin m → ℤ := fun t => d ((N - m) + t)

/-- **The log from a stored prefix and a supplied suffix.** The reactive log over the horizon
is the negation of the record assembled from the stored prefix and the supplied suffix. -/
theorem reactive_log_eq_prefix_suffix (d : ℕ → ℤ) (N m : ℕ) (hm : m ≤ N) :
    actionLog (reactiveLog d) N
      = fun t => -(assemble N m hm (prefixOf d N m) (suffixOf d N m) t) := by
  funext t
  have ht := t.isLt
  simp only [actionLog, reactiveLog, assemble, prefixOf, suffixOf]
  split_ifs with h
  · rfl
  · have : N - m + ((t : ℕ) - (N - m)) = (t : ℕ) := by omega
    rw [this]

/-- **The construction supplies `hlog`.** The log is the fixed map `asmObj` (cost `basm`) of
the encoded suffix and prefix, paired suffix first so that the pair is the one `CondChain`
describes; the prefix projects from `R` at one `slack` (`hprefix`, a fact about the initial
state); the suffix is described literally in `m` bits plus framing `cLit` (`hsuffix`); the
conditional chain rule composes the two (`hchain`). Then
`K(U | yR, R) ≤ m + (cLit + basm + 2·slack)`, the `hlog` of `residual_with_preload`.
Obligations outside the frame: `hsuffix` holds for a binary disturbance under effective
encodings, by the literal-description argument with its framing cost (an arbitrary integer
suffix has no `m`-bit description); `hprefix` is the initial stored-prefix fact; and the
decoder and assembly must be one uniform algorithm over the admitted horizons and splits,
since a separate map for each `N, m` does not by itself give a uniform cost. -/
theorem hlog_from_prefix_suffix (N m : ℕ) (hm : m ≤ N) (d : ℕ → ℤ)
    (encLog : (Fin N → ℤ) → F.Obj) (encPre : (Fin (N - m) → ℤ) → F.Obj)
    (encSuf : (Fin m → ℤ) → F.Obj) (asmObj : F.Obj → F.Obj) (basm cLit : ℕ) (yR R : F.Obj)
    (hasm : ∀ p s, asmObj (F.pair (encSuf s) (encPre p))
        = encLog (fun t => -(assemble N m hm p s t)))
    (hcost : ConditionalMapBound F asmObj basm)
    (hprefix : (F.cond (encPre (prefixOf d N m)) (F.pair yR R) : Int) ≤ (F.slack : Int))
    (hsuffix : (F.cond (encSuf (suffixOf d N m))
        (F.pair (encPre (prefixOf d N m)) (F.pair yR R)) : Int) ≤ (m : Int) + (cLit : Int))
    (hchain : CondChain F (encSuf (suffixOf d N m)) (encPre (prefixOf d N m)) (F.pair yR R)) :
    (F.cond (encLog (actionLog (reactiveLog d) N)) (F.pair yR R) : Int)
      ≤ (m : Int) + ((cLit : Int) + (basm : Int) + 2 * (F.slack : Int)) := by
  rw [reactive_log_eq_prefix_suffix d N m hm, ← hasm]
  have h := hcost (F.pair (encSuf (suffixOf d N m)) (encPre (prefixOf d N m))) (F.pair yR R)
  simp only [CondChain] at hchain
  omega

/-- First differences of a record of length `N + 1`. -/
def firstDiff (N : ℕ) (z : Fin (N + 1) → ℤ) : Fin N → ℤ :=
  fun t => z ⟨(t : ℕ) + 1, by have := t.isLt; omega⟩ - z ⟨t, by have := t.isLt; omega⟩
/-- The cumulative sums of a length-`N` disturbance, as a record of length `N + 1`. -/
def cumulate (N : ℕ) (δ : Fin N → ℤ) : Fin (N + 1) → ℤ :=
  fun t => ∑ j : Fin N, if (j : ℕ) < (t : ℕ) then δ j else 0

/-- **First differences of the null record are the disturbances.** -/
theorem firstDiff_null_eq_disturbance (d : ℕ → ℤ) (N : ℕ) :
    firstDiff N (nullRecord d N) = fun (t : Fin N) => d t := by
  funext t
  simp only [firstDiff, nullRecord, trajectory]
  ring

/-- **Cumulative sums of the disturbances are the null record.** -/
theorem cumulate_disturbance_eq_null (d : ℕ → ℤ) (N : ℕ) :
    cumulate N (fun (t : Fin N) => d t) = nullRecord d N := by
  funext t
  have ht := t.isLt
  simp only [cumulate, nullRecord]
  rw [sum_fin_truncate N t (by omega) d, trajectory_zero_action]

/-- **First differences supply `hrec`.** With `diffObj` the fixed map agreeing with
`firstDiff` on encodings and `DescriptionMapBound` cost `cdiff`, `K d ≤ K y∅ + cdiff`. -/
theorem hrec_from_first_difference (N : ℕ) (d : ℕ → ℤ)
    (encRec : (Fin (N + 1) → ℤ) → F.Obj) (encDist : (Fin N → ℤ) → F.Obj)
    (diffObj : F.Obj → F.Obj) (cdiff : ℕ)
    (hdiffObj : ∀ z, diffObj (encRec z) = encDist (firstDiff N z))
    (hcost : DescriptionMapBound F diffObj cdiff) :
    (F.K (encDist (fun (t : Fin N) => d t)) : Int)
      ≤ (F.K (encRec (nullRecord d N)) : Int) + cdiff := by
  have h := hcost (encRec (nullRecord d N))
  rw [hdiffObj, firstDiff_null_eq_disturbance] at h
  omega

/-- **Cumulative sums supply the upper bounds of the reactive case.** With `cumObj` agreeing
with `cumulate` on encodings, `K(y∅ | ctx) ≤ K(d | ctx) + ccum` and `K y∅ ≤ K d + ccum`. The
conditional and unconditional conclusions follow separately from `ConditionalMapBound` and
`DescriptionMapBound` for the same cumulative map; neither premise is inferred from the
other. -/
theorem hcum_from_cumulative (N : ℕ) (d : ℕ → ℤ)
    (encRec : (Fin (N + 1) → ℤ) → F.Obj) (encDist : (Fin N → ℤ) → F.Obj)
    (cumObj : F.Obj → F.Obj) (ccum : ℕ)
    (hcumObj : ∀ δ, cumObj (encDist δ) = encRec (cumulate N δ))
    (hcond : ConditionalMapBound F cumObj ccum) (hdesc : DescriptionMapBound F cumObj ccum)
    (ctx : F.Obj) :
    (F.cond (encRec (nullRecord d N)) ctx : Int)
        ≤ (F.cond (encDist (fun (t : Fin N) => d t)) ctx : Int) + ccum ∧
    (F.K (encRec (nullRecord d N)) : Int)
        ≤ (F.K (encDist (fun (t : Fin N) => d t)) : Int) + ccum := by
  have h1 := hcond (encDist (fun (t : Fin N) => d t)) ctx
  have h2 := hdesc (encDist (fun (t : Fin N) => d t))
  rw [hcumObj, cumulate_disturbance_eq_null] at h1 h2
  constructor <;> omega

end Finite

/-! ## The reactive case: two-sided bounds

`dObj` encodes the disturbance, `ynull` the null record, `yR` the (zero) regulated record,
`R` the fixed short controller. The fixed-map costs `ccum`, `cdiff`, `czero`, `cR` are the
example's `O(1)` constants. `slack` is the frame's uniform tolerance: read as the general
`O(log N)` allowance, these theorems give `L = K(d | C, N) + O(log N)` and `I = O(log N)`;
the paper's stronger `O(1)` reading holds for the fixed reactive controller with exact records
and `N` supplied, because every instance consumed here (the cumulative and first-difference
programs, regenerating the zero output and the fixed controller, ignoring or projecting a
fixed pair) has uniform constant cost. That reading is a choice of constant bounds for these
particular instances, or the direct program argument at paper level; a frame allowance that
also covers unrelated logarithmic chain estimates is not thereby constant. -/

/-- **Residual versus disturbance complexity, both directions:**
`K d − (cdiff + czero + cR + 2s) ≤ L ≤ K d + ccum + s`. Upper: the null record is the
cumulative map of `d` (`hup`, from `hcum_from_cumulative`) and the context can be ignored
(`hign`, `CondMono`). Lower: `d` is the first difference of the null record (`hrec`),
subadditivity through the pair `⟨yR, R⟩` (`hsub`), pair subadditivity (`hpair`), a fixed
zero record (`hzero`) and a short controller (`hR`). -/
theorem reactive_residual_two_sided (ynull yR dObj R : F.Obj) (ccum cdiff czero cR : ℕ)
    (hup : (F.cond ynull (F.pair yR R) : Int) ≤ (F.cond dObj (F.pair yR R) : Int) + ccum)
    (hign : CondMono F dObj (F.pair yR R))
    (hrec : (F.K dObj : Int) ≤ (F.K ynull : Int) + cdiff)
    (hsub : Subadd F ynull (F.pair yR R))
    (hpair : (F.K (F.pair yR R) : Int) ≤ (F.K yR : Int) + (F.K R : Int) + (F.slack : Int))
    (hzero : (F.K yR : Int) ≤ czero) (hR : (F.K R : Int) ≤ cR) :
    (F.K dObj : Int) - ((cdiff : Int) + czero + cR + 2 * (F.slack : Int))
        ≤ residual F yR ynull R ∧
    residual F yR ynull R ≤ (F.K dObj : Int) + ccum + (F.slack : Int) := by
  simp only [CondMono, Subadd, GroundedRegulation.residual] at *
  constructor <;> omega

/-- **Gap versus disturbance complexity, both directions:**
`K d − (cdiff + czero) ≤ Δ ≤ K d + ccum`. -/
theorem reactive_gap_two_sided (ynull yR dObj : F.Obj) (ccum cdiff czero : ℕ)
    (hcum : (F.K ynull : Int) ≤ (F.K dObj : Int) + ccum)
    (hrec : (F.K dObj : Int) ≤ (F.K ynull : Int) + cdiff)
    (hzero : (F.K yR : Int) ≤ czero) :
    (F.K dObj : Int) - ((cdiff : Int) + czero) ≤ gap F yR ynull ∧
    gap F yR ynull ≤ (F.K dObj : Int) + ccum := by
  simp only [gap]
  constructor <;> omega

/-- **Initial shared information of a short controller is bounded on both sides:**
`−s ≤ I ≤ cR + s`, from the ceiling and the nonnegativity of mutual information up to
`slack` (`hnonneg`, a named fact). -/
theorem reactive_initial_information_bounded (W R : F.Obj) (cR : ℕ)
    (hceil : IKCeiling F W R) (hR : (F.K R : Int) ≤ cR)
    (hnonneg : IK F W R ≥ -(F.slack : Int)) :
    -(F.slack : Int) ≤ IK F W R ∧ IK F W R ≤ (cR : Int) + (F.slack : Int) := by
  simp only [IKCeiling] at hceil
  constructor <;> omega

end ActionLog
end KTAIT
