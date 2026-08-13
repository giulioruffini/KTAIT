/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic
import KTAIT.GroundedRegulation

/-!
# KTAIT.Localization — localization coordinates and the recoverable-description
overlap (WP0218, Levels 1 and 3)

WP0218 (*What Flows When Information Is Conserved?*) rewrites the standard pair
complexity profile `(K A, K W, K(A,W))` in localization coordinates
`Λ = (L_A, I_K, L_W)` with `L_A = K(A,W) − K W`, `L_W = K(A,W) − K A`, and asks
how they redistribute under fixed reversible dynamics. This module checks:

* **Level 1 — exact algebra** on abstract `Int` coordinates:
  `L_A + I_K + L_W = K(A,W)` (`localization_sum_exact`), the endpoint-difference
  identities (`localization_delta_exact`, `marginal_delta_exact`), and exact
  conservation when the joint budget is fixed (`localization_conserved_exact`).
  These are notation checks: the coordinates are an invertible reparameterization
  of the standard profile, not a new invariant.

* **Reversible invariance wrapper** (WP0218 Lemma, standard): if two objects
  reconstruct one another within `ε` conditional bits and plain subadditivity
  holds both ways, their complexities agree up to `ε + slack`
  (`reversible_complexity_invariance`), and hence the localization-coordinate
  sum of a partitioned pair changes by at most `ε + slack` under the specified
  reversible evolution (`localization_balance_reversible`) — WP0218's
  Algorithmic Localization Balance, reversible specialization.

* **Level 3 — recoverable-description overlap** (WP0218): a description
  `D` cheaply recoverable from both `X` and `Y` is paid for by their mutual
  algorithmic information,
  `I_K(X:Y) ≥ K D − K(D|X) − K(D|Y) − O(slack)`
  (`recoverable_description_overlap`), and its temporal instantiation
  (`recurrent_recoverability_implies_mai_bound`,
  `recurrent_recoverability_persistence_bound`): recurrent `ε`-recoverability of
  a named identity description `D_P` from the pattern descriptions at two times
  lower-bounds their cross-time MAI and normalized persistence.

**Semantic boundary (WP0218 §7, audit items 4–5).** Nothing here says generic
`I_K` is an extractable common string — the overlap lemma is one-directional,
and its converse is false in general (nonmaterializable mutual information).
Nothing here identifies recurrent recoverability with persistence — the
persistence statements are lower bounds only; `D_P` is just a finite string
satisfying recoverability hypotheses, with all identity semantics left in the
manuscript.

The AIT inputs are the existing frame hypotheses (`MutualChain`, `Subadd`) plus
one further standard fact stated in the same idiom: `CondDataProcessing`,
`I_K(D:Y) ≤ I_K(X:Y) + K(D|X) + slack` (describe `D` from `X`, then process).
As throughout KTAIT these are named hypotheses about a frame, never global
axioms.

The overlap lemma is the plain-conditioned sibling of WP0215's
`IS.common_semantics_bound` (there: recoverability conditioned on shortest
programs `p*, q*` via `condStar` and `DataProcessingIK`; here: plain `cond`,
matching WP0218's recoverability tests `K(D_P | S_t^α, C) ≤ ε`). The two are
kept separate because they consume different named hypotheses; neither derives
the other without a cond-vs-condStar bridge fact.
-/

namespace KTAIT
namespace Localization

open RegulationBalance GroundedRegulation

/-! ## Level 1: exact localization algebra on abstract coordinates -/

/-- `A`-specific description requirement `L_A := K(A,W) − K W`. -/
def localization_left (KW KAW : Int) : Int := KAW - KW

/-- Cross-partition dependence coordinate `I_K := K A + K W − K(A,W)`. -/
def localization_mutual (KA KW KAW : Int) : Int := KA + KW - KAW

/-- `W`-specific description requirement `L_W := K(A,W) − K A`. -/
def localization_right (KA KAW : Int) : Int := KAW - KA

/-- **Exact sum identity**: `L_A + I_K + L_W = K(A,W)`. -/
theorem localization_sum_exact (KA KW KAW : Int) :
    localization_left KW KAW + localization_mutual KA KW KAW
      + localization_right KA KAW = KAW := by
  simp only [localization_left, localization_mutual, localization_right]
  omega

/-- **Exact difference identity**: between two endpoints, the change of the
    localization-coordinate sum is the change of the joint budget. -/
theorem localization_delta_exact (KA0 KW0 KAW0 KA1 KW1 KAW1 : Int) :
    (localization_left KW1 KAW1 + localization_mutual KA1 KW1 KAW1
        + localization_right KA1 KAW1)
      - (localization_left KW0 KAW0 + localization_mutual KA0 KW0 KAW0
        + localization_right KA0 KAW0)
      = KAW1 - KAW0 := by
  simp only [localization_left, localization_mutual, localization_right]
  omega

/-- **Marginal form of the difference identity**:
    `ΔK_A + ΔK_W − ΔI_K = ΔK(A,W)` — WP0218's Eq. (marginal-balance) written
    exactly, the two-system change decomposition of Ebtekar–Hutter. -/
theorem marginal_delta_exact (KA0 KW0 KAW0 KA1 KW1 KAW1 : Int) :
    (KA1 - KA0) + (KW1 - KW0)
      - (localization_mutual KA1 KW1 KAW1 - localization_mutual KA0 KW0 KAW0)
      = KAW1 - KAW0 := by
  simp only [localization_mutual]
  omega

/-- **Exact conservation**: if the joint budget is unchanged, the
    localization-coordinate sum is conserved exactly. -/
theorem localization_conserved_exact (KA0 KW0 KAW0 KA1 KW1 KAW1 : Int)
    (h : KAW1 = KAW0) :
    localization_left KW1 KAW1 + localization_mutual KA1 KW1 KAW1
        + localization_right KA1 KAW1
      = localization_left KW0 KAW0 + localization_mutual KA0 KW0 KAW0
        + localization_right KA0 KAW0 := by
  simp only [localization_left, localization_mutual, localization_right]
  omega

variable (F : AITFrame)

/-- The abstract mutual coordinate instantiated at frame complexities is
    definitionally the frame's `I_K`. -/
theorem localization_mutual_eq_IK (A W : F.Obj) :
    localization_mutual (F.K A : Int) (F.K W : Int) (F.K (F.pair A W) : Int)
      = IK F A W := rfl

/-! ## The reversible invariance wrapper -/

/-- **Reversible complexity invariance** (standard; the WP0218 invariance lemma). If `x` and
    `y` reconstruct one another within `ε` conditional bits — as when
    `y = F^T x` for a specified computable reversible `F, T` in the context —
    then `|K y − K x| ≤ ε + slack`. The wrapper is exactly plain subadditivity
    applied in both directions. -/
theorem reversible_complexity_invariance (x y : F.Obj) (eps : Int)
    (hfwd : (F.cond y x : Int) ≤ eps) (hbwd : (F.cond x y : Int) ≤ eps)
    (hyx : Subadd F y x) (hxy : Subadd F x y) :
    |(F.K y : Int) - (F.K x : Int)| ≤ eps + (F.slack : Int) := by
  simp only [Subadd] at hyx hxy
  rw [abs_le]
  omega

/-- **Algorithmic Localization Balance, reversible specialization** (WP0218). For a fixed partition of endpoint states that reconstruct one
    another within `ε` conditional bits, the localization-coordinate sum
    changes by at most `ε + slack`: marginal coordinates may redistribute, but
    only against the joint budget's `O(1)` drift. -/
theorem localization_balance_reversible (A0 W0 A1 W1 : F.Obj) (eps : Int)
    (hfwd : (F.cond (F.pair A1 W1) (F.pair A0 W0) : Int) ≤ eps)
    (hbwd : (F.cond (F.pair A0 W0) (F.pair A1 W1) : Int) ≤ eps)
    (h10 : Subadd F (F.pair A1 W1) (F.pair A0 W0))
    (h01 : Subadd F (F.pair A0 W0) (F.pair A1 W1)) :
    |(localization_left (F.K W1) (F.K (F.pair A1 W1))
        + localization_mutual (F.K A1) (F.K W1) (F.K (F.pair A1 W1))
        + localization_right (F.K A1) (F.K (F.pair A1 W1)))
      - (localization_left (F.K W0) (F.K (F.pair A0 W0))
        + localization_mutual (F.K A0) (F.K W0) (F.K (F.pair A0 W0))
        + localization_right (F.K A0) (F.K (F.pair A0 W0)))|
      ≤ eps + (F.slack : Int) := by
  have h := reversible_complexity_invariance F (F.pair A0 W0) (F.pair A1 W1)
    eps hfwd hbwd h10 h01
  rw [localization_sum_exact, localization_sum_exact]
  exact h

/-! ## Level 3: the recoverable-description overlap and persistence -/

/-- **Conditional data processing**: `I_K(D:Y) ≤ I_K(X:Y) + K(D|X) + slack` —
    reconstruct `D` from `X` at cost `K(D|X)`, then any information `D` shares
    with `Y` was already available through `X`. Standard; named hypothesis
    (new to KTAIT with this module; flagged in WP0218's Lean appendix). -/
def CondDataProcessing (D X Y : F.Obj) : Prop :=
  IK F D Y ≤ IK F X Y + (F.cond D X : Int) + (F.slack : Int)

/-- **Recoverable-description overlap** (WP0218). Any description
    cheaply recoverable from both sides is paid for by their mutual algorithmic
    information: `I_K(X:Y) ≥ K D − K(D|X) − K(D|Y) − 2·slack`. One direction
    only — generic MAI need not be materializable as a common string, and no
    converse is stated. -/
theorem recoverable_description_overlap (D X Y : F.Obj)
    (hmut : MutualChain F D Y)
    (hdp : CondDataProcessing F D X Y) :
    IK F X Y ≥ (F.K D : Int) - (F.cond D X : Int) - (F.cond D Y : Int)
      - 2 * (F.slack : Int) := by
  simp only [MutualChain] at hmut
  simp only [CondDataProcessing] at hdp
  omega

/-- **Recurrent recoverability lower-bounds cross-time MAI** (WP0218).
    If a named description `D` is `ε`-recoverable from the pattern description
    at both times, then
    `I_K(S_t : S_{t+τ}) ≥ K D − ε_t − ε_{t+τ} − 2·slack`. A sufficient
    mechanism for persistence, not a definition of it: the converse is
    deliberately not stated. -/
theorem recurrent_recoverability_implies_mai_bound (D St Stau : F.Obj)
    (epst epstau : Int)
    (hmut : MutualChain F D Stau)
    (hdp : CondDataProcessing F D St Stau)
    (ht : (F.cond D St : Int) ≤ epst)
    (htau : (F.cond D Stau : Int) ≤ epstau) :
    IK F St Stau ≥ (F.K D : Int) - epst - epstau - 2 * (F.slack : Int) := by
  have h := recoverable_description_overlap F D St Stau hmut hdp
  omega

/-- **Normalized persistence bound**: dividing the MAI bound by the larger
    endpoint complexity bounds the WP0216 persistence score
    `Pers = NMAI`. Pure arithmetic on top of the MAI bound. -/
theorem recurrent_recoverability_persistence_bound (D St Stau : F.Obj)
    (epst epstau : Int)
    (hmut : MutualChain F D Stau)
    (hdp : CondDataProcessing F D St Stau)
    (ht : (F.cond D St : Int) ≤ epst)
    (htau : (F.cond D Stau : Int) ≤ epstau) :
    (((F.K D : Int) - epst - epstau - 2 * (F.slack : Int) : Int) : Rat)
        / (max (F.K St) (F.K Stau) : Rat)
      ≤ NMAI F St Stau := by
  have h := recurrent_recoverability_implies_mai_bound F D St Stau epst epstau
    hmut hdp ht htau
  unfold NMAI
  gcongr

end Localization
end KTAIT
