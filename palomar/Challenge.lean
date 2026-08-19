/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib

/-!
# KT conservation–localization–persistence spine (Palomar Challenge)

Kolmogorov Theory (KT) measures the persistence of a pattern by the normalized
algorithmic mutual information between its present and future descriptions.
This Challenge states five theorems forming the spine of that account:
conservation of description complexity, its localization across a partition,
and the resulting persistence bounds.

Every algorithmic-information input is a named `Prop` about an abstract frame
(`AITFrame`), carried as an explicit hypothesis by each theorem that uses it —
never as a global axiom. The inputs are standard AIT facts (symmetry of
information, subadditivity, the mutual-information chain rule, conditional
data processing; see Li–Vitányi, *An Introduction to Kolmogorov Complexity*,
and Gács, *Lecture Notes on Descriptional Complexity*). The registered claim
is exactly this: the KT statements follow from the stated assumptions.

The compared theorems:

1. `persistence_conservation` — world-output complexity splits into mutual
   information with the regulator plus a conditional residual, up to slack
   (WP0162 Prop. 2, bounded form).
2. `conservation_tradeoff` — at a fixed exact ledger, maximizing shared
   information is equivalent to minimizing the residual (WP0162).
3. `Localization.localization_balance_reversible` — under reversible endpoint
   reconstruction, the localization-coordinate sum moves by at most
   `ε + slack` (WP0218, Algorithmic Localization Balance, reversible case).
4. `Localization.recurrent_recoverability_persistence_bound` — a description
   recoverable from the pattern at two times lower-bounds its normalized
   cross-time mutual information (WP0218).
5. `meta_persistence` — a collective submodel of stable complexity `k` with
   transient `≤ L` has persistence at least `1 − (L + slack)/k`
   (WP0162 Prop. 1).

Substantive development: https://github.com/giulioruffini/KTAIT — this file is
a thin statement surface; the proofs are in `Solution.lean`.
-/

namespace KTAIT

/-- The abstract algorithmic-information interface: a carrier of descriptions,
Kolmogorov complexity `K`, pairing, conditional complexity `K(x | y)`, the
shortest-program map `y ↦ y*`, and a `slack` standing for the `O(log)`/`O(1)`
correction terms of the classical identities. -/
structure AITFrame where
  /-- The carrier of descriptions (bitstrings, tape configurations, …). -/
  Obj : Type
  /-- Kolmogorov complexity `K(x)`. -/
  K : Obj → Nat
  /-- Pairing `⟨x, y⟩` into a single object. -/
  pair : Obj → Obj → Obj
  /-- Conditional complexity `K(x | y)`. -/
  cond : Obj → Obj → Nat
  /-- Shortest-program form `y ↦ y*` (carries `y` together with `K(y)`). -/
  star : Obj → Obj
  /-- Placeholder for the `O(log)` / `O(1)` correction terms. -/
  slack : Nat

variable (F : AITFrame)

/-- Conditioning on the shortest program `y*`, i.e. `K(x | y*)`. -/
def condStar (x y : F.Obj) : Nat := F.cond x (F.star y)

/-- Mutual algorithmic information `I_K(x : y) = K(x) + K(y) − K(⟨x,y⟩)`,
an `Int` because it can be negative before the `O(log)` correction. -/
def IK (x y : F.Obj) : Int :=
  (F.K x : Int) + (F.K y : Int) - (F.K (F.pair x y) : Int)

/-- Normalized mutual algorithmic information `I_K(x:y) / max (K x) (K y)`,
a `Rat` in `[−1, 1]` (morally); division by `0` yields `0`. -/
def NMAI (x y : F.Obj) : Rat :=
  (IK F x y : Rat) / (max (F.K x) (F.K y) : Rat)

/-- **Symmetry of information** (standard, with `O(log)` slack):
`I_K(x : y) = K(x) − K(x | y*) + O(log)`, encoded as "the two sides differ by
at most `slack`". -/
def SymmetryOfInformation (F : AITFrame) : Prop :=
  ∀ x y : F.Obj,
    (IK F x y - ((F.K x : Int) - (condStar F x y : Int))).natAbs ≤ F.slack

/-- **Plain subadditivity** (standard): `K a ≤ K b + K(a|b) + slack`. -/
def Subadd (a b : F.Obj) : Prop :=
  (F.K a : Int) ≤ (F.K b : Int) + (F.cond a b : Int) + (F.slack : Int)

/-- **Mutual-information chain rule** (standard), in the inequality form
consumed here: `K(y) ≤ I_K(y : R) + K(y | R) + slack`. -/
def MutualChain (y R : F.Obj) : Prop :=
  (F.K y : Int) ≤ IK F y R + (F.cond y R : Int) + (F.slack : Int)

/-- Discrete time indexing pattern trajectories. -/
abbrev Time := Nat

/-- **Persistence**: normalized temporal self-information of a trajectory with
its future self, `Pers S t τ = NMAI(S_t, S_{t+τ})`. -/
def Pers (F : AITFrame) (S : Time → F.Obj) (t τ : Time) : Rat :=
  NMAI F (S t) (S (t + τ))

/-- The conservation ledger, exact form: `K(O_W) = I_K(O_W:R) + K(O_W | R*)`. -/
def ConservationLedger (F : AITFrame) (OW R : F.Obj) : Prop :=
  (F.K OW : Int) = IK F OW R + (condStar F OW R : Int)

namespace Localization

/-- `A`-specific description requirement `L_A := K(A,W) − K W`. -/
def localization_left (KW KAW : Int) : Int := KAW - KW

/-- Cross-partition dependence coordinate `I_K := K A + K W − K(A,W)`. -/
def localization_mutual (KA KW KAW : Int) : Int := KA + KW - KAW

/-- `W`-specific description requirement `L_W := K(A,W) − K A`. -/
def localization_right (KA KAW : Int) : Int := KAW - KA

variable (F : AITFrame)

/-- **Conditional data processing** (standard):
`I_K(D:Y) ≤ I_K(X:Y) + K(D|X) + slack` — reconstruct `D` from `X`, then any
information `D` shares with `Y` was already available through `X`. -/
def CondDataProcessing (D X Y : F.Obj) : Prop :=
  IK F D Y ≤ IK F X Y + (F.cond D X : Int) + (F.slack : Int)

end Localization

/-! ## Compared theorems -/

/-- **Persistence conservation** (WP0162 Prop. 2, bounded form). From the
symmetry of information, world-output complexity is accounted for up to slack:
`|K(O_W) − (I_K(O_W:R) + K(O_W|R*))| ≤ slack`. -/
theorem persistence_conservation (F : AITFrame) (hsym : SymmetryOfInformation F)
    (OW R : F.Obj) :
    ((F.K OW : Int) - (IK F OW R + (condStar F OW R : Int))).natAbs ≤ F.slack := by
  sorry

/-- **Conservation trade-off** (WP0162). At fixed world-output complexity
(exact ledger), maximizing the mutual algorithmic information `I_K(O_W:R)` is
equivalent to minimizing the conditional residual `K(O_W | R*)`. -/
theorem conservation_tradeoff (F : AITFrame) (OW R₁ R₂ : F.Obj)
    (h₁ : ConservationLedger F OW R₁) (h₂ : ConservationLedger F OW R₂) :
    IK F OW R₂ ≤ IK F OW R₁ ↔ (condStar F OW R₁ : Int) ≤ (condStar F OW R₂ : Int) := by
  sorry

/-- **Algorithmic Localization Balance, reversible specialization** (WP0218).
For a fixed partition of endpoint states that reconstruct one another within
`ε` conditional bits, the localization-coordinate sum changes by at most
`ε + slack`: marginal coordinates may redistribute, but only against the joint
budget's drift. -/
theorem Localization.localization_balance_reversible (F : AITFrame)
    (A0 W0 A1 W1 : F.Obj) (eps : Int)
    (hfwd : (F.cond (F.pair A1 W1) (F.pair A0 W0) : Int) ≤ eps)
    (hbwd : (F.cond (F.pair A0 W0) (F.pair A1 W1) : Int) ≤ eps)
    (h10 : Subadd F (F.pair A1 W1) (F.pair A0 W0))
    (h01 : Subadd F (F.pair A0 W0) (F.pair A1 W1)) :
    |(Localization.localization_left (F.K W1) (F.K (F.pair A1 W1))
        + Localization.localization_mutual (F.K A1) (F.K W1) (F.K (F.pair A1 W1))
        + Localization.localization_right (F.K A1) (F.K (F.pair A1 W1)))
      - (Localization.localization_left (F.K W0) (F.K (F.pair A0 W0))
        + Localization.localization_mutual (F.K A0) (F.K W0) (F.K (F.pair A0 W0))
        + Localization.localization_right (F.K A0) (F.K (F.pair A0 W0)))|
      ≤ eps + (F.slack : Int) := by
  sorry

/-- **Recurrent recoverability bounds persistence from below** (WP0218). If a
named description `D` is `ε`-recoverable from the pattern description at both
times, the normalized cross-time mutual information — the persistence score —
is at least `(K D − ε_t − ε_{t+τ} − 2·slack) / max (K S_t) (K S_{t+τ})`.
One direction only: no converse is stated. -/
theorem Localization.recurrent_recoverability_persistence_bound (F : AITFrame)
    (D St Stau : F.Obj) (epst epstau : Int)
    (hmut : MutualChain F D Stau)
    (hdp : Localization.CondDataProcessing F D St Stau)
    (ht : (F.cond D St : Int) ≤ epst)
    (htau : (F.cond D Stau : Int) ≤ epstau) :
    (((F.K D : Int) - epst - epstau - 2 * (F.slack : Int) : Int) : Rat)
        / (max (F.K St) (F.K Stau) : Rat)
      ≤ NMAI F St Stau := by
  sorry

/-- **Meta-persistence** (WP0162 Prop. 1). With the symmetry of information, a
collective submodel `Sc` of stable complexity `k > 0` and bounded transient
`K(Sc_t | (Sc_{t+τ})*) ≤ L` has collective persistence at least
`1 − (L + slack)/k`. No property of the constituents' objectives appears in
the hypotheses. -/
theorem meta_persistence (F : AITFrame) (hsym : SymmetryOfInformation F)
    (Sc : Time → F.Obj) (t τ : Time) (k L : Nat) (hpos : 0 < k)
    (hkt : F.K (Sc t) = k) (hktau : F.K (Sc (t + τ)) = k)
    (hdrift : condStar F (Sc t) (Sc (t + τ)) ≤ L) :
    (1 : Rat) - ((L : Rat) + (F.slack : Rat)) / (k : Rat) ≤ Pers F Sc t τ := by
  sorry

end KTAIT
