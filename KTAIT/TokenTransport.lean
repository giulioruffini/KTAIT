/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/

/-!
# KTAIT.TokenTransport — canonical reversible localization transport (WP0218, Level 2)

WP0218 (*What Flows When Information Is Conserved?*) studies how the binary
localization profile `(L_A, I_K, L_W)` of a partitioned reversible system can
redistribute while the joint budget stays fixed. This module machine-checks the
paper's finite combinatorial layer — the **canonical independent-token
transport calculus** — with no Kolmogorov complexity in sight:

* the three canonical modes `A(x) = (x,0)`, `AB(x) = (x,x)`, `W(x) = (0,x)` of a
  named content string on a paired register (`Mode`, `canonical`);
* the reversible gates `CNOT_{A→W}`, `CNOT_{W→A}`, `SWAP` are involutions, and a
  single gate from that vocabulary converts any mode into any other
  (`canonical_mode_reachable`);
* any pair of equal-total profiles admits a 3×3 transport plan — a matrix with
  the source profile as row sums and the target as column sums
  (`transport_plan_exists`, northwest-corner construction);
* a transport plan is realized entrywise by disjoint token-pair gates, and the
  realizing map is an involution (`transport_plan_realizable`,
  `applyGates_involutive`);
* the minimum token mass that must change mode between two equal-total profiles
  is `N − Σᵢ min(pᵢ, p'ᵢ) = ½‖p − p'‖₁` (`diag_le_min`,
  `exists_min_moved_plan`, `minimum_moved_mass` — the ℓ₁ form is stated as the
  doubled `Nat` identity to avoid parity bookkeeping).

**Scope guard (WP0218 §5).** This is a theorem about the canonical
independent-token sector: plan-adapted representatives built from disjoint
incompressible blocks. Nothing here says an arbitrary pair of strings with a
given complexity profile factors into such tokens — that claim is false in
general (nonmaterializable mutual information), and no declaration below
states it. The bridge from token lengths to Kolmogorov profile coordinates is
manuscript-level (`O(log N)`) and deliberately not formalized.

Everything in this module is elementary finite combinatorics over `Nat` and
`BitVec`; no `AITFrame`, no Mathlib.
-/

namespace KTAIT
namespace TokenTransport

/-- The three canonical localization modes of a named content string on a
    paired register: `A`-only, materialized on both sides, `W`-only. -/
inductive Mode
  | a
  | ab
  | w
deriving DecidableEq, Repr

/-- A localization profile: total token length in each mode. -/
def LocalizationProfile := Mode → Nat

/-- Total token budget of a profile. -/
def total (p : LocalizationProfile) : Nat := p .a + p .ab + p .w

/-- A transport plan: `t i j` is the token mass assigned to move from mode `i`
    to mode `j`. -/
def LocalizationPlan := Mode → Mode → Nat

/-- Row sum of a plan: mass leaving mode `i`. -/
def rowSum (t : LocalizationPlan) (i : Mode) : Nat := t i .a + t i .ab + t i .w

/-- Column sum of a plan: mass arriving in mode `j`. -/
def colSum (t : LocalizationPlan) (j : Mode) : Nat := t .a j + t .ab j + t .w j

/-- `t` transports profile `p` to profile `p'`: rows sum to the source,
    columns to the target. -/
def IsPlan (t : LocalizationPlan) (p p' : LocalizationProfile) : Prop :=
  (∀ i, rowSum t i = p i) ∧ (∀ j, colSum t j = p' j)

/-! ## Transport plans exist (northwest-corner construction) -/

/-- Cumulative mass of a profile in the fixed order `a < ab < w`. -/
def cum (p : LocalizationProfile) : Mode → Nat
  | .a => p .a
  | .ab => p .a + p .ab
  | .w => p .a + p .ab + p .w

/-- Cumulative mass strictly before a mode. -/
def cumBefore (p : LocalizationProfile) : Mode → Nat
  | .a => 0
  | .ab => p .a
  | .w => p .a + p .ab

/-- The northwest-corner plan: `t i j` is the overlap of the source interval
    `[cumBefore p i, cum p i)` with the target interval
    `[cumBefore p' j, cum p' j)` on the common mass line. -/
def nwPlan (p p' : LocalizationProfile) : LocalizationPlan :=
  fun i j => min (cum p i) (cum p' j) - max (cumBefore p i) (cumBefore p' j)

/-- **Transport plans exist.** Any two profiles with equal total budget are
    connected by a transport plan (the northwest-corner plan). -/
theorem transport_plan_exists (p p' : LocalizationProfile)
    (htot : total p = total p') : IsPlan (nwPlan p p') p p' := by
  simp only [total] at htot
  constructor
  · intro i
    cases i <;>
      simp only [rowSum, nwPlan, cum, cumBefore] <;> omega
  · intro j
    cases j <;>
      simp only [colSum, nwPlan, cum, cumBefore] <;> omega

/-! ## Canonical modes and reversible gates -/

/-- A paired register of `n`-bit words. -/
abbrev PairReg (n : Nat) := BitVec n × BitVec n

/-- Canonical encoding of content `x` in each localization mode. -/
def canonical (m : Mode) (x : BitVec n) : PairReg n :=
  match m with
  | .a => (x, 0#n)
  | .ab => (x, x)
  | .w => (0#n, x)

/-- `CNOT_{A→W}`: XOR the `A` register into the `W` register. -/
def cnotAW (s : PairReg n) : PairReg n := (s.1, s.2 ^^^ s.1)

/-- `CNOT_{W→A}`: XOR the `W` register into the `A` register. -/
def cnotWA (s : PairReg n) : PairReg n := (s.1 ^^^ s.2, s.2)

/-- `SWAP`: exchange the two registers. -/
def swapReg (s : PairReg n) : PairReg n := (s.2, s.1)

/-- `CNOT_{A→W}` is an involution. -/
theorem cnotAW_involutive (s : PairReg n) : cnotAW (cnotAW s) = s := by
  simp [cnotAW, BitVec.xor_assoc]

/-- `CNOT_{W→A}` is an involution. -/
theorem cnotWA_involutive (s : PairReg n) : cnotWA (cnotWA s) = s := by
  simp [cnotWA, BitVec.xor_assoc]

/-- `SWAP` is an involution. -/
theorem swap_involutive (s : PairReg n) : swapReg (swapReg s) = s := rfl

/-- The gate converting canonical mode `i` into canonical mode `j`:
    `CNOT_{A→W}` for `A ↔ AB`, `CNOT_{W→A}` for `W ↔ AB`, `SWAP` for `A ↔ W`,
    identity on the diagonal. -/
def gateFor : Mode → Mode → (PairReg n → PairReg n)
  | .a, .ab | .ab, .a => cnotAW
  | .w, .ab | .ab, .w => cnotWA
  | .a, .w | .w, .a => swapReg
  | _, _ => id

/-- **Canonical mode reachability.** One gate from the vocabulary
    `{CNOT_{A→W}, CNOT_{W→A}, SWAP, id}` converts any canonical mode into any
    other while preserving the named content. -/
theorem canonical_mode_reachable (i j : Mode) (x : BitVec n) :
    gateFor i j (canonical i x) = canonical j x := by
  cases i <;> cases j <;>
    simp [gateFor, canonical, cnotAW, cnotWA, swapReg]

/-- The mode-conversion gates are involutions (the diagonal gate is `id`). -/
theorem gateFor_involutive (i j : Mode) (s : PairReg n) :
    gateFor i j (gateFor i j s) = s := by
  cases i <;> cases j <;>
    simp [gateFor, cnotAW_involutive, cnotWA_involutive, swap_involutive]

/-! ## Realizing a transport plan by disjoint token-pair gates -/

/-- A plan-adapted register configuration: one paired register per plan entry,
    of exactly the entry's length. -/
def Config (t : LocalizationPlan) := (i j : Mode) → PairReg (t i j)

/-- Source configuration for content assignment `x`: the `(i,j)` block sits in
    mode `i`. -/
def sourceConfig (t : LocalizationPlan) (x : (i j : Mode) → BitVec (t i j)) :
    Config t := fun i j => canonical i (x i j)

/-- Target configuration: the `(i,j)` block sits in mode `j`. -/
def targetConfig (t : LocalizationPlan) (x : (i j : Mode) → BitVec (t i j)) :
    Config t := fun i j => canonical j (x i j)

/-- Apply the mode-conversion gate on every (disjoint) block register pair. -/
def applyGates (t : LocalizationPlan) (c : Config t) : Config t :=
  fun i j => gateFor i j (c i j)

/-- **Transport plans are realizable.** For any plan and any content
    assignment, the disjoint family of token-pair gates converts the source
    configuration into the target configuration, realizing every prescribed
    mode-to-mode entry. -/
theorem transport_plan_realizable (t : LocalizationPlan)
    (x : (i j : Mode) → BitVec (t i j)) :
    applyGates t (sourceConfig t x) = targetConfig t x := by
  funext i j
  exact canonical_mode_reachable i j (x i j)

/-- The realizing circuit is an involution, hence a bijection: the transport is
    reversible. -/
theorem applyGates_involutive (t : LocalizationPlan) (c : Config t) :
    applyGates t (applyGates t c) = c := by
  funext i j
  exact gateFor_involutive i j (c i j)

/-! ## Minimum moved token mass -/

/-- Diagonal mass of a plan: token length whose localization mode does not
    change. -/
def diag (t : LocalizationPlan) : Nat := t .a .a + t .ab .ab + t .w .w

/-- Token mass moved by a plan: everything off the diagonal. -/
def moved (t : LocalizationPlan) (p : LocalizationProfile) : Nat :=
  total p - diag t

/-- The stayed mass in each mode is capped by both endpoint profiles:
    `diag t ≤ Σᵢ min(pᵢ, p'ᵢ)`. -/
theorem diag_le_min (t : LocalizationPlan) (p p' : LocalizationProfile)
    (h : IsPlan t p p') :
    diag t ≤ min (p .a) (p' .a) + min (p .ab) (p' .ab) + min (p .w) (p' .w) := by
  obtain ⟨hrow, hcol⟩ := h
  have hra := hrow .a; have hrab := hrow .ab; have hrw := hrow .w
  have hca := hcol .a; have hcab := hcol .ab; have hcw := hcol .w
  simp only [rowSum, colSum] at *
  simp only [diag]
  omega

/-- **A minimum-turnover plan exists**: diagonal-first (keep `min(pᵢ, p'ᵢ)` in
    place), then transport the residuals by a northwest-corner plan. The
    residual profiles have disjoint supports, so the residual plan puts nothing
    on the diagonal. -/
theorem exists_min_moved_plan (p p' : LocalizationProfile)
    (htot : total p = total p') :
    ∃ t, IsPlan t p p' ∧
      diag t = min (p .a) (p' .a) + min (p .ab) (p' .ab) + min (p .w) (p' .w) := by
  simp only [total] at htot
  -- diagonal-first: keep min(pᵢ, p'ᵢ) in place, northwest-transport the residuals.
  -- The residual plan is used only through its row/column equations, never unfolded.
  obtain ⟨hrow, hcol⟩ := transport_plan_exists
      (fun k => p k - min (p k) (p' k)) (fun k => p' k - min (p k) (p' k))
      (by simp only [total]; omega)
  have hra := hrow .a; have hrab := hrow .ab; have hrw := hrow .w
  have hca := hcol .a; have hcab := hcol .ab; have hcw := hcol .w
  simp only [rowSum, colSum] at hra hrab hrw hca hcab hcw
  refine ⟨fun i j => (if i = j then min (p i) (p' i) else 0)
      + nwPlan (fun k => p k - min (p k) (p' k))
          (fun k => p' k - min (p k) (p' k)) i j, ⟨?_, ?_⟩, ?_⟩
  · intro i
    cases i <;> (simp only [rowSum]; simp; omega)
  · intro j
    cases j <;> (simp only [colSum]; simp; omega)
  · -- residual supports are disjoint, so the residual diagonal vanishes
    simp only [diag]; simp; omega

/-- Truncation-free absolute difference on `Nat`. -/
def natAbsDiff (a b : Nat) : Nat := (a - b) + (b - a)

/-- **Minimum moved token mass** (doubled `Nat` form of the `½‖p − p'‖₁`
    identity): for equal-total profiles,
    `2 (N − Σᵢ min(pᵢ, p'ᵢ)) = Σᵢ |pᵢ − p'ᵢ|`. Together with `diag_le_min` and
    `exists_min_moved_plan`, the least mass any transport plan must move is
    exactly `½‖p − p'‖₁`. -/
theorem minimum_moved_mass (p p' : LocalizationProfile)
    (htot : total p = total p') :
    2 * (total p - (min (p .a) (p' .a) + min (p .ab) (p' .ab)
        + min (p .w) (p' .w)))
      = natAbsDiff (p .a) (p' .a) + natAbsDiff (p .ab) (p' .ab)
        + natAbsDiff (p .w) (p' .w) := by
  simp only [total, natAbsDiff] at *
  omega

end TokenTransport
end KTAIT
