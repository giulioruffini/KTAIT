/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic
import KTAIT.RegulationBalance
import KTAIT.PersistenceFlow

/-!
# KTAIT.CompletionLedger — reconstruction and capacity with neutral names (WP0218)

The reconstruction-and-capacity account that WP0216's Algorithmic Persistence Balance
(`PersistenceFlow`) and WP0203's residual identification
(`RegulationBalance.residual_in_completion`) both instantiate, stated once with neutral names
for the WP0218 companion revision (October 2026).

Objects: a target record `D`, an initial context `B`, and completion records. Two forms.

* **Grouped**: one internal record `S` and one complementary record `E`. If `D` is
  reconstructible from `⟨E, ⟨S, B⟩⟩` within `δ` bits, then
  `K(D|B) ≤ K(S|B) + M(D : E | ⟨S,B⟩) + δ + 2·slack` (`grouped_completion_balance`);
  an internal budget `K(S|B) ≤ b` forces `M(D : E | ⟨S,B⟩) ≥ K(D|B) − b − δ − 2·slack`
  (`grouped_bounded_internal_forces_external`), and with no complement
  `K(D|B) ≤ b + δ + slack` (`grouped_internal_capacity`).
* **Ordered**: a list of records supplied in a declared order, each conditioned on the
  context and on the records before it (`ctxAfter`, `orderedInfo`, `orderedCost`). The
  ordered split `OrderedSplit` generalizes `PersistenceFlow.FlowSplit5`; with `k` internal
  records capped by `OrderedCeilings`, the external records carry
  `K(D|B) − (ordered internal cost) − δ − (2 + k)·slack`
  (`ordered_bounded_internal_forces_external`), and with two external records one of
  them carries half of that (`ordered_two_external_pigeonhole`).

The allowances stay distinct: `δ` is the reconstruction allowance; `slack` bounds each named
estimate; `(2 + k)·slack` counts hypothesis uses (chain rule, split, `k` ceilings), not
elementary chain-rule steps, and the split's slack covers the whole ordered split as one
named hypothesis. The five-record APB is the instance `[Z⁺, 𝒲⁺, σ, a, Ξ]` with `k = 3`
(`flowSplit5_iff_orderedSplit`, `apb_flow_from_ordered`), which recovers WP0216's
`δ + 5·slack` exactly. The grouped remainder `2·slack` is not the ordered `(2 + k)·slack`;
the two forms consume different named hypotheses.

## Discipline

Every AIT fact consumed (`CondSubadd`, `CondChain`, `CIKCeiling`, the ordered split) is a
named `Prop` hypothesis about a frame, never an axiom. No temporal conservation or
reversibility premise appears; the account applies to irreversible realizations.
-/

namespace KTAIT
namespace CompletionLedger

open RegulationBalance PersistenceFlow

variable (F : AITFrame)

/-! ## Grouped form: one internal and one complementary record -/

/-- **Grouped completion balance.** With `D` the target, `B` the initial context, `S` the
    later internal record, and `E` the complementary record: conditional subadditivity
    through `S`, the conditional chain rule for `⟨D,E⟩` given `⟨S,B⟩`, and reconstruction
    `K(D | ⟨E,⟨S,B⟩⟩) ≤ δ` give

    `K(D|B) ≤ K(S|B) + M(D : E | ⟨S,B⟩) + δ + 2·slack`. -/
theorem grouped_completion_balance (D B S E : F.Obj) (δ : ℕ)
    (hsub : CondSubadd F S D B)
    (hchain : CondChain F D E (F.pair S B))
    (hrec : ReconstructionBound F D E (F.pair S B) δ) :
    (F.cond D B : Int)
      ≤ (F.cond S B : Int) + cIK F D E (F.pair S B) + (δ : Int) + 2 * (F.slack : Int) := by
  simp only [CondSubadd] at hsub
  simp only [CondChain] at hchain
  simp only [ReconstructionBound] at hrec
  simp only [cIK]
  omega

/-- **Bounded internal update forces external information** (grouped form). An internal
    budget `K(S|B) ≤ b` leaves `M(D : E | ⟨S,B⟩) ≥ K(D|B) − b − δ − 2·slack` to the
    complementary record. -/
theorem grouped_bounded_internal_forces_external (D B S E : F.Obj) (δ : ℕ) (b : Int)
    (hsub : CondSubadd F S D B)
    (hchain : CondChain F D E (F.pair S B))
    (hrec : ReconstructionBound F D E (F.pair S B) δ)
    (hb : (F.cond S B : Int) ≤ b) :
    cIK F D E (F.pair S B) ≥ (F.cond D B : Int) - b - (δ : Int) - 2 * (F.slack : Int) := by
  have h := grouped_completion_balance F D B S E δ hsub hchain hrec
  omega

/-- **Internal capacity** (no complement). If `D` is reconstructible from the internal
    record alone, `K(D | ⟨S,B⟩) ≤ δ`, and `K(S|B) ≤ b`, then `K(D|B) ≤ b + δ + slack`.
    `PersistenceFlow.bounded_self_code_update_capacity` is the case `S = Z₁`, `B = ⟨Z₀,C⟩`. -/
theorem grouped_internal_capacity (D B S : F.Obj) (δ b : Int)
    (hsub : CondSubadd F S D B)
    (hrec : (F.cond D (F.pair S B) : Int) ≤ δ)
    (hb : (F.cond S B : Int) ≤ b) :
    (F.cond D B : Int) ≤ b + δ + (F.slack : Int) := by
  simp only [CondSubadd] at hsub
  omega

/-! ## Ordered form: a list of records in a declared order -/

/-- The context after supplying records in order:
    `ctxAfter B [Q₁, …, Qᵢ] = ⟨Qᵢ, … ⟨Q₁, B⟩⟩`. -/
def ctxAfter (B : F.Obj) : List F.Obj → F.Obj
  | [] => B
  | Q :: Qs => ctxAfter (F.pair Q B) Qs

/-- Ordered conditional-information sum `Σᵢ M(D : Qᵢ | ⟨Q_{i−1}, …, Q₁, B⟩)`. -/
def orderedInfo (D B : F.Obj) : List F.Obj → Int
  | [] => 0
  | Q :: Qs => cIK F D Q B + orderedInfo D (F.pair Q B) Qs

/-- Ordered description cost `Σᵢ K(Qᵢ | ⟨Q_{i−1}, …, Q₁, B⟩)`. -/
def orderedCost (B : F.Obj) : List F.Obj → Int
  | [] => 0
  | Q :: Qs => (F.cond Q B : Int) + orderedCost (F.pair Q B) Qs

/-- Each listed record's channel is capped by its own ordered conditional description:
    `CIKCeiling` along the list. -/
def OrderedCeilings (D B : F.Obj) : List F.Obj → Prop
  | [] => True
  | Q :: Qs => CIKCeiling F D Q B ∧ OrderedCeilings D (F.pair Q B) Qs

/-- **Ordered split** (named hypothesis): the joint channel of the completion object `Q`
    splits along the declared record order within one slack. Generalizes
    `PersistenceFlow.FlowSplit5`; the slack covers the whole split as one named estimate. -/
def OrderedSplit (D Q B : F.Obj) (Qs : List F.Obj) : Prop :=
  cIK F D Q B ≤ orderedInfo F D B Qs + (F.slack : Int)

/-- `orderedInfo` over a concatenation is the sum over the prefix plus the sum over the
    suffix in the context the prefix leaves behind. -/
theorem orderedInfo_append (D B : F.Obj) (Ps Qs : List F.Obj) :
    orderedInfo F D B (Ps ++ Qs)
      = orderedInfo F D B Ps + orderedInfo F D (ctxAfter F B Ps) Qs := by
  induction Ps generalizing B with
  | nil => simp [orderedInfo, ctxAfter]
  | cons P Ps ih => simp [orderedInfo, ctxAfter, ih, add_assoc]

/-- Under ordered ceilings, the ordered information is at most the ordered cost plus one
    slack per record. -/
theorem orderedInfo_le_orderedCost (D B : F.Obj) (Ps : List F.Obj)
    (h : OrderedCeilings F D B Ps) :
    orderedInfo F D B Ps ≤ orderedCost F B Ps + (Ps.length : Int) * (F.slack : Int) := by
  induction Ps generalizing B with
  | nil => simp [orderedInfo, orderedCost]
  | cons P Ps ih =>
    obtain ⟨hP, hPs⟩ := h
    simp only [CIKCeiling] at hP
    have hrest := ih (F.pair P B) hPs
    simp only [orderedInfo, orderedCost, List.length_cons]
    push_cast
    rw [add_mul, one_mul]
    omega

/-- **Ordered completion balance.** Reconstruction of `D` from the completion object `Q`
    given `B` within `δ`, the chain rule, and the ordered split give
    `K(D|B) ≤ orderedInfo + δ + 2·slack`. -/
theorem ordered_completion_balance (D Q B : F.Obj) (Qs : List F.Obj) (δ : ℕ)
    (hchain : CondChain F D Q B)
    (hrec : ReconstructionBound F D Q B δ)
    (hsplit : OrderedSplit F D Q B Qs) :
    (F.cond D B : Int) ≤ orderedInfo F D B Qs + (δ : Int) + 2 * (F.slack : Int) := by
  simp only [CondChain] at hchain
  simp only [ReconstructionBound] at hrec
  simp only [OrderedSplit, cIK] at hsplit
  omega

/-- **Bounded internal updates force external information** (ordered form). With the
    internal records `Ps` capped by their ordered conditional descriptions and the external
    records `Qs` following them,

    `orderedInfo (external) ≥ K(D|B) − orderedCost (internal) − δ − (2 + k)·slack`,
    `k = Ps.length`. -/
theorem ordered_bounded_internal_forces_external (D Q B : F.Obj) (Ps Qs : List F.Obj)
    (δ : ℕ)
    (hchain : CondChain F D Q B)
    (hrec : ReconstructionBound F D Q B δ)
    (hsplit : OrderedSplit F D Q B (Ps ++ Qs))
    (hceil : OrderedCeilings F D B Ps) :
    orderedInfo F D (ctxAfter F B Ps) Qs
      ≥ (F.cond D B : Int) - orderedCost F B Ps - (δ : Int)
        - (2 + (Ps.length : Int)) * (F.slack : Int) := by
  have h1 := ordered_completion_balance F D Q B (Ps ++ Qs) δ hchain hrec hsplit
  rw [orderedInfo_append] at h1
  have h2 := orderedInfo_le_orderedCost F D B Ps hceil
  rw [add_mul]
  omega

/-- **Two external records, pigeonhole.** With internal records `Ps` and external records
    `E₁, E₂`, twice the larger external channel dominates the residual. -/
theorem ordered_two_external_pigeonhole (D Q B : F.Obj) (Ps : List F.Obj) (E₁ E₂ : F.Obj)
    (δ : ℕ)
    (hchain : CondChain F D Q B)
    (hrec : ReconstructionBound F D Q B δ)
    (hsplit : OrderedSplit F D Q B (Ps ++ [E₁, E₂]))
    (hceil : OrderedCeilings F D B Ps) :
    2 * max (cIK F D E₁ (ctxAfter F B Ps)) (cIK F D E₂ (F.pair E₁ (ctxAfter F B Ps)))
      ≥ (F.cond D B : Int) - orderedCost F B Ps - (δ : Int)
        - (2 + (Ps.length : Int)) * (F.slack : Int) := by
  have h := ordered_bounded_internal_forces_external F D Q B Ps [E₁, E₂] δ
    hchain hrec hsplit hceil
  simp only [orderedInfo, add_zero] at h
  rcases le_total (cIK F D E₁ (ctxAfter F B Ps))
      (cIK F D E₂ (F.pair E₁ (ctxAfter F B Ps))) with hle | hle
  · rw [max_eq_right hle]; omega
  · rw [max_eq_left hle]; omega

/-! ## The five-record Algorithmic Persistence Balance is the ordered instance -/

/-- `FlowSplit5` is the ordered split for the record list `[Z⁺, 𝒲⁺, σ, a, Ξ]`. -/
theorem flowSplit5_iff_orderedSplit (iota Ctx Znext Mnext sigma action exhaust : F.Obj) :
    FlowSplit5 F iota Znext Mnext sigma action exhaust Ctx
      ↔ OrderedSplit F iota (flowTuple F Znext Mnext sigma action exhaust) Ctx
          [Znext, Mnext, sigma, action, exhaust] := by
  simp only [FlowSplit5, OrderedSplit, orderedInfo, add_zero]
  constructor <;> intro h <;> omega

/-- The ordered cost of the three internal records is `d_Z + d_M + d_σ`. -/
theorem orderedCost_internal_three (Ctx Znext Mnext sigma : F.Obj) :
    orderedCost F Ctx [Znext, Mnext, sigma]
      = (F.cond Znext Ctx : Int) + (F.cond Mnext (F.pair Znext Ctx) : Int)
        + (F.cond sigma (F.pair Mnext (F.pair Znext Ctx)) : Int) := by
  simp only [orderedCost, add_zero]
  omega

/-- **The five-record APB flow bound is the ordered instance** with `k = 3`: the conclusion of
    `PersistenceFlow.bounded_persistence_forces_flow_with_error`, derived from
    `ordered_bounded_internal_forces_external`, with `(2 + 3)·slack = 5·slack`. -/
theorem apb_flow_from_ordered (iota Ctx Znext Mnext sigma action exhaust : F.Obj) (δ : ℕ)
    (hchain : CondChain F iota (flowTuple F Znext Mnext sigma action exhaust) Ctx)
    (hrec : ReconstructionBound F iota (flowTuple F Znext Mnext sigma action exhaust) Ctx δ)
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
        - (δ : Int) - 5 * (F.slack : Int) := by
  have hsplit' : OrderedSplit F iota (flowTuple F Znext Mnext sigma action exhaust) Ctx
      ([Znext, Mnext, sigma] ++ [action, exhaust]) :=
    (flowSplit5_iff_orderedSplit F iota Ctx Znext Mnext sigma action exhaust).mp hsplit
  have hceil : OrderedCeilings F iota Ctx [Znext, Mnext, sigma] := ⟨hcZ, hcM, hcS, trivial⟩
  have h := ordered_bounded_internal_forces_external F iota
    (flowTuple F Znext Mnext sigma action exhaust) Ctx [Znext, Mnext, sigma] [action, exhaust]
    δ hchain hrec hsplit' hceil
  simp only [orderedInfo, orderedCost, ctxAfter, List.length_cons, List.length_nil,
    add_zero] at h
  push_cast at h
  norm_num at h
  omega

end CompletionLedger
end KTAIT
