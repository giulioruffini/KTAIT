/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Codex)
-/
import KTAIT.CompletionLedger

/-!
# ModelAccounting: acquired models, residuals, and completion capacity (WP0218)

A model acquired during an episode is a later record. Its conditional description,
its finite parameters, and a lossless residual all count. These results check the
AIT implications from named coding and reconstruction hypotheses. They do not
assert that learning finds a short model, that prediction bounds a residual, or
that an admissible physical complementary record exists.

The finite example records a repeated parameter block and one innovation bit per
block. The list proofs check recovery and length, independently of the AIT frame.
Incompressibility of the innovation string remains a stated hypothesis.
-/

namespace KTAIT.ModelAccounting

open RegulationBalance PersistenceFlow CompletionLedger

variable (F : AITFrame)

/-- Fixed mutually reconstructible recodings preserve conditional complexity within
    the larger reconstruction allowance plus one subadditivity slack. -/
theorem lossless_recode_complexity (D Z B : F.Obj) (eps : Int)
    (hDZ : CondSubadd F D Z B) (hZD : CondSubadd F Z D B)
    (henc : (F.cond Z (F.pair D B) : Int) ≤ eps)
    (hdec : (F.cond D (F.pair Z B) : Int) ≤ eps) :
    |(F.cond Z B : Int) - (F.cond D B : Int)| ≤ eps + (F.slack : Int) := by
  simp only [CondSubadd] at hDZ hZD
  rw [abs_le]
  omega

/-- Describe the acquired model, its parameters, then its residual. Three named
    subadditivity estimates and the decoder allowance bound the target cost. -/
theorem model_parameter_residual_bound (D M param residual B : F.Obj) (delta : Int)
    (hM : CondSubadd F M D B)
    (hp : CondSubadd F param D (F.pair M B))
    (hr : CondSubadd F residual D (F.pair param (F.pair M B)))
    (hdec : (F.cond D (F.pair residual (F.pair param (F.pair M B))) : Int) ≤ delta) :
    (F.cond D B : Int) ≤ (F.cond M B : Int)
      + (F.cond param (F.pair M B) : Int)
      + (F.cond residual (F.pair param (F.pair M B)) : Int)
      + delta + 3 * (F.slack : Int) := by
  simp only [CondSubadd] at hM hp hr
  omega

/-- If the record recovers parameter and innovations, conditional incompressibility
    of the innovations lower-bounds the record cost in addition to parameter cost. -/
theorem innovation_lower_bound (D param innovations B : F.Obj)
    (n deficiency eps : Int)
    (hsplit : CondChainLower F innovations param B)
    (hsub : CondSubadd F D (F.pair innovations param) B)
    (hrec : (F.cond (F.pair innovations param) (F.pair D B) : Int) ≤ eps)
    (hnew : n - deficiency ≤ (F.cond innovations (F.pair param B) : Int)) :
    (F.cond param B : Int) + n - deficiency - eps - 2 * (F.slack : Int)
      ≤ (F.cond D B : Int) := by
  simp only [CondChainLower] at hsplit
  simp only [CondSubadd] at hsub
  omega

/-- An internal record with only `extra` description bits beyond the parameter cost
    leaves the innovation excess to its complement, under grouped reconstruction.
    Four slacks count two uses in the novelty lower bound and two in the completion bound. -/
theorem innovations_force_complement (D param innovations B S E : F.Obj)
    (n deficiency eps extra : Int) (delta : Nat)
    (hsplit : CondChainLower F innovations param B)
    (hsubPair : CondSubadd F D (F.pair innovations param) B)
    (hrecPair : (F.cond (F.pair innovations param) (F.pair D B) : Int) ≤ eps)
    (hnew : n - deficiency ≤ (F.cond innovations (F.pair param B) : Int))
    (hsub : CondSubadd F S D B)
    (hchain : CondChain F D E (F.pair S B))
    (hrec : ReconstructionBound F D E (F.pair S B) delta)
    (hb : (F.cond S B : Int) ≤ (F.cond param B : Int) + extra) :
    n - deficiency - extra - eps - (delta : Int) - 4 * (F.slack : Int)
      ≤ cIK F D E (F.pair S B) := by
  have hlo := innovation_lower_bound F D param innovations B n deficiency eps
    hsplit hsubPair hrecPair hnew
  have hcomp := grouped_completion_balance F D B S E delta hsub hchain hrec
  omega

/-- Without a complementary record, the extra internal description and reconstruction
    advice must cover the innovations, up to the declared deficiencies and coding costs. -/
theorem innovations_limit_internal_retention (D param innovations B S : F.Obj)
    (n deficiency eps extra delta : Int)
    (hsplit : CondChainLower F innovations param B)
    (hsubPair : CondSubadd F D (F.pair innovations param) B)
    (hrecPair : (F.cond (F.pair innovations param) (F.pair D B) : Int) ≤ eps)
    (hnew : n - deficiency ≤ (F.cond innovations (F.pair param B) : Int))
    (hsub : CondSubadd F S D B)
    (hrec : (F.cond D (F.pair S B) : Int) ≤ delta)
    (hb : (F.cond S B : Int) ≤ (F.cond param B : Int) + extra) :
    n ≤ extra + delta + deficiency + eps + 3 * (F.slack : Int) := by
  have hlo := innovation_lower_bound F D param innovations B n deficiency eps
    hsplit hsubPair hrecPair hnew
  have hcap := grouped_internal_capacity F D B S delta
    ((F.cond param B : Int) + extra) hsub hrec hb
  omega

/-! ## Finite repeated-block example -/

/-- Record blocks before the fixed serialization to a bit string. -/
def blockRecord (param innovations : List Bool) : List (List Bool × Bool) :=
  innovations.map fun bit => (param, bit)

/-- The separate final bit of each block is its innovation. -/
def blockResidual (record : List (List Bool × Bool)) : List Bool :=
  record.map Prod.snd

/-- At a positive horizon the first block identifies the learned parameter. -/
def blockParameter (record : List (List Bool × Bool)) : Option (List Bool) :=
  record.head?.map Prod.fst

theorem block_residual_recovery (param innovations : List Bool) :
    blockResidual (blockRecord param innovations) = innovations := by
  simp [blockResidual, blockRecord, List.map_map]

theorem block_parameter_recovery (param innovations : List Bool)
    (hne : innovations ≠ []) :
    blockParameter (blockRecord param innovations) = some param := by
  cases innovations with
  | nil => exact False.elim (hne rfl)
  | cons bit rest => rfl

/-- Recovery of the residual reconstitutes the selected record with its model parameter. -/
theorem block_record_recovery (param innovations : List Bool) :
    blockRecord param (blockResidual (blockRecord param innovations))
      = blockRecord param innovations := by
  rw [block_residual_recovery]

/-- The raw stream repeats `param` before each innovation bit. -/
def blockStream (param : List Bool) : List Bool → List Bool
  | [] => []
  | bit :: rest => param ++ [bit] ++ blockStream param rest

theorem block_stream_length (param innovations : List Bool) :
    (blockStream param innovations).length = innovations.length * (param.length + 1) := by
  induction innovations with
  | nil => simp [blockStream]
  | cons bit rest ih => simp [blockStream, ih, Nat.add_mul]; omega

end KTAIT.ModelAccounting
