/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib

/-!
# KTAIT.Decoder — WP0058 Proposition 1: no universal decoder

WP0058 (*Inheritance Architecture*) recasts the Darwinian/Lamarckian distinction as a
question about a **write-back channel**: whether acquired structure can be compiled back
into the transmissible program. Such a channel is an *inverse compiler* `C` for the
**developmental map** `D`, which carries a heritable program to the acquired state it
generates.

Proposition 1 of that paper asserts that no *total* computable such `C` exists, so every
realized write-back channel is a partial map whose **validity domain is fixed in advance**
rather than computed — which is what charges the domain to the heritable program, and
what makes Lamarckian channels narrow and parasitic on prior Darwinian search
(Corollary 1 there).

The mathematical content is captured here by `achievable_computable_of_inverse`: a total
computable inverse that also **recognizes its own domain** (returning `none` exactly off
the achievable set) would decide membership in that set. Since the achievable set of a
computable `D` is in general recursively enumerable but *not* decidable, no such `C` can
exist (`no_universal_decoder`).

Note the epistemic status. Unlike most modules here, the core theorem needs **no assumed
AIT fact at all** — it is unconditional. Only the *non-vacuity* of the hypothesis (that
some computable `D` really has an undecidable achievable set) is taken as a standard
computability fact, in the named-`Prop` style of the project methodology
(`ExistsUndecidableAchievableSet`); it is the usual consequence of the halting problem.

The complementary claim of WP0058 Proposition 1 — that `K(C_𝒟) ≤ K(H) + O(1)`, i.e. the
decoder is charged to the heritable program — is an AIT statement rather than a
computability one, and is not formalized here.

## Main results

* `achievable_computable_of_inverse` — a total, domain-recognizing inverse decides achievability.
* `no_universal_decoder` — hence none exists when achievability is undecidable.
* `exists_map_without_decoder` — some computable developmental map admits no such inverse.
* `inverts_id` — satisfiability witness: the statement is not vacuous.
-/

namespace KTAIT
namespace Decoder

variable {D : ℕ → ℕ}

/-- The **achievable set** of a developmental map `D`: the acquired states that some
heritable program actually generates. Recursively enumerable when `D` is computable, but
in general not decidable. -/
def Achievable (D : ℕ → ℕ) : Set ℕ := Set.range D

/-- `C` is a **domain-recognizing inverse compiler** for the developmental map `D`.

`C a = some H` is a write-back: it claims `H` is a program generating the acquired state
`a`, and `sound` demands the claim be true. `C a = none` is a refusal, and `recognizes`
demands that `C` refuse only on genuinely unachievable states — that is, `C` knows its own
validity domain rather than having it stipulated. -/
structure Inverts (D : ℕ → ℕ) (C : ℕ → Option ℕ) : Prop where
  /-- Whatever `C` returns really does generate the target state. -/
  sound : ∀ a H, C a = some H → D H = a
  /-- `C` refuses only on unachievable states: it recognizes its own domain. -/
  recognizes : ∀ a, C a = none → a ∉ Achievable D

/-- A domain-recognizing inverse succeeds exactly on the achievable set. -/
theorem mem_achievable_iff_isSome {C : ℕ → Option ℕ} (hinv : Inverts D C) (a : ℕ) :
    a ∈ Achievable D ↔ (C a).isSome = true := by
  constructor
  · intro ha
    cases h : C a with
    | none => exact absurd ha (hinv.recognizes a h)
    | some H => simp
  · intro h
    obtain ⟨H, hH⟩ := Option.isSome_iff_exists.mp h
    exact ⟨H, hinv.sound a H hH⟩

/-- **The engine of WP0058 Proposition 1.** A *total computable* inverse compiler that
recognizes its own domain would decide membership in the achievable set: run it and test
whether it refused. Unconditional — no AIT fact is assumed. -/
theorem achievable_computable_of_inverse {C : ℕ → Option ℕ}
    (hC : Computable C) (hinv : Inverts D C) :
    ComputablePred (fun a => a ∈ Achievable D) := by
  have hsome : Computable fun a => (C a).isSome := (Primrec.option_isSome.to_comp).comp hC
  have hpred : ComputablePred fun a => (C a).isSome = true :=
    ComputablePred.computable_iff.mpr ⟨_, hsome, rfl⟩
  exact hpred.of_eq fun a => (mem_achievable_iff_isSome hinv a).symm

/-- **WP0058 Proposition 1 (no universal decoder).** If achievability is undecidable, then
no total computable, domain-recognizing inverse compiler exists.

Consequently any physically realized write-back channel is a *partial* map whose validity
domain must be fixed in advance rather than computed — the claim WP0058 uses to charge the
domain to the heritable program. -/
theorem no_universal_decoder (hundec : ¬ ComputablePred fun a => a ∈ Achievable D) :
    ¬ ∃ C : ℕ → Option ℕ, Computable C ∧ Inverts D C := by
  rintro ⟨C, hC, hinv⟩
  exact hundec (achievable_computable_of_inverse hC hinv)

/-- Standard computability fact, assumed as a named `Prop` per the project methodology:
some computable developmental map has an undecidable achievable set. This is the usual
consequence of the unsolvability of the halting problem — an r.e. set that is not
recursive, presented as the range of a computable function. -/
def ExistsUndecidableAchievableSet : Prop :=
  ∃ D : ℕ → ℕ, Computable D ∧ ¬ ComputablePred fun a => a ∈ Achievable D

/-- Some computable developmental map admits no total, domain-recognizing inverse
compiler: Lamarckian write-back is not available in general. -/
theorem exists_map_without_decoder (h : ExistsUndecidableAchievableSet) :
    ∃ D : ℕ → ℕ, Computable D ∧ ¬ ∃ C : ℕ → Option ℕ, Computable C ∧ Inverts D C := by
  obtain ⟨D, hD, hundec⟩ := h
  exact ⟨D, hD, no_universal_decoder hundec⟩

/-- **Satisfiability witness** (the statement is not vacuous). When development is the
identity — the acquired state *is* the program, so there is nothing to invert — the
identity write-back is a domain-recognizing inverse. Every state is achievable, and
`achievable_computable_of_inverse` correctly reports a decidable achievable set. -/
theorem inverts_id : Inverts id (fun a => some a) where
  sound := by
    intro a H h
    simp only [Option.some.injEq] at h
    exact h.symm
  recognizes := by
    intro a h
    simp at h

/-- The witness really does feed the engine: with `D = id` the achievable set is decidable,
as it must be. Guards against `achievable_computable_of_inverse` being vacuously true. -/
theorem toy_achievable_computable :
    ComputablePred (fun a => a ∈ Achievable (id : ℕ → ℕ)) :=
  achievable_computable_of_inverse (Computable.option_some.comp Computable.id) inverts_id

end Decoder
end KTAIT
