/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib

/-!
# KTAIT.Decoder — WP0058 Proposition 1: no uniform domain-recognizing encoder

WP0058 (*Inheritance Architecture*) recasts the Darwinian/Lamarckian distinction as a
question about a **write-back channel**: whether acquired structure can be compiled back
into the transmissible program. Such a channel is a **write-back encoder** `C`, or
credit-assignment operator, which to be adaptive must act — on the changes worth
transmitting — as an approximate inverse of the **developmental map** `D`, the map carrying
a heritable program to the acquired state it generates. Calling `C` an *inverse compiler* is
an analogy and a misleading one: backpropagation computes gradients of a chosen loss, and
distillation fits a student to a teacher's outputs. Neither inverts development.

Proposition 1 of that paper has three parts.

1. If the achievable set of `D` is undecidable, there is no *total* computable `C` returning
   a preimage for every achievable state and a distinguished refusal symbol for every
   unachievable one.
2. Such maps exist.
3. A partial inverse on the achievable set does exist, by dovetailing, but it fails to halt
   off that set and is unbounded in time on it.

Hence every realized channel is a partial map whose validity domain must be **supplied or
learned** rather than recognized by the encoder itself.

Part (i) is captured by `achievable_computable_of_inverse`: a total computable inverse that
also **recognizes its own domain** (returning `none` exactly off the achievable set) would
decide membership in that set. Since the achievable set of a computable `D` is in general
recursively enumerable but *not* decidable, no such `C` can exist (`no_universal_decoder`).
Part (ii) is `exists_map_without_decoder`.

Part (iii) is `partial_inverse_exists`, which is what makes the proposition a statement about
*total, domain-recognizing* inverses rather than about inverses as such — the quantifier the
paper says is load-bearing. What is proved there: the dovetailing search `dovetail D` is
partial recursive, is defined at exactly the achievable states, and returns a genuine
preimage wherever it is defined. Since its domain is exactly the achievable set, it diverges
off that set, which is the second clause of part (iii). What is **not** proved: that the
search is *unbounded in time* on the achievable set. That is a resource statement about the
running time of a machine, and this development has no cost model, so it stays informal.

Note the epistemic status. Unlike most modules here, the core theorem needs **no assumed
AIT fact at all** — it is unconditional. Only the *non-vacuity* of the hypothesis (that
some computable `D` really has an undecidable achievable set) is taken as a standard
computability fact, in the named-`Prop` style of the project methodology
(`ExistsUndecidableAchievableSet`); it is the usual consequence of the halting problem.

The complementary claim of WP0058 — that the encoder is charged to the heritable program,
`K(C_𝒟) ≤ K(H) + O(log)` — is an AIT statement rather than a computability one and lives in
`KTAIT.WriteBack`: `WriteBack.decoder_charged`, and `WriteBack.decoder_charged_rel` for the
version stated net of a background `B` that supplies part of the machinery.

## Main results

* `achievable_computable_of_inverse` — a total, domain-recognizing inverse decides achievability.
* `no_universal_decoder` — hence none exists when achievability is undecidable.
* `exists_map_without_decoder` — some computable developmental map admits no such inverse.
* `partial_inverse_exists` — but a *partial* recursive inverse does exist, with domain exactly
  the achievable set.
* `achievable_rePred` — the achievable set of a computable map is recursively enumerable.
* `inverts_id` — satisfiability witness: the statement is not vacuous.
-/

namespace KTAIT
namespace Decoder

variable {D : ℕ → ℕ}

/-- The **achievable set** of a developmental map `D`: the acquired states that some
heritable program actually generates. Recursively enumerable when `D` is computable, but
in general not decidable. -/
def Achievable (D : ℕ → ℕ) : Set ℕ := Set.range D

/-- `C` is a **domain-recognizing write-back encoder** for the developmental map `D`.

`C a = some H` is a write-back: it claims `H` is a program generating the acquired state
`a`, and `sound` demands the claim be true. `C a = none` is a refusal, and `recognizes`
demands that `C` refuse only on genuinely unachievable states — that is, `C` knows its own
validity domain rather than having it supplied. -/
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

/-- **The engine of WP0058 Proposition 1.** A *total computable* write-back encoder that
recognizes its own domain would decide membership in the achievable set: run it and test
whether it refused. Unconditional — no AIT fact is assumed. -/
theorem achievable_computable_of_inverse {C : ℕ → Option ℕ}
    (hC : Computable C) (hinv : Inverts D C) :
    ComputablePred (fun a => a ∈ Achievable D) := by
  have hsome : Computable fun a => (C a).isSome := (Primrec.option_isSome.to_comp).comp hC
  have hpred : ComputablePred fun a => (C a).isSome = true :=
    ComputablePred.computable_iff.mpr ⟨_, hsome, rfl⟩
  exact hpred.of_eq fun a => (mem_achievable_iff_isSome hinv a).symm

/-- **WP0058 Proposition 1(i).** If achievability is undecidable, then no total computable,
domain-recognizing write-back encoder exists.

Consequently any physically realized write-back channel is a *partial* map whose validity
domain must be supplied or learned rather than recognized by the encoder itself. A partial
inverse is still available — see `partial_inverse_exists` — so it is the totality and the
self-certification that fail, not inversion as such. -/
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

/-- **WP0058 Proposition 1(ii).** Some computable developmental map admits no total,
domain-recognizing write-back encoder: a uniform exact inverse is not available in general. -/
theorem exists_map_without_decoder (h : ExistsUndecidableAchievableSet) :
    ∃ D : ℕ → ℕ, Computable D ∧ ¬ ∃ C : ℕ → Option ℕ, Computable C ∧ Inverts D C := by
  obtain ⟨D, hD, hundec⟩ := h
  exact ⟨D, hD, no_universal_decoder hundec⟩

/-! ### The partial inverse that does exist (Proposition 1(iii)) -/

/-- **Dovetailing search for a preimage.** `dovetail D a` runs the unbounded search for the
least heritable program `H` with `D H = a`, as a partial function `ℕ →. ℕ`. This is the
"partial inverse by dovetailing" of WP0058 Proposition 1(iii). -/
def dovetail (D : ℕ → ℕ) : ℕ →. ℕ :=
  fun a => Nat.rfind fun H => Part.some (decide (D H = a))

/-- **WP0058 Proposition 1(iii), existence half.** For any computable developmental map `D`
there is a *partial recursive* inverse whose domain is exactly the achievable set and which
returns a genuine preimage wherever it is defined.

This is what makes Proposition 1 a statement about **total, domain-recognizing** inverses
rather than about inverses as such. Dropping totality, inversion is available; what is lost
is the ability to refuse. Because the domain is exactly the achievable set, the search
diverges off it — the second clause of part (iii) — and there is no computable way to turn
that divergence into a refusal, which is `no_universal_decoder` read the other way.

Not covered here: the remaining clause of part (iii), that the search is **unbounded in time**
on the achievable set. That is a resource statement about running time, and this development
carries no cost model, so it remains informal. A time-bounded or Levin-complexity
formulation would be the way to state it, and WP0058 does not have one either. -/
theorem partial_inverse_exists (hD : Computable D) :
    ∃ C : ℕ →. ℕ, Partrec C ∧ (∀ a, (C a).Dom ↔ a ∈ Achievable D) ∧
      ∀ a H, H ∈ C a → D H = a := by
  refine ⟨dovetail D, ?_, ?_, ?_⟩
  · have hstep : Computable₂ fun a H : ℕ => decide (D H = a) :=
      Primrec.eq.decide.to_comp.comp₂ (hD.comp Computable.snd) Computable.fst
    exact Partrec.rfind hstep.partrec₂
  · intro a
    simp [dovetail, Achievable, Set.mem_range, eq_comm]
  · intro a H h
    simpa using Nat.rfind_spec h

/-- The achievable set of a computable developmental map is **recursively enumerable**: it is
the domain of the dovetailing search. The informal half of WP0058's proof of Proposition 1
("`𝒜` is recursively enumerable — enumerate programs, run `D`, collect outputs") is therefore
machine-checked, and only the undecidability half stays assumed
(`ExistsUndecidableAchievableSet`). -/
theorem achievable_rePred (hD : Computable D) : REPred fun a => a ∈ Achievable D := by
  obtain ⟨C, hC, hdom, -⟩ := partial_inverse_exists hD
  exact hC.dom_re.of_eq hdom

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

/-- **Satisfiability witness for the dovetailing search.** It really searches and really
halts: with `D = id` the search for a preimage of `7` returns `7`. Guards against
`partial_inverse_exists` being witnessed by the empty partial function. -/
theorem toy_dovetail_id : (7 : ℕ) ∈ dovetail (id : ℕ → ℕ) 7 := by
  refine Nat.mem_rfind.mpr ⟨by simp, ?_⟩
  intro m hm
  simp only [Part.mem_some_iff, id, eq_comm (a := false), decide_eq_false_iff_not]
  omega

end Decoder
end KTAIT
