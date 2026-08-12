/-
Copyright (c) 2026 Giulio Ruffini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Ruffini (with Claude Code)
-/
import Mathlib
import KTAIT.Basic
import KTAIT.RegulationBalance

/-!
# KTAIT.PersistenceAccounting — the Algorithmic Persistence Accounting Theorem (APAT)

Phase I of the worldview-document theorem programme (KT canonical working document v0.1,
2026-08-12; WP0216 *Pattern, Persist!* / WP0203 companion). The persistence reading of the
Regulation Balance: identity-relevant boundary novelty that the current organization failed
to predict must be accounted for by the later self-code, the updated model, retained state,
the outgoing action transcript, or a complementary world record. Nothing accumulates
"nowhere".

## Reading of the objects

* `B` — the identity-relevant incoming boundary record `B^P_N` over the horizon, a fixed
  computable projection of the interface history declared *before* the comparison.
* `D` — the initial controlled description `D_t = ⟨Z_t, 𝒲_t, C⟩`: current self-code,
  current reusable model structure, and frame. Abstract here; the interpretation lives in
  the papers. The left-hand side `K(B | D)` is then exactly the *residual identity-relevant
  novelty* `ν_P(N)`: what the present organization fails to predict about its own boundary.
* `Znext, Mnext` — the later self-code `Z_{t+N}` and later reusable model `𝒲_{t+N}`.
* `sigma` — other retained internal state at the horizon.
* `action` — the outgoing action/interface transcript.
* `exhaust` — an admissible complementary world record. As in `KTAIT.RegulationBalance`,
  in a complete reversible realization a full endpoint/episode record always provides
  closure; *minimality and physical localization are additional modelling hypotheses*
  (see the Localization section of that module), not part of this abstract statement.

## The statement

With `Q = ⟨Z', ⟨M', ⟨σ, ⟨a, Ξ⟩⟩⟩⟩` and information closure `K(B | ⟨Q,D⟩) ≤ slack`,

  `K(B|D) ≤ M(B:Z'|D) + M(B:M'|⟨Z',D⟩) + M(B:σ|⟨M',⟨Z',D⟩⟩)`
  `        + M(B:a|⟨σ,…⟩) + M(B:Ξ|⟨a,…⟩) + 3·slack`.

The chain order is fixed for interpretation (self-code first, then model, state, action,
world record); the individual terms are order-dependent while the joint total is invariant
up to slack. **No orthogonal decomposition is claimed.**

The proof is `residual_in_completion` (chain rule + closure) followed by the declared
five-way ordered split — the same architecture as `balance`/`gap_forces_exhaust`, with the
completion enlarged from three components to five and the conditioning object now the
*initial controlled description* rather than the visible ART record. That relocation of the
model into the conditioning tuple is the persistence interpretation: the left side becomes
the novelty the current organization failed to predict.

## Discipline

The AIT facts consumed (`CondChain`, `InfoClosed`, and the split) are named `Prop`
hypotheses about a frame, never axioms, exactly as in `KTAIT.RegulationBalance`.
-/

namespace KTAIT
namespace PersistenceAccounting

open RegulationBalance

variable (F : AITFrame)

/-! ## The completion tuple -/

/-- The APAT completion tuple `Q = ⟨Z', ⟨M', ⟨σ, ⟨a, Ξ⟩⟩⟩⟩`: later self-code, later
    model, retained state, action transcript, complementary world record. -/
def apatTuple (Znext Mnext sigma action exhaust : F.Obj) : F.Obj :=
  F.pair Znext (F.pair Mnext (F.pair sigma (F.pair action exhaust)))

/-! ## The AIT fact used, as a named hypothesis -/

/-- **Five-way ordered split of the persistence flow** (conditional chain rule), with
    `Q = apatTuple` the completion and `D` the initial controlled description:

    `M(B : Q | D) ≤ M(B : Z' | D) + M(B : M' | ⟨Z',D⟩) + M(B : σ | ⟨M',⟨Z',D⟩⟩)`
    `             + M(B : a | ⟨σ,⟨M',⟨Z',D⟩⟩⟩) + M(B : Ξ | ⟨a,⟨σ,⟨M',⟨Z',D⟩⟩⟩⟩) + slack`.

    The order (self-code, model, state, action, world record) is fixed for
    interpretation; only the joint total is order-invariant up to slack. -/
def PersistenceSplit (B Znext Mnext sigma action exhaust D : F.Obj) : Prop :=
  cIK F B (apatTuple F Znext Mnext sigma action exhaust) D
    ≤ cIK F B Znext D
      + cIK F B Mnext (F.pair Znext D)
      + cIK F B sigma (F.pair Mnext (F.pair Znext D))
      + cIK F B action (F.pair sigma (F.pair Mnext (F.pair Znext D)))
      + cIK F B exhaust (F.pair action (F.pair sigma (F.pair Mnext (F.pair Znext D))))
      + (F.slack : Int)

/-! ## The theorem -/

/-- **Algorithmic Persistence Accounting Theorem (APAT).** Under information closure of
    the episode and the declared five-way split, the residual identity-relevant novelty
    `K(B | D)` is bounded by what the later self-code, later model, retained state,
    action transcript, and complementary world record each carry about the boundary
    record, in the declared order:

    `K(B|D) ≤ M(B:Z'|D) + M(B:M'|⟨Z',D⟩) + M(B:σ|…) + M(B:a|…) + M(B:Ξ|…) + 3·slack`.

    Identity-relevant novelty is never unaccounted for: it is predicted-away, kept,
    consolidated, acted out, or left in the world. -/
theorem algorithmic_persistence_accounting
    (B D Znext Mnext sigma action exhaust : F.Obj)
    (hchain : CondChain F B (apatTuple F Znext Mnext sigma action exhaust) D)
    (hclosed : InfoClosed F B (apatTuple F Znext Mnext sigma action exhaust) D)
    (hsplit : PersistenceSplit F B Znext Mnext sigma action exhaust D) :
    (F.cond B D : Int)
      ≤ cIK F B Znext D
        + cIK F B Mnext (F.pair Znext D)
        + cIK F B sigma (F.pair Mnext (F.pair Znext D))
        + cIK F B action (F.pair sigma (F.pair Mnext (F.pair Znext D)))
        + cIK F B exhaust (F.pair action (F.pair sigma (F.pair Mnext (F.pair Znext D))))
        + 3 * (F.slack : Int) := by
  have hres :=
    residual_in_completion F B (apatTuple F Znext Mnext sigma action exhaust) D
      hchain hclosed
  simp only [PersistenceSplit] at hsplit
  omega

/-! ## Finite-horizon pigeonhole corollary -/

/-- **No unmanaged novelty (finite-horizon pigeonhole form).** If the later self-code,
    model update, retained state, and action transcript each carry only bounded
    information about the identity-relevant boundary record, the complementary world
    record must carry the rest:

    `M(B:Ξ|…) ≥ K(B|D) − r_Z − r_M − r_σ − r_a − 3·slack`.

    A bounded pattern facing a positive residual-novelty budget cannot remain within its
    channel bounds unless the balance is carried by world-side records — the finite core
    of the worldview document's rate corollary (asymptotic rates are analysis on top of
    this and are deliberately not formalized here). -/
theorem no_unmanaged_novelty
    (B D Znext Mnext sigma action exhaust : F.Obj) (rZ rM rS rA : Int)
    (hchain : CondChain F B (apatTuple F Znext Mnext sigma action exhaust) D)
    (hclosed : InfoClosed F B (apatTuple F Znext Mnext sigma action exhaust) D)
    (hsplit : PersistenceSplit F B Znext Mnext sigma action exhaust D)
    (hZ : cIK F B Znext D ≤ rZ)
    (hM : cIK F B Mnext (F.pair Znext D) ≤ rM)
    (hS : cIK F B sigma (F.pair Mnext (F.pair Znext D)) ≤ rS)
    (hA : cIK F B action (F.pair sigma (F.pair Mnext (F.pair Znext D))) ≤ rA) :
    cIK F B exhaust (F.pair action (F.pair sigma (F.pair Mnext (F.pair Znext D))))
      ≥ (F.cond B D : Int) - rZ - rM - rS - rA - 3 * (F.slack : Int) := by
  have h :=
    algorithmic_persistence_accounting F B D Znext Mnext sigma action exhaust
      hchain hclosed hsplit
  omega

end PersistenceAccounting
end KTAIT
