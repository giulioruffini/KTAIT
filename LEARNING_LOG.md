# Learning Log

A 2–3 line note after each milestone: what we learned / what tripped us up.

## M0 — Toolchain & hello-Lean (2026-06-27)

- Installed `elan` (Lean's version manager, à la rustup); it provides `lean` + `lake`.
  The project's `lean-toolchain` file auto-selects the matching Lean version, so version
  drift between our code and Mathlib can't happen silently.
- Scaffolded with `lake new KTAIT math` (the `math` template wires in Mathlib and pins
  both `lakefile.toml` → Mathlib `v4.31.0` and `lean-toolchain` → Lean `v4.31.0`).
  `lake exe cache get` downloads **prebuilt** Mathlib — skipping it means a ~1h compile.
  Tripped up: first `cache get` had 667 transient decompression failures; re-running it
  fetched the rest and finished clean.
- Three lessons in reading Lean's output:
  1. **Warning ≠ error.** The "Copyright too short!" linter warning still built green
     (fixed by adding a standard header). An error has a red ✗ and exit code 1.
  2. **A false statement cannot compile.** `example : 1 + 1 = 3 := by decide` produced
     "Tactic `decide` proved that the proposition 1 + 1 = 3 is false" and failed the
     build. This is exactly the guarantee we're buying.
  3. `decide` *computes* a decidable proposition; `rfl` reduces both sides to the same
     normal form; `exact` supplies a proof term (e.g. a Mathlib lemma like `Nat.add_comm`).

## M1 — Typed ontology (2026-06-27)

- Each KT role is its own one-field `structure` wrapping a common carrier `C`
  (`SubstrateState`, `Pattern`, `Readout`, `Regulator`). Being distinct *types* (not
  defeq to `C`) is what makes Lean reject role-mixing.
- `SelfCode C Sub` bakes the proof obligation into the type: its `isSub` field is a
  proof `Sub carrier parent.carrier`. You cannot build a `SelfCode` without exhibiting
  that its carrier really is a sub-pattern of its parent `Pattern`. The whole-vs-part
  vacuity bug becomes a *typed obligation*, not a silent mistake.
- Design choice (faithful to the kickoff): we register NO automatic `Coe` instances.
  The only role→carrier bridge is the explicit `.carrier` projection, so any mixing is
  visible in the source. (An auto-`Coe` would re-hide it.)
- Ontology.lean imports no Mathlib → builds in ~250ms, great for iteration. Use
  `lake build KTAIT.Ontology` to compile just this module.
- Two teaching tools used: `#check_failure e` SUCCEEDS iff `e` fails to type-check
  (documents a forbidden statement while keeping the build green); the `isSub` witness
  `⟨[false, true], rfl⟩` shows an existential proof — give the witness `t`, then `rfl`
  closes `[true,false,true] = [true] ++ [false,true]` by computation.

## M2 — AIT interface (2026-06-27)

- `AITFrame` bundles the *data*: `Obj, K, pair, cond, star, slack`. From it we DEFINE
  `IK` (`Int`), `condStar` = `K(x|y*)` (`Nat`), `NMAI` (`Rat`, computable — no
  `noncomputable` needed since `ℚ` division is computable; `a/0 = 0` in Lean).
- KEY SOUNDNESS DECISION: the AIT facts are stated as named `Prop`s about a frame
  (`Invariance`, `SymmetryOfInformation`) — i.e. as *hypotheses* — NOT as global
  `axiom (F : AITFrame) : P F`. A global `∀F` axiom is INCONSISTENT here: one can
  build a frame with `slack=0` and mismatched `K` violating the law, then derive
  `False`. Hypotheses keep every corollary a sound implication; M5's toy model
  witnesses the facts are jointly satisfiable. (Bonus: `#print axioms` on corollaries
  will show NO custom axioms — stronger than the kickoff's target.)
- Symmetry of information uses the CORRECT form: `|I_K(x:y) − (K(x) − K(x|y*))| ≤ slack`,
  i.e. with `y*` (via `condStar`/`star`) and an `O(log)` `slack`, not a single `O(1)`.
- Two trip-ups: (1) `F.condStar x y` FAILS — dot-notation projects a *field* of the
  value's type; `condStar` is a top-level function, so call it `condStar F x y`.
  (2) The whitespace style linter wants single spaces (`Obj : Type`, not aligned cols).

## M2.5 — Probabilistic ART, Stage A: Theorem 2 (2026-06-27)

- Reality check (K corrected the AI): ART is a PROBABILISTIC statement (Thm 2 of
  entropy-28-00257): `P((W,R) | x, E) ≤ C·2^{M(W:R)}·2^{−Δ}`, a bound on a Bayesian
  posterior. Our Level-1 `ART_gap_bound` was only its deterministic shadow. So we
  added a real probabilistic layer (Level 1.5).
- `AITProb extends AITFrame` adds `post : Obj → Obj → ℝ` — the posterior `P(e|x)`.
  The probabilistic conditioning now lives explicitly in `post`.
- PROVED `probabilistic_regulator_theorem` (Thm 2) from two hypotheses: the wrapper
  bound Eq (6) (`post ≤ C̃·2^{K(x)−K(W,R)}` — the probability→complexity BRIDGE) and
  Lemma 2 (`K(O_{W,∅}) ≤ K(W)+c₀`). Proof = integer-exponent algebra: rewrite the
  exponent via `M(W:R)=IK` and `Δ`, bound with `omega`, lift to `2^·` with `gcongr`,
  split with `zpow_add₀`, finish with `ring`.
- `#print axioms` → `[propext, Classical.choice, Quot.sound]` only. No `sorry`, no
  custom axiom: the theorem rests solely on its stated hypotheses + Lean core.
- Lean lessons: (a) `gcongr` auto-discharges side goals from context (it found `hexp`
  by `assumption`) and left only `1 ≤ 2` → finish with `norm_num`. (b) `zpow` works on
  ℤ exponents over ℝ; `(2:ℝ)^(a+b) = 2^a*2^b` via `zpow_add₀ (two ≠ 0)`. (c) The build
  warned `hc0 : 0 ≤ c0` was UNUSED — dropping it makes the theorem strictly stronger
  (the bound never needed c₀'s sign). Reading warnings sharpened the statement.

## M2.5 — Probabilistic ART, Stage B: Lemma 1, the conditioning bridge (2026-06-27)

- `PrefixMachine` carries `Prog, Out, U, len, K, m` (semimeasure, `m x > 0`). `prior p =
  2^{−|p|}`; `posterior p = prior p / m (U p)` — Bayes with deterministic likelihood and
  evidence `m(x)`. This makes PROBABILISTIC conditioning `P(p|x)` a concrete object.
- `CodingTheorem c1 c2`: `c₁·2^{−K x} ≤ m x ≤ c₂·2^{−K x}` — the probability↔complexity
  bridge, as a hypothesis.
- PROVED `lemma1_posterior_bounds`: `(1/c₂)·2^{K x−|p|} ≤ P(p|x) ≤ (1/c₁)·2^{K x−|p|}`.
  This is THE place where Bayesian conditioning becomes a K-quantity. Combined with a
  canonical `K(W,R)+O(1)` code it yields the wrapper bound Eq. (6) that ART.lean assumes.
- `#print axioms` → only `[propext, Classical.choice, Quot.sound]`.
- Lean lessons: (a) Mathlib renamed `div_le_div_iff` → `div_le_div_iff₀` (the `₀` suffix
  marks the field/GroupWithZero version with positivity hyps). `grep` in
  `.lake/packages/mathlib` finds the current name fast. (b) Proof pattern for real-number
  bounds: rewrite into `(ratio) · 2^e` via `zpow_add₀` + `mul_div_right_comm`, bound the
  ratio with `div_le_div_iff₀` + `linarith`, lift by `mul_le_mul_of_nonneg_right`.

## M4 — Proposition 3: self-regulation requires a temporal self-model (2026-06-27)

- Read the actual statement (WP0162 App. K, Prop 3 — kickoff's `self_regulation_temporal_model`).
  Setup is TEMPORAL: regulated source = self-code trajectory `S t → S(t+τ)`, regulator
  `E = A\S`, gap `Δ_self = K(O_{S,∅}) − K(O_{S,E})`. Conclusion (Eq. 44):
  `K(S(t+τ) | S t, E, C) ≪ K(S(t+τ) | C)` — present organization makes the future
  self-code cheap. (The static `IK(A:S)` is vacuous since `S ⊂ A`; the ontology's
  temporal `SelfCode` is exactly what avoids that.)
- Proof chain, all `omega`: `Δ_self > 0` →(ART) high conditional mutual info `cmi` →
  (symmetry of information: complexity drop = mutual info) future self-code cheap.
  AIT facts are hypotheses: `hSI` (drop ≥ cmi − slack), `hART` (`Δ_self>0 → cmi ≥
  Δ_self − slack`). Conditioning on `S t, E, C` modeled as `cond _ (pair (S t) (pair E C))`.
- `#print axioms` → `[propext, Quot.sound]` (no `Classical.choice` — pure integer
  reasoning). No `sorry`, no custom axiom: a sound implication from named AIT facts.
- Lean lessons: (a) `Time` lives in Ontology — import it (with `relaxedAutoImplicit =
  false`, an undefined multi-char identifier is a hard ERROR, not a silent autobound var
  — a good safety net). (b) Unused-variable warning on `hΔ` revealed the cleaner, more
  faithful encoding: make ART the IMPLICATION `gap>0 → bound`, so `hΔ` fires it
  (`have hbound := hART hΔ`). Warnings → better statements, twice now.

## M3 — Persistence (2026-06-27, after M4)

- `Pers F S t τ := NMAI (S t) (S (t+τ))` (ℚ): persistence = normalized temporal
  self-information of the self-code with its FUTURE self (the non-vacuous temporal
  quantity, vs static `IK(A:S)`). `TemporalSelfInfo` = un-normalized `IK(S_t:S_{t+τ})`.
- `Persistent F S t τ θ := θ ≤ Pers …`; lemmas `pers_eq_nmai` (`rfl`) and
  `persistent_pos` (`lt_of_lt_of_le`). All sorry-free. Done out of kickoff order
  (after M4) since M4 didn't depend on it.

## M5 — Toy model + bad statements (2026-06-27)

- ToyModel.lean (the non-negotiable satisfiability witness): `Toy` (degenerate all-zero
  `AITFrame`) satisfies `SymmetryOfInformation` (`toy_symmetry`); `ToyMachine` (m≡1)
  satisfies the `CodingTheorem` (`toyMachine_coding`); `ToyGap` (`K := id`) has a real
  gap `Δ_self = 3 > 0` and the self-model corollary FIRES on it (`toy_self_model_fires`)
  — so the corollaries are non-vacuous, not vacuously true from inconsistent hypotheses.
- BadStatements.lean: (1) part-whole guard re-demonstrated (`#check_failure peers A S`);
  (2) the y-vs-y* demo in `FrameYStar` — at `(10,3)` the starred form holds
  (`ystar_form_holds`) while the raw-`y` form FAILS (`rawy_form_fails`, proved by
  `decide`). Concrete proof that symmetry of information must use `y*`, not `y`.
- Lean lessons: (a) numerals at a projected carrier type (`ToyGap.Obj`) fail OfNat
  synthesis — write `(3 : Nat)`, which unifies by defeq. (b) `decide` refuses goals with
  free variables even when value-independent (`Toy.K` ignores its arg) — `simp [defs]`
  reduces them away first, then it closes. (c) `decide` evaluates `if`/`natAbs`/`Int`
  comparisons on concrete frames — ideal for "this instance holds / that one fails".

## Phase 1 — close the ART chain (2026-06-27)

- Refactored `AITProb` to carry the semimeasure `m` and DEFINE the posterior
  `post e x := 2^{-K e}/m x` (canonical-code posterior = Lemma 1 specialized). Coding
  theorem now a frame predicate: `CodingLB`/`CodingUB`.
- DERIVED the wrapper bound Eq. (6) (`wrapper_bound`): `post e x ≤ (1/c₁)·2^{K x − K e}`
  — previously an assumed hypothesis, now a theorem from `CodingLB` (proof = Lemma 1's
  upper half via `post_factor` + `div_le_div_iff₀` + `mul_le_mul_of_nonneg_right`).
- `theorem1_posterior_tilt`: two-sided posterior tilt; key trick — the exponent
  `K x − K W − K R + IK = K x − K(pair W R)` by `simp only [IK]; ring`, reducing to the
  two-sided wrapper.
- `probabilistic_regulator_theorem` re-proved to consume `wrapper_bound` (no free
  wrapper hypothesis): now rests on `CodingLB` + Lemma 2.
- `theorem3_onoff_evidence` in LOG-FREE multiplicative form
  `(c₁/c₂)2^Δ ≤ m_on/m_off ≤ (c₂/c₁)2^Δ` (avoids `Real.logb`); proof = `div_le_div₀`
  (Mathlib's 4-arg division-monotonicity) + an algebra lemma via `mul_div_mul_comm` and
  `zpow_sub₀`. All four `#print axioms` = Lean core only.
- Lean lessons: Mathlib's 4-arg monotone-division is `div_le_div₀ (0≤c)(a≤c)(0<d)(d≤b)`;
  `mul_div_mul_comm : a*b/(c*d) = a/c*(b/d)`; choosing a multiplicative statement sidesteps
  the whole `Real.logb` API.
- Added `probabilistic_regulator_theorem_sharp`: the ART Thm 2 sharp form retaining
  `2^{−K(R)}` (clarification (ii) / WP0162 Eq. 22). No extra hypothesis — the exponent
  identity is EXACT (the headline form just drops `2^{−K(R)} ≤ 1`). The headline is then
  re-derived as `probabilistic_regulator_theorem_of_sharp` via
  `zpow_le_one_of_nonpos₀ (by norm_num) (by omega)` (note: the non-positive-exponent side
  goal `−K(R) ≤ 0` is `omega`, not `positivity`).

## Phase 3 — regulator selection (WP0162 Prop 1) (2026-06-27)

- `ChainRule F W R`: `K(R|W) = K(R) − M(W:R)` (i.e. `cond R W = K R − IK W R`), the chain
  rule / symmetry of information as a named AIT hypothesis.
- `regulator_selection_order`: `cond R₁ W ≤ cond R₂ W ↔ (M−K)(R₂) ≤ (M−K)(R₁)` —
  minimizing conditional complexity `K(·|W)` = maximizing `M(W:·) − K(·)`. Pure `omega`
  after `simp only [ChainRule]`.
- `regulator_selection`: set form over the sufficiency set `S` (`R*` minimizes `K(·|W)` on
  `S` ↔ maximizes `M−K` on `S`), via the order lemma.
- `probabilistic_regulator_theorem_conditional`: ties the SHARP ART form to the `2^{−K(R|W)}`
  reading — `M(W:R) − K(R) = −K(R|W)` by the chain rule, so the regulator-cost factors
  `2^{M}·2^{−K(R)}` collapse to `2^{−K(R|W)}`. Directly answers the conditioning thread: the
  posterior favors regulators simple *given the world*.
- `#print axioms`: `regulator_selection = [propext, Quot.sound]` (no `Classical.choice`);
  conditional corollary = Lean core.

## Phase 2 — persistence conservation (WP0162 Prop 2) (2026-06-27)

- `ConservationLedger F OW R`: `K(O_W) = I_K(O_W:R) + K(O_W|R*)` — the symmetry of
  algorithmic information rearranged (the residual splits further into action + innovation,
  the third sink, not modeled).
- `persistence_conservation`: bounded form `|K(O_W) − (IK + condStar)| ≤ slack` straight
  from `SymmetryOfInformation`. Proof: the inside is the negation of `hsym OW R`'s term, so
  `rw [show … = −(…) from by ring, Int.natAbs_neg]; exact h`. `#print axioms = [propext]`.
- `conservation_tradeoff`: at fixed `K(O_W)`, `IK(O_W:R₂) ≤ IK(O_W:R₁) ↔ condStar R₁ ≤
  condStar R₂` — maximizing shared structure = minimizing the conditional residual. `omega`.
- Pattern noticed: WP0162 §D Props 1 & 2 are both "order-equivalence under an AIT identity"
  (chain rule / symmetry of info) + `omega` — the same proof shape as the self-model.

## Phase 4 — self-model incompleteness (WP0192 Principle 1 / WP0162 Prop 4) (2026-06-27)

- Three INDEPENDENT obstructions, each with a clean faithful core:
  - `quine_floor`: a lossless self-model (`U selfA = A`) has `len selfA ≥ K A`, straight from
    `KIsShortest` (the defining property of `K`). Completeness costs ≥ K(A).
  - `self_prediction_dichotomy`: a genuine DIAGONALIZATION — if the agent acts to contravene
    its consulted prediction (`act = flip`, `flip` fixed-point-free) then exactness
    `act pred = pred` gives `flip pred = pred`, contradiction. AXIOM-FREE; the contravention
    is witnessed by boolean `not` (no fixed point, `by decide`).
  - `chaitin_blocks_minimality`: if certified lower bounds are capped at `c` (Chaitin), then
    for `K x > c+1` the near-minimal bound `K x > K x − 1` is uncertifiable. `omega`.
- Methodology held: the standard computability theorems (Kleene, Chaitin) enter as the
  hypotheses (`KIsShortest`, the certifier ceiling); the KT content is their self-modeling
  consequence. The diagonalization needing NO axioms is a nice surprise.

## Phase 5 — coarse-graining uncomputability (WP0193) (2026-06-27)

- Abstract computability: `CompT`/`CompS` predicates on the two solver shapes; `specialize T`
  sets `y := x`; `ReductionClosure` (a computable targeted solver specializes to a computable
  structure-function solver); `VV` axiom (`¬ CompS sf0`, Vereshchagin–Vitányi).
- `theoremB` / `corollaryB`: a *correct* targeted/regulatory solver (`specialize T = sf0`) is
  uncomputable, by reduction to V–V (`rw [hcorrect]` then `exact hvv`). Both depend on NO
  axioms — the reduction is pure logic; V–V is the named hypothesis.
- ROADMAP COMPLETE (5/5). Whole KT corpus of WP0162/WP0192/WP0193 + the probabilistic ART
  is formalized; KT corollaries sorry-free, axioms = Lean core + named AIT facts.

## Easy + medium batch (2026-06-27, after roadmap)

- `Contrast.lean` (Q3, Eq. 26): `contrast_posterior_ranks_by_complexity` — the fiber posterior
  ranks by joint simplicity, no `2^{−Δ}` tilt. First `Finset.sum` piece; key lemma names:
  `Finset.sum_pos`, `div_le_div_iff_of_pos_right` (NOT `div_le_div_iff_right`, which is the
  ordered-GROUP `/`), `zpow_le_zpow_iff_right₀ (1<2)`. Gotcha: do the `div` rewrite BEFORE
  `unfold cweight`, else the denominator in the goal (`2^…`) no longer matches `hZ` (`cweight …`).
- `OrbitLabel.lean` (App. C): `genEnergy_conserved` — generalized energy = conserved orbit label
  of a bijective dynamics `F : Equiv.Perm X`; orbit Setoid + `Quotient.sound`. Axiom-free dynamics.
- `Persistence.boundary_sufficient` (App. E): two one-sided conditional bounds → two-sided
  sufficiency `|Δcond| ≤ slack` by `omega`.
- `ART.low_complexity_shrinkage` (Thm A4): counting bound + `idx < K(W)` ⇒ strict shrinkage (`omega`).
- `CoarseGraining.theoremA` (selection uncomputability, = the `theoremB` reduction) and
  `CoarseGraining.existence` (WP0193 Prop 1, `∃` from the bounded self-code witness) — axiom-free.
- All six `#print axioms` = Lean core (two axiom-free). Easy+medium batch done.

## Geometry track — generalized Noether (2026-06-27)

- `NoetherFlow.lean`: the flow = an `AddAction` of a time group `T` on state space `X`.
  `Conserved T C := ∀ t x, C (t +ᵥ x) = C x`; `trajLabel` (flow-orbit label) via Setoid/Quotient;
  `trajLabel_conserved` (the universal conserved quantity); `conserved_comp_symm` (a symmetry
  commuting with the flow carries conserved quantities to conserved quantities — the Noether
  correspondence). Continuous-time analogue of `OrbitLabel`; axiom-free dynamics.
- Lean lesson: with `variable {T}`, `Conserved C` cannot infer `T` (it is not in `C`'s type) →
  "typeclass `AddAction ?m X` stuck"; same for `X` in the `Setoid X`-typed defs. Fix: make BOTH
  `T` and `X` EXPLICIT variables. Also a `show` that beta-reduces the goal trips the style linter —
  use `change`.
- `Homogeneous.homogeneousSpace` (G2, Theorem A4 core): a transitive symmetry action makes the
  state space a homogeneous space, `X ≃ G ⧸ stabilizer x`, via Mathlib `orbitEquivQuotientStabilizer`
  + `orbit_eq_univ` + `Equiv.Set.univ`/`Equiv.setCongr`. The dimension formula `dim X = dim G −
  dim H` needs manifold dimension (deferred).
- Remaining geometry (deferred): the manifold/dimension refinements, Lie pseudogroups, moduli
  stacks, Mostow rigidity (not in Mathlib); and Level-2 grounding.

## Algorithmic-emergence hook (2026-06-28)

- `CoarseGraining.algorithmic_emergence` (WP0007, generic form): a correct general coarse-graining
  solver computing the structure function `sf0` cannot be computable — "reduction is not
  construction." Substance is V–V (`hvv`); the regulatory specialization is `corollaryB` (WP0193).
  A thin named hook so WP0007 can cite a machine-checked statement. KTAIT is now PUBLIC (Actions
  free; CI already de-stacked).


- `Persistence.meta_persistence` / `meta_persistence_limit` (WP0162 §6, meta-persistence Prop.):
  "persistence one scale up." Symmetry of information + a stable-complexity collective submodel
  (`K(Sc t)=K(Sc (t+τ))=k`) + bounded transient `condStar(Sc t, Sc(t+τ)) ≤ L` give
  `Pers_C ≥ 1 − (L+slack)/k`. Proof = `omega` for the IK lower bound (natAbs from `SymmetryOfInformation`),
  then `unfold Pers NMAI; rw [hkt,hktau,max_self]; rw [show 1-(…)/k = (k-L-slack)/k …]; gcongr`.
  Key point: the hypotheses mention ONLY `Sc,k,L,slack` — no individual objective — so the parts
  need share no goal. `toy_meta_persistence_fires` witnesses non-vacuity on `ToyMeta` (K≡3, so k>0,
  unlike `Toy` where K≡0). `#print axioms` = Lean core only.

## M-Decoder — WP0058 Proposition 1: no universal decoder (2026-07-10)

- `Decoder.no_universal_decoder` (WP0058 Prop. 1): a *total* computable inverse compiler `C` for a
  developmental map `D` that also **recognizes its own domain** (`C a = none` exactly off
  `Set.range D`) would decide membership in the achievable set — run it, test for `none`. Since a
  computable `D` has an r.e.-but-undecidable range in general, no such `C` exists. Hence every
  realized Lamarckian write-back channel is a *partial* map whose validity domain is fixed in
  advance, which is what charges the domain to the heritable program.
- Novel for this repo: the engine (`achievable_computable_of_inverse`) assumes **no AIT fact at
  all** — it is unconditional, `#print axioms` = Lean core only. Only non-vacuity (that some
  computable `D` really has an undecidable range) enters as a named `Prop`,
  `ExistsUndecidableAchievableSet`. Rice is cited in the paper's prose but is *not needed* in the
  Lean proof: the decidability contradiction is direct and cheaper.
- Tripped us up briefly: framing. The naive statement "no computable inverse of `D`" is FALSE — a
  partial inverse exists by dovetailing over `Set.range D`. The theorem must quantify over *total*
  inverses that *recognize their domain*; that is exactly the distinction WP0058 needs (partial,
  domain-restricted channels are precisely what biology has). Encoding it as the two fields of
  `Inverts` (`sound` + `recognizes`) made the proof three lines.
- Idiom: `Primrec.option_isSome.to_comp |>.comp hC` → `ComputablePred.computable_iff.mpr ⟨_, ·, rfl⟩`
  → transfer along the characterization with `ComputablePred.of_eq`. `inverts_id` is the
  satisfiability witness (`D = id`), guarding against a vacuous hypothesis.
- Still open from WP0058: Prop. 1's AIT half (`K(C_𝒟) ≤ K(H) + O(1)`) and Prop. 2 (Darwinian gain
  bounded by the entropy of the selection signal — a data-processing bound in the `AITFrame` style).

## M-WriteBack — WP0058 Prop. 1 (AIT half) + Prop. 2 (2026-07-10)

- `WriteBack.bandwidth_le_cond` is the whole module in one line: with `λ_B := I(a : H'|H)`,
  joint-dominates-marginal gives `λ_B ≤ K(H'|H) + slack`. **Nothing about `a` survives on the
  right.** Both regimes are then corollaries that differ only in how `K(H'|H)` is bounded:
  Darwinian by `K(σ)` (the selection signal), Lamarckian by `K(C(a)|H)` (the decoder image).
  That asymmetry *is* WP0058 Prop. 2 (zeroth- vs first-order search) — it fell out of the
  definition rather than needing a new hypothesis, which is the sign the definition was right.
- `decoder_charged` (Prop. 1, AIT half): `K(C) ≤ K(H) + 2·slack` from conditional subadditivity
  plus `RecoverableFrom`. Two AIT facts total, both named `Prop`s: `JointGeMarginal`,
  `SubadditivityCond`.
- `trivial_decoder_transmits_nothing` is the one worth quoting: a decoder with trivial image
  transmits nothing *however much was acquired* — the bound never mentions `a`. That is
  Corollary 1 (write-back cannot bootstrap novelty) with teeth.
- `ToyWB` (`K := id`, `cond := (· - ·)`, `pair := max`, `slack := 0`) satisfies both hypotheses
  AND **attains** the Darwinian bound (`toyWB_selection_bound_tight`: λ_B = K(σ) = 3). Tightness,
  not just non-vacuity — worth doing, since a satisfiable-but-slack witness proves little.
- Gotchas, both already in the skill and both still bit: numerals at `ToyWB.Obj` need `(4 : Nat)`;
  and `simp only [ToyWB]` leaves `id 3` opaque to `omega` — must be `simp only [ToyWB, id]`.
- WP0058's Lean track is now complete except Hypothesis 1 (λ_P* ~ τ_E), which is a conjecture and
  is marked `n/a` in WP0195 rather than forced.
