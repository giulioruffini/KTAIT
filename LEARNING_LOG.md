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
