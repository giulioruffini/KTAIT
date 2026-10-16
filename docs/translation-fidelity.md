# Translation fidelity: pitfalls between a paper and its Lean counterpart

October 16, 2026. Written after the WP0203 Round 1 audit (Klaus and Kaiti), prompted by
Bastounis, Circelli and Hansen, *Navier–Stokes lost in translation: why Lean verification of AI
autoformalisation does not guarantee correct natural language proofs* (arXiv:2610.08144).
Read this before stating a new KT result in Lean, before citing a declaration in a paper, and
before writing "machine-checked" anywhere.

## What a KTAIT check does and does not establish

`AITFrame` (`KTAIT/Basic.lean`) gives a carrier, a function `K`, a conditional `cond`, a pairing
and one natural number `slack`. Nothing ties `K` to a universal machine. Each AIT fact enters a
theorem as a named inequality about the objects in that theorem, and most proofs close with
`omega`. A compiled declaration therefore says: *for every function called K, if these instance
inequalities hold, the conclusion holds.* It checks the derivation from the hypotheses. It does
not check that the hypotheses are true of prefix Kolmogorov complexity, that the Lean statement
says what the paper says, or that the paper's written proof is correct. Lean's acceptance is
silent on all three, and each needs its own check.

## Pitfalls found so far

Each entry gives the pitfall, the case where it occurred, and the rule that prevents it.

1. **A hypothesis stronger than the true AIT fact.** `RegulationBalance.CondMono` states
   `cond x R ≤ K x` with no allowance; `ARTExactForm` uses the same exact form. For prefix
   complexity the fact holds only up to a fixed constant. A premise stronger than the true fact
   may fail for the intended `K`, so the theorem may not apply to it. Raising `slack` does not
   help when `slack` does not occur in the premise.
   *Rule:* every named AIT hypothesis carries its tolerance (`slack` or an explicit constant).
   Its docstring cites the standard result it instantiates and the overhead that result gives.

2. **A Lean hypothesis the paper explicitly excludes.** WP0203's Eq. (forcesL) holds "without
   the null-output computability assumption". The cited `simple_regulator_forces_residual`
   assumes `DataProcessing F z0 W R`. The paper's claim is still covered: instantiating
   `W := z0` makes the hypothesis trivial. But that bridge appeared nowhere, and a reader
   comparing statements sees a stronger premise.
   *Rule:* cite a declaration whose hypotheses are implied by the paper's stated assumptions.
   When a specialization is needed, write it as its own one-line declaration and cite that.

3. **A weaker conclusion or a smaller domain.** `horizon_bound_sup` takes a supremum over a
   finite `Finset`; the paper takes it over an arbitrary nonempty set. A per-horizon theorem
   with one `slack` does not prove the paper's `O(log N)` uniformity across horizons.
   *Rule:* record the direction of every specialization. Say in the paper exactly which part
   is checked, and supply uniformity as a stated paper-level argument (for example
   `slack_N ≤ c·log B_N + c₀` with constants independent of `N` and of the episode).

4. **Context absorbed silently.** The paper conditions every term on a coding frame `C` (and
   often the horizon `N`); KTAIT writes unconditional `K`. This is legitimate under the
   interpretation `K_F(u) = K_U(u ∣ C, N)`, `cond_F(u, v) = K_U(u ∣ v, C, N)`, but only if that
   map is written down and nested side information is checked for duplication or omission.
   *Rule:* every correspondence record includes the interpretation map for objects, conditioning
   and pairing.

5. **A Lean definition that names the paper's object but differs from it.** `AITProb.post e x`
   is `2^(−K e)/m(x)`. The paper's specified-code posterior uses the weight of a
   simulator-wrapped canonical code among the programs producing `x`. The two agree only after
   the wrapper, code injectivity and normalization are justified.
   *Rule:* never identify a Lean definition with a paper quantity on the strength of its name.
   Write the bridge lemma or state the interpretation obligation.

6. **Global versus local hypotheses.** `independent_regulation_threshold` requires the regulator
   inequality on the whole positive-weight support; the paper assumes it only where `L ≤ η`. A
   variable allowance bridges the two (Kaiti, `fidelity_bridge_checks.lean`), but substituting
   one constant everywhere would silently strengthen the hypothesis.
   *Rule:* match the region on which each hypothesis is assumed, not only its form.

7. **A different proof.** A valid Lean proof by a different route establishes the theorem, not
   the paper's written argument. A wrong written proof can sit beside a correct formal one.
   *Rule:* the correspondence record pairs each substantive written step with a formal lemma or
   an explicit external argument. When the routes differ, align them or say so in the paper.

8. **Documentation drift.** Stale names ("Global Algorithmic Regulator Theorem (WP0203 v20)"),
   docstrings that say "equivalently" for an unproved step, and comments that drop a term or a
   sign (`art_with_residual`). These become errors when copied into a paper.
   *Rule:* audit docstrings with the types. Treat a docstring as a claim.

9. **Satisfiability mistaken for instantiation.** A toy frame shows the hypotheses are jointly
   consistent. It does not show they hold for Kolmogorov complexity.
   *Rule:* argue instantiation by the intended `K` separately, hypothesis by hypothesis, with
   its overhead.

10. **Counting citations instead of claims.** WP0203 v34.5 has 133 `\ktait{}` occurrences and
    81 distinct strings, with short and qualified names for the same declaration. Unnumbered
    claims used in proofs or advertised as checked are easy to miss.
    *Rule:* inventory paper claims first, then resolve aliases to declarations.

## The workflow that avoids them

1. Write the paper statement with all quantifiers, domains and assumptions before any Lean.
2. Write the Lean *statement* and its correspondence record (below), and have a second agent
   or Giulio approve the record **before** proving. Most mistranslation happens here.
3. Prove it. If the proof needs a stronger hypothesis or a weaker conclusion, stop. Change
   the record, tell the paper owner, and decide whether the paper or the Lean changes. Never
   adjust a statement only to make a proof compile. AI provers are rewarded for compiling, so
   this incentive is the main risk (arXiv:2610.08144, Section 3.4).
4. Every named AIT hypothesis carries its tolerance and cites its source and overhead.
5. The paper's correspondence table is generated from the records and claims only what their
   verdicts support.
6. After any prose revision of a cited result, re-run the correspondence check: wording
   changes can add a quantifier or drop a condition.

## The correspondence record

One record per paper claim (Kaiti's protocol, WP0203 `notes/round1/kaiti_2026-10-16/FIDELITY_PROTOCOL.md`):

- paper anchor and exact claim, with all standing assumptions;
- pinned declarations with elaborated types (`#check`), and the definitions those types use;
- interpretation map (objects, conditioning, pairing, probability law, events);
- hypothesis obligations (source, conditioning, overhead; assumed, proved or cited);
- constants and quantifiers (fixed over what; `∃ c ∀ N` versus `∀ N ∃ c`);
- proof-step correspondence;
- three verdicts:
  - *statement relation*: equivalent under the interpretation, paper specializes Lean, Lean
    specializes paper, Lean weaker, different, or unresolved;
  - *proof correspondence*: same argument, same core with steps omitted, different valid
    argument, gap in the written argument, or unresolved;
  - *formal coverage*: concrete construction, consequence of named hypotheses, arithmetic
    implication, paper-only, or unresolved;
- repair, owner, build and axiom evidence, cross-reviewer and final pin.

"Bridge required" is a verdict of its own, never folded into "equivalent".
