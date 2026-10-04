# WP0218 model accounting: proof scope and axiom audit

October 4, 2026. `ModelAccounting.lean` records the role of an acquired model,
finite parameters, and a lossless residual in the general completion account.

The five AIT results use named conditional coding hypotheses. The recoding
result consumes two reconstruction bounds and two subadditivity bounds.
The model–parameter–residual result composes three subadditivity bounds with
an explicit target-reconstruction allowance. The innovation lower bound
uses a lower chain rule, recovery of the parameter/innovation pair from the
target, and an explicit conditional-incompressibility hypothesis. Combining
that lower bound with `CompletionLedger` gives the complementary-record
bound (four slacks) and the internal-retention limit (three slacks). These
counts differ from the APB's five-record count.

Four finite list results check recovery of innovation bits, recovery of the
parameter at positive horizon, reconstruction of the block record, and raw
stream length. They do not infer Kolmogorov complexity from a finite test or
formalize the prefix-machine coding of those lists.

All nine declarations were checked with `#print axioms`. The parameter
recovery result uses no axioms; conditional recoding uses `propext`,
`Classical.choice`, and `Quot.sound`; the others use `propext` and
`Quot.sound`. No `sorryAx` or custom axiom occurs. The full build passes
(8,606 jobs). WP0195 records the module, its implications, and all nine
results. The source and rebuilt PDF are committed together.

Model discovery, future predictive validity, low residual complexity, and
physical availability of complementary records are not conclusions of these
implications. A model acquired during an episode remains among its later
records; using it as subsequent initial context changes the episode being
accounted for.
