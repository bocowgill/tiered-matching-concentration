# Concentration of match types in tiered random matching markets

This repository proves concentration of match types in balanced random matching markets with a fixed finite tier structure. With independent popularity-based preferences and fixed positive tier shares and scores, the fraction of couples joining any two tiers converges in probability to the product of their population shares under men-proposing deferred acceptance.

The result resolves the concentration statement posed in Remark H.1 of [*Tiered Random Matching Markets: Rank Is Proportional to Popularity* (2021)](https://arxiv.org/abs/2009.05124v2), by Itai Ashlagi, Mark Braverman, Amin Saberi, Clayton Thomas, and Geng Zhao. This repository contains the Lean proof of the exact formulation in [Formal Conjectures PR #7841](https://github.com/google-deepmind/formal-conjectures/pull/7841).

## The economic question

A matching assigns each participant on one side of a market to one participant on the other. A matching is **stable** if there is no pair who would both prefer one another to their assigned partners. Stability is central to the economics of market design because such a pair would have a reason to leave their assignments.

Here the two sides are called men and women, following the source. The market has equally many participants on each side, complete rankings, and one-to-one assignments. **Deferred acceptance** proceeds by proposals: an unmatched man proposes to his most preferred woman who has not rejected him; each woman keeps her favorite proposal so far and rejects the rest. The process ends when everyone is matched. We study this particular, men-proposing outcome.

Participants belong to finitely many **tiers**. A tier is a group with a common positive public score. It is not a rule requiring participants to rank everyone in one tier above everyone in another. Instead, each participant builds a ranking by repeatedly selecting an as-yet unranked candidate with probability proportional to that candidate's score. A score of two gives a candidate twice the selection weight of a candidate with score one at each such draw. Every participant's ranking is drawn independently.

For economists, this is a popularity-based random preference model, with sequential choices of the multinomial-logit form. It combines a common component of attractiveness with individual differences. The theorem asks what happens to the **composition of the resulting matches**, after the proposal process has linked everyone's decisions.

## What is proved

Let $`a_i`$ be the population share of women's tier $`i`$, and $`b_j`$ the share of men's tier $`j`$. Let $`X_{ij}^{(n)}`$ count couples between those tiers in a market with $`n`$ participants on each side. Then, for every fixed pair of tiers and every $`\varepsilon>0`$,

$$
\Pr\!\left(\left|\frac{X_{ij}^{(n)}}{n}-a_i b_j\right|\leq\varepsilon\right)
\longrightarrow 1.
$$

All tier shares and scores are fixed and strictly positive as $`n`$ grows. Each side has a fixed finite number of tiers. Integer tier sizes may differ from their prescribed shares times $`n`$ by at most one. The conclusion holds for every sequence of tier labels satisfying those bounds. Since there are only finitely many cells, the entire table also converges jointly by a finite union bound; the recorded Lean theorem states the result for each cell.

For example, suppose women's tier shares are 60% and 40%, and men's are 30% and 70%. The limiting table, expressed as shares of **all couples**, is:

| | Men's tier 1 | Men's tier 2 | Total |
|---|---:|---:|---:|
| Women's tier 1 | 18% | 42% | 60% |
| Women's tier 2 | 12% | 28% | 40% |
| Total | 30% | 70% | 100% |

Thus, among women in either tier, the limiting shares of partners from the two men's tiers are 30% and 70%. The table is a limit in probability, not an exact prediction for a finite market. The public scores can differ across tiers while remaining fixed positive numbers.

This is an aggregate composition result. It does not give a uniform random assignment of individual partners or make partner ranks and welfare independent of attractiveness. It concerns balanced, complete-list, one-to-one markets under the stated random preferences. It does not cover growing numbers of tiers, scores that change with market size, incomplete lists, or unbalanced markets.

## Why concentration is the missing step

The source's Theorem 5.2 addresses a fixed woman's probability of matching to a men's tier. Remark H.1 asks for the realized market-wide table to concentrate. Expected proportions alone do not establish that conclusion: many outcomes can move together. The proof must control the dependence created by the proposal process.

The formal proof constructs independent exponential-arrival streams with exactly the original ranking law. It proves the fixed-woman proposal-count estimate needed from Proposition G.2, uniformly over the allowed rounded populations. It then couples actual outcomes to independent reference outcomes. Concentration of the reference averages and a vanishing coupling error yield the claimed table. [The expanded proof guide](docs/proof-guide.md) states the decisive estimates and derives the result, including the rounding argument, coupling calculation, and final probability bound, with links to the Lean proofs.

## Supporting results

The proof library also establishes the following results:

| Result | What is proved | Lean source |
|---|---|---|
| Exact preference law | The exponential-arrival construction induces exactly the original weighted-ranking profile law, including under adaptive proposal selection. | [ConcreteLaw.lean](TieredMatching/ConcreteLaw.lean) |
| Uniform proposal counts | For a fixed woman, proposal counts from each men's tier concentrate around their logarithmic scale, with uniformity over the allowed rounded populations. | [G2Assembly.lean](TieredMatching/G2Assembly.lean) |
| Transfer to actual matches | A coupling to independent reference outcomes transfers proposal-count concentration to concentration of the realized match table. | [FinalCoupling.lean](TieredMatching/FinalCoupling.lean) |

These are supporting results in the Lean library. The main theorem selected by [comparator.json](comparator.json) is [`TieredMatching.match_type_concentration`](Solution.lean); the supporting results are not separate Comparator selections.

## Reading and checking the repository

No knowledge of Lean is needed to read the explanation above. For further detail:

- [Exact statement and correspondence with the source](docs/statement.md): assumptions, rounding, probability law, and Lean notation.
- [Expanded proof guide](docs/proof-guide.md): the mathematical argument, quantitative estimates, and their Lean references.
- [Provenance and production account](docs/provenance.md): sources, attribution, review, and scope.
- [Literature context](docs/literature.md): the concentration question and related results.
- [Challenge.lean](Challenge.lean): the complete auditable model and theorem statement; imports Mathlib alone.
- [Solution.lean](Solution.lean): the same statement with its proof, importing the substantive development in [TieredMatching/](TieredMatching/).
- [formalization.yaml](formalization.yaml): structured metadata for Palomar.

Lean is a proof assistant: it checks that a proof term has the stated type. Palomar's Comparator checks that the proved declaration implements the independently compiled statement, with only the permitted axioms. The deliberate `sorry` in `Challenge.lean` marks the question to be compared; the Solution and its proof dependencies contain no unresolved proof holes.

Install [elan](https://github.com/leanprover/elan), then run from this directory:

```sh
lake exe cache get
lake --wfail build TieredMatching Challenge Solution Verification
lake env lean Verification.lean
lake comparator --config comparator.json
```

The project pins Lean 4.35.0 and its matching Mathlib revision. The only permitted axioms are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. The [Palomar preflight workflow](.github/workflows/palomar-preflight.yml) runs their complete mechanical checks against the exact commit. A local build is not a substitute for that workflow or for Palomar review.

The code is licensed under [Apache-2.0](LICENSE); see [NOTICE](NOTICE) for reused source provenance.

## Notes

Codex helped me formalize the proof in Lean.
A paper presenting the proof is forthcoming.
