# Sources, authorship, and verification

## Mathematical source

Itai Ashlagi, Mark Braverman, Amin Saberi, Clayton Thomas and Geng Zhao, *Tiered Random Matching Markets: Rank Is Proportional to Popularity*, [arXiv:2009.05124v2](https://arxiv.org/abs/2009.05124v2), 12 January 2021. The conference version appeared at [ITCS 2021, article 46](https://doi.org/10.4230/LIPIcs.ITCS.2021.46).

Definition 2.2 specifies the tiered model; footnote 5 permits integer rounding. Theorem 5.2 gives the fixed-agent match-type conclusion. Remark H.1 poses concentration of the realized table. The proof uses and formalizes the relevant proposal-process analysis, including the fixed-woman part of Proposition G.2, with explicit uniformity for rounded populations. The final concentration argument uses the independent reference coupling described in the proof guide.

This repository proves the conjectured concentration statement under the exact PR assumptions. It does not assert that this is the first solution in all subsequent literature. No comprehensive up-to-date priority search is claimed.

Deferred acceptance originates with David Gale and Lloyd Shapley, *College Admissions and the Stability of Marriage*, [American Mathematical Monthly 69 (1962), 9–15](https://doi.org/10.2307/2312726). Sylvain Mauras's [*Analysis of Random Models for Stable Matchings* (2021), Definition 3.2](https://www.irif.fr/~mauras/thesis/thesis.pdf), is the reference supplied by the reused weighted-ranking module.

## Previous Lean statement and reused definitions

The formal starting point is [Formal Conjectures PR #7841](https://github.com/google-deepmind/formal-conjectures/pull/7841), authored by `bocowgill`, at immutable commit `9f2a84284e69f992c113f894869cd7cdf292390f`. It states `Arxiv.«2009.05124».match_type_concentration` with an admitted proof.

The finite profile, weighted-ranking, and deferred-acceptance definitions are reused from that commit. They are retained under their source namespaces in `MarketModel.lean`, with compatibility imports at their original module paths in `FormalConjecturesForMathlib/` and `FormalConjectures/`. The repository includes only the needed model modules, rather than the larger conjecture collection. The original admitted theorem is not imported by the proof.

`Challenge.lean` reproduces the finite model in one Mathlib-only file. `Solution.lean` independently states the same theorem and supplies the completed proof through `Ashlagi.Complete.match_type_concentration`. The selected Comparator declaration retains the original theorem name and quantifiers.

The development was first checked with Lean 4.33.1. The submission repository ports it to Lean 4.35.0 with matching Mathlib. Porting updates renamed lemmas and measurability interfaces. Mathlib no longer supplies the old uniform probability-mass-function constructor; its occurrences are expressed using `PMF.ofFintype` with constant mass equal to the reciprocal cardinality, preserving the uniform distribution and the zero-weight fallback. Positive scores are required by the theorem. The source theorem's assumptions and conclusion are unchanged.

## Production and review

Bo Cowgill is the responsible author and maintainer. Codex helped me formalize the proof in Lean. Its role included Lean implementation, library search, compiler-guided checking, and audits of probability-law and statement alignment. Automated review examined the exponential-arrival law, the proposal estimates and their uniformity, and the final composition. These checks are distinct from human peer review; no independent human peer-review endorsement is claimed.

A paper presenting the proof is forthcoming. No publication date, venue, or unavailable manuscript is offered as evidence for the formal claim.

## What the verification establishes

The proof development has no unresolved `sorry` or `admit` terms and introduces no custom axioms. The final declaration's transitive axiom closure is limited to `propext`, `Classical.choice`, and `Quot.sound`. `Verification.lean` prints closures for the probability-law identity, the G.2 estimate, and the endpoint theorem.

Comparator compares the independent Challenge with the Solution, including the definitions on which their types depend. The complete Palomar mechanical preflight additionally enforces its dependency and source rules and replays the exported proof through its required independent checker. Passing local Lean checks is not Palomar registration, editorial acceptance, or a novelty certification. Submission and registration await the author's approval.

The root `LICENSE` is Apache-2.0. It covers this repository snapshot, while cited papers and external dependencies retain their own licenses. Original source headers and source credits are preserved; see `NOTICE`.
