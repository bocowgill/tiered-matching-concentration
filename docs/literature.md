# Where the result fits

The research question belongs to probabilistic matching theory and the economics
of market design. A stable matching uses everyone's preferences at once, so
independent preference draws can generate dependent assignments. Understanding
which aggregate outcomes nevertheless become predictable is the central issue
here.

The following sources distinguish the specific contribution from nearby work:

| Source | Result or role | Relation to this repository |
|---|---|---|
| Gale and Shapley (1962), [*College Admissions and the Stability of Marriage*](https://doi.org/10.2307/2312726) | Deferred acceptance and stable matching | Supplies the underlying allocation procedure. |
| Pittel (1989), [*The Average Number of Stable Matchings*](https://doi.org/10.1137/0402048) | Asymptotic analysis of uniformly random stable marriage, including partner ranks | Background for the random-market approach; the present preferences allow common popularity differences. |
| Ashlagi, Braverman, Saberi, Thomas and Zhao (2021), [*Tiered Random Matching Markets*](https://arxiv.org/abs/2009.05124v2) | Tiered popularity preferences, proposal and rank estimates, a fixed-agent match-type result, and the realized-table conjecture | Direct mathematical source. Theorem 5.2 and Remark H.1 separate the known marginal result from the concentration question addressed here. |
| [Formal Conjectures PR #7841](https://github.com/google-deepmind/formal-conjectures/pull/7841) | Lean statement of the realized-table concentration conjecture | The exact statement and finite probability model used for this proof. |

There are three distinctions to keep in view. First, **rank** asks how high an
assigned partner appears in someone's preference list; **match type** asks which
population tier that partner belongs to. Second, a fixed participant's marginal
probability does not by itself give concentration of the realized table. Third,
balanced markets, fixed positive scores, and complete preference lists are
substantive assumptions of the theorem.

The contribution presented here is the completed Lean proof of that exact
concentration statement, including the exact-law representation and the
rounded-population uniformity required by its proposal estimate. The formal
development contains the estimates it uses; it does not assume the cited
probabilistic results as additional axioms. A paper presenting the proof is
forthcoming.

Targeted searches on 9 November 2026 for the paper title, Remark H.1, and
match-type concentration located the source and the Formal Conjectures problem.
This is not a comprehensive literature or priority determination. The claim
here is that the stated conjecture is proved, without asserting first-solution
priority or that no other proof exists.
