# The exact statement

The recorded declaration is `Arxiv.«2009.05124».match_type_concentration`. It is stated independently in [Challenge.lean](../Challenge.lean) and proved in [Solution.lean](../Solution.lean). Its mathematical content is the statement in [Formal Conjectures PR #7841 at commit 9f2a84284e69f992c113f894869cd7cdf292390f](https://github.com/google-deepmind/formal-conjectures/blob/9f2a84284e69f992c113f894869cd7cdf292390f/FormalConjectures/Arxiv/2009.05124/TieredRandomMatching.lean).

## Assumptions, in order

1. Choose finite numbers of women's and men's tiers, `I` and `J`.
2. Choose positive shares `a : Fin I → ℝ` and `b : Fin J → ℝ`, each summing to one.
3. Choose strictly positive public scores `α : Fin I → ℝ≥0` and `β : Fin J → ℝ≥0`. Scores need not be distinct, ordered, or normalized.
4. For every natural number `n`, choose labels `womanTier n` and `manTier n` for the `n` participants on each side. For every tier, its cardinality differs from `n` times its share by at most one.
5. Choose tiers `i`, `j` and a positive tolerance `ε`.

The probability of `|Xᵢⱼ/n − aᵢbⱼ| ≤ ε` then tends to one as `n` tends to infinity. The limiting shares, scores, and numbers of tiers are chosen before the limit. The integer labels can vary arbitrarily with `n`, subject to the bounds. No random population labels, divisibility condition, additional score normalization, or assumed concentration lemma is required.

## The probability law

A ranking is a permutation assigning each candidate a zero-based rank; smaller ranks are better. If `r` is a ranking and candidate `x` has weight `q(x)`, its likelihood is

$$
L_q(r)=\prod_{k=0}^{n-1}
\frac{q(r^{-1}(k))}{\sum_{x:\,r(x)\geq k}q(x)}.
$$

The profile law normalizes the product of these row likelihoods. Men's weights for a woman are her tier's score `α`; women's weights for a man are his tier's score `β`. With positive scores, these are the independent weighted rankings obtained by draws without replacement. [ConcreteLaw.lean](../Ashlagi/ConcreteLaw.lean) proves equality of the exponential-arrival construction with this exact profile law; the proof does not replace it with independent pair assignments.

`matchCount` runs the stated men-proposing deferred-acceptance algorithm and counts women of tier `i` whose held proposal at termination comes from a man of tier `j`. The algorithm selects the first unmatched man, in label order, with an untried candidate. It permits at most `n²` proposals. The proof development verifies termination and the matching properties needed for the count.

## Relation to Remark H.1

The source writes women's shares as `εᵢ` and men's shares as `δⱼ`; here they are `aᵢ` and `bⱼ`. It conjectures multiplicative concentration around `aᵢbⱼ n`. The PR uses an arbitrary positive additive tolerance after division by `n`. These formulations are equivalent because every product `aᵢbⱼ` is fixed and strictly positive: use additive tolerance `r aᵢbⱼ` for any relative tolerance `r>0`, and conversely use `r=ε/(aᵢbⱼ)`.

The at-most-one rounding convention makes the integer populations explicit. It follows the convention in Definition 2.2, footnote 5 of the full source. The fixed-woman estimate from G.2 is proved with constants and thresholds that are uniform over the relevant finite-market share vectors, rather than applied to changing shares with an unspecified dependence of constants.

## Small markets and scope

The sequences include `n=0`; the empty profile and empty matching are well-defined, and Lean's division by zero is defined. No conclusion about that single market is needed for a limit at infinity. At `n=1`, exactly one couple forms. A tier can be empty in a small market under the rounding bounds; strict positivity of its limiting share makes it nonempty eventually. A zero number of tiers is incompatible with positive shares summing to one, so it introduces no substantive exception.

The recorded theorem is cellwise convergence in probability. Simultaneous convergence of the finite table follows mathematically by a finite union bound. The repository does not advertise an explicit finite-market error rate for the final table, almost-sure convergence, or a statement about every stable matching.
