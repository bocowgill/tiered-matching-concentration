# Match-type concentration: mathematical argument

This guide presents the model, the quantitative estimates, and the argument connecting them to the theorem. The finite-process estimates in Section 3 are invoked as proved lemmas, with their hypotheses and quantifier order stated explicitly. Their formal proofs are linked below; the detailed finite-state continuation analysis is not reproduced line by line. In particular, the proposal-count estimate is a result of the development, not an additional assumption of the final theorem.

## 1. Model and theorem

There are $`n`$ men and $`n`$ women. Women's tiers are indexed by $`i=1,\ldots,I`$ and men's tiers by $`j=1,\ldots,J`$. The numbers of tiers are fixed. Their limiting population shares satisfy

```math
a_i>0,\qquad b_j>0,\qquad \sum_i a_i=\sum_j b_j=1.
```

Write $`W_i^{(n)}`$ and $`M_j^{(n)}`$ for the sets of agents in those tiers. Labels are deterministic and may vary arbitrarily with market size, subject to

```math
\bigl||W_i^{(n)}|-na_i\bigr|\le1,
\qquad
\bigl||M_j^{(n)}|-nb_j\bigr|\le1.
```

A woman in tier $`i`$ has public score $`\alpha_i>0`$; a man in tier $`j`$ has score $`\beta_j>0`$. Scores remain fixed as $`n`$ increases. Each participant independently generates a complete strict ranking by successive draws without replacement, with each remaining candidate's selection probability proportional to that candidate's score.

Run men-proposing deferred acceptance: an unmatched man proposes to his best untried candidate, and each woman retains her favorite proposal so far. Let $`X_{ij}^{(n)}`$ be the number of resulting couples between women's tier $`i`$ and men's tier $`j`$.

**Theorem.** For every fixed $`i,j`$ and every $`\varepsilon>0`$,

```math
\Pr_n\!\left(\left|X_{ij}^{(n)}/n-a_i b_j\right|>\varepsilon\right)
\longrightarrow0.
```

Here $`\Pr_n`$ is the independent-ranking law for the size-$`n`$ market. We do not require a common probability space across market sizes. Positivity and the rounding assumptions imply that every tier has linear size eventually. We work with these sufficiently large markets, so empty and singleton markets do not affect any limit.

The theorem is the additive, normalized form of the multiplicative concentration conjecture in Remark H.1 of [*Tiered Random Matching Markets: Rank Is Proportional to Popularity* (2021)](https://arxiv.org/abs/2009.05124v2). For fixed positive $`a_i b_j`$, relative tolerance $`r>0`$ corresponds to additive tolerance $`r a_i b_j`$.

## 2. An exact probability space for the proposal process

### Exponential races give the ranking law

For finitely many independent exponential variables $`E_x`$ of rates $`q_x>0`$,

```math
\Pr(E_x=\min_y E_y)
=\int_0^\infty q_xe^{-q_xt}\prod_{y\ne x}e^{-q_yt}\,dt
=\frac{q_x}{\sum_y q_y}.
```

After the first arrival, the residual clocks of the other candidates are independent exponentials with their original rates. Repeating this calculation shows that the probability of a ranking $`r`$ is exactly

```math
\prod_{k=0}^{n-1}
\frac{q_{r^{-1}(k)}}{\sum_{x:\,r(x)\ge k}q_x}.
```

This is the sampling-without-replacement likelihood used by the PR. Independent rows give the product profile law. Continuous clocks have no ties with probability one.

### Adaptive source allocation preserves that law

For each woman $`w`$ and each men's tier $`j`$, fix a deterministic ordering of that tier's labels and prepare independent source clocks

```math
E_{w,j,1},\ldots,E_{w,j,|M_j^{(n)}|}
\quad\text{with rate }\beta_j.
```

All these rows are independent, and they are independent of the men's rankings. On the first proposal by a new man in tier $`j`$ to $`w`$, assign him the next unused source in that block. Subsequent comparisons involving the same man use his assigned source, rather than drawing again.

The choice of which new coordinate to query is determined before its value is revealed. Given the revealed history, the next unused source is independent of that history and has the rate required by the queried man's tier. Induction over the queries therefore preserves the joint law of the revealed comparisons. Completing the unqueried coordinates gives the original independent profile law. At most $`n^2`$ distinct proposals are possible, so this induction has a deterministic finite horizon.

This also gives a pathwise identity. Let $`S_{wj}^{(n)}`$ be the number of distinct tier-$`j`$ men who propose to $`w`$. The sources used for those men are precisely the first $`S_{wj}^{(n)}`$ sources in block $`(w,j)`$. At termination, the tier of $`w`$'s partner is the tier containing the smallest used source clock. Assignment of sources stays within tiers, so this identity gives the actual partner's tier even though a source label need not be the proposing man's original label.

The law identity and the terminal-prefix identity are proved separately in [ConcreteLaw.lean](../TieredMatching/ConcreteLaw.lean), [ArrivalPolicy.lean](../TieredMatching/ArrivalPolicy.lean), [ArrivalPrefixes.lean](../TieredMatching/ArrivalPrefixes.lean), and [ArrivalWinner.lean](../TieredMatching/ArrivalWinner.lean). The identities do not assert that stopping counts are independent of the clocks they reveal.

## 3. Uniform finite-process estimates

We first state the estimates under score normalization. Multiplying every score on one side by the same positive constant leaves every ranking probability unchanged. Normalize women's minimum score and men's minimum score separately to one. Write $`u_w\in[1,A]`$ and $`v_m\in[1,B]`$ for the resulting individual scores, where $`A,B\ge1`$ are fixed.

Suppose at least $`\rho n`$ women have the minimum score one, for some fixed $`\rho>0`$. Set

```math
W\triangleq\sum_w u_w,\qquad
D\triangleq\sum_m v_m^{-1},\qquad
d_M\triangleq\frac{\sum_{m\in M}v_m^{-1}}{D}.
```

Let $`R_m`$ be man $`m`$'s number of genuine, distinct proposals and let $`S\triangleq\sum_m R_m`$. A raw proposal process allows repeated draws of a previously tried woman; erasing those draws recovers the ordinary proposal process. Write $`\tau`$ for its total raw draws and $`R\triangleq\tau-S`$ for its discarded repeats. The raw destination probabilities are $`q_w\triangleq u_w/W`$.

**Finite-process moment lemma.** For fixed $`A,B,\rho`$, there are finite constants and a common population threshold, independent of the labeled score vectors, such that

```math
\left|\mathbb ES-W\log n\right|\le C_0n,
\qquad
\mathrm{Var}(S)\le C_1n^2\log n,
\qquad
\mathbb ER\le C_2(\log n)^3,
```

and, for all men $`m,k`$,

```math
\left|v_m\mathbb ER_m-v_k\mathbb ER_k\right|\le K_0,
\qquad
\mathrm{Cov}(R_m,R_k)\ge-C_3\log n\quad(m\ne k).
```

The raw clock also satisfies

```math
\Pr(\tau>H)\le n\exp\!\left(-\frac{H}{An}\right).
```

The moment statements are [TotalMoments.eventually_uniform_total_moments](../TieredMatching/TotalMoments.lean) and [GlobalPairMoments.uniform_pair_moments](../TieredMatching/GlobalPairMoments.lean); the repeat and clock estimates are in [TotalMoments.lean](../TieredMatching/TotalMoments.lean). These are statements about the actual process, not a surrogate with independent assignments.

The raw clock is a weighted coupon-collection clock: the process ends when every woman has received a proposal. Each draw reaches $`w`$ with probability $`q_w`$, so a union bound gives

```math
\Pr(\tau>H)\le\sum_w(1-q_w)^H
\le n e^{-H/(An)},
```

because $`W\le An`$ and $`u_w\ge1`$. Minimum-score women supply the matching lower scale for the coupon clock. The formal moment proof combines this clock analysis with repeat estimates and individual proposal tails; a mean bound on repeats alone would not justify the variance estimate.

For the pair estimates, the formal proof exposes a partial matching before inserting two specified men. On the controlled setup states, the conditional initial proposal means share one inverse-popularity scale; the actual post-acceptance remainders have bounded conditional means. Exceptional states are controlled using proposal tails and clipping. This gives the unconditional weighted-mean comparison and covariance lower bound above. The setup, continuation, remainder, and mixture estimates are proved in [InitialAsymptotics.lean](../TieredMatching/InitialAsymptotics.lean), [RestAfterAcceptance.lean](../TieredMatching/RestAfterAcceptance.lean), [MixtureBounds.lean](../TieredMatching/MixtureBounds.lean), and [GlobalPairMoments.lean](../TieredMatching/GlobalPairMoments.lean).

The direction of the covariance estimate matters. If the conditional means are $`G(H)/v_m+e_m(H)`$ and $`G(H)/v_k+e_k(H)`$, with bounded errors and $`G(H)=O(\log n)`$, the covariance of these means contains

```math
\frac{\mathrm{Var}(G(H))}{v_mv_k}\ge0.
```

The cross terms involving the bounded errors are $`O(\log n)`$. Thus this common-mean variance can be retained to obtain a lower covariance bound. No unconditional small upper covariance is needed in the next step.

## 4. From total proposals to a fixed woman's proposals

Fix a proposer subset $`M`$ with $`|M|\ge\rho n`$, an equal-score set $`T`$ of women with $`|T|\ge\rho n`$, and a specified $`w\in T`$. Define

```math
U_M\triangleq\sum_{m\in M}R_m,
\qquad t_M\triangleq Wd_M\log n,
\qquad h_w\triangleq q_wt_M=u_wd_M\log n.
```

All bounds in this section are uniform in $`M,T,w`$ and the admissible score vectors.

### Concentration of the proposer subset's total

Let $`z_m\triangleq v_m\mathbb ER_m`$. The weighted-mean comparison in Section 3 implies that all $`z_m`$ lie in an interval of length at most $`K_0`$. Their reciprocal-score weighted average is

```math
\bar z=\frac{\sum_m z_m/v_m}{D}=\frac{\mathbb ES}{D}.
```

Hence $`|z_m-\bar z|\le K_0`$. Since $`v_m\ge1`$,

```math
\left|\mathbb EU_M-d_M\mathbb ES\right|
=\left|\sum_{m\in M}\frac{z_m-\bar z}{v_m}\right|
\le K_0n.
```

Combining this with the total mean estimate gives $`|\mathbb EU_M-t_M|\le Cn`$ for a fixed constant $`C`$.

For variance, put $`V_M\triangleq S-U_M`$. The lower pair covariance bound yields

```math
\mathrm{Cov}(U_M,V_M)
\ge-C_3|M||M^c|\log n\ge-C_3n^2\log n.
```

Because $`\mathrm{Var}(V_M)\ge0`$,

```math
\mathrm{Var}(U_M)
=\mathrm{Var}(S)-\mathrm{Var}(V_M)
 -2\mathrm{Cov}(U_M,V_M)
\le(C_1+2C_3)n^2\log n.
```

Moreover $`D\le n`$, $`\sum_{m\in M}v_m^{-1}\ge\rho n/B`$, and $`W\ge n`$, so

```math
d_M\ge\rho/B,\qquad t_M\ge(\rho/B)n\log n,
\qquad h_w\ge(\rho/B)\log n.
```

For each $`0<\eta\le1`$, the mean bias is eventually at most $`\eta t_M/2`$. Chebyshev's inequality then gives

```math
\Pr\bigl(|U_M-t_M|>\eta t_M\bigr)
\le\frac{C_4}{\eta^2\log n},
```

with $`C_4`$ independent of $`\eta`$. Only the eventual threshold depends on $`\eta`$. See [TierConcentration.lean](../TieredMatching/TierConcentration.lean).

### A predictable destination martingale and the repeat correction

Choose a deterministic raw horizon $`H=O(n\log n)`$ large enough that $`\Pr(\tau>H)\le n^{-4}`$. Before raw draw $`t`$, let $`I_t`$ indicate that the process is active and the selected man belongs to $`M`$. If $`\xi_t`$ is the fresh destination, then

```math
Z_H\triangleq\sum_{t<H}I_t\bigl(\mathbf1_{\{\xi_t=w\}}-q_w\bigr)
```

has mean zero. Selection is predictable and the fresh destination has conditional probability $`q_w`$, so martingale differences are orthogonal and $`\mathbb E Z_H^2\le Hq_w`$. Therefore

```math
\Pr(|Z_H|>x)\le Hq_w/x^2\qquad(x>0).
```

Let $`R_w`$ be the number of discarded repeats reaching $`w`$. Within the equal-score class $`T`$, relabeling symmetry makes $`\mathbb ER_w`$ the same for each woman. Since $`\sum_{w\in T}R_w\le R`$,

```math
\mathbb E(R_w+q_wR)
\le\left(\frac1{|T|}+q_w\right)\mathbb ER
\le C_5\frac{(\log n)^3}{n},
```

using $`q_w\le A/n`$. On $`\{\tau\le H\}`$, comparison of raw and distinct counts gives

```math
|S_{wM}-h_w|
\le |Z_H|+q_w|U_M-t_M|+R_w+q_wR,
```

where $`S_{wM}`$ counts distinct proposals from $`M`$ to $`w`$. Splitting the error allowance into three equal parts, using Chebyshev for $`Z_H`$ and Markov for the nonnegative repeat correction, gives

```math
\Pr(|S_{wM}-h_w|>\eta h_w)
\le n^{-4}
 +\frac{Hq_w}{(\eta h_w/3)^2}
 +\frac{C_4}{(\eta/3)^2\log n}
 +\frac{\mathbb E(R_w+q_wR)}{\eta h_w/3}.
```

Here $`Hq_w=O(\log n)`$ and $`h_w\ge(\rho/B)\log n`$. The last term is $`O((\log n)^2/(\eta n))`$. Since $`(\log n)^3\le n`$ eventually and $`\eta\le1`$, all four terms are bounded by

```math
\frac{K}{\eta^2\log n}.
```

One $`K=K(A,B,\rho)`$ works for every $`\eta\in(0,1]`$; for each tolerance there is a threshold uniform in all admissible vectors and specified agents. The raw law, predictability, repeat symmetry, and error decomposition are formalized in [GlobalDraws.lean](../TieredMatching/GlobalDraws.lean), [DestinationMartingale.lean](../TieredMatching/DestinationMartingale.lean), [LabelSymmetry.lean](../TieredMatching/LabelSymmetry.lean), and [G2Assembly.lean](../TieredMatching/G2Assembly.lean).

## 5. Rounding and the exact fixed-woman estimate

Return to the original tier scores. Write

```math
\alpha_*\triangleq\min_i\alpha_i>0,\qquad
D_b\triangleq\sum_h b_h/\beta_h>0,\qquad
c_{ij}\triangleq\frac{\alpha_i}{\alpha_*}
                 \frac{b_j/\beta_j}{D_b}>0.
```

Let $`a_i^{(n)}=|W_i^{(n)}|/n`$ and $`b_j^{(n)}=|M_j^{(n)}|/n`$. Rounding gives $`|a_i^{(n)}-a_i|,|b_j^{(n)}-b_j|\le1/n`$. Choose $`\rho>0`$ below half the smallest limiting share. All finite shares, including a minimum-score women's tier, are at least $`\rho`$ eventually.

Applied to the actual finite shares, Section 4 gives the same bound with coefficient

```math
c_{ij}^{(n)}=\frac{\alpha_i}{\alpha_*}
\frac{b_j^{(n)}/\beta_j}{\sum_h b_h^{(n)}/\beta_h}.
```

Its constant is fixed before the tolerance, market size, labels, and specified woman. Score normalization has not changed the law or this coefficient: multiplying all men's scores by one constant cancels between numerator and denominator, and multiplying women's scores cancels in $`\alpha_i/\alpha_*`$.

To compare coefficients, the denominator differs from $`D_b`$ by at most $`n^{-1}\sum_h\beta_h^{-1}`$. It is therefore at least $`D_b/2`$ eventually. Subtraction of the two fractions shows $`c_{ij}^{(n)}-c_{ij}=O(1/n)`$, with a fixed constant for the finite tier system.

For fixed $`\eta\in(0,1)`$, eventually

```math
|c_{ij}^{(n)}-c_{ij}|\le\eta c_{ij}/4,
\qquad c_{ij}^{(n)}\le2c_{ij}.
```

Consequently, if $`|S_{wj}^{(n)}-c_{ij}^{(n)}\log n|\le(\eta/4)c_{ij}^{(n)}\log n`$, then

```math
|S_{wj}^{(n)}-c_{ij}\log n|
\le(\eta/4)c_{ij}^{(n)}\log n
   +|c_{ij}^{(n)}-c_{ij}|\log n
\le(3\eta/4)c_{ij}\log n.
```

Thus the fixed-coefficient failure probability tends to zero uniformly over women in tier $`i`$ and men's tiers $`j`$. This is the fixed-woman assertion needed from G.2. It is **not** a claim that every woman simultaneously satisfies the bands with high probability; that would require a union bound over $`n`$ women which the estimate does not supply. The later argument needs only their average failure probability.

See [G2Rounding.lean](../TieredMatching/G2Rounding.lean), [G2Scaling.lean](../TieredMatching/G2Scaling.lean), and `proposition_g2` in [G2Assembly.lean](../TieredMatching/G2Assembly.lean).

## 6. Independent reference matches

Fix women's tier $`i`$. Put $`L_n\triangleq\log n`$ and define deterministic central counts

```math
k_{ij}^{0}(n)\triangleq\lfloor c_{ij}L_n\rfloor.
```

These counts are eventually positive and feasible: they grow logarithmically, whereas each men's tier has linear size. For each $`w\in W_i^{(n)}`$, let $`B_w^{(n)}`$ be the tier of the minimum clock among the first $`k_{ih}^{0}(n)`$ sources from every men's tier $`h`$. These reference labels use independent source rows and deterministic sets, so they are independent across women.

The exponential race identity gives, for all sufficiently large $`n`$,

```math
r_{ij}^{(n)}\triangleq\Pr(B_w^{(n)}=j)
=\frac{\beta_j k_{ij}^{0}(n)}{\sum_h\beta_h k_{ih}^{0}(n)}.
```

Since $`k_{ij}^{0}(n)/L_n\to c_{ij}`$ and

```math
\beta_jc_{ij}=\frac{\alpha_i}{\alpha_*}\frac{b_j}{D_b},
\qquad
\sum_h\beta_hc_{ih}=\frac{\alpha_i}{\alpha_*D_b},
```

we have $`r_{ij}^{(n)}\to b_j`$. Define the reference frequency, normalized by all couples, by

```math
Y_{ij}^{(n)}\triangleq\frac1n\sum_{w\in W_i^{(n)}}
\mathbf1_{\{B_w^{(n)}=j\}}.
```

Then $`\mathbb EY_{ij}^{(n)}=(|W_i^{(n)}|/n)r_{ij}^{(n)}\to a_i b_j`$. Independence and the Bernoulli variance bound give

```math
\mathrm{Var}(Y_{ij}^{(n)})
\le\frac{|W_i^{(n)}|}{4n^2}\le\frac1{4n}.
```

Thus $`Y_{ij}^{(n)}\to a_i b_j`$ in probability. These are the reference mean and variance results in [ReferenceModel.lean](../TieredMatching/ReferenceModel.lean) and [RowIndependence.lean](../TieredMatching/RowIndependence.lean).

## 7. A sandwich bounds disagreement without conditioning on proposer sets

Fix $`0<\eta<1`$. Define lower and upper counts by

```math
k_{ij}^-(n)\triangleq\lfloor(1-\eta)c_{ij}L_n\rfloor,
\qquad
k_{ij}^+(n)\triangleq\lceil(1+\eta)c_{ij}L_n\rceil.
```

Central counts lie between them, and upper counts are feasible eventually. Let $`A_i^-,A_i^0,A_i^+`$ be the corresponding deterministic source sets for a woman in tier $`i`$. Let $`G_w^{(n)}(\eta)`$ be the event that every actual count $`S_{wj}^{(n)}`$ lies between its lower and upper count. Section 5 and a union bound over the fixed finite number of men's tiers imply

```math
d_n(\eta)\triangleq
\sup_{w\in W_i^{(n)}}\Pr(G_w^{(n)}(\eta)^c)\longrightarrow0.
```

On $`G_w^{(n)}(\eta)`$, the actual used set lies between $`A_i^-`$ and $`A_i^+`$. If the unique minimum over $`A_i^+`$ belongs to $`A_i^-`$, that same source is the minimum of every intermediate set, including the actual and central sets. Therefore disagreement between actual and reference partner tiers is contained in band failure or the shell event

```math
Q_w^{(n)}(\eta)\triangleq
\{\arg\min_{x\in A_i^+}E_{w,x}\notin A_i^-\}.
```

For deterministic nested sets, the race identity gives the exact shell probability

```math
s_n(\eta)\triangleq\Pr(Q_w^{(n)}(\eta))
=1-\frac{\sum_h\beta_h k_{ih}^-(n)}
          {\sum_h\beta_h k_{ih}^+(n)}
\longrightarrow1-\frac{1-\eta}{1+\eta}
=\frac{2\eta}{1+\eta}.
```

This calculation is unconditional. The actual counts depend on the clocks; we have not conditioned on them and then asserted independence.

Let $`F_{ij}^{(n)}\triangleq X_{ij}^{(n)}/n`$, evaluated on the exact source construction of Section 2. Pointwise, the absolute difference of the actual and reference tier-$`j`$ indicators is bounded by the indicator that the full tier labels disagree. Averaging and taking expectations gives

```math
e_n\triangleq\mathbb E|F_{ij}^{(n)}-Y_{ij}^{(n)}|
\le\frac{|W_i^{(n)}|}{n}\bigl(d_n(\eta)+s_n(\eta)\bigr)
\le d_n(\eta)+s_n(\eta).
```

The left side uses the fixed central counts and does not depend on $`\eta`$. For every fixed $`\eta\in(0,1)`$,

```math
0\le\limsup_{n\to\infty}e_n\le\frac{2\eta}{1+\eta}.
```

Letting $`\eta\downarrow0`$ proves $`e_n\to0`$. The order is important: first take the market-size limit with fixed tolerance; then let the tolerance decrease. No rate uniform in a shrinking tolerance is required.

See [Sandwich.lean](../TieredMatching/Sandwich.lean), [ArrivalBands.lean](../TieredMatching/ArrivalBands.lean), and `couplingError_tendsto_zero_of_propositionG2` in [FinalCoupling.lean](../TieredMatching/FinalCoupling.lean).

## 8. Complete the probability limit

Fix $`\varepsilon>0`$. Eventually $`|\mathbb EY_{ij}^{(n)}-a_i b_j|\le\varepsilon/3`$. Markov's inequality for the coupling error and Chebyshev's inequality for the reference frequency then give

```math
\begin{aligned}
\Pr_n\bigl(|F_{ij}^{(n)}-a_i b_j|>\varepsilon\bigr)
&\le\Pr_n\bigl(|F_{ij}^{(n)}-Y_{ij}^{(n)}|>\varepsilon/3\bigr)
 +\Pr_n\bigl(|Y_{ij}^{(n)}-\mathbb EY_{ij}^{(n)}|>\varepsilon/3\bigr)\\
&\le\frac{3e_n}{\varepsilon}
 +\frac{9\mathrm{Var}(Y_{ij}^{(n)})}{\varepsilon^2}\\
&\le\frac{3e_n}{\varepsilon}+\frac{9}{4n\varepsilon^2}
\longrightarrow0.
\end{aligned}
```

The source profile has exactly the PR market law, so this is the required probability limit for the original model. The argument is assembled in [Complete.lean](../TieredMatching/Complete.lean) and exported as `TieredMatching.match_type_concentration` in [Solution.lean](../Solution.lean).

Because the table has finitely many cells, a finite union bound also gives simultaneous convergence of the table. This is a consequence of the cellwise theorem, rather than an additional exported declaration.

The economic cancellation is visible in Section 6: proposal counts have a reciprocal men's-score factor, while winning an exponential race weights each proposal by that score. Those factors cancel in the limiting tier composition. The proof establishes aggregate composition; it does not make individual assignments uniform or partner ranks independent of popularity.

Codex helped me formalize the proof in Lean.
