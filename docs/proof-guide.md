# How the proof works

The final theorem is assembled in [Complete.lean](../Ashlagi/Complete.lean), and exposed for comparison in [Solution.lean](../Solution.lean). This guide describes the actual proof architecture. Supporting estimates are proved in Lean; Proposition G.2 is not an additional assumption of the final theorem.

## 1. Represent preferences without changing their law

Give each candidate an independent exponential clock whose rate is the candidate's positive public score. Earlier clock times give better ranks. Exponential races produce the same weighted ranking as sequential draws without replacement.

The proposal process reveals preferences adaptively. To use independent arrival streams, one must also show that assigning fresh randomness as the process runs preserves the joint law, and that the terminal prefixes correspond to the actual proposers. These are law and process identities, not informal independence assumptions.

Start with [IIDRanking.lean](../Ashlagi/IIDRanking.lean), [AdaptiveExposure.lean](../Ashlagi/AdaptiveExposure.lean), [ArrivalPolicy.lean](../Ashlagi/ArrivalPolicy.lean), [ArrivalPrefixes.lean](../Ashlagi/ArrivalPrefixes.lean), and [ConcreteLaw.lean](../Ashlagi/ConcreteLaw.lean). The latter contains `Ashlagi.Arrival.concreteArrivalProfile_market_law`.

## 2. Prove proposal-count concentration uniformly

For a woman in tier `i`, the relevant fixed-woman part of Proposition G.2 says that the number of proposals from men's tier `j` is concentrated around `cᵢⱼ log n`, where

$$
c_{ij}=\frac{\alpha_i}{\alpha_{\min}}
\frac{b_j/\beta_j}{\sum_h b_h/\beta_h}.
$$

The proof analyzes proposal streams with repeats, erases repeats to recover deferred acceptance, and controls both the proposal clock and repeated destinations. Continuation estimates from smooth partial matchings give the moment bounds needed for total proposal counts. A two-agent argument handles dependence. Deconditioning retains the common conditional-mean contribution to covariance; the proof uses the lower covariance bound needed by the subsequent concentration argument.

Uniformity matters because actual finite-population shares differ from their limiting values. The estimates are uniform on a positive neighborhood of the fixed limiting shares. Finite-population coefficients are then compared with the limiting coefficients. Scaling removes the auxiliary score normalization. No rate constant is silently allowed to depend on `n` through its rounded populations.

The principal entry points are [GlobalPairMoments.lean](../Ashlagi/GlobalPairMoments.lean), [G2Rounding.lean](../Ashlagi/G2Rounding.lean), [G2Scaling.lean](../Ashlagi/G2Scaling.lean), [G2Coefficients.lean](../Ashlagi/G2Coefficients.lean), and [G2Assembly.lean](../Ashlagi/G2Assembly.lean). The last supplies `uniform_vector_g2`, `uniform_g2_bound`, and `proposition_g2`.

## 3. Build independent reference outcomes

For each woman, take deterministic prefixes of the independent arrival streams, of lengths close to `cᵢⱼ log n` for each men's tier. The tier containing the earliest arrival wins. Because different women's reference rows use independent randomness, their reference indicators are independent.

Multiplying the prefix size by the exponential rate `βⱼ` cancels the factor `1/βⱼ` in `cᵢⱼ`. The reference winning-tier probability therefore tends to `bⱼ`. Averaging reference indicators over women's tier `i` gives a quantity whose expectation tends to `aᵢbⱼ` and whose variance is at most `1/(4n)`.

See [ReferenceModel.lean](../Ashlagi/ReferenceModel.lean), [ReferenceRace.lean](../Ashlagi/ReferenceRace.lean), and [RowIndependence.lean](../Ashlagi/RowIndependence.lean).

## 4. Transfer concentration to the actual matching

Proposition G.2 places the actual terminal proposal prefixes between deterministic lower and upper prefixes. If the earliest arrival in the upper prefixes is already in the lower prefixes, every intermediate prefix has the same winning tier. The probability that this fails is controlled by the intervening shell of arrivals. Its limiting bound tends to zero as the relative prefix tolerance tends to zero.

This comparison handles the dependence between a woman's stopping prefixes and her revealed preferences. It does not condition on the actual set of proposers and then presume independence. The expected fraction of actual outcomes that disagree with the independent reference outcomes tends to zero. Markov's inequality transfers reference concentration to the actual match table.

See [ArrivalBands.lean](../Ashlagi/ArrivalBands.lean), [ArrivalWinner.lean](../Ashlagi/ArrivalWinner.lean), [Transfer.lean](../Ashlagi/Transfer.lean), and [FinalCoupling.lean](../Ashlagi/FinalCoupling.lean). [Complete.lean](../Ashlagi/Complete.lean) supplies the proved G.2 estimate to finish the exact PR statement.
