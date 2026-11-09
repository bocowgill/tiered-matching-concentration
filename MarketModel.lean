/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.
-/
module

public import Mathlib

/-! # Finite tiered-market model

This is the independent Solution-side copy of the model stated in Challenge.lean.
The definitions are ported from the pinned Formal Conjectures source; see docs/provenance.md.
-/

@[expose] public section

open scoped ENNReal

/-!
# Stable marriage

A minimal finite model of the stable marriage problem with complete strict preferences.
-/

namespace StableMarriage

/-- A preference profile for `n` men and `n` women. Each permutation maps a candidate to their
rank, with lower ranks preferred. -/
structure Profile (n : ℕ) where
  /-- The rank that each man assigns to each woman. -/
  manRank : Fin n → Equiv.Perm (Fin n)
  /-- The rank that each woman assigns to each man. -/
  womanRank : Fin n → Equiv.Perm (Fin n)
  deriving Inhabited

/-- Preference profiles form a finite type. -/
instance {n : ℕ} : Fintype (Profile n) :=
  Fintype.ofEquiv
    ((Fin n → Equiv.Perm (Fin n)) × (Fin n → Equiv.Perm (Fin n)))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun p => (p.manRank, p.womanRank)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- A complete matching of `n` men to `n` women. -/
abbrev Matching (n : ℕ) := Equiv.Perm (Fin n)

/-- A man and woman form a blocking pair when they are not matched to each other and each ranks
the other above their current partner. -/
def IsBlockingPair {n : ℕ} (p : Profile n) (μ : Matching n) (m w : Fin n) : Prop :=
  μ m ≠ w ∧
    p.manRank m w < p.manRank m (μ m) ∧
      p.womanRank w m < p.womanRank w (μ.symm w)

/-- A matching is stable when it has no blocking pair. -/
def IsStable {n : ℕ} (p : Profile n) (μ : Matching n) : Prop :=
  ∀ m w, ¬ IsBlockingPair p μ m w

/-- The number of stable complete matchings for a preference profile. -/
noncomputable def numStableMatchings {n : ℕ} (p : Profile n) : ℕ := by
  classical
  exact Fintype.card {μ : Matching n // IsStable p μ}

/-- The discrete measurable structure on preference profiles. -/
instance {n : ℕ} : MeasurableSpace (Profile n) := ⊤

/-- The uniform probability mass function on preference profiles. -/
noncomputable def uniformProfile (n : ℕ) : PMF (Profile n) :=
  PMF.ofFintype (fun _ ↦ (Fintype.card (Profile n) : ℝ≥0∞)⁻¹)
    (by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (by simp) (by simp))

/-- The expected number of stable matchings under the uniform profile distribution. -/
noncomputable def expectedNumStableMatchings (n : ℕ) : ℝ :=
  ∫ p, (numStableMatchings p : ℝ) ∂((uniformProfile n).toMeasure)

end StableMarriage

/-!
# Deferred acceptance with complete strict preferences

A deterministic implementation of men-proposing deferred acceptance. At each step the first
unmatched man with an untried candidate proposes. There are at most $n^2$ proposals.

Reference: D. Gale and L. S. Shapley, *College Admissions and the Stability of Marriage*
(1962), https://doi.org/10.2307/2312726.
-/



namespace StableMarriage

/-- The proposal counters and the tentative partner held by each woman. -/
structure ProposalState (n : ℕ) where
  /-- Number of proposals already made by each man. -/
  next : Fin n → ℕ
  /-- Man whose proposal each woman currently holds. -/
  held : Fin n → Option (Fin n)

/-- One proposal, or no change if every man is matched or has exhausted his list. -/
def proposalStep {n : ℕ} (p : Profile n) (s : ProposalState n) : ProposalState n :=
  match (List.finRange n).find? (fun m ↦ s.next m < n ∧ ∀ w, s.held w ≠ some m) with
  | none => s
  | some m =>
    if h : s.next m < n then
      let w := (p.manRank m).symm ⟨s.next m, h⟩
      let accept := match s.held w with
        | none => true
        | some old => decide (p.womanRank w m < p.womanRank w old)
      ⟨Function.update s.next m (s.next m + 1),
        if accept then Function.update s.held w (some m) else s.held⟩
    else s

/-- The terminal state of men-proposing deferred acceptance, after $n^2$ possible proposals. -/
def deferredAcceptance {n : ℕ} (p : Profile n) : ProposalState n :=
  (proposalStep p)^[n * n] ⟨fun _ ↦ 0, fun _ ↦ none⟩

/-- The total number of proposals in men-proposing deferred acceptance. -/
def numProposals {n : ℕ} (p : Profile n) : ℕ :=
  ∑ m, (deferredAcceptance p).next m

/-- In the empty market no proposal is made. -/
theorem numProposals_zero (p : Profile 0) : numProposals p = 0 := by
  simp [numProposals]

/-- In the singleton market exactly one proposal is made. -/
theorem numProposals_one : numProposals (default : Profile 1) = 1 := by
  decide

/-- For two men, averaging over their four ranking profiles gives five halves proposals,
regardless of the women's rankings. -/
theorem proposal_sum_two :
    ∀ Q : Fin 2 → Equiv.Perm (Fin 2),
      ∑ P : Fin 2 → Equiv.Perm (Fin 2), numProposals ⟨P, Q⟩ = 10 := by
  decide

end StableMarriage

/-!
# Weighted random complete rankings

A ranking maps candidates to zero-based ranks. Its likelihood is the product of the probabilities
of successive draws without replacement, each proportional to the remaining candidates' weights.
All agents draw independently.

Reference: S. Mauras, *Analysis of Random Models for Stable Matchings* (2021), Definition 3.2,
https://www.irif.fr/~mauras/thesis/thesis.pdf.
-/



open scoped NNReal ENNReal

namespace RandomRanking

/-- A nonnegative finite weight vector induces a distribution after normalization.
If every weight is zero, use the uniform distribution. -/
noncomputable def ofWeights {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ≥0) : PMF α := by
  classical
  exact if h : ∑ a, f a = 0 then PMF.ofFintype (fun _ ↦ (Fintype.card α : ℝ≥0∞)⁻¹)
    (by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (by simp) (by simp)) else
    PMF.normalize (fun a ↦ (f a : ℝ≥0∞))
      (by
        rw [tsum_fintype, ← ENNReal.ofNNReal_finsetSum]
        exact fun hz ↦ h (ENNReal.coe_eq_zero.mp hz))
      (by
        rw [tsum_fintype, ← ENNReal.ofNNReal_finsetSum]
        exact ENNReal.coe_ne_top)

/-- Normalization divides each weight by the total weight when that total is nonzero. -/
theorem ofWeights_apply {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ≥0)
    (hf : ∑ a, f a ≠ 0) (a : α) :
    ofWeights f a = (f a : ℝ≥0∞) / (∑ b, f b : ℝ≥0) := by
  classical
  simp only [ofWeights, dite_eq_right hf, PMF.normalize_apply, tsum_fintype,
    ← ENNReal.ofNNReal_finsetSum, div_eq_mul_inv]

/-- Sampling-without-replacement likelihood of a complete ranking. Positive weights give the
usual product of successive choice probabilities. -/
noncomputable def likelihood {n : ℕ} (weight : Fin n → ℝ≥0)
    (rank : Equiv.Perm (Fin n)) : ℝ≥0 :=
  ∏ k, weight (rank.symm k) / ∑ x with k ≤ rank x, weight x

/-- Every complete ranking has positive likelihood when all candidates have positive weight. -/
theorem likelihood_pos {n : ℕ} (weight : Fin n → ℝ≥0) (hw : ∀ i, 0 < weight i)
    (rank : Equiv.Perm (Fin n)) : 0 < likelihood weight rank := by
  apply Finset.prod_pos
  intro k _
  apply div_pos (hw _)
  apply Finset.sum_pos'
  · intro i _
    exact le_of_lt (hw i)
  · exact ⟨rank.symm k, by simp, hw _⟩

/-- Independent weighted rankings on the two sides of a matching market.
The first matrix gives men's weights for women; the second gives women's weights for men,
with both matrices indexed by man then woman. -/
noncomputable def profile {n : ℕ} (P Q : Fin n → Fin n → ℝ≥0) :
    PMF (StableMarriage.Profile n) :=
  ofWeights fun p ↦ (∏ m, likelihood (P m) (p.manRank m)) *
    ∏ w, likelihood (fun m ↦ Q m w) (p.womanRank w)

/-- The weighted profile distribution has total mass one. -/
theorem profile_univ {n : ℕ} (P Q : Fin n → Fin n → ℝ≥0) :
    (profile P Q).toMeasure Set.univ = 1 := by
  simp

/-- An empty ranking has likelihood one. -/
theorem likelihood_zero (weight : Fin 0 → ℝ≥0) (rank : Equiv.Perm (Fin 0)) :
    likelihood weight rank = 1 := by
  simp [likelihood]

/-- A singleton ranking with positive weight has likelihood one. -/
theorem likelihood_one (weight : Fin 1 → ℝ≥0) (h : weight 0 ≠ 0) :
    likelihood weight (Equiv.refl _) = 1 := by
  simp [likelihood, h]

/-- With weights two and one, the identity ranking has probability two thirds. -/
theorem likelihood_two : likelihood ![2, 1] (Equiv.refl (Fin 2)) = 2 / 3 := by
  change (∏ k : Fin 2, (![2, 1] : Fin 2 → ℝ≥0) k /
    ∑ x : Fin 2 with k ≤ x, (![2, 1] : Fin 2 → ℝ≥0) x) = 2 / 3
  simp only [Fin.prod_univ_two]
  have hs : (∑ x : Fin 2 with (1 : Fin 2) ≤ x, (![2, 1] : Fin 2 → ℝ≥0) x) = 1 := by
    rw [Finset.sum_filter]
    norm_num [Fin.sum_univ_two]
  norm_num [Finset.sum_filter, Fin.sum_univ_two, hs]

/-- With weights two and one, the reverse ranking has probability one third. -/
theorem likelihood_two_swap : likelihood ![2, 1] (Equiv.swap (0 : Fin 2) 1) = 1 / 3 := by
  norm_num [likelihood, Fin.prod_univ_two, Finset.sum_filter, Fin.sum_univ_two]

end RandomRanking



open Filter
open scoped Topology NNReal

namespace Arxiv.«2009.05124»

/-- Number of couples between women's tier $i$ and men's tier $j$ under men-proposing DA. -/
noncomputable def matchCount {n I J : ℕ} (womanTier : Fin n → Fin I)
    (manTier : Fin n → Fin J) (i : Fin I) (j : Fin J)
    (p : StableMarriage.Profile n) : ℕ := by
  classical
  exact (Finset.univ.filter fun w ↦ womanTier w = i ∧
    ∃ m, (StableMarriage.deferredAcceptance p).held w = some m ∧ manTier m = j).card

/-- Independent rankings sampled proportionally to the public scores of the opposite side. -/
noncomputable def market {n I J : ℕ} (womanTier : Fin n → Fin I)
    (manTier : Fin n → Fin J) (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) :
    PMF (StableMarriage.Profile n) :=
  RandomRanking.profile (fun _ w ↦ α (womanTier w)) (fun m _ ↦ β (manTier m))

end Arxiv.«2009.05124»
