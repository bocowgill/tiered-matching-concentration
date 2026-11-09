/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import TieredMatching.G2Rounding
public import TieredMatching.TierConcentration
public import TieredMatching.ProposalCounts
public import TieredMatching.ReferenceModel

/-! # Exact vector-to-tier coefficients for Proposition G.2

The uniform score-vector estimate is defined as a property, not asserted as a theorem here.
Its implication to the exact normalized tier statement is proved by finite grouping and the
unchanged PR proposal-count and market identities.
-/

@[expose] public section

namespace TieredMatching

open StableMarriage MeasureTheory
open scoped ENNReal NNReal

/-- Uniform vector-form G.2 on normalized scores, with a constant preceding the tolerance.
The original-profile process estimate remains an explicit premise of the transfer theorem. -/
def UniformVectorG2 (A B : ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ K : ℝ, 0 < K ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 2 ≤ n →
      ∀ (a b : Fin n → ℝ≥0),
      (∀ w, 1 ≤ (a w : ℝ)) → (∀ w, (a w : ℝ) ≤ A) →
      (∀ m, 1 ≤ (b m : ℝ)) → (∀ m, (b m : ℝ) ≤ B) →
      ρ * n ≤ ((CouponMoments.minimumCoupons a).card : ℝ) →
      ∀ J T : Finset (Fin n), ρ * n ≤ (J.card : ℝ) → ρ * n ≤ (T.card : ℝ) →
      (∀ x ∈ T, ∀ y ∈ T, a x = a y) → ∀ w ∈ T,
      (VisitBounds.profileLaw a b).toMeasure
        {p | |(ProposalCounts.genuineWomanCount p J w : ℝ) -
            (a w : ℝ) * TierConcentration.share b J * Real.log n| >
          η * ((a w : ℝ) * TierConcentration.share b J * Real.log n)} ≤
        ENNReal.ofReal (K / (η ^ 2 * Real.log n))

namespace G2Coefficients

/-- Each exact finite tier size is population times its exact finite share. -/
theorem tier_card_eq {n K : ℕ} (tier : Fin n → Fin K) (hn : 0 < n) (k : Fin K) :
    ((Arrival.tierMen tier k).card : ℝ) = (n : ℝ) * tierShare tier k := by
  rw [ReferenceModel.tierMen_card_eq]
  unfold tierShare
  field_simp


/-- Every reciprocal-score tier weight is exactly its finite tier size over its score. -/
theorem reciprocal_tier {n K : ℕ} (tier : Fin n → Fin K) (β : Fin K → ℝ≥0) (j : Fin K) :
    TierConcentration.weight (fun m ↦ β (tier m)) (Arrival.tierMen tier j) =
      ((Arrival.tierMen tier j).card : ℝ) / (β j : ℝ) := by
  classical
  unfold TierConcentration.weight
  have he (m : Fin n) (hm : m ∈ Arrival.tierMen tier j) : tier m = j :=
    (Finset.mem_filter.mp hm).2
  simp only [Finset.sum_congr rfl (fun m hm ↦ congrArg (fun k ↦ ((β k : ℝ)⁻¹)) (he m hm))]
  simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- The exact reciprocal-score denominator is population times the grouped tier denominator. -/
theorem reciprocal_total {n K : ℕ} (tier : Fin n → Fin K) (β : Fin K → ℝ≥0) :
    (∑ m : Fin n, 1 / (β (tier m) : ℝ)) =
      (n : ℝ) * ∑ j, tierShare tier j / (β j : ℝ) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  calc
    _ = ∑ j, ∑ m ∈ Arrival.tierMen tier j, (1 / (β (tier m) : ℝ)) :=
      (Finset.sum_fiberwise Finset.univ tier _).symm
    _ = ∑ j, ((Arrival.tierMen tier j).card : ℝ) / (β j : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      simpa only [TierConcentration.weight, one_div] using reciprocal_tier tier β j
    _ = _ := by
      simp_rw [tier_card_eq tier hn0]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Finite tier reciprocal shares equal the source coefficient's normalized tier shares. -/
theorem share_tier {n K : ℕ} (tier : Fin n → Fin K) (β : Fin K → ℝ≥0)
    (hn : 0 < n) (j : Fin K) :
    TierConcentration.share (fun m ↦ β (tier m)) (Arrival.tierMen tier j) =
      (tierShare tier j / (β j : ℝ)) / ∑ k, tierShare tier k / (β k : ℝ) := by
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold TierConcentration.share
  rw [reciprocal_tier, tier_card_eq tier hn]
  have ht : TierConcentration.weight (fun m ↦ β (tier m)) Finset.univ =
      (n : ℝ) * ∑ k, tierShare tier k / (β k : ℝ) := by
    simpa only [TierConcentration.weight, one_div] using reciprocal_total tier β
  rw [ht]
  have he : (n : ℝ) * tierShare tier j / (β j : ℝ) =
      (n : ℝ) * (tierShare tier j / (β j : ℝ)) := by ring
  rw [he, mul_div_mul_left _ _ hN]

/-- The vector fixed-woman leading coefficient is exactly normalized source G.2's coefficient. -/
theorem vector_coefficient {n I J : ℕ} (womanTier : Fin n → Fin I)
    (manTier : Fin n → Fin J) (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (hn : 0 < n) (i : Fin I) (w : Fin n) (hw : womanTier w = i) (j : Fin J) :
    (α (womanTier w) : ℝ) * TierConcentration.share (fun m ↦ β (manTier m))
        (Arrival.tierMen manTier j) = proposalCoefficient (tierShare manTier) α β 1 i j := by
  rw [hw, share_tier manTier β hn]
  unfold proposalCoefficient
  ring

/-- A tier's positive share fence implies the exact finite cardinal fence. -/
theorem tier_card_fence {n K : ℕ} (tier : Fin n → Fin K) (hn : 0 < n)
    {ρ : ℝ} (hρ : ∀ k, ρ ≤ tierShare tier k) (k : Fin K) :
    ρ * n ≤ ((Arrival.tierMen tier k).card : ℝ) := by
  rw [tier_card_eq tier hn]
  nlinarith [mul_le_mul_of_nonneg_left (hρ k) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- An attained score-one tier supplies the vector coupon hypothesis in every finite market. -/
theorem minimumCoupons_fence {n I : ℕ} (womanTier : Fin n → Fin I)
    (α : Fin I → ℝ≥0) (hn : 0 < n) (hmin : IsMinimumScore α 1)
    {ρ : ℝ} (hshare : ∀ i, ρ ≤ tierShare womanTier i) :
    ρ * n ≤ ((CouponMoments.minimumCoupons (fun w ↦ α (womanTier w))).card : ℝ) := by
  classical
  obtain ⟨i, hi⟩ := hmin.2
  have hαi : α i = 1 := NNReal.coe_eq_one.mp hi.symm
  have hsub : Arrival.tierMen womanTier i ⊆
      CouponMoments.minimumCoupons (fun w ↦ α (womanTier w)) := by
    intro w hw
    have he := (Finset.mem_filter.mp hw).2
    simp only [CouponMoments.minimumCoupons, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [he, hαi]
  exact (tier_card_fence womanTier hn hshare i).trans
    (by exact_mod_cast Finset.card_le_card hsub)


end G2Coefficients

/-- The vector-form process estimate implies the exact normalized tier-form G.2 bound.
All size fences and coefficients use actual finite tier cardinalities. -/
theorem UniformVectorG2.uniformG2Bound {A B : ℝ} (h : UniformVectorG2 A B)
    {I J : ℕ} (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (hαA : ∀ i, (α i : ℝ) ≤ A) (hβ1 : ∀ j, 1 ≤ (β j : ℝ))
    (hβB : ∀ j, (β j : ℝ) ≤ B) (hmin : IsMinimumScore α 1) :
    UniformG2Bound α β 1 := by
  classical
  intro ρ hρ
  obtain ⟨K, hK, hbound⟩ := h ρ hρ
  refine ⟨K, hK, ?_⟩
  intro η hη hη1
  obtain ⟨N, hN⟩ := hbound η hη hη1
  refine ⟨N, ?_⟩
  intro n hn hn2 womanTier manTier hwa hma _hwaSum _hmaSum i w hw j
  have hn0 : 0 < n := by omega
  let a : Fin n → ℝ≥0 := fun x ↦ α (womanTier x)
  let b : Fin n → ℝ≥0 := fun m ↦ β (manTier m)
  let Jset := Arrival.tierMen manTier j
  let T := Arrival.tierMen womanTier i
  have hJ : ρ * n ≤ (Jset.card : ℝ) := G2Coefficients.tier_card_fence manTier hn0 hma j
  have hT : ρ * n ≤ (T.card : ℝ) := G2Coefficients.tier_card_fence womanTier hn0 hwa i
  have hconst : ∀ x ∈ T, ∀ y ∈ T, a x = a y := by
    intro x hx y hy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    dsimp only [a]
    rw [hx', hy']
  have hwT : w ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
  have hprocess := hN n hn hn2 a b (fun x ↦ hmin.1 (womanTier x))
    (fun x ↦ hαA (womanTier x)) (fun m ↦ hβ1 (manTier m)) (fun m ↦ hβB (manTier m))
    (G2Coefficients.minimumCoupons_fence womanTier α hn0 hmin hwa)
    Jset T hJ hT hconst w hwT
  have hc := G2Coefficients.vector_coefficient womanTier manTier α β hn0 i w hw j
  change (VisitBounds.profileLaw a b).toMeasure
    {p | |(ProposalCounts.genuineWomanCount p Jset w : ℝ) -
      ((a w : ℝ) * TierConcentration.share b Jset) * Real.log n| >
      η * (((a w : ℝ) * TierConcentration.share b Jset) * Real.log n)} ≤ _ at hprocess
  change (VisitBounds.profileLaw a b).toMeasure
    {p | |(proposalCount manTier j p w : ℝ) -
      proposalCoefficient (tierShare manTier) α β 1 i j * Real.log n| >
      η * (proposalCoefficient (tierShare manTier) α β 1 i j * Real.log n)} ≤ _
  change (a w : ℝ) * TierConcentration.share b Jset =
    proposalCoefficient (tierShare manTier) α β 1 i j at hc
  rw [hc] at hprocess
  simpa only [Jset, Arrival.tierMen,
    ProposalCounts.genuineWomanCount_eq_proposalCount] using hprocess

end TieredMatching
