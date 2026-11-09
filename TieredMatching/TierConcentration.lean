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

public import TieredMatching.TotalMoments
public import TieredMatching.G2Deconditioning

/-! # Tier concentration from explicit actual-profile moment inputs

This is a conditional reduction. Popularity-weighted individual means and distinct-pair
covariance lower bounds remain explicit inputs awaiting the finite-state moment assembly.
The total moments are the proved bounds for the original PR preference-profile law.
-/

@[expose] public section

namespace TieredMatching.TierConcentration

open MeasureTheory ProbabilityTheory StableMarriage Filter
open scoped ENNReal NNReal Topology

/-- The exact ordinary proposal count of a tier subset, on the original profile space. -/
noncomputable def tierTotal {n : ℕ} (J : Finset (Fin n)) (p : Profile n) : ℝ :=
  ∑ m ∈ J, (RankTail.rank p m : ℝ)

/-- Reciprocal popularity weight of a tier subset. -/
noncomputable def weight {n : ℕ} (b : Fin n → ℝ≥0) (J : Finset (Fin n)) : ℝ :=
  ∑ m ∈ J, (b m : ℝ)⁻¹

/-- The exact tier coefficient, including finite-population tier sizes. -/
noncomputable def share {n : ℕ} (b : Fin n → ℝ≥0) (J : Finset (Fin n)) : ℝ :=
  weight b J / weight b Finset.univ

/-- The deterministic tier leading term, under normalized public scores. -/
noncomputable def target {n : ℕ} (a b : Fin n → ℝ≥0) (J : Finset (Fin n)) : ℝ :=
  CouponMoments.totalWeight a * share b J * Real.log n

/-- Explicit pending individual-mean input on the actual original PR profile law. -/
def ComparableMeans {n : ℕ} (a b : Fin n → ℝ≥0) (K : ℝ) : Prop :=
  ∀ m k, |(b m : ℝ) * (∫ p, (RankTail.rank p m : ℝ) ∂(VisitBounds.profileLaw a b).toMeasure) -
    (b k : ℝ) * (∫ p, (RankTail.rank p k : ℝ) ∂(VisitBounds.profileLaw a b).toMeasure)| ≤ K

/-- Explicit pending distinct-pair covariance input on the same original PR profile law. -/
def CovarianceLower {n : ℕ} (a b : Fin n → ℝ≥0) (C : ℝ) : Prop :=
  ∀ m k, m ≠ k → -C * Real.log n ≤ covariance
    (fun p ↦ (RankTail.rank p m : ℝ)) (fun p ↦ (RankTail.rank p k : ℝ))
      (VisitBounds.profileLaw a b).toMeasure

/-- Positive scores give a strictly positive full reciprocal denominator. -/
theorem weight_univ_pos {n : ℕ} [NeZero n] (b : Fin n → ℝ≥0)
    (hb : ∀ m, 0 < b m) : 0 < weight b Finset.univ := by
  apply Finset.sum_pos
  · intro m _
    exact inv_pos.mpr (by exact_mod_cast hb m)
  · exact Finset.univ_nonempty

/-- Reciprocal tier weights are nonnegative and bounded by the full weight. -/
theorem weight_bounds {n : ℕ} (b : Fin n → ℝ≥0) (J : Finset (Fin n)) :
    0 ≤ weight b J ∧ weight b J ≤ weight b Finset.univ := by
  exact ⟨Finset.sum_nonneg (fun m _ ↦ inv_nonneg.mpr (b m).coe_nonneg),
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun m _ _ ↦ inv_nonneg.mpr (b m).coe_nonneg)⟩

/-- Normalization puts every tier coefficient in [0,1], including the empty tier. -/
theorem share_bounds {n : ℕ} [NeZero n] (b : Fin n → ℝ≥0)
    (hb : ∀ m, 0 < b m) (J : Finset (Fin n)) : 0 ≤ share b J ∧ share b J ≤ 1 := by
  have hD := weight_univ_pos b hb
  exact ⟨div_nonneg (weight_bounds b J).1 hD.le, (div_le_one hD).mpr (weight_bounds b J).2⟩

/-- Scores at least one bound the reciprocal tier weight by the tier's cardinality. -/
theorem weight_le_card {n : ℕ} (b : Fin n → ℝ≥0) (hb : ∀ m, 1 ≤ (b m : ℝ))
    (J : Finset (Fin n)) : weight b J ≤ J.card := by
  calc
    _ ≤ ∑ _m ∈ J, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro m _
      exact inv_le_one_of_one_le₀ (hb m)
    _ = _ := by simp

/-- Close popularity-weighted scalar means determine every subset's reciprocal-weight share. -/
theorem scalar_mean_share_error {n : ℕ} [NeZero n] (β r : Fin n → ℝ) (K : ℝ)
    (hβ : ∀ m, 0 < β m) (hpair : ∀ m k, |β m * r m - β k * r k| ≤ K)
    (J : Finset (Fin n)) :
    |(∑ m ∈ J, r m) - ((∑ m ∈ J, (β m)⁻¹) / (∑ m, (β m)⁻¹)) * (∑ m, r m)| ≤
      2 * K * (∑ m ∈ J, (β m)⁻¹) := by
  let ell := β 0 * r 0
  have herr : ∀ m ∈ Finset.univ, |β m * r m - ell| ≤ K := fun m _ ↦ hpair m 0
  have hD : 0 < ∑ m, (β m)⁻¹ :=
    Finset.sum_pos (fun m _ ↦ inv_pos.mpr (hβ m)) Finset.univ_nonempty
  have hJ := G2Moments.abs_sum_sub_signal_sum_inv_le J β r ell K (fun m _ ↦ hβ m)
    (fun m _ ↦ hpair m 0)
  have hsig := G2Moments.abs_signal_sub_total_div_sum_inv_le Finset.univ β r ell K
    (fun m _ ↦ hβ m) herr hD
  have hJ0 : 0 ≤ ∑ m ∈ J, (β m)⁻¹ :=
    Finset.sum_nonneg (fun m _ ↦ (inv_pos.mpr (hβ m)).le)
  have he : (∑ m ∈ J, r m) - ((∑ m ∈ J, (β m)⁻¹) / (∑ m, (β m)⁻¹)) * (∑ m, r m) =
      ((∑ m ∈ J, r m) - ell * (∑ m ∈ J, (β m)⁻¹)) +
        (ell - (∑ m, r m) / (∑ m, (β m)⁻¹)) * (∑ m ∈ J, (β m)⁻¹) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_nonneg hJ0]
  have hm := mul_le_mul_of_nonneg_right hsig hJ0
  nlinarith

/-- All actual rank functions and tier totals are square integrable on the finite PR space. -/
theorem memLp_rank {n : ℕ} (a b : Fin n → ℝ≥0) (m : Fin n) :
    MemLp (fun p ↦ (RankTail.rank p m : ℝ)) 2 (VisitBounds.profileLaw a b).toMeasure :=
  G2Deconditioning.memLp_finite _ _

/-- Finite linearity identifies the exact tier mean with the sum of individual rank means. -/
theorem integral_tierTotal {n : ℕ} (a b : Fin n → ℝ≥0) (J : Finset (Fin n)) :
    (∫ p, tierTotal J p ∂(VisitBounds.profileLaw a b).toMeasure) =
      ∑ m ∈ J, ∫ p, (RankTail.rank p m : ℝ) ∂(VisitBounds.profileLaw a b).toMeasure := by
  exact integral_finsetSum J (fun m _ ↦ (memLp_rank a b m).integrable one_le_two)

/-- Every individual PR proposal counter contributes once to the exact original total. -/
theorem tierTotal_univ {n : ℕ} (p : Profile n) : tierTotal Finset.univ p = numProposals p := by
  simp [tierTotal, RankTail.rank, numProposals]

/-- Explicit weighted mean comparability gives the tier's exact finite-population allocation. -/
theorem tier_mean_share_error {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (hb : ∀ m, 0 < b m) (K : ℝ) (hpair : ComparableMeans a b K) (J : Finset (Fin n)) :
    |(∫ p, tierTotal J p ∂(VisitBounds.profileLaw a b).toMeasure) - share b J *
      (∫ p, (numProposals p : ℝ) ∂(VisitBounds.profileLaw a b).toMeasure)| ≤
        2 * K * weight b J := by
  have ht : (∫ p, (numProposals p : ℝ) ∂(VisitBounds.profileLaw a b).toMeasure) =
      ∑ m, ∫ p, (RankTail.rank p m : ℝ) ∂(VisitBounds.profileLaw a b).toMeasure := by
    simpa only [← tierTotal_univ] using integral_tierTotal a b Finset.univ
  rw [integral_tierTotal, ht]
  exact scalar_mean_share_error (fun m ↦ (b m : ℝ)) _ K
    (fun m ↦ by exact_mod_cast hb m) hpair J

/-- Total mean control and weighted individual comparability give a linear tier mean error. -/
theorem tier_mean_error_le {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (hb1 : ∀ m, 1 ≤ (b m : ℝ)) {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hpair : ComparableMeans a b K) (J : Finset (Fin n))
    (hmean : |(∫ p, (numProposals p : ℝ) ∂(VisitBounds.profileLaw a b).toMeasure) -
      CouponMoments.totalWeight a * Real.log n| ≤ C * n) :
    |(∫ p, tierTotal J p ∂(VisitBounds.profileLaw a b).toMeasure) - target a b J| ≤
      (C + 2 * K) * n := by
  have hb : ∀ m, 0 < b m := fun m ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (hb1 m)
  have hq := share_bounds b hb J
  have hDJ : weight b J ≤ (n : ℝ) := (weight_le_card b hb1 J).trans (by
    have hn : J.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ J)
    exact_mod_cast hn)
  have hshare := tier_mean_share_error a b hb K hpair J
  have htotal := mul_le_mul_of_nonneg_left hmean hq.1
  have he : (∫ p, tierTotal J p ∂(VisitBounds.profileLaw a b).toMeasure) - target a b J =
      ((∫ p, tierTotal J p ∂(VisitBounds.profileLaw a b).toMeasure) - share b J *
        (∫ p, (numProposals p : ℝ) ∂(VisitBounds.profileLaw a b).toMeasure)) +
      share b J * ((∫ p, (numProposals p : ℝ) ∂(VisitBounds.profileLaw a b).toMeasure) -
        CouponMoments.totalWeight a * Real.log n) := by unfold target; ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_nonneg hq.1]
  have h1 := mul_le_mul_of_nonneg_left hDJ (by positivity : 0 ≤ 2 * K)
  have h2 := mul_le_mul_of_nonneg_right hq.2 (mul_nonneg hC (Nat.cast_nonneg n))
  nlinarith

/-- Only distinct cross-tier lower covariances are needed for the exact tier variance. -/
theorem tier_variance_le {n : ℕ} (a b : Fin n → ℝ≥0) (J : Finset (Fin n))
    {C V : ℝ} (hC : 0 ≤ C) (hlog : 0 ≤ Real.log n)
    (hcov : CovarianceLower a b C)
    (hvar : variance (fun p ↦ (numProposals p : ℝ)) (VisitBounds.profileLaw a b).toMeasure ≤
      V * (n : ℝ) ^ 2 * Real.log n) :
    variance (tierTotal J) (VisitBounds.profileLaw a b).toMeasure ≤
      (V + 2 * C) * (n : ℝ) ^ 2 * Real.log n := by
  classical
  let X : Fin n → Profile n → ℝ := fun m p ↦ (RankTail.rank p m : ℝ)
  have ht : (∑ m ∈ J, X m) + (∑ m ∈ Jᶜ, X m) =
      fun p ↦ (numProposals p : ℝ) := by
    rw [Finset.sum_add_sum_compl]
    funext p
    simpa only [Finset.sum_apply, tierTotal, X] using tierTotal_univ p
  have hv := G2Moments.variance_group_le_total_of_cross_covariance_lower
    (VisitBounds.profileLaw a b).toMeasure J Jᶜ X X
    (fun m _ ↦ memLp_rank a b m) (fun m _ ↦ memLp_rank a b m)
    (K := C * Real.log n) (by
      intro m hm k hk
      have hne : m ≠ k := by
        intro heq
        exact (Finset.mem_compl.mp hk) (heq ▸ hm)
      simpa only [X, neg_mul] using hcov m k hne)
  rw [ht] at hv
  have hj : (J.card : ℝ) ≤ n := by
    have hn : J.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ J)
    exact_mod_cast hn
  have hc : (Jᶜ.card : ℝ) ≤ n := by
    have hn : Jᶜ.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ Jᶜ)
    exact_mod_cast hn
  have hp : (J.card : ℝ) * Jᶜ.card ≤ (n : ℝ) ^ 2 := by
    exact (mul_le_mul hj hc (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans_eq (pow_two _).symm
  have hm := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hC hlog))
  have hX : (∑ m ∈ J, X m) = tierTotal J := by
    funext p
    simp only [Finset.sum_apply, X, tierTotal]
  rw [hX] at hv
  nlinarith

/-- A fixed positive tier fraction bounds its reciprocal-weight coefficient below. -/
theorem share_lower {n : ℕ} [NeZero n] (b : Fin n → ℝ≥0) (J : Finset (Fin n))
    {B ρ : ℝ} (hB : 0 < B) (hρ : 0 ≤ ρ) (hb1 : ∀ m, 1 ≤ (b m : ℝ))
    (hbB : ∀ m, (b m : ℝ) ≤ B) (hcard : ρ * n ≤ J.card) : ρ / B ≤ share b J := by
  have hb : ∀ m, 0 < b m := fun m ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (hb1 m)
  have hD := weight_univ_pos b hb
  have hDn : weight b Finset.univ ≤ n := by simpa using weight_le_card b hb1 Finset.univ
  have hJ : (J.card : ℝ) / B ≤ weight b J := by
    calc
      _ = ∑ _m ∈ J, (1 / B : ℝ) := by simp [div_eq_mul_inv]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro m _
        simpa [one_div] using one_div_le_one_div_of_le
          (by linarith [hb1 m] : 0 < (b m : ℝ)) (hbB m)
  apply (le_div_iff₀ hD).mpr
  calc
    _ ≤ (ρ / B) * n := mul_le_mul_of_nonneg_left hDn (div_nonneg hρ hB.le)
    _ ≤ (J.card : ℝ) / B := by
      simpa only [div_mul_eq_mul_div] using div_le_div_of_nonneg_right hcard hB.le
    _ ≤ _ := hJ

/-- A positive tier fraction gives a deterministic n log n lower scale for its leading term. -/
theorem target_lower {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0) (J : Finset (Fin n))
    {B ρ : ℝ} (hB : 0 < B) (hρ : 0 ≤ ρ) (hlog : 0 ≤ Real.log n)
    (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (hb1 : ∀ m, 1 ≤ (b m : ℝ))
    (hbB : ∀ m, (b m : ℝ) ≤ B) (hcard : ρ * n ≤ J.card) :
    (ρ / B) * n * Real.log n ≤ target a b J := by
  have hW : (n : ℝ) ≤ CouponMoments.totalWeight a := by
    simpa using CouponMoments.card_le_totalWeight a (fun w ↦ by exact_mod_cast ha1 w)
  have hq := share_lower b J hB hρ hb1 hbB hcard
  have hw0 : 0 ≤ CouponMoments.totalWeight a := by unfold CouponMoments.totalWeight; positivity
  have hm := mul_le_mul hW hq (div_nonneg hρ hB.le) hw0
  have hl := mul_le_mul_of_nonneg_right hm hlog
  simpa only [target, mul_comm (ρ / B) (n : ℝ)] using hl

/-- Constant popularity inside a tier gives exactly its cardinality divided by that popularity. -/
theorem weight_of_constant {n : ℕ} (b : Fin n → ℝ≥0) (J : Finset (Fin n)) (β : ℝ)
    (hβ : ∀ m ∈ J, (b m : ℝ) = β) : weight b J = J.card / β := by
  calc
    _ = ∑ _m ∈ J, β⁻¹ := Finset.sum_congr rfl (fun m hm ↦ by rw [hβ m hm])
    _ = _ := by simp [div_eq_mul_inv]

/-- A quantitative relative Chebyshev bound with explicit mean bias and leading scale. -/
theorem relative_deviation_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → ℝ) (hU : MemLp U 2 μ)
    {N L t d M V η : ℝ} (hN : 0 < N) (hL : 0 < L) (hd : 0 < d) (hη : 0 < η)
    (ht : d * N * L ≤ t) (hbias : |(∫ p, U p ∂μ) - t| ≤ M * N)
    (hsmall : 2 * M ≤ η * d * L) (hvar : variance U μ ≤ V * N ^ 2 * L) :
    μ.real {p | η * t < |U p - t|} ≤ 4 * V / (η ^ 2 * d ^ 2 * L) := by
  let ε := η * d * N * L / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hb : |(∫ p, U p ∂μ) - t| ≤ ε := by
    have hm := mul_le_mul_of_nonneg_right hsmall hN.le
    dsimp only [ε]
    nlinarith
  have he : 2 * ε ≤ η * t := by
    have hm := mul_le_mul_of_nonneg_left ht hη.le
    dsimp only [ε]
    nlinarith
  have hcheb := meas_ge_le_variance_div_sq hU hε
  have hreal : μ.real {p | ε ≤ |U p - ∫ q, U q ∂μ|} ≤ variance U μ / ε ^ 2 := by
    have hm := ENNReal.toReal_mono (by simp) hcheb
    simpa only [measureReal_def,
      ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] using hm
  have hsub : {p | η * t < |U p - t|} ⊆ {p | ε ≤ |U p - ∫ q, U q ∂μ|} := by
    intro p hp
    have htri : |U p - t| ≤ |U p - ∫ q, U q ∂μ| + |(∫ q, U q ∂μ) - t| := by
      rw [show U p - t = (U p - ∫ q, U q ∂μ) + ((∫ q, U q ∂μ) - t) by ring]
      exact abs_add_le _ _
    change η * t < |U p - t| at hp
    change ε ≤ |U p - ∫ q, U q ∂μ|
    linarith
  calc
    _ ≤ μ.real {p | ε ≤ |U p - ∫ q, U q ∂μ|} := measureReal_mono hsub
    _ ≤ variance U μ / ε ^ 2 := hreal
    _ ≤ (V * N ^ 2 * L) / ε ^ 2 :=
      div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ = _ := by dsimp only [ε]; field_simp; ring

/-- The absolute leading-term deviation is exactly the usual relative-deviation event. -/
theorem relative_event_eq {Ω : Type*} (U : Ω → ℝ) {t : ℝ} (ht : 0 < t) (η : ℝ) :
    {p | η < |U p / t - 1|} = {p | η * t < |U p - t|} := by
  ext p
  have he : U p / t - 1 = (U p - t) / t := by field_simp
  simp only [Set.mem_ofPred_eq, he, abs_div, abs_of_pos ht]
  exact lt_div_iff₀ ht

/-- Exact actual-PR tier concentration from named mean and covariance inputs. -/
theorem tier_relative_deviation_le {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (J : Finset (Fin n)) {B ρ K Ccov Cmean Cvar η : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ) (hK : 0 ≤ K) (hCcov : 0 ≤ Ccov) (hCmean : 0 ≤ Cmean)
    (hlog : 0 < Real.log n) (hη : 0 < η)
    (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (hb1 : ∀ m, 1 ≤ (b m : ℝ))
    (hbB : ∀ m, (b m : ℝ) ≤ B) (hcard : ρ * n ≤ J.card)
    (hpair : ComparableMeans a b K) (hcov : CovarianceLower a b Ccov)
    (hmean : |(∫ p, (numProposals p : ℝ) ∂(VisitBounds.profileLaw a b).toMeasure) -
      CouponMoments.totalWeight a * Real.log n| ≤ Cmean * n)
    (hvar : variance (fun p ↦ (numProposals p : ℝ)) (VisitBounds.profileLaw a b).toMeasure ≤
      Cvar * (n : ℝ) ^ 2 * Real.log n)
    (hsmall : 2 * (Cmean + 2 * K) ≤ η * (ρ / B) * Real.log n) :
    (VisitBounds.profileLaw a b).toMeasure.real
      {p | η < |tierTotal J p / target a b J - 1|} ≤
        4 * (Cvar + 2 * Ccov) / (η ^ 2 * (ρ / B) ^ 2 * Real.log n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have ht := target_lower a b J hB hρ.le hlog.le ha1 hb1 hbB hcard
  have hpos : 0 < target a b J := lt_of_lt_of_le (by positivity) ht
  rw [relative_event_eq (tierTotal J) hpos η]
  exact relative_deviation_le _ _ (G2Deconditioning.memLp_finite _ _) hn hlog
    (div_pos hρ hB) hη ht (tier_mean_error_le a b hb1 hK hCmean hpair J hmean) hsmall
    (tier_variance_le a b J hCcov hlog.le hcov hvar)

/-- Proved total moments discharge those inputs; only the two pending pair inputs remain.
The finite-state pair assembly must still establish ComparableMeans and CovarianceLower. -/
theorem eventually_tier_relative_deviation_le {A B ρmin ρtier K Ccov η : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hρmin : 0 < ρmin) (hρtier : 0 < ρtier)
    (hK : 0 ≤ K) (hCcov : 0 ≤ Ccov) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ [NeZero n] (a b : Fin n → ℝ≥0),
      (∀ w, 1 ≤ (a w : ℝ)) → (∀ w, (a w : ℝ) ≤ A) →
      (∀ m, 1 ≤ (b m : ℝ)) → (∀ m, (b m : ℝ) ≤ B) →
      ρmin * n ≤ (CouponMoments.minimumCoupons a).card →
      ∀ J : Finset (Fin n), ρtier * n ≤ J.card →
        ComparableMeans a b K → CovarianceLower a b Ccov →
        (VisitBounds.profileLaw a b).toMeasure.real
          {p | η < |tierTotal J p / target a b J - 1|} ≤
            4 * (TotalMoments.varianceConstant A B ρmin + 2 * Ccov) /
              (η ^ 2 * (ρtier / B) ^ 2 * Real.log n) := by
  have hBp : 0 < B := by linarith
  have hd : 0 < η * (ρtier / B) := mul_pos hη (div_pos hρtier hBp)
  have hg := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (2 * (TotalMoments.meanConstant A B ρmin + 2 * K) / (η * (ρtier / B)))
  filter_upwards [TotalMoments.eventually_uniform_total_moments hA hB hρmin,
    ContinuationAsymptotics.eventually_one_le_log, hg] with n ht hlog hgrowth
  intro _ a b ha1 haA hb1 hbB hmin J hcard hpair hcov
  obtain ⟨hmean, hvar⟩ := ht a b ha1 haA hb1 hbB hmin
  have hsmall : 2 * (TotalMoments.meanConstant A B ρmin + 2 * K) ≤
      η * (ρtier / B) * Real.log n := by
    have hm := (div_le_iff₀ hd).mp hgrowth
    simpa only [mul_comm, Function.comp_apply] using hm
  exact tier_relative_deviation_le a b J hBp hρtier hK hCcov
    (TotalMoments.constants_pos hA hB ρmin).2.1.le (by linarith) hη ha1 hb1 hbB hcard
    hpair hcov hmean hvar hsmall

/-- For a genuine constant-popularity tier, the leading coefficient is exactly N_j/beta_j. -/
theorem target_of_constant {n : ℕ} (a b : Fin n → ℝ≥0) (J : Finset (Fin n)) (β : ℝ)
    (hβ : ∀ m ∈ J, (b m : ℝ) = β) :
    target a b J = CouponMoments.totalWeight a *
      ((J.card / β) / weight b Finset.univ) * Real.log n := by
  rw [target, share, weight_of_constant b J β hβ]

end TieredMatching.TierConcentration
