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

public import TieredMatching.ConcreteLaw
public import TieredMatching.Main
public import TieredMatching.ReferenceModel

/-! # Exact concrete-arrival count bands from an explicit Proposition G.2 premise

The unchanged PR premise transfers through the proved concrete arrival pushforward law.
Exact floor and ceiling endpoints and a finite tier union give a uniformly vanishing
source band-failure probability. Proposition G.2 remains an explicit hypothesis.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

namespace TieredMatching.ArrivalBands

open Arrival ReferenceModel

/-- The concrete arrival profile is measurable also at the empty-market boundary. -/
theorem measurable_concreteArrivalProfile {n J : ℕ} (manTier : Fin n → Fin J) :
    Measurable (concreteArrivalProfile manTier) := by
  classical
  by_cases hn : n = 0
  · simp only [concreteArrivalProfile, dite_eq_left hn]
    exact measurable_const
  · have : NeZero n := ⟨hn⟩
    have hm := measurePreserving_arrivalMatrices (fun _ _ ↦ (1 : ℝ≥0))
      (fun _ _ ↦ (1 : ℝ≥0)) (by intros; norm_num) (by intros; norm_num)
      (fun r ↦ pick r manTier) (concrete_policy_valid manTier (fun _ ↦ 1)) (n * n)
    simpa only [concreteArrivalProfile, dite_eq_right hn, arrivalProfile] using
      (measurable_rankProfile exponentialRank measurableSet_exponentialRank_fiber).comp
        hm.measurable

/-- A relative real error bound implies the exact natural floor and ceiling count bands. -/
theorem count_band_of_abs_le (s : ℕ) (x η : ℝ) (h : |(s : ℝ) - x| ≤ η * x) :
    ⌊(1 - η) * x⌋₊ ≤ s ∧ s ≤ ⌈(1 + η) * x⌉₊ := by
  obtain ⟨hl, hu⟩ := abs_le.mp h
  refine ⟨Nat.floor_le_of_le (by nlinarith), ?_⟩
  have hs : (s : ℝ) ≤ (1 + η) * x := by nlinarith
  exact_mod_cast hs.trans (Nat.le_ceil ((1 + η) * x))

/-- The exact proposal counter of the completed concrete arrival profile. -/
noncomputable def sourceProposalCount {n J : ℕ} (manTier : Fin n → Fin J) (j : Fin J)
    (w : Fin n) (z : (Fin n → Fin n → ℝ) × (ArrivalCoordinates n → ℝ)) : ℕ :=
  proposalCount manTier j (concreteArrivalProfile manTier z) w

/-- The actual count is always feasible in its original source tier, pointwise in the input. -/
theorem sourceProposalCount_le_tier {n J : ℕ} (manTier : Fin n → Fin J) (j : Fin J)
    (w : Fin n) (z : (Fin n → Fin n → ℝ) × (ArrivalCoordinates n → ℝ)) :
    sourceProposalCount manTier j w z ≤ (tierMen manTier j).card :=
  proposalCount_le_tier manTier j (concreteArrivalProfile manTier z) w

/-- Failure of at least one deterministic integer tier-count band at a specified woman. -/
def bandFailure {n J : ℕ} (manTier : Fin n → Fin J) (lower upper : Fin J → ℕ)
    (w : Fin n) : Set ((Fin n → Fin n → ℝ) × (ArrivalCoordinates n → ℝ)) :=
  {z | ¬ ∀ j, lower j ≤ sourceProposalCount manTier j w z ∧
    sourceProposalCount manTier j w z ≤ upper j}

/-- A successful actual count band puts its original-label source set between the endpoints. -/
theorem sourceSet_sandwich_of_not_mem_bandFailure {n J : ℕ}
    (manTier : Fin n → Fin J) (lower upper : Fin J → ℕ) (w : Fin n)
    (z : (Fin n → Fin n → ℝ) × (ArrivalCoordinates n → ℝ))
    (hz : z ∉ bandFailure manTier lower upper w) :
    sourceSet manTier lower ⊆ sourceSet manTier (fun j ↦ sourceProposalCount manTier j w z) ∧
      sourceSet manTier (fun j ↦ sourceProposalCount manTier j w z) ⊆ sourceSet manTier upper := by
  have h : ∀ j, lower j ≤ sourceProposalCount manTier j w z ∧
      sourceProposalCount manTier j w z ≤ upper j := not_not.mp hz
  exact ⟨sourceSet_mono _ _ _ (fun j ↦ (h j).1), sourceSet_mono _ _ _ (fun j ↦ (h j).2)⟩

/-- Actual count-band failure is measurable in the original independent arrival inputs. -/
theorem measurableSet_bandFailure {n J : ℕ} (manTier : Fin n → Fin J)
    (lower upper : Fin J → ℕ) (w : Fin n) :
    MeasurableSet (bandFailure manTier lower upper w) := by
  change MeasurableSet (concreteArrivalProfile manTier ⁻¹'
    {p | ¬ ∀ j, lower j ≤ proposalCount manTier j p w ∧ proposalCount manTier j p w ≤ upper j})
  exact (show MeasurableSet _ from MeasurableSet.of_discrete).preimage
    (measurable_concreteArrivalProfile manTier)

/-- Band failure is contained in the union of the original relative G.2 failures. -/
theorem bandFailure_subset_relative {n I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin η : ℝ)
    (manTier : Fin n → Fin J) (i : Fin I) (w : Fin n) :
    bandFailure manTier (lowerCounts b α β αmin η n i) (upperCounts b α β αmin η n i) w ⊆
      ⋃ j : Fin J, {z | |(sourceProposalCount manTier j w z : ℝ) -
        proposalCoefficient b α β αmin i j * Real.log n| >
          η * (proposalCoefficient b α β αmin i j * Real.log n)} := by
  intro z hz
  by_contra hnot
  apply hz
  intro j
  have hj : |(sourceProposalCount manTier j w z : ℝ) -
      proposalCoefficient b α β αmin i j * Real.log n| ≤
        η * (proposalCoefficient b α β αmin i j * Real.log n) := by
    exact le_of_not_gt (fun hj ↦ hnot (Set.mem_iUnion.mpr ⟨j, hj⟩))
  simpa only [lowerCounts, upperCounts, mul_assoc] using
    count_band_of_abs_le (sourceProposalCount manTier j w z)
      (proposalCoefficient b α β αmin i j * Real.log n) η hj

/-- A finite tier union costs at most one prescribed total error, including zero-tier markets. -/
theorem finite_union_measure_le {Ω : Type*} [MeasurableSpace Ω] {J : ℕ}
    (μ : Measure Ω) (E : Fin J → Set Ω) (δ : ℝ≥0∞)
    (hE : ∀ j, μ (E j) ≤ δ / (J + 1 : ℝ≥0∞)) : μ (⋃ j, E j) ≤ δ := by
  calc
    _ ≤ ∑ j, μ (E j) := measure_iUnion_fintype_le μ E
    _ ≤ ∑ _j : Fin J, δ / (J + 1 : ℝ≥0∞) := Finset.sum_le_sum (fun j _ ↦ hE j)
    _ = (J : ℝ≥0∞) * (δ / (J + 1 : ℝ≥0∞)) := by simp
    _ ≤ (J + 1 : ℝ≥0∞) * (δ / (J + 1 : ℝ≥0∞)) := by gcongr; exact le_add_of_nonneg_right zero_le
    _ = δ := ENNReal.mul_div_cancel (by positivity) (by finiteness)

/-- Exact G.2 gives arbitrarily small actual arrival band failure, uniformly over the whole tier. -/
theorem bandFailure_eventually_le {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (i : Fin I) (hG2 : PropositionG2 b α β αmin womanTier manTier i)
    (η : ℝ) (hη : 0 < η) (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ w : Fin n, womanTier n w = i →
      referenceSourceLaw (womanTier n) (manTier n) α β
        (bandFailure (manTier n) (lowerCounts b α β αmin η n i)
          (upperCounts b α β αmin η n i) w) ≤ δ := by
  have hsmall : 0 < δ / (J + 1 : ℝ≥0∞) :=
    ENNReal.div_pos_iff.mpr ⟨ne_of_gt hδ, by finiteness⟩
  have h := hG2.pullback b α β αmin womanTier manTier i
    (fun n ↦ referenceSourceLaw (womanTier n) (manTier n) α β)
    (fun n ↦ concreteArrivalProfile (manTier n))
    (fun n ↦ measurable_concreteArrivalProfile (manTier n))
    (fun n ↦ concreteArrivalProfile_market_law (womanTier n) (manTier n) α β hα hβ)
    η hη (δ / (J + 1 : ℝ≥0∞)) hsmall
  filter_upwards [h] with n hn w hw
  calc
    _ ≤ referenceSourceLaw (womanTier n) (manTier n) α β
        (⋃ j : Fin J, {z | |(sourceProposalCount (manTier n) j w z : ℝ) -
          proposalCoefficient b α β αmin i j * Real.log n| >
            η * (proposalCoefficient b α β αmin i j * Real.log n)}) :=
      measure_mono (bandFailure_subset_relative b α β αmin η (manTier n) i w)
    _ ≤ δ := finite_union_measure_le _ _ δ (hn w hw)

/-- An explicit worst-woman failure probability, with zero for an empty woman tier. -/
noncomputable def bandFailureEnvelope {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin η : ℝ)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (i : Fin I) (n : ℕ) : ℝ≥0∞ :=
  (tierMen (womanTier n) i).sup fun w ↦
    referenceSourceLaw (womanTier n) (manTier n) α β
      (bandFailure (manTier n) (lowerCounts b α β αmin η n i)
        (upperCounts b α β αmin η n i) w)

/-- The envelope bounds every specified woman in the designated tier, at every market size. -/
theorem bandFailure_le_envelope {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin η : ℝ)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (i : Fin I) (n : ℕ) (w : Fin n) (hw : womanTier n w = i) :
    referenceSourceLaw (womanTier n) (manTier n) α β
      (bandFailure (manTier n) (lowerCounts b α β αmin η n i)
        (upperCounts b α β αmin η n i) w) ≤
      bandFailureEnvelope b α β αmin η womanTier manTier i n := by
  unfold bandFailureEnvelope
  exact Finset.le_sup (f := fun v : Fin n ↦
    referenceSourceLaw (womanTier n) (manTier n) α β
      (bandFailure (manTier n) (lowerCounts b α β αmin η n i)
        (upperCounts b α β αmin η n i) v))
    (show w ∈ tierMen (womanTier n) i from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩)

/-- The actual worst-woman envelope is a probability, including at zero and empty-tier sizes. -/
theorem bandFailureEnvelope_le_one {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin η : ℝ)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (i : Fin I) (n : ℕ) : bandFailureEnvelope b α β αmin η womanTier manTier i n ≤ 1 := by
  have : IsProbabilityMeasure (referenceSourceLaw (womanTier n) (manTier n) α β) :=
    isProbabilityMeasure_referenceSourceLaw _ _ α β hα hβ
  exact Finset.sup_le (fun _ _ ↦ prob_le_one)

/-- The exact G.2 premise gives one explicit uniformly vanishing ENNReal band-failure sequence. -/
theorem bandFailureEnvelope_tendsto_zero {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (i : Fin I) (hG2 : PropositionG2 b α β αmin womanTier manTier i)
    (η : ℝ) (hη : 0 < η) :
    Tendsto (bandFailureEnvelope b α β αmin η womanTier manTier i) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro δ hδ
  filter_upwards [bandFailure_eventually_le b α β αmin hα hβ womanTier manTier i hG2 η hη δ hδ]
    with n hn
  exact Finset.sup_le fun w hw ↦ hn w (Finset.mem_filter.mp hw).2

/-- The same explicit uniformly dominating failure sequence vanishes in real probability. -/
theorem bandFailureEnvelope_real_tendsto_zero {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (i : Fin I) (hG2 : PropositionG2 b α β αmin womanTier manTier i)
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun n ↦ (bandFailureEnvelope b α β αmin η womanTier manTier i n).toReal)
      atTop (𝓝 0) :=
  (ENNReal.tendsto_toReal_zero_iff (fun n ↦ ne_of_lt
    ((bandFailureEnvelope_le_one b α β αmin η hα hβ womanTier manTier i n).trans_lt
      ENNReal.one_lt_top))).mpr
    (bandFailureEnvelope_tendsto_zero b α β αmin hα hβ womanTier manTier i hG2 η hη)

/-- A fixed woman's real failure probability is bounded by the same explicit uniform sequence. -/
theorem bandFailure_real_le_envelope {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin η : ℝ)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (i : Fin I) (n : ℕ) (w : Fin n) (hw : womanTier n w = i) :
    (referenceSourceLaw (womanTier n) (manTier n) α β).real
      (bandFailure (manTier n) (lowerCounts b α β αmin η n i)
        (upperCounts b α β αmin η n i) w) ≤
      (bandFailureEnvelope b α β αmin η womanTier manTier i n).toReal := by
  exact ENNReal.toReal_mono (ne_of_lt
    ((bandFailureEnvelope_le_one b α β αmin η hα hβ womanTier manTier i n).trans_lt
      ENNReal.one_lt_top))
    (bandFailure_le_envelope b α β αmin η womanTier manTier i n w hw)

/-- The expected normalized number of women whose actual count vector leaves its bands. -/
noncomputable def averageBandFailure {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin η : ℝ)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (i : Fin I) (n : ℕ) : ℝ :=
  (∑ w ∈ tierMen (womanTier n) i,
    (referenceSourceLaw (womanTier n) (manTier n) α β).real
      (bandFailure (manTier n) (lowerCounts b α β αmin η n i)
        (upperCounts b α β αmin η n i) w)) / n

/-- An average of actual failure probabilities is nonnegative. -/
theorem averageBandFailure_nonneg {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin η : ℝ)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (i : Fin I) (n : ℕ) : 0 ≤ averageBandFailure b α β αmin η womanTier manTier i n := by
  exact div_nonneg (Finset.sum_nonneg (fun _ _ ↦ ENNReal.toReal_nonneg)) (Nat.cast_nonneg n)

/-- Normalization by the whole market makes the actual average at most the uniform envelope. -/
theorem averageBandFailure_le_envelope {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin η : ℝ)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (i : Fin I) (n : ℕ) : averageBandFailure b α β αmin η womanTier manTier i n ≤
      (bandFailureEnvelope b α β αmin η womanTier manTier i n).toReal := by
  by_cases hn : n = 0
  · subst n
    simp only [averageBandFailure, Nat.cast_zero, div_zero]
    exact ENNReal.toReal_nonneg
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    unfold averageBandFailure
    apply (div_le_iff₀ hn0).mpr
    calc
      _ ≤ ∑ _w ∈ tierMen (womanTier n) i,
          (bandFailureEnvelope b α β αmin η womanTier manTier i n).toReal := by
        apply Finset.sum_le_sum
        intro w hw
        exact bandFailure_real_le_envelope b α β αmin η hα hβ womanTier manTier i n w
          (Finset.mem_filter.mp hw).2
      _ = ((tierMen (womanTier n) i).card : ℝ) *
          (bandFailureEnvelope b α β αmin η womanTier manTier i n).toReal := by simp
      _ ≤ _ := by
        rw [mul_comm _ (n : ℝ)]
        exact mul_le_mul_of_nonneg_right (RowIndependence.card_finset_fin_le_market _)
          ENNReal.toReal_nonneg

/-- G.2 makes the exact average band-failure probability vanish under the concrete arrival law. -/
theorem averageBandFailure_tendsto_zero {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (i : Fin I) (hG2 : PropositionG2 b α β αmin womanTier manTier i)
    (η : ℝ) (hη : 0 < η) :
    Tendsto (averageBandFailure b α β αmin η womanTier manTier i) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (bandFailureEnvelope_real_tendsto_zero b α β αmin hα hβ womanTier manTier i hG2 η hη)
    (averageBandFailure_nonneg b α β αmin η womanTier manTier i)
    (averageBandFailure_le_envelope b α β αmin η hα hβ womanTier manTier i)

end TieredMatching.ArrivalBands
