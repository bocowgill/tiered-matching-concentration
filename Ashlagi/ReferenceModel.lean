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

public import Ashlagi.ReferenceRace
public import Ashlagi.RowIndependence
public import Ashlagi.Coefficients

/-! # Deterministic tier-prefix reference models in the exact arrival source

Canonical original-label source prefixes define exponential race categories. Their finite
probabilities, independent reference frequencies, rounded feasibility, and limits are derived
from the exact source law. They do not assume a coupling to actual DA categories.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

namespace Ashlagi.ReferenceModel

open Arrival ReferenceRace RowIndependence

local instance {J : ℕ} : MeasurableSpace (Option (Fin J)) := ⊤

/-- The deterministic source set is the union of the original-label prefix in every tier. -/
noncomputable def sourceSet {n J : ℕ} (tier : Fin n → Fin J) (c : Fin J → ℕ) :
    Finset (Fin n) := Finset.univ.biUnion fun j ↦ tierPrefix tier j (c j)

/-- A source prefix contains only labels from its designated tier. -/
theorem mem_tierPrefix_tier {n J : ℕ} (tier : Fin n → Fin J) (j : Fin J) (k : ℕ)
    {m : Fin n} (hm : m ∈ tierPrefix tier j k) : tier m = j :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2

/-- Distinct tier prefixes are disjoint in original source labels. -/
theorem disjoint_tierPrefix {n J : ℕ} (tier : Fin n → Fin J) (c : Fin J → ℕ)
    (j k : Fin J) (hjk : j ≠ k) :
    Disjoint (tierPrefix tier j (c j)) (tierPrefix tier k (c k)) := by
  apply Finset.disjoint_left.mpr
  intro m hm hk
  exact hjk ((mem_tierPrefix_tier tier j _ hm).symm.trans (mem_tierPrefix_tier tier k _ hk))

/-- Filtering the source union back to one tier recovers exactly its canonical prefix. -/
theorem sourceSet_filter_tier {n J : ℕ} (tier : Fin n → Fin J) (c : Fin J → ℕ)
    (j : Fin J) : (sourceSet tier c).filter (fun m ↦ tier m = j) = tierPrefix tier j (c j) := by
  classical
  ext m
  simp only [Finset.mem_filter, sourceSet, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨k, hk⟩, hm⟩
    have hkj : k = j := (mem_tierPrefix_tier tier k _ hk).symm.trans hm
    simpa only [hkj] using hk
  · intro hm
    exact ⟨⟨j, hm⟩, mem_tierPrefix_tier tier j _ hm⟩

/-- Feasible tier prefixes have exactly the supplied deterministic source counts. -/
theorem sourceSet_card {n J : ℕ} (tier : Fin n → Fin J) (c : Fin J → ℕ)
    (hc : ∀ j, c j ≤ (tierMen tier j).card) : (sourceSet tier c).card = ∑ j, c j := by
  classical
  rw [sourceSet, Finset.card_biUnion (fun j _ k _ hjk ↦ disjoint_tierPrefix tier c j k hjk)]
  exact Finset.sum_congr rfl fun j _ ↦ card_firstPrefix_of_le _ (hc j)

/-- Each tier's race-rate numerator is its score times its feasible source-prefix length. -/
theorem sourceSet_tier_rate {n J : ℕ} (tier : Fin n → Fin J) (c : Fin J → ℕ)
    (β : Fin J → ℝ) (hc : ∀ j, c j ≤ (tierMen tier j).card) (j : Fin J) :
    (∑ m ∈ sourceSet tier c with tier m = j, β (tier m)) = β j * (c j : ℝ) := by
  classical
  rw [sourceSet_filter_tier]
  calc
    _ = ∑ _m ∈ tierPrefix tier j (c j), β j :=
      Finset.sum_congr rfl fun m hm ↦ congrArg β (mem_tierPrefix_tier tier j _ hm)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, tierPrefix_card, Nat.min_eq_left (hc j)]; ring

/-- The complete source race rate is the sum of the feasible tier-weighted counts. -/
theorem sourceSet_rate {n J : ℕ} (tier : Fin n → Fin J) (c : Fin J → ℕ)
    (β : Fin J → ℝ) (hc : ∀ j, c j ≤ (tierMen tier j).card) :
    (∑ m ∈ sourceSet tier c, β (tier m)) = ∑ j, β j * (c j : ℝ) := by
  classical
  rw [← Finset.sum_fiberwise (sourceSet tier c) tier (fun m ↦ β (tier m))]
  exact Finset.sum_congr rfl fun j _ ↦ sourceSet_tier_rate tier c β hc j

/-- Canonical source sets are monotone in every tier count. -/
theorem sourceSet_mono {n J : ℕ} (tier : Fin n → Fin J) (c d : Fin J → ℕ)
    (hcd : ∀ j, c j ≤ d j) : sourceSet tier c ⊆ sourceSet tier d := by
  classical
  intro m hm
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hm
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_univ _, ?_⟩
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,
    lt_of_lt_of_le (Finset.mem_filter.mp hj).2 (hcd j)⟩

/-- The deterministic reference race categorizes its winning original source man by tier. -/
noncomputable def tierCategory {n J : ℕ} (tier : Fin n → Fin J) (c : Fin J → ℕ) :
    (Fin n → ℝ) → Option (Fin J) := category (sourceSet tier c) tier

/-- The deterministic reference tier is measurable in its original source row. -/
theorem measurable_tierCategory {n J : ℕ} (tier : Fin n → Fin J) (c : Fin J → ℕ) :
    Measurable (tierCategory tier c) := measurable_category _ _

/-- Its exact category probability is the ratio of score-weighted feasible tier counts. -/
theorem tierCategory_real {n J : ℕ} (tier : Fin n → Fin J) (c : Fin J → ℕ)
    (β : Fin J → ℝ≥0) (hβ : ∀ j, 0 < β j)
    (hc : ∀ j, c j ≤ (tierMen tier j).card) (j : Fin J) :
    (Measure.pi fun m ↦ expMeasure (β (tier m) : ℝ)).real
      {x | tierCategory tier c x = some j} =
      (β j : ℝ) * (c j : ℝ) / ∑ k, (β k : ℝ) * (c k : ℝ) := by
  change (Measure.pi fun m ↦ expMeasure (β (tier m) : ℝ)).real
    {x | category (sourceSet tier c) tier x = some j} = _
  rw [ReferenceRace.category_real (fun m ↦ (β (tier m) : ℝ))
    (fun m ↦ by exact_mod_cast hβ (tier m)),
    sourceSet_tier_rate tier c (fun j ↦ (β j : ℝ)) hc j,
    sourceSet_rate tier c (fun j ↦ (β j : ℝ)) hc]

/-- Each woman uses the deterministic count vector prescribed for her own tier. -/
noncomputable def referenceLabels {n I J : ℕ} (womanTier : Fin n → Fin I)
    (manTier : Fin n → Fin J) (c : Fin I → Fin J → ℕ) :
    Fin n → (Fin n → ℝ) → Option (Fin J) :=
  fun w ↦ tierCategory manTier (c (womanTier w))

/-- The actual-source deterministic reference frequency for one woman-tier/man-tier pair. -/
noncomputable def referenceFrequency {n I J : ℕ} (womanTier : Fin n → Fin I)
    (manTier : Fin n → Fin J) (c : Fin I → Fin J → ℕ) (i : Fin I) (j : Fin J) :
    ((Fin n → Fin n → ℝ) × (ArrivalCoordinates n → ℝ)) → ℝ :=
  categoryFrequency (tierMen womanTier i) (flatCategory (referenceLabels womanTier manTier c))
    (some j) n

/-- The deterministic reference frequency has exact source-derived mean and variance. -/
theorem reference_frequency_moments {n I J : ℕ}
    (P : Fin n → Fin n → ℝ≥0) (hP : ∀ m w, 0 < P m w)
    (womanTier : Fin n → Fin I) (manTier : Fin n → Fin J)
    (β : Fin J → ℝ≥0) (hβ : ∀ j, 0 < β j) (c : Fin I → Fin J → ℕ)
    (i : Fin I) (j : Fin J) (hc : ∀ k, c i k ≤ (tierMen manTier k).card) :
    MemLp (referenceFrequency womanTier manTier c i j) 2
      (arrivalInputLaw P (fun m _ ↦ β (manTier m))) ∧
    (∫ z, referenceFrequency womanTier manTier c i j z
      ∂arrivalInputLaw P (fun m _ ↦ β (manTier m))) =
      ((tierMen womanTier i).card : ℝ) / n *
        ((β j : ℝ) * (c i j : ℝ) / ∑ k, (β k : ℝ) * (c i k : ℝ)) ∧
    variance (referenceFrequency womanTier manTier c i j)
      (arrivalInputLaw P (fun m _ ↦ β (manTier m))) ≤
      ((tierMen womanTier i).card : ℝ) / (4 * (n : ℝ)^2) := by
  classical
  have hf (w : Fin n) : Measurable (referenceLabels womanTier manTier c w) :=
    measurable_tierCategory _ _
  obtain ⟨hlp, hmean, hvar⟩ := arrival_frequency_moments P (fun m _ ↦ β (manTier m)) hP
    (fun m _ ↦ hβ (manTier m)) (referenceLabels womanTier manTier c) hf
    (tierMen womanTier i) (some j)
  refine ⟨hlp, ?_, hvar⟩
  change (∫ z, referenceFrequency womanTier manTier c i j z
    ∂arrivalInputLaw P (fun m _ ↦ β (manTier m))) = _ at hmean
  rw [hmean]
  have he (w : Fin n) (hw : w ∈ tierMen womanTier i) :
      (Measure.pi fun m ↦ expMeasure (β (manTier m) : ℝ)).real
        {x | referenceLabels womanTier manTier c w x = some j} =
        (β j : ℝ) * (c i j : ℝ) / ∑ k, (β k : ℝ) * (c i k : ℝ) := by
    have hwi : womanTier w = i := (Finset.mem_filter.mp hw).2
    change (Measure.pi fun m ↦ expMeasure (β (manTier m) : ℝ)).real
      {x | tierCategory manTier (c (womanTier w)) x = some j} = _
    rw [hwi]
    exact tierCategory_real manTier (c i) β hβ hc j
  rw [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul]
  ring

/-- The standard reference variance bound holds directly in the exact flat arrival source. -/
theorem reference_frequency_variance_le {n I J : ℕ}
    (P : Fin n → Fin n → ℝ≥0) (hP : ∀ m w, 0 < P m w)
    (womanTier : Fin n → Fin I) (manTier : Fin n → Fin J)
    (β : Fin J → ℝ≥0) (hβ : ∀ j, 0 < β j) (c : Fin I → Fin J → ℕ)
    (i : Fin I) (j : Fin J) (hn : 0 < n) :
    variance (referenceFrequency womanTier manTier c i j)
      (arrivalInputLaw P (fun m _ ↦ β (manTier m))) ≤ 1 / (4 * n) :=
  arrival_frequency_variance_le P (fun m _ ↦ β (manTier m)) hP
    (fun m _ ↦ hβ (manTier m)) (referenceLabels womanTier manTier c)
    (fun _ ↦ measurable_tierCategory _ _) (tierMen womanTier i) (some j) hn

/-- Actual reference frequencies are measurable before imposing any feasibility conditions. -/
theorem measurable_referenceFrequency {n I J : ℕ} (womanTier : Fin n → Fin I)
    (manTier : Fin n → Fin J) (c : Fin I → Fin J → ℕ) (i : Fin I) (j : Fin J) :
    Measurable (referenceFrequency womanTier manTier c i j) := by
  unfold referenceFrequency categoryFrequency
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro w hw
  apply measurable_const.ite _ measurable_const
  exact (measurableSet_singleton (some j)).preimage
    (measurable_flatCategory (referenceLabels womanTier manTier c)
      (fun _ ↦ measurable_tierCategory _ _) w)

/-- Reference square integrability holds at all sizes, including before eventual feasibility. -/
theorem memLp_referenceFrequency {n I J : ℕ}
    (P : Fin n → Fin n → ℝ≥0) (hP : ∀ m w, 0 < P m w)
    (womanTier : Fin n → Fin I) (manTier : Fin n → Fin J)
    (β : Fin J → ℝ≥0) (hβ : ∀ j, 0 < β j) (c : Fin I → Fin J → ℕ)
    (i : Fin I) (j : Fin J) :
    MemLp (referenceFrequency womanTier manTier c i j) 2
      (arrivalInputLaw P (fun m _ ↦ β (manTier m))) :=
  (arrival_frequency_moments P (fun m _ ↦ β (manTier m)) hP
    (fun m _ ↦ hβ (manTier m)) (referenceLabels womanTier manTier c)
    (fun _ ↦ measurable_tierCategory _ _) (tierMen womanTier i) (some j)).1

/-- Central reference counts round down the exact fixed G.2 coefficient times log n. -/
noncomputable def centralCounts {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ) (n : ℕ) : Fin I → Fin J → ℕ :=
  fun i j ↦ ⌊proposalCoefficient b α β αmin i j * Real.log n⌋₊

/-- The lower deterministic sandwich endpoint, rounded down. -/
noncomputable def lowerCounts {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin η : ℝ) (n : ℕ) : Fin I → Fin J → ℕ :=
  fun i j ↦ ⌊((1 - η) * proposalCoefficient b α β αmin i j) * Real.log n⌋₊

/-- The upper deterministic sandwich endpoint, rounded up. -/
noncomputable def upperCounts {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin η : ℝ) (n : ℕ) : Fin I → Fin J → ℕ :=
  fun i j ↦ ⌈((1 + η) * proposalCoefficient b α β αmin i j) * Real.log n⌉₊

/-- Natural logarithms of market sizes tend to infinity. -/
theorem log_market_tendsto : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- Floors of any fixed positive logarithmic scale occupy a vanishing market share. -/
theorem floor_log_share_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ (⌊c * Real.log n⌋₊ : ℝ) / n) atTop (𝓝 0) := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := (floor_mul_div_tendsto log_market_tendsto hc).mul hlog
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hln : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  dsimp only [Function.comp_def, id_eq]
  field_simp

/-- Ceilings of any fixed positive logarithmic scale also occupy a vanishing market share. -/
theorem ceil_log_share_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ (⌈c * Real.log n⌉₊ : ℝ) / n) atTop (𝓝 0) := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := (ceil_mul_div_tendsto log_market_tendsto hc).mul hlog
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hln : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  dsimp only [Function.comp_def, id_eq]
  field_simp

/-- A vanishing source count is eventually feasible in a tier with positive limiting share. -/
theorem eventually_count_le_of_shares (c v : ℕ → ℕ) (b : ℝ) (hb : 0 < b)
    (hc : Tendsto (fun n ↦ (c n : ℝ) / n) atTop (𝓝 0))
    (hv : Tendsto (fun n ↦ (v n : ℝ) / n) atTop (𝓝 b)) :
    ∀ᶠ n in atTop, c n ≤ v n := by
  have hsmall := hc (gt_mem_nhds (show (0 : ℝ) < b / 2 by positivity))
  have hlarge := hv (lt_mem_nhds (show b / 2 < b by linarith))
  filter_upwards [hsmall, hlarge, eventually_ge_atTop (1 : ℕ)] with n hs hl hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt : (c n : ℝ) < v n :=
    (div_lt_div_iff_of_pos_right hn0).mp (lt_trans hs hl)
  exact_mod_cast hlt.le

/-- The original tier-set cardinal is exactly its subtype cardinal used by the PR. -/
theorem tierMen_card_eq {n J : ℕ} (tier : Fin n → Fin J) (j : Fin J) :
    (tierMen tier j).card = Fintype.card {m // tier m = j} := by
  simp [tierMen, Fintype.card_subtype]

/-- All central reference prefixes are eventually feasible under the PR's rounded tier shares. -/
theorem centralCounts_eventually_feasible {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ)
    (hb : ∀ j, 0 < b j) (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j) (hmin : 0 < αmin)
    (manTier : (n : ℕ) → Fin n → Fin J)
    (hm : ∀ n j, |(Fintype.card {m // manTier n m = j} : ℝ) - n * b j| ≤ 1) :
    ∀ᶠ n in atTop, ∀ i j,
      centralCounts b α β αmin n i j ≤ (tierMen (manTier n) j).card := by
  rw [eventually_all]
  intro i
  rw [eventually_all]
  intro j
  apply eventually_count_le_of_shares _ _ (b j) (hb j)
  · exact floor_log_share_tendsto (proposalCoefficient_pos b α β αmin hb hα hβ hmin i j)
  · simpa only [tierMen_card_eq] using rounded_share_tendsto
      (fun n ↦ Fintype.card {m // manTier n m = j}) (b j) (fun n ↦ hm n j)

/-- The reference source is the unchanged independent flat source used by the actual arrival law. -/
noncomputable def referenceSourceLaw {n I J : ℕ} (womanTier : Fin n → Fin I)
    (manTier : Fin n → Fin J) (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) :=
  arrivalInputLaw (fun _ w ↦ α (womanTier w)) (fun m _ ↦ β (manTier m))

/-- The reference's original independent source law is a probability measure. -/
theorem isProbabilityMeasure_referenceSourceLaw {n I J : ℕ}
    (womanTier : Fin n → Fin I) (manTier : Fin n → Fin J)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j) :
    IsProbabilityMeasure (referenceSourceLaw womanTier manTier α β) := by
  have (w : Fin n) : IsProbabilityMeasure (expMeasure (α (womanTier w) : ℝ)) :=
    isProbabilityMeasure_expMeasure (by exact_mod_cast hα (womanTier w))
  have (m : Fin n) : IsProbabilityMeasure (expMeasure (β (manTier m) : ℝ)) :=
    isProbabilityMeasure_expMeasure (by exact_mod_cast hβ (manTier m))
  unfold referenceSourceLaw arrivalInputLaw
  infer_instance

/-- Central reference means converge to the product of the two stipulated population shares. -/
theorem central_reference_mean_tendsto {I J : ℕ} (a : Fin I → ℝ) (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ)
    (hb : ∀ j, 0 < b j) (hbsum : ∑ j, b j = 1)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j) (hmin : 0 < αmin)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (hw : ∀ n i, |(Fintype.card {w // womanTier n w = i} : ℝ) - n * a i| ≤ 1)
    (hm : ∀ n j, |(Fintype.card {m // manTier n m = j} : ℝ) - n * b j| ≤ 1)
    (i : Fin I) (j : Fin J) :
    Tendsto (fun n ↦ ∫ z,
      referenceFrequency (womanTier n) (manTier n) (centralCounts b α β αmin n) i j z
      ∂referenceSourceLaw (womanTier n) (manTier n) α β) atTop (𝓝 (a i * b j)) := by
  have hshare := rounded_share_tendsto
    (fun n ↦ Fintype.card {w // womanTier n w = i}) (a i) (fun n ↦ hw n i)
  have hratio := reference_tier_probability_tendsto log_market_tendsto b α β αmin
    hb hbsum hα hβ hmin i j
  apply (hshare.mul hratio).congr'
  filter_upwards [centralCounts_eventually_feasible b α β αmin hb hα hβ hmin manTier hm]
    with n hn
  have he := (reference_frequency_moments (fun _ w ↦ α (womanTier n w))
    (fun _ w ↦ hα (womanTier n w)) (womanTier n) (manTier n) β hβ
    (centralCounts b α β αmin n) i j (hn i)).2.1
  simpa only [referenceSourceLaw, centralCounts, tierMen_card_eq] using he.symm

/-- Reference variance vanishes under the unchanged arrival source for any count vectors. -/
theorem reference_variance_tendsto_zero {I J : ℕ}
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (c : (n : ℕ) → Fin I → Fin J → ℕ) (i : Fin I) (j : Fin J) :
    Tendsto (fun n ↦ variance (referenceFrequency (womanTier n) (manTier n) (c n) i j)
      (referenceSourceLaw (womanTier n) (manTier n) α β)) atTop (𝓝 0) := by
  have hu : Tendsto (fun n : ℕ ↦ 1 / (4 * (n : ℝ))) atTop (𝓝 0) := by
    simpa only [zero_div] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 4 |>.congr
        (fun _ ↦ by ring)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    (Eventually.of_forall (fun _ ↦ variance_nonneg _ _))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact reference_frequency_variance_le (fun _ w ↦ α (womanTier n w))
    (fun _ w ↦ hα (womanTier n w)) (womanTier n) (manTier n) β hβ (c n) i j hn

/-- Lower, central, and upper integer endpoints are ordered for every natural market size. -/
theorem lower_central_upper_counts {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin η : ℝ) (hη : 0 ≤ η)
    (hb : ∀ j, 0 < b j) (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j) (hmin : 0 < αmin)
    (n : ℕ) (i : Fin I) (j : Fin J) :
    lowerCounts b α β αmin η n i j ≤ centralCounts b α β αmin n i j ∧
      centralCounts b α β αmin n i j ≤ upperCounts b α β αmin η n i j := by
  have hc := (proposalCoefficient_pos b α β αmin hb hα hβ hmin i j).le
  have hlog := Real.log_natCast_nonneg n
  constructor
  · apply Nat.floor_mono
    nlinarith [mul_nonneg hη (mul_nonneg hc hlog)]
  · apply (Nat.floor_le_ceil _).trans
    apply Nat.ceil_mono
    nlinarith [mul_nonneg hη (mul_nonneg hc hlog)]

/-- The upper rounded logarithmic prefixes are eventually feasible in every positive-share tier. -/
theorem upperCounts_eventually_feasible {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin η : ℝ) (hη : 0 ≤ η)
    (hb : ∀ j, 0 < b j) (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j) (hmin : 0 < αmin)
    (manTier : (n : ℕ) → Fin n → Fin J)
    (hm : ∀ n j, |(Fintype.card {m // manTier n m = j} : ℝ) - n * b j| ≤ 1) :
    ∀ᶠ n in atTop, ∀ i j,
      upperCounts b α β αmin η n i j ≤ (tierMen (manTier n) j).card := by
  rw [eventually_all]
  intro i
  rw [eventually_all]
  intro j
  apply eventually_count_le_of_shares _ _ (b j) (hb j)
  · exact ceil_log_share_tendsto (mul_pos (by linarith)
      (proposalCoefficient_pos b α β αmin hb hα hβ hmin i j))
  · simpa only [tierMen_card_eq] using rounded_share_tendsto
      (fun n ↦ Fintype.card {m // manTier n m = j}) (b j) (fun n ↦ hm n j)

/-- All three deterministic endpoint families are eventually feasible simultaneously. -/
theorem endpointCounts_eventually_feasible {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin η : ℝ) (hη : 0 ≤ η)
    (hb : ∀ j, 0 < b j) (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j) (hmin : 0 < αmin)
    (manTier : (n : ℕ) → Fin n → Fin J)
    (hm : ∀ n j, |(Fintype.card {m // manTier n m = j} : ℝ) - n * b j| ≤ 1) :
    ∀ᶠ n in atTop, ∀ i j,
      lowerCounts b α β αmin η n i j ≤ (tierMen (manTier n) j).card ∧
      centralCounts b α β αmin n i j ≤ (tierMen (manTier n) j).card ∧
      upperCounts b α β αmin η n i j ≤ (tierMen (manTier n) j).card := by
  filter_upwards [upperCounts_eventually_feasible b α β αmin η hη hb hα hβ hmin manTier hm]
    with n hn i j
  have ho := lower_central_upper_counts b α β αmin η hη hb hα hβ hmin n i j
  exact ⟨ho.1.trans (ho.2.trans (hn i j)), ho.2.trans (hn i j), hn i j⟩

/-- The shell event is that the upper reference winner is absent from the lower source set. -/
def rowShell {n J : ℕ} (tier : Fin n → Fin J) (lower upper : Fin J → ℕ)
    (x : Fin n → ℝ) : Prop :=
  ¬ ∃ m ∈ sourceSet tier lower, winner (sourceSet tier upper) x = some m

/-- The source shell is measurable, including empty-prefix and tie cases. -/
theorem measurableSet_rowShell {n J : ℕ} (tier : Fin n → Fin J)
    (lower upper : Fin J → ℕ) : MeasurableSet {x | rowShell tier lower upper x} := by
  let E : Set (Option (Fin n)) := {o | ¬ ∃ m ∈ sourceSet tier lower, o = some m}
  exact (show MeasurableSet E from MeasurableSet.of_discrete).preimage (measurable_winner _)

/-- The exact shell probability is one minus the lower-to-upper total rate ratio. -/
theorem rowShell_real {n J : ℕ} (tier : Fin n → Fin J) (lower upper : Fin J → ℕ)
    (β : Fin J → ℝ≥0) (hβ : ∀ j, 0 < β j) (hlu : ∀ j, lower j ≤ upper j)
    (hu : ∀ j, upper j ≤ (tierMen tier j).card) :
    (Measure.pi fun m ↦ expMeasure (β (tier m) : ℝ)).real
      {x | rowShell tier lower upper x} =
      1 - (∑ j, (β j : ℝ) * (lower j : ℝ)) /
        ∑ j, (β j : ℝ) * (upper j : ℝ) := by
  have (m : Fin n) : IsProbabilityMeasure (expMeasure (β (tier m) : ℝ)) :=
    isProbabilityMeasure_expMeasure (by exact_mod_cast hβ (tier m))
  have hE : MeasurableSet {x : Fin n → ℝ |
      ∃ m ∈ sourceSet tier lower, winner (sourceSet tier upper) x = some m} := by
    simpa only [rowShell, Set.compl_ofPred, not_not] using
      (measurableSet_rowShell tier lower upper).compl
  change (Measure.pi fun m ↦ expMeasure (β (tier m) : ℝ)).real
    ({x | ∃ m ∈ sourceSet tier lower, winner (sourceSet tier upper) x = some m}ᶜ) = _
  rw [probReal_compl_eq_one_sub hE]
  congr 1
  rw [measureReal_def, winner_in_measure (fun m ↦ (β (tier m) : ℝ))
    (fun m ↦ by exact_mod_cast hβ (tier m)) _ _ (sourceSet_mono tier lower upper hlu),
    ENNReal.toReal_ofReal (div_nonneg
      (Finset.sum_nonneg (fun m _ ↦ NNReal.coe_nonneg _))
      (Finset.sum_nonneg (fun m _ ↦ NNReal.coe_nonneg _))),
    sourceSet_rate tier lower (fun j ↦ (β j : ℝ)) (fun j ↦ (hlu j).trans (hu j)),
    sourceSet_rate tier upper (fun j ↦ (β j : ℝ)) hu]

/-- The same shell probability holds for a fixed woman's row in the original arrival source. -/
theorem arrival_rowShell_real {n J : ℕ}
    (P : Fin n → Fin n → ℝ≥0) (hP : ∀ m w, 0 < P m w)
    (tier : Fin n → Fin J) (lower upper : Fin J → ℕ)
    (β : Fin J → ℝ≥0) (hβ : ∀ j, 0 < β j) (hlu : ∀ j, lower j ≤ upper j)
    (hu : ∀ j, upper j ≤ (tierMen tier j).card) (w : Fin n) :
    (arrivalInputLaw P (fun m _ ↦ β (tier m))).real
      {z | rowShell tier lower upper (fun m ↦ z.2 (w, m))} =
      1 - (∑ j, (β j : ℝ) * (lower j : ℝ)) /
        ∑ j, (β j : ℝ) * (upper j : ℝ) := by
  let E : Set (Option (Fin n)) := {o | ¬ ∃ m ∈ sourceSet tier lower, o = some m}
  have he := congrArg ENNReal.toReal (arrivalCategory_measure P (fun m _ ↦ β (tier m)) hP
    (fun m _ ↦ hβ (tier m)) (fun _ ↦ winner (sourceSet tier upper))
    (fun _ ↦ measurable_winner _) w E MeasurableSet.of_discrete)
  exact he.trans (rowShell_real tier lower upper β hβ hlu hu)

/-- A winner retained by a smaller source set remains its winner when source scores are distinct. -/
theorem winner_eq_of_subset {n : ℕ} (S T : Finset (Fin n)) (hST : S ⊆ T)
    (x : Fin n → ℝ) (hx : Set.InjOn x T) (m : Fin n)
    (hm : m ∈ S) (hw : winner T x = some m) : winner S x = some m := by
  apply (winner_eq_some_iff_strict S x (hx.mono hST) m).mpr
  refine ⟨hm, fun k hk hkm ↦ ?_⟩
  exact ((winner_eq_some_iff_strict T x hx m).mp hw).2 k (hST hk) hkm

/-- Outside the source shell, every two intermediate tier-prefix categories coincide pathwise. -/
theorem tierCategory_eq_of_sandwich {n J : ℕ} (tier : Fin n → Fin J)
    (lower actual central upper : Fin J → ℕ) (x : Fin n → ℝ)
    (hla : ∀ j, lower j ≤ actual j) (hlc : ∀ j, lower j ≤ central j)
    (hau : ∀ j, actual j ≤ upper j) (hcu : ∀ j, central j ≤ upper j)
    (hx : Set.InjOn x (sourceSet tier upper)) (hshell : ¬ rowShell tier lower upper x) :
    tierCategory tier actual x = tierCategory tier central x := by
  obtain ⟨m, hm, hw⟩ := not_not.mp hshell
  have ha := winner_eq_of_subset _ _ (sourceSet_mono tier actual upper hau) x hx m
    (sourceSet_mono tier lower actual hla hm) hw
  have hc := winner_eq_of_subset _ _ (sourceSet_mono tier central upper hcu) x hx m
    (sourceSet_mono tier lower central hlc hm) hw
  change (winner (sourceSet tier actual) x).map tier =
    (winner (sourceSet tier central) x).map tier
  rw [ha, hc]

/-- Weighted lower-floor to upper-ceiling shell ratios have the prescribed two-sided limit. -/
theorem shell_rate_ratio_tendsto {J : ℕ} (β c : Fin J → ℝ)
    (hβ : ∀ j, 0 < β j) (hc : ∀ j, 0 < c j) (η : ℝ)
    (hη : 0 < η) (hη1 : η < 1) (j0 : Fin J) :
    Tendsto (fun n : ℕ ↦ 1 -
      (∑ j, β j * (⌊((1 - η) * c j) * Real.log n⌋₊ : ℝ)) /
      ∑ j, β j * (⌈((1 + η) * c j) * Real.log n⌉₊ : ℝ))
      atTop (𝓝 (2 * η / (1 + η))) := by
  let S := ∑ j, β j * c j
  have hS : 0 < S := by
    apply Finset.sum_pos'
    · intro j _
      exact (mul_pos (hβ j) (hc j)).le
    · exact ⟨j0, Finset.mem_univ _, mul_pos (hβ j0) (hc j0)⟩
  have hlow : Tendsto (fun n : ℕ ↦
      ∑ j, β j * ((⌊((1 - η) * c j) * Real.log n⌋₊ : ℝ) / Real.log n))
      atTop (𝓝 ((1 - η) * S)) := by
    have h := tendsto_finsetSum Finset.univ (fun j _ ↦
      (floor_mul_div_tendsto (c := (1 - η) * c j) log_market_tendsto
        (mul_pos (by linarith) (hc j))).const_mul (β j))
    have he : (∑ j, β j * ((1 - η) * c j)) = (1 - η) * S := by
      dsimp only [S]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
    rw [he] at h
    exact h
  have hupp : Tendsto (fun n : ℕ ↦
      ∑ j, β j * ((⌈((1 + η) * c j) * Real.log n⌉₊ : ℝ) / Real.log n))
      atTop (𝓝 ((1 + η) * S)) := by
    have h := tendsto_finsetSum Finset.univ (fun j _ ↦
      (ceil_mul_div_tendsto (c := (1 + η) * c j) log_market_tendsto
        (mul_pos (by linarith) (hc j))).const_mul (β j))
    have he : (∑ j, β j * ((1 + η) * c j)) = (1 + η) * S := by
      dsimp only [S]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
    rw [he] at h
    exact h
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (hlow.div hupp (by positivity))
  have he : (1 : ℝ) - ((1 - η) * S) / ((1 + η) * S) = 2 * η / (1 + η) := by
    field_simp
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hln : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  simp only [Pi.div_apply, ← mul_div_assoc, ← Finset.sum_div]
  rw [div_div_div_cancel_right₀ hln]

/-- The actual deterministic reference shell probability has the expected asymptotic limit. -/
theorem rowShell_probability_tendsto {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin η : ℝ)
    (hη : 0 < η) (hη1 : η < 1)
    (hb : ∀ j, 0 < b j) (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j) (hmin : 0 < αmin)
    (manTier : (n : ℕ) → Fin n → Fin J)
    (hm : ∀ n j, |(Fintype.card {m // manTier n m = j} : ℝ) - n * b j| ≤ 1)
    (i : Fin I) (j0 : Fin J) :
    Tendsto (fun n ↦ (Measure.pi fun m ↦ expMeasure (β (manTier n m) : ℝ)).real
      {x | rowShell (manTier n) (lowerCounts b α β αmin η n i)
        (upperCounts b α β αmin η n i) x}) atTop (𝓝 (2 * η / (1 + η))) := by
  have h := shell_rate_ratio_tendsto (fun j ↦ (β j : ℝ))
    (proposalCoefficient b α β αmin i) (fun j ↦ by exact_mod_cast hβ j)
    (proposalCoefficient_pos b α β αmin hb hα hβ hmin i) η hη hη1 j0
  apply h.congr'
  filter_upwards [upperCounts_eventually_feasible b α β αmin η hη.le hb hα hβ hmin manTier hm]
    with n hn
  exact (rowShell_real (manTier n) (lowerCounts b α β αmin η n i)
    (upperCounts b α β αmin η n i) β hβ (fun j ↦
      (lower_central_upper_counts b α β αmin η hη.le hb hα hβ hmin n i j).1.trans
        (lower_central_upper_counts b α β αmin η hη.le hb hα hβ hmin n i j).2)
      (hn i)).symm

/-- The central deterministic reference frequency concentrates under the unchanged source law. -/
theorem central_reference_convergesInProbability {I J : ℕ}
    (a : Fin I → ℝ) (b : Fin J → ℝ) (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ)
    (hb : ∀ j, 0 < b j) (hbsum : ∑ j, b j = 1)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j) (hmin : 0 < αmin)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (hw : ∀ n i, |(Fintype.card {w // womanTier n w = i} : ℝ) - n * a i| ≤ 1)
    (hm : ∀ n j, |(Fintype.card {m // manTier n m = j} : ℝ) - n * b j| ≤ 1)
    (i : Fin I) (j : Fin J) :
    ConvergesInProbability (fun n ↦ referenceSourceLaw (womanTier n) (manTier n) α β)
      (fun n ↦ referenceFrequency (womanTier n) (manTier n) (centralCounts b α β αmin n) i j)
      (a i * b j) := by
  have (n : ℕ) : IsProbabilityMeasure
      (referenceSourceLaw (womanTier n) (manTier n) α β) :=
    isProbabilityMeasure_referenceSourceLaw _ _ α β hα hβ
  apply convergesInProbability_of_mean_variance
  · intro n
    exact memLp_referenceFrequency (fun _ w ↦ α (womanTier n w))
      (fun _ w ↦ hα (womanTier n w)) (womanTier n) (manTier n) β hβ
      (centralCounts b α β αmin n) i j
  · exact central_reference_mean_tendsto a b α β αmin hb hbsum hα hβ hmin
      womanTier manTier hw hm i j
  · exact reference_variance_tendsto_zero α β hα hβ womanTier manTier
      (centralCounts b α β αmin) i j

end Ashlagi.ReferenceModel
