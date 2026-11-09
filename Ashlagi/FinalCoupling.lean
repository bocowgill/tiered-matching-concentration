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

public import Ashlagi.ArrivalWinner
public import Ashlagi.ArrivalBands

/-!
# Exact match-type concentration conditional only on Proposition G.2

The concrete arrival law and deterministic source-prefix winner identity couple actual held
tiers to a fixed central reference. Count-band failures and exponential source shells bound
its expected frequency error. The only remaining source proposition is explicit in the final
theorem; no coupling or reference-law hypothesis is assumed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

namespace Ashlagi.FinalCoupling

open Arrival ReferenceModel ArrivalBands RowIndependence

local instance {J : ℕ} : MeasurableSpace (Option (Fin J)) := ⊤

/-- The exact PR match frequency evaluated on the concrete arrival profile. -/
noncomputable def actualFrequency {n I J : ℕ} (womanTier : Fin n → Fin I)
    (manTier : Fin n → Fin J) (i : Fin I) (j : Fin J)
    (z : (Fin n → Fin n → ℝ) × (ArrivalCoordinates n → ℝ)) : ℝ :=
  (Arxiv.«2009.05124».matchCount womanTier manTier i j
    (concreteArrivalProfile manTier z) : ℝ) / n

/-- Actual held-tier labels are measurable at every size, including the empty market. -/
theorem measurable_actualLabel {n J : ℕ} (manTier : Fin n → Fin J) (w : Fin n) :
    Measurable (fun z ↦ heldTier manTier (concreteArrivalProfile manTier z) w) :=
  (show Measurable (fun p : StableMarriage.Profile n ↦ heldTier manTier p w) from
    measurable_from_top).comp (measurable_concreteArrivalProfile manTier)

/-- The reference label reads only the designated original source row. -/
theorem measurable_referenceLabel {n J : ℕ} (manTier : Fin n → Fin J)
    (c : Fin J → ℕ) (w : Fin n) :
    Measurable (fun z : (Fin n → Fin n → ℝ) × (ArrivalCoordinates n → ℝ) ↦
      tierCategory manTier c (fun m ↦ z.2 (w, m))) :=
  (measurable_tierCategory manTier c).comp
    (Measurable.of_eval (fun m ↦ (measurable_pi_apply (w, m)).comp measurable_snd))

/-- Exact normalized match counts are the category frequencies of actual held-tier labels. -/
theorem actualFrequency_eq_categoryFrequency {n I J : ℕ} (womanTier : Fin n → Fin I)
    (manTier : Fin n → Fin J) (i : Fin I) (j : Fin J) :
    actualFrequency womanTier manTier i j =
      categoryFrequency (tierMen womanTier i)
        (fun w z ↦ heldTier manTier (concreteArrivalProfile manTier z) w) (some j) n := by
  funext z
  exact (categoryFrequency_heldTier womanTier manTier i j
    (concreteArrivalProfile manTier) z).symm

/-- A source shell has its original row probability under the full arrival input law. -/
theorem arrival_rowShell_real_eq_row {n J : ℕ}
    (P : Fin n → Fin n → ℝ≥0) (hP : ∀ m w, 0 < P m w)
    (manTier : Fin n → Fin J) (lower upper : Fin J → ℕ)
    (β : Fin J → ℝ≥0) (hβ : ∀ j, 0 < β j) (w : Fin n) :
    (arrivalInputLaw P (fun m _ ↦ β (manTier m))).real
      {z | rowShell manTier lower upper (fun m ↦ z.2 (w, m))} =
      (Measure.pi fun m ↦ expMeasure (β (manTier m) : ℝ)).real
        {x | rowShell manTier lower upper x} := by
  let E : Set (Option (Fin n)) :=
    {o | ¬ ∃ m ∈ sourceSet manTier lower, o = some m}
  exact congrArg ENNReal.toReal (arrivalCategory_measure P
    (fun m _ ↦ β (manTier m)) hP (fun m _ ↦ hβ (manTier m))
    (fun _ ↦ ReferenceRace.winner (sourceSet manTier upper))
    (fun _ ↦ ReferenceRace.measurable_winner _) w E MeasurableSet.of_discrete)

/-- Actual and central labels disagree only through a count-band failure or a source shell. -/
theorem actual_label_mismatch_le {n I J : ℕ} [NeZero n]
    (womanTier : Fin n → Fin I) (manTier : Fin n → Fin J)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (lower central upper : Fin J → ℕ)
    (hlc : ∀ j, lower j ≤ central j) (hcu : ∀ j, central j ≤ upper j) (w : Fin n) :
    (referenceSourceLaw womanTier manTier α β).real
      {z | heldTier manTier (concreteArrivalProfile manTier z) w ≠
        tierCategory manTier central (fun m ↦ z.2 (w, m))} ≤
      (referenceSourceLaw womanTier manTier α β).real
        (bandFailure manTier lower upper w) +
        (Measure.pi fun m ↦ expMeasure (β (manTier m) : ℝ)).real
          {x | rowShell manTier lower upper x} := by
  classical
  let μ := referenceSourceLaw womanTier manTier α β
  have : IsProbabilityMeasure μ :=
    isProbabilityMeasure_referenceSourceLaw womanTier manTier α β hα hβ
  let B := bandFailure manTier lower upper w
  let S := {z : (Fin n → Fin n → ℝ) × (ArrivalCoordinates n → ℝ) |
    rowShell manTier lower upper (fun m ↦ z.2 (w, m))}
  have hsub : ∀ᵐ z ∂μ,
      (heldTier manTier (concreteArrivalProfile manTier z) w ≠
        tierCategory manTier central (fun m ↦ z.2 (w, m))) → z ∈ B ∪ S := by
    filter_upwards [ae_injective_input_women (fun _ v ↦ α (womanTier v))
      (fun m _ ↦ β (manTier m)) (fun m _ ↦ hβ (manTier m))] with z hz hne
    by_cases hb : z ∈ B
    · exact Or.inl hb
    by_cases hs : z ∈ S
    · exact Or.inr hs
    have hcounts : ∀ j, lower j ≤ sourceProposalCount manTier j w z ∧
        sourceProposalCount manTier j w z ≤ upper j := not_not.mp hb
    have hactual : heldTier manTier (concreteArrivalProfile manTier z) w =
        tierCategory manTier (fun j ↦ sourceProposalCount manTier j w z)
          (fun m ↦ z.2 (w, m)) := by
      have ha := ArrivalWinner.heldTier_eq_tierCategory
        (arrivalMenRanks z.1) manTier z.2 hz w
      change heldTier manTier (arrivalProfile (fun r ↦ pick r manTier) (n * n) z) w =
        tierCategory manTier (fun j ↦ proposalCount manTier j
          (arrivalProfile (fun r ↦ pick r manTier) (n * n) z) w)
          (fun m ↦ z.2 (w, m)) at ha
      simpa only [sourceProposalCount, concreteArrivalProfile, dite_eq_right (NeZero.ne n)] using ha
    have hcat := tierCategory_eq_of_sandwich manTier lower
      (fun j ↦ sourceProposalCount manTier j w z) central upper (fun m ↦ z.2 (w, m))
      (fun j ↦ (hcounts j).1) hlc (fun j ↦ (hcounts j).2) hcu (hz w).injOn hs
    exact False.elim (hne (hactual.trans hcat))
  have hm : μ {z | heldTier manTier (concreteArrivalProfile manTier z) w ≠
      tierCategory manTier central (fun m ↦ z.2 (w, m))} ≤ μ (B ∪ S) :=
    measure_mono_ae hsub
  have hrow : μ.real S = (Measure.pi fun m ↦ expMeasure (β (manTier m) : ℝ)).real
      {x | rowShell manTier lower upper x} :=
    arrival_rowShell_real_eq_row (fun _ v ↦ α (womanTier v))
      (fun _ v ↦ hα (womanTier v)) manTier lower upper β hβ w
  calc
    _ ≤ μ.real (B ∪ S) := ENNReal.toReal_mono (measure_ne_top _ _) hm
    _ ≤ μ.real B + μ.real S := measureReal_union_le B S
    _ = _ := by rw [hrow]

/-- Actual frequencies are integrable under every finite measure on their source inputs. -/
theorem integrable_actualFrequency {n I J : ℕ} (womanTier : Fin n → Fin I)
    (manTier : Fin n → Fin J) (i : Fin I) (j : Fin J)
    (μ : Measure ((Fin n → Fin n → ℝ) × (ArrivalCoordinates n → ℝ)))
    [IsFiniteMeasure μ] :
    Integrable (actualFrequency womanTier manTier i j) μ := by
  rw [actualFrequency_eq_categoryFrequency]
  exact integrable_categoryFrequency μ _ _ _ _ (fun w _ ↦
    (measurableSet_singleton (some j)).preimage (measurable_actualLabel manTier w))

/-- The fixed central reference coupling error, independent of the sandwich tolerance. -/
noncomputable def couplingError {n I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ)
    (womanTier : Fin n → Fin I) (manTier : Fin n → Fin J) (i : Fin I) (j : Fin J) : ℝ :=
  ∫ z, |actualFrequency womanTier manTier i j z -
    referenceFrequency womanTier manTier (centralCounts b α β αmin n) i j z|
      ∂referenceSourceLaw womanTier manTier α β

/-- Every fixed central coupling error is nonnegative. -/
theorem couplingError_nonneg {n I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ)
    (womanTier : Fin n → Fin I) (manTier : Fin n → Fin J) (i : Fin I) (j : Fin J) :
    0 ≤ couplingError b α β αmin womanTier manTier i j :=
  integral_nonneg (fun _ ↦ abs_nonneg _)

/-- Uniform count-band and row-shell errors control the expected exact frequency difference. -/
theorem couplingError_le_band_shell {n I J : ℕ} [NeZero n] (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin η : ℝ)
    (hb : ∀ j, 0 < b j) (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (hmin : 0 < αmin) (hη : 0 ≤ η)
    (womanTier : Fin n → Fin I) (manTier : Fin n → Fin J) (i : Fin I) (j : Fin J)
    {d : ℝ} (hd : 0 ≤ d)
    (hfailure : ∀ w, womanTier w = i →
      (referenceSourceLaw womanTier manTier α β).real
        (bandFailure manTier (lowerCounts b α β αmin η n i)
          (upperCounts b α β αmin η n i) w) ≤ d) :
    couplingError b α β αmin womanTier manTier i j ≤ d +
      (Measure.pi fun m ↦ expMeasure (β (manTier m) : ℝ)).real
        {x | rowShell manTier (lowerCounts b α β αmin η n i)
          (upperCounts b α β αmin η n i) x} := by
  classical
  let μ := referenceSourceLaw womanTier manTier α β
  have : IsProbabilityMeasure μ :=
    isProbabilityMeasure_referenceSourceLaw womanTier manTier α β hα hβ
  let A := fun w z ↦ heldTier manTier (concreteArrivalProfile manTier z) w
  let B := flatCategory (M := Fin n → Fin n → ℝ)
    (referenceLabels womanTier manTier (centralCounts b α β αmin n))
  have hA (w : Fin n) : Measurable (A w) := measurable_actualLabel manTier w
  have hB (w : Fin n) : Measurable (B w) :=
    measurable_flatCategory _ (fun _ ↦ measurable_tierCategory _ _) w
  have hu := integral_abs_category_counts_sub_le_uniform μ (tierMen womanTier i)
    A B (some j) (fun w _ ↦ (measurableSet_singleton _).preimage (hA w))
    (fun w _ ↦ (measurableSet_singleton _).preimage (hB w))
    (fun w _ ↦ (measurableSet_eq_fun (hA w) (hB w)).compl)
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n) : (0 : ℝ) < n)
    (card_finset_fin_le_market _) (add_nonneg hd ENNReal.toReal_nonneg) (by
      intro w hw
      have hwi : womanTier w = i := (Finset.mem_filter.mp hw).2
      change μ.real {z | heldTier manTier (concreteArrivalProfile manTier z) w ≠
        tierCategory manTier (centralCounts b α β αmin n (womanTier w))
          (fun m ↦ z.2 (w, m))} ≤ _
      rw [hwi]
      have hmismatch := actual_label_mismatch_le womanTier manTier α β hα hβ
        (lowerCounts b α β αmin η n i) (centralCounts b α β αmin n i)
        (upperCounts b α β αmin η n i)
        (fun k ↦ (lower_central_upper_counts b α β αmin η hη hb hα hβ hmin n i k).1)
        (fun k ↦ (lower_central_upper_counts b α β αmin η hη hb hα hβ hmin n i k).2) w
      exact hmismatch.trans (add_le_add (hfailure w hwi) le_rfl))
  simpa only [couplingError, actualFrequency_eq_categoryFrequency, referenceFrequency,
    categoryFrequency, sub_div, A, B, μ, measureReal_def] using hu

/-- Proposition G.2 makes the fixed central coupling error vanish in the exact source law. -/
theorem couplingError_tendsto_zero_of_propositionG2 {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ)
    (hb : ∀ j, 0 < b j) (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (hm : ∀ n j, |(Fintype.card {m // manTier n m = j} : ℝ) - n * b j| ≤ 1)
    (i : Fin I) (j : Fin J) (hG2 : PropositionG2 b α β αmin womanTier manTier i) :
    Tendsto (fun n ↦ couplingError b α β αmin (womanTier n) (manTier n) i j)
      atTop (𝓝 0) := by
  have hmin : 0 < αmin := hG2.1.pos hα
  apply tendsto_zero_of_shell_bounds _
    (fun n ↦ couplingError_nonneg b α β αmin (womanTier n) (manTier n) i j)
  intro η hη hη1
  let r := fun n ↦ (bandFailureEnvelope b α β αmin η womanTier manTier i n).toReal +
    (Measure.pi fun m ↦ expMeasure (β (manTier n m) : ℝ)).real
      {x | rowShell (manTier n) (lowerCounts b α β αmin η n i)
        (upperCounts b α β αmin η n i) x}
  refine ⟨r, ?_, ?_⟩
  · have he := bandFailureEnvelope_real_tendsto_zero b α β αmin hα hβ
      womanTier manTier i hG2 η hη
    have hs := rowShell_probability_tendsto b α β αmin η hη hη1 hb hα hβ hmin manTier hm i j
    simpa only [zero_add] using he.add hs
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have : NeZero n := ⟨by omega⟩
    exact couplingError_le_band_shell b α β αmin η hb hα hβ hmin hη.le
      (womanTier n) (manTier n) i j ENNReal.toReal_nonneg (fun w hw ↦
        bandFailure_real_le_envelope b α β αmin η hα hβ womanTier manTier i n w hw)

/-- The exact PR match-type concentration conclusion follows from Proposition G.2 alone.
The concrete law, central reference moments, and vanishing coupling error are all proved. -/
theorem match_type_concentration_of_propositionG2
    (I J : ℕ) (a : Fin I → ℝ) (b : Fin J → ℝ)
    (_ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (_ha_sum : ∑ i, a i = 1) (hb_sum : ∑ j, b j = 1)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (hw : ∀ n i, |(Fintype.card {w // womanTier n w = i} : ℝ) - n * a i| ≤ 1)
    (hm : ∀ n j, |(Fintype.card {m // manTier n m = j} : ℝ) - n * b j| ≤ 1)
    (i : Fin I) (j : Fin J) (αmin : ℝ)
    (hG2 : PropositionG2 b α β αmin womanTier manTier i) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (Arxiv.«2009.05124».market (womanTier n) (manTier n) α β).toMeasure
      {p | |(Arxiv.«2009.05124».matchCount (womanTier n) (manTier n) i j p : ℝ) / n -
        a i * b j| ≤ ε}) atTop (𝓝 1) := by
  let ν := fun n ↦ referenceSourceLaw (womanTier n) (manTier n) α β
  let p := fun n ↦ concreteArrivalProfile (manTier n)
  let Y := fun n ↦ referenceFrequency (womanTier n) (manTier n)
    (centralCounts b α β αmin n) i j
  have (n : ℕ) : IsProbabilityMeasure (ν n) :=
    isProbabilityMeasure_referenceSourceLaw _ _ α β hα hβ
  have hY (n : ℕ) : MemLp (Y n) 2 (ν n) :=
    memLp_referenceFrequency (fun _ w ↦ α (womanTier n w))
      (fun _ w ↦ hα (womanTier n w)) (womanTier n) (manTier n) β hβ
      (centralCounts b α β αmin n) i j
  apply match_type_concentration_of_integral_coupling a b α β womanTier manTier i j ν p
    (fun n ↦ measurable_concreteArrivalProfile (manTier n))
    (fun n ↦ concreteArrivalProfile_market_law (womanTier n) (manTier n) α β hα hβ)
    Y hY
  · exact central_reference_mean_tendsto a b α β αmin hb hb_sum hα hβ (hG2.1.pos hα)
      womanTier manTier hw hm i j
  · exact reference_variance_tendsto_zero α β hα hβ womanTier manTier
      (centralCounts b α β αmin) i j
  · intro n
    exact (integrable_actualFrequency (womanTier n) (manTier n) i j (ν n)).sub
      ((hY n).integrable one_le_two)
  · exact couplingError_tendsto_zero_of_propositionG2 b α β αmin hb hα hβ
      womanTier manTier hm i j hG2
  · exact hε

end Ashlagi.FinalCoupling
