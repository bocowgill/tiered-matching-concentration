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

public import Mathlib.Probability.Moments.Variance

/-!
# Probability transfer from a coupled reference family

These lemmas permit the actual variables to be dependent. The reference family's
concentration is supplied through its mean and variance. The spaces and measures may
vary with the index, as they do in finite random matching markets.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

namespace TieredMatching

/-- Convergence in probability to a real constant on varying probability spaces. -/
def ConvergesInProbability {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) (X : (n : ℕ) → Ω n → ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fun n ↦ (μ n).real {ω | ε < |X n ω - c|}) atTop (𝓝 0)

/-- A real-valued Markov bound for strict absolute-deviation events. -/
theorem tailReal_le_integral_abs {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ) (hX : Integrable X μ)
    {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε < |X ω|} ≤ (∫ ω, |X ω| ∂μ) / ε := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω ↦ |X ω|) (ae_of_all _ fun _ ↦ abs_nonneg _) hX.abs ε
  apply (le_div_iff₀ hε).2
  calc
    μ.real {ω | ε < |X ω|} * ε ≤ μ.real {ω | ε ≤ |X ω|} * ε := by
      exact mul_le_mul_of_nonneg_right
        (measureReal_mono (μ := μ) (fun ω (h : ε < |X ω|) ↦ h.le)
          (measure_ne_top _ _)) hε.le
    _ ≤ ∫ ω, |X ω| ∂μ := by simpa [mul_comm] using hm

/-- An `L¹`-small coupling error transfers convergence in probability. -/
theorem ConvergesInProbability.of_integral_abs_sub
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {μ : (n : ℕ) → Measure (Ω n)} [∀ n, IsFiniteMeasure (μ n)]
    {X Y : (n : ℕ) → Ω n → ℝ} {c : ℝ}
    (hY : ConvergesInProbability μ Y c)
    (hXY : ∀ n, Integrable (fun ω ↦ X n ω - Y n ω) (μ n))
    (herr : Tendsto (fun n ↦ ∫ ω, |X n ω - Y n ω| ∂μ n) atTop (𝓝 0)) :
    ConvergesInProbability μ X c := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hbound (n : ℕ) :
      (μ n).real {ω | ε < |X n ω - c|} ≤
        (∫ ω, |X n ω - Y n ω| ∂μ n) / (ε / 2) +
          (μ n).real {ω | ε / 2 < |Y n ω - c|} := by
    calc
      (μ n).real {ω | ε < |X n ω - c|} ≤
          (μ n).real ({ω | ε / 2 < |X n ω - Y n ω|} ∪
            {ω | ε / 2 < |Y n ω - c|}) := by
        refine measureReal_mono (μ := μ n) ?_ (measure_ne_top _ _)
        intro ω hω
        by_contra h
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at h
        have ht : |X n ω - c| ≤ |X n ω - Y n ω| + |Y n ω - c| := by
          rw [show X n ω - c = (X n ω - Y n ω) + (Y n ω - c) by ring]
          exact abs_add_le _ _
        change ε < |X n ω - c| at hω
        linarith [h.1, h.2]
      _ ≤ (μ n).real {ω | ε / 2 < |X n ω - Y n ω|} +
          (μ n).real {ω | ε / 2 < |Y n ω - c|} := measureReal_union_le _ _
      _ ≤ _ := add_le_add (tailReal_le_integral_abs (μ n) _ (hXY n) hhalf) le_rfl
  have hu := (herr.div_const (ε / 2)).add (hY (ε / 2) hhalf)
  simp only [zero_div, zero_add] at hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun _ ↦ measureReal_nonneg) hbound

/-- Mean convergence and vanishing variance imply concentration on varying spaces. -/
theorem convergesInProbability_of_mean_variance
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {μ : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {X : (n : ℕ) → Ω n → ℝ} {c : ℝ}
    (hX : ∀ n, MemLp (X n) 2 (μ n))
    (hmean : Tendsto (fun n ↦ ∫ ω, X n ω ∂μ n) atTop (𝓝 c))
    (hvar : Tendsto (fun n ↦ variance (X n) (μ n)) atTop (𝓝 0)) :
    ConvergesInProbability μ X c := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hmean' : ∀ᶠ n in atTop, |(∫ ω, X n ω ∂μ n) - c| < ε / 2 := by
    simpa [Real.dist_eq] using (Metric.tendsto_nhds.mp hmean) (ε / 2) hhalf
  have hbound : ∀ᶠ n in atTop,
      (μ n).real {ω | ε < |X n ω - c|} ≤ variance (X n) (μ n) / (ε / 2) ^ 2 := by
    filter_upwards [hmean'] with n hn
    have hcheb := meas_ge_le_variance_div_sq (hX n) hhalf
    have hreal : (μ n).real {ω | ε / 2 ≤ |X n ω - ∫ t, X n t ∂μ n|} ≤
        variance (X n) (μ n) / (ε / 2) ^ 2 := by
      have hh := ENNReal.toReal_mono (by simp) hcheb
      simpa only [measureReal_def,
        ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] using hh
    refine (measureReal_mono (μ := μ n) ?_ (measure_ne_top _ _)).trans hreal
    intro ω hω
    change ε < |X n ω - c| at hω
    change ε / 2 ≤ |X n ω - ∫ t, X n t ∂μ n|
    have ht : |X n ω - c| ≤
        |X n ω - ∫ t, X n t ∂μ n| + |(∫ t, X n t ∂μ n) - c| := by
      rw [show X n ω - c = (X n ω - ∫ t, X n t ∂μ n) +
        ((∫ t, X n t ∂μ n) - c) by ring]
      exact abs_add_le _ _
    linarith
  have hu := hvar.div_const ((ε / 2) ^ 2)
  simp only [zero_div] at hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    (Eventually.of_forall fun _ ↦ measureReal_nonneg) hbound

/-- The real-tail formulation yields the `ENNReal` good-event limit used in the PR. -/
theorem ConvergesInProbability.good_event_tendsto_one
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {μ : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {X : (n : ℕ) → Ω n → ℝ} {c : ℝ}
    (h : ConvergesInProbability μ X c) (hX : ∀ n, Measurable (X n))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ μ n {ω | |X n ω - c| ≤ ε}) atTop (𝓝 1) := by
  have heq (n : ℕ) : (μ n).real {ω | |X n ω - c| ≤ ε} =
      1 - (μ n).real {ω | ε < |X n ω - c|} := by
    have hm : MeasurableSet {ω | ε < |X n ω - c|} :=
      by simpa only [Real.norm_eq_abs] using
        measurableSet_lt measurable_const ((hX n).sub_const c).norm
    simpa only [Set.compl_ofPred, not_lt] using probReal_compl_eq_one_sub (μ := μ n) hm
  have hr : Tendsto (fun n ↦ (μ n).real {ω | |X n ω - c| ≤ ε}) atTop (𝓝 1) := by
    simp_rw [heq]
    simpa using tendsto_const_nhds.sub (h ε hε)
  have ho := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
  have heq' : (fun n ↦ μ n {ω | |X n ω - c| ≤ ε}) =
      (fun n ↦ ENNReal.ofReal ((μ n).real {ω | |X n ω - c| ≤ ε})) := by
    funext n
    exact (ofReal_measureReal (μ := μ n) (s := {ω | |X n ω - c| ≤ ε})
      (measure_ne_top _ _)).symm
  rw [heq']
  simpa only [Function.comp_def, ENNReal.ofReal_one] using ho

/-- A finite empirical coupling bound. No independence of the summands is required. -/
theorem integral_abs_normalized_sum_sub_le
    {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : Finset ι)
    (X Y : ι → Ω → ℝ) (P : ι → Set Ω)
    (hX : ∀ w ∈ s, Integrable (X w) μ) (hY : ∀ w ∈ s, Integrable (Y w) μ)
    (hP : ∀ w ∈ s, MeasurableSet (P w))
    (hXY : ∀ w ∈ s, ∀ ω, |X w ω - Y w ω| ≤ (P w).indicator (fun _ ↦ (1 : ℝ)) ω)
    {N : ℝ} (hN : 0 < N) :
    (∫ ω, |((∑ w ∈ s, X w ω) - ∑ w ∈ s, Y w ω) / N| ∂μ) ≤
      (∑ w ∈ s, μ.real (P w)) / N := by
  have hd : ∀ w ∈ s, Integrable (fun ω ↦ X w ω - Y w ω) μ :=
    fun w hw ↦ (hX w hw).sub (hY w hw)
  have hi : ∀ w ∈ s, Integrable ((P w).indicator (fun _ ↦ (1 : ℝ))) μ :=
    fun w hw ↦ (integrable_const (1 : ℝ)).indicator (hP w hw)
  calc
    (∫ ω, |((∑ w ∈ s, X w ω) - ∑ w ∈ s, Y w ω) / N| ∂μ) =
        (∫ ω, |∑ w ∈ s, (X w ω - Y w ω)| ∂μ) / N := by
      simp_rw [← Finset.sum_sub_distrib, abs_div, abs_of_pos hN]
      exact integral_div N _
    _ ≤ (∫ ω, ∑ w ∈ s, (P w).indicator (fun _ ↦ (1 : ℝ)) ω ∂μ) / N := by
      apply div_le_div_of_nonneg_right _ hN.le
      apply integral_mono (integrable_finsetSum s hd).abs (integrable_finsetSum s hi)
      intro ω
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun w hw ↦ hXY w hw ω)
    _ = (∑ w ∈ s, μ.real (P w)) / N := by
      rw [integral_finsetSum s hi]
      congr 1
      exact Finset.sum_congr rfl fun w hw ↦ integral_indicator_one (hP w hw)

/-- The indicators of a category disagree only when the underlying labels disagree. -/
theorem abs_category_indicator_sub_le {κ : Type*} [DecidableEq κ] (a b j : κ) :
    |(if a = j then (1 : ℝ) else 0) - (if b = j then 1 else 0)| ≤
      if a ≠ b then 1 else 0 := by
  by_cases hab : a = b
  · subst b
    simp
  · simp only [hab, ne_eq, not_false_eq_true, ite_true]
    split_ifs <;> norm_num

/-- Expected normalized category-count errors are bounded by average mismatch probabilities. -/
theorem integral_abs_category_counts_sub_le
    {Ω ι κ : Type*} [MeasurableSpace Ω] [DecidableEq κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : Finset ι) (A B : ι → Ω → κ) (j : κ)
    (hA : ∀ w ∈ s, MeasurableSet {ω | A w ω = j})
    (hB : ∀ w ∈ s, MeasurableSet {ω | B w ω = j})
    (hne : ∀ w ∈ s, MeasurableSet {ω | A w ω ≠ B w ω})
    {N : ℝ} (hN : 0 < N) :
    (∫ ω, |((∑ w ∈ s, if A w ω = j then (1 : ℝ) else 0) -
      ∑ w ∈ s, if B w ω = j then 1 else 0) / N| ∂μ) ≤
        (∑ w ∈ s, μ.real {ω | A w ω ≠ B w ω}) / N := by
  apply integral_abs_normalized_sum_sub_le μ s
    (fun w ω ↦ if A w ω = j then 1 else 0)
    (fun w ω ↦ if B w ω = j then 1 else 0)
    (fun w ↦ {ω | A w ω ≠ B w ω}) _ _ hne _ hN
  · intro w hw
    have hf : (fun ω ↦ if A w ω = j then (1 : ℝ) else 0) =
        {ω | A w ω = j}.indicator (fun _ ↦ (1 : ℝ)) := by
      funext ω
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [hf]
    exact (integrable_const (μ := μ) (1 : ℝ)).indicator (hA w hw)
  · intro w hw
    have hf : (fun ω ↦ if B w ω = j then (1 : ℝ) else 0) =
        {ω | B w ω = j}.indicator (fun _ ↦ (1 : ℝ)) := by
      funext ω
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [hf]
    exact (integrable_const (μ := μ) (1 : ℝ)).indicator (hB w hw)
  · intro w hw ω
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply] using
      abs_category_indicator_sub_le (A w ω) (B w ω) j

/-- A common per-agent mismatch bound also bounds expected normalized count error. -/
theorem integral_abs_category_counts_sub_le_uniform
    {Ω ι κ : Type*} [MeasurableSpace Ω] [DecidableEq κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : Finset ι) (A B : ι → Ω → κ) (j : κ)
    (hA : ∀ w ∈ s, MeasurableSet {ω | A w ω = j})
    (hB : ∀ w ∈ s, MeasurableSet {ω | B w ω = j})
    (hne : ∀ w ∈ s, MeasurableSet {ω | A w ω ≠ B w ω})
    {N d : ℝ} (hN : 0 < N) (hcard : (s.card : ℝ) ≤ N) (hd : 0 ≤ d)
    (hbound : ∀ w ∈ s, μ.real {ω | A w ω ≠ B w ω} ≤ d) :
    (∫ ω, |((∑ w ∈ s, if A w ω = j then (1 : ℝ) else 0) -
      ∑ w ∈ s, if B w ω = j then 1 else 0) / N| ∂μ) ≤ d := by
  refine (integral_abs_category_counts_sub_le μ s A B j hA hB hne hN).trans ?_
  apply (div_le_iff₀ hN).2
  calc
    (∑ w ∈ s, μ.real {ω | A w ω ≠ B w ω}) ≤ ∑ _w ∈ s, d :=
      Finset.sum_le_sum hbound
    _ = (s.card : ℝ) * d := by simp
    _ ≤ d * N := by nlinarith

/-- The fraction of agents in a specified category, with an arbitrary real normalization. -/
noncomputable def categoryFrequency {Ω ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (A : ι → Ω → κ) (j : κ) (N : ℝ) (ω : Ω) : ℝ :=
  (∑ w ∈ s, if A w ω = j then (1 : ℝ) else 0) / N

/-- Category indicators are integrable on a finite measure space. -/
theorem integrable_category_indicator {Ω κ : Type*} [MeasurableSpace Ω] [DecidableEq κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : Ω → κ) (j : κ)
    (hA : MeasurableSet {ω | A ω = j}) :
    Integrable (fun ω ↦ if A ω = j then (1 : ℝ) else 0) μ := by
  have hf : (fun ω ↦ if A ω = j then (1 : ℝ) else 0) =
      {ω | A ω = j}.indicator (fun _ ↦ (1 : ℝ)) := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [hf]
  exact (integrable_const (μ := μ) (1 : ℝ)).indicator hA

/-- Finite category frequencies are integrable, including at zero normalization. -/
theorem integrable_categoryFrequency {Ω ι κ : Type*}
    [MeasurableSpace Ω] [DecidableEq κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : Finset ι) (A : ι → Ω → κ) (j : κ) (N : ℝ)
    (hA : ∀ w ∈ s, MeasurableSet {ω | A w ω = j}) :
    Integrable (categoryFrequency s A j N) μ := by
  exact (integrable_finsetSum s fun w hw ↦ integrable_category_indicator μ (A w) j
    (hA w hw)).div_const N

/-- Coupled category counts concentrate when reference means converge, reference variances vanish,
and the common per-agent mismatch bound tends to zero. Actual labels may be dependent. -/
theorem categoryFrequency_converges_of_coupling
    {Ω ι : ℕ → Type*} {κ : Type*} [∀ n, MeasurableSpace (Ω n)] [DecidableEq κ]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (s : (n : ℕ) → Finset (ι n)) (A B : (n : ℕ) → ι n → Ω n → κ)
    (j : κ) (N d : ℕ → ℝ) (c : ℝ)
    (hA : ∀ n w, w ∈ s n → MeasurableSet {ω | A n w ω = j})
    (hB : ∀ n w, w ∈ s n → MeasurableSet {ω | B n w ω = j})
    (hne : ∀ n w, w ∈ s n → MeasurableSet {ω | A n w ω ≠ B n w ω})
    (hN : ∀ᶠ n in atTop, 0 < N n)
    (hcard : ∀ᶠ n in atTop, ((s n).card : ℝ) ≤ N n)
    (hd : ∀ n, 0 ≤ d n) (hd0 : Tendsto d atTop (𝓝 0))
    (hbound : ∀ n w, w ∈ s n → (μ n).real {ω | A n w ω ≠ B n w ω} ≤ d n)
    (hB2 : ∀ n, MemLp (categoryFrequency (s n) (B n) j (N n)) 2 (μ n))
    (hmean : Tendsto (fun n ↦ ∫ ω, categoryFrequency (s n) (B n) j (N n) ω ∂μ n)
      atTop (𝓝 c))
    (hvar : Tendsto (fun n ↦ variance (categoryFrequency (s n) (B n) j (N n)) (μ n))
      atTop (𝓝 0)) :
    ConvergesInProbability μ (fun n ↦ categoryFrequency (s n) (A n) j (N n)) c := by
  have hreference := convergesInProbability_of_mean_variance hB2 hmean hvar
  have hint (n : ℕ) : Integrable (fun ω ↦ categoryFrequency (s n) (A n) j (N n) ω -
      categoryFrequency (s n) (B n) j (N n) ω) (μ n) :=
    (integrable_categoryFrequency (μ n) (s n) (A n) j (N n) (hA n)).sub
      (integrable_categoryFrequency (μ n) (s n) (B n) j (N n) (hB n))
  apply hreference.of_integral_abs_sub hint
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hd0
    (Eventually.of_forall fun n ↦ integral_nonneg fun _ ↦ abs_nonneg _) ?_
  filter_upwards [hN, hcard] with n hn hc
  simpa only [categoryFrequency, ← sub_div] using
    integral_abs_category_counts_sub_le_uniform (μ n) (s n) (A n) (B n) j
      (hA n) (hB n) (hne n) hn hc (hd n) (hbound n)

/-- A real indicator has variance at most one quarter. -/
theorem variance_le_quarter_of_sq_eq_self {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : MemLp X 2 μ) (hsq : ∀ ω, X ω ^ 2 = X ω) :
    variance X μ ≤ 1 / 4 := by
  rw [variance_eq_sub hX]
  have heq : X ^ 2 = X := by
    funext ω
    exact hsq ω
  rw [heq]
  nlinarith [sq_nonneg ((∫ ω, X ω ∂μ) - 1 / 2)]

/-- The variance of a normalized sum of pairwise independent indicators is at most
its population size divided by four times the square of the normalization. -/
theorem variance_normalized_sum_le {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι) (X : ι → Ω → ℝ)
    (hX : ∀ w ∈ s, MemLp (X w) 2 μ)
    (hsq : ∀ w ∈ s, ∀ ω, X w ω ^ 2 = X w ω)
    (hind : Set.Pairwise (s : Set ι) (fun w v ↦ IndepFun (X w) (X v) μ)) (N : ℝ) :
    variance (fun ω ↦ (∑ w ∈ s, X w ω) / N) μ ≤ (s.card : ℝ) / (4 * N ^ 2) := by
  have hs : variance (fun ω ↦ ∑ w ∈ s, X w ω) μ = ∑ w ∈ s, variance (X w) μ := by
    have hfun : (fun ω ↦ ∑ w ∈ s, X w ω) = ∑ w ∈ s, X w := by
      funext ω
      simp
    rw [hfun]
    exact IndepFun.variance_sum hX hind
  have heq : (fun ω ↦ (∑ w ∈ s, X w ω) / N) =
      (fun ω ↦ (∑ w ∈ s, X w ω) * N⁻¹) := by
    funext ω
    exact div_eq_mul_inv _ _
  rw [heq, variance_mul_const, hs]
  calc
    (∑ w ∈ s, variance (X w) μ) * (N⁻¹) ^ 2 ≤
        (∑ _w ∈ s, (1 : ℝ) / 4) * (N⁻¹) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact Finset.sum_le_sum fun w hw ↦ variance_le_quarter_of_sq_eq_self μ (X w)
        (hX w hw) (hsq w hw)
    _ = (s.card : ℝ) / (4 * N ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring

/-- The mean of a category indicator is the probability of that category. -/
theorem integral_category_indicator {Ω κ : Type*} [MeasurableSpace Ω] [DecidableEq κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : Ω → κ) (j : κ)
    (hA : MeasurableSet {ω | A ω = j}) :
    (∫ ω, if A ω = j then (1 : ℝ) else 0 ∂μ) = μ.real {ω | A ω = j} := by
  have hf : (fun ω ↦ if A ω = j then (1 : ℝ) else 0) =
      {ω | A ω = j}.indicator (fun _ ↦ (1 : ℝ)) := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [hf]
  exact integral_indicator_one hA

/-- The mean frequency is the normalized sum of the individual category probabilities. -/
theorem integral_categoryFrequency {Ω ι κ : Type*}
    [MeasurableSpace Ω] [DecidableEq κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : Finset ι) (A : ι → Ω → κ) (j : κ) (N : ℝ)
    (hA : ∀ w ∈ s, MeasurableSet {ω | A w ω = j}) :
    (∫ ω, categoryFrequency s A j N ω ∂μ) =
      (∑ w ∈ s, μ.real {ω | A w ω = j}) / N := by
  simp only [categoryFrequency]
  rw [integral_div,
    integral_finsetSum s (fun w hw ↦ integrable_category_indicator μ (A w) j (hA w hw))]
  congr 1
  exact Finset.sum_congr rfl fun w hw ↦ integral_category_indicator μ (A w) j (hA w hw)

/-- With a common category probability, the expected frequency is population share times
that category probability. -/
theorem integral_categoryFrequency_of_common_probability {Ω ι κ : Type*}
    [MeasurableSpace Ω] [DecidableEq κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : Finset ι) (A : ι → Ω → κ)
    (j : κ) (N q : ℝ)
    (hA : ∀ w ∈ s, MeasurableSet {ω | A w ω = j})
    (hq : ∀ w ∈ s, μ.real {ω | A w ω = j} = q) :
    (∫ ω, categoryFrequency s A j N ω ∂μ) = (s.card : ℝ) / N * q := by
  rw [integral_categoryFrequency μ s A j N hA]
  rw [Finset.sum_congr rfl hq]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

/-- Category indicators belong to every finite `Lᵖ` space on a finite measure space. -/
theorem memLp_category_indicator {Ω κ : Type*} [MeasurableSpace Ω] [DecidableEq κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : Ω → κ) (j : κ)
    (hA : MeasurableSet {ω | A ω = j}) (p : ℝ≥0∞) :
    MemLp (fun ω ↦ if A ω = j then (1 : ℝ) else 0) p μ := by
  have hf : (fun ω ↦ if A ω = j then (1 : ℝ) else 0) =
      {ω | A ω = j}.indicator (fun _ ↦ (1 : ℝ)) := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [hf]
  exact (memLp_const (1 : ℝ)).indicator hA.nullMeasurableSet

/-- Finite category frequencies are square-integrable. -/
theorem memLp_categoryFrequency {Ω ι κ : Type*}
    [MeasurableSpace Ω] [DecidableEq κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : Finset ι) (A : ι → Ω → κ) (j : κ) (N : ℝ)
    (hA : ∀ w ∈ s, MeasurableSet {ω | A w ω = j}) :
    MemLp (categoryFrequency s A j N) 2 μ := by
  unfold categoryFrequency
  simpa only [div_eq_mul_inv] using
    (memLp_finsetSum s fun w hw ↦
      memLp_category_indicator μ (A w) j (hA w hw) 2).mul_const N⁻¹

/-- The usual `1/(4N)` reference bound when the population has at most `N` agents. -/
theorem variance_normalized_sum_le_of_card_le {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι) (X : ι → Ω → ℝ)
    (hX : ∀ w ∈ s, MemLp (X w) 2 μ)
    (hsq : ∀ w ∈ s, ∀ ω, X w ω ^ 2 = X w ω)
    (hind : Set.Pairwise (s : Set ι) (fun w v ↦ IndepFun (X w) (X v) μ))
    {N : ℝ} (hN : 0 < N) (hcard : (s.card : ℝ) ≤ N) :
    variance (fun ω ↦ (∑ w ∈ s, X w ω) / N) μ ≤ 1 / (4 * N) := by
  calc
    _ ≤ (s.card : ℝ) / (4 * N ^ 2) := variance_normalized_sum_le μ s X hX hsq hind N
    _ ≤ N / (4 * N ^ 2) := div_le_div_of_nonneg_right hcard (by positivity)
    _ = 1 / (4 * N) := by field_simp

/-- The deterministic reference frequency has the independent-indicator variance bound. -/
theorem variance_categoryFrequency_le {Ω ι κ : Type*}
    [MeasurableSpace Ω] [DecidableEq κ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι) (A : ι → Ω → κ) (j : κ)
    (hA : ∀ w ∈ s, MeasurableSet {ω | A w ω = j})
    (hind : Set.Pairwise (s : Set ι) (fun w v ↦
      IndepFun (fun ω ↦ if A w ω = j then (1 : ℝ) else 0)
        (fun ω ↦ if A v ω = j then (1 : ℝ) else 0) μ))
    {N : ℝ} (hN : 0 < N) (hcard : (s.card : ℝ) ≤ N) :
    variance (categoryFrequency s A j N) μ ≤ 1 / (4 * N) := by
  apply variance_normalized_sum_le_of_card_le μ s
    (fun w ω ↦ if A w ω = j then (1 : ℝ) else 0)
    (fun w hw ↦ memLp_category_indicator μ (A w) j (hA w hw) 2) _ hind hN hcard
  intro w hw ω
  split_ifs <;> norm_num

end TieredMatching
