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

public import TieredMatching.G2Moments
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Finite-mixture covariance and clipping repairs

Total covariance retains the covariance of conditional means. The explicit finite mixture
needs no regular conditional distributions. Perturbation and clipping estimates use global
integrated errors rather than unsupported pointwise conditional tail estimates.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TieredMatching.G2Deconditioning

/-- Every real function on a finite measurable space is square integrable under a finite measure. -/
theorem memLp_finite {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ) :
    MemLp X 2 μ := by
  apply MemLp.of_bound (measurable_of_finite X).aestronglyMeasurable (∑ ω, |X ω|)
  apply ae_of_all
  intro ω
  simpa only [Real.norm_eq_abs] using
    Finset.single_le_sum (fun i _ ↦ abs_nonneg (X i)) (Finset.mem_univ ω)

/-- The real mass of a finite PMF bind is the weighted sum of its conditional real masses. -/
theorem bind_mass_toReal {H Ω : Type*} [Fintype H]
    (ν : PMF H) (law : H → PMF Ω) (ω : Ω) :
    ((ν.bind law) ω).toReal = ∑ h, (ν h).toReal * (law h ω).toReal := by
  rw [PMF.bind_apply, tsum_fintype,
    ENNReal.toReal_sum (fun h _ ↦
      ENNReal.mul_ne_top (ν.apply_ne_top h) ((law h).apply_ne_top ω))]
  simp only [ENNReal.toReal_mul]

/-- Exact total expectation for a finite latent-state mixture. -/
theorem integral_bind {H Ω : Type*} [Fintype H] [Fintype Ω]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (ν : PMF H) (law : H → PMF Ω) (X : Ω → ℝ) :
    (∫ ω, X ω ∂(ν.bind law).toMeasure) =
      ∫ h, (∫ ω, X ω ∂(law h).toMeasure) ∂ν.toMeasure := by
  simp_rw [PMF.integral_eq_sum, smul_eq_mul, bind_mass_toReal, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- The exact finite law of total covariance, including covariance of the conditional means. -/
theorem covariance_bind {H Ω : Type*} [Fintype H] [Fintype Ω]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (ν : PMF H) (law : H → PMF Ω) (X Y : Ω → ℝ) :
    covariance X Y (ν.bind law).toMeasure =
      (∫ h, covariance X Y (law h).toMeasure ∂ν.toMeasure) +
        covariance (fun h ↦ ∫ ω, X ω ∂(law h).toMeasure)
          (fun h ↦ ∫ ω, Y ω ∂(law h).toMeasure) ν.toMeasure := by
  have hc (h : H) := covariance_eq_sub
    (memLp_finite (law h).toMeasure X) (memLp_finite (law h).toMeasure Y)
  rw [covariance_eq_sub (memLp_finite (ν.bind law).toMeasure X)
    (memLp_finite (ν.bind law).toMeasure Y)]
  rw [covariance_eq_sub
    (memLp_finite ν.toMeasure (fun h ↦ ∫ ω, X ω ∂(law h).toMeasure))
    (memLp_finite ν.toMeasure (fun h ↦ ∫ ω, Y ω ∂(law h).toMeasure))]
  simp_rw [hc]
  rw [integral_sub
    ((memLp_finite ν.toMeasure (fun h ↦ ∫ ω, (X * Y) ω ∂(law h).toMeasure)).integrable
      one_le_two)
    ((memLp_finite ν.toMeasure (fun h ↦ (∫ ω, X ω ∂(law h).toMeasure) *
      ∫ ω, Y ω ∂(law h).toMeasure)).integrable one_le_two)]
  simp only [Pi.mul_apply]
  rw [integral_bind ν law (fun ω ↦ X ω * Y ω), integral_bind ν law X, integral_bind ν law Y]
  ring

/-- The weighted-sum form of total covariance for direct finite-history applications. -/
theorem covariance_bind_eq_sum {H Ω : Type*} [Fintype H] [Fintype Ω]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (ν : PMF H) (law : H → PMF Ω) (X Y : Ω → ℝ) :
    covariance X Y (ν.bind law).toMeasure =
      (∑ h, (ν h).toReal * covariance X Y (law h).toMeasure) +
        covariance (fun h ↦ ∫ ω, X ω ∂(law h).toMeasure)
          (fun h ↦ ∫ ω, Y ω ∂(law h).toMeasure) ν.toMeasure := by
  rw [covariance_bind, PMF.integral_eq_sum]
  simp only [smul_eq_mul]

/-- Bounding one factor controls covariance by the other factor's `L¹` norm. -/
theorem abs_covariance_le_bound_mul_integral_abs
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    {M : ℝ} (hYM : ∀ ω, |Y ω| ≤ M) :
    |covariance X Y μ| ≤ 2 * M * (∫ ω, |X ω| ∂μ) := by
  have hx : |∫ ω, X ω ∂μ| ≤ ∫ ω, |X ω| ∂μ := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ) X
  have hy : |∫ ω, Y ω ∂μ| ≤ M := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := μ) (f := Y)
        (ae_of_all _ fun ω ↦ by simpa only [Real.norm_eq_abs] using hYM ω)
  have hp : |∫ ω, X ω * Y ω ∂μ| ≤ M * (∫ ω, |X ω| ∂μ) := by
    calc
      _ ≤ ∫ ω, |X ω * Y ω| ∂μ := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := μ) (fun ω ↦ X ω * Y ω)
      _ ≤ ∫ ω, M * |X ω| ∂μ := by
        apply integral_mono (hX.integrable_mul hY).abs
          ((hX.integrable one_le_two).abs.const_mul M)
        intro ω
        simpa only [Pi.mul_apply, abs_mul, mul_comm] using
          mul_le_mul_of_nonneg_left (hYM ω) (abs_nonneg (X ω))
      _ = M * (∫ ω, |X ω| ∂μ) := integral_const_mul M _
  rw [covariance_eq_sub hX hY]
  simp only [Pi.mul_apply]
  refine (abs_sub _ _).trans ?_
  have hprod := mul_le_mul hx hy (abs_nonneg _) (integral_nonneg (f := fun ω ↦ |X ω|)
    (μ := μ) (fun ω ↦ abs_nonneg (X ω)))
  rw [abs_mul]
  nlinarith

/-- Covariance is stable in `L¹` under uniformly bounded comparison variables.
Only `Y` and `X'` need the uniform bound, so the usual four-variable bound is a special case. -/
theorem covariance_perturbation_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y X' Y' : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hX' : MemLp X' 2 μ) (hY' : MemLp Y' 2 μ)
    {M : ℝ} (hYM : ∀ ω, |Y ω| ≤ M) (hX'M : ∀ ω, |X' ω| ≤ M) :
    |covariance X Y μ - covariance X' Y' μ| ≤
      2 * M * ((∫ ω, |X ω - X' ω| ∂μ) + ∫ ω, |Y ω - Y' ω| ∂μ) := by
  have heq : covariance X Y μ - covariance X' Y' μ =
      covariance (X - X') Y μ + covariance X' (Y - Y') μ := by
    rw [covariance_sub_left hX hX' hY, covariance_sub_right hX' hY hY']
    ring
  have h₁ := abs_covariance_le_bound_mul_integral_abs μ (X - X') Y (hX.sub hX') hY hYM
  have h₂ : |covariance X' (Y - Y') μ| ≤ 2 * M * (∫ ω, |Y ω - Y' ω| ∂μ) := by
    rw [covariance_comm]
    exact abs_covariance_le_bound_mul_integral_abs μ (Y - Y') X' (hY.sub hY') hX' hX'M
  rw [heq]
  refine (abs_add_le _ _).trans ?_
  calc
    _ ≤ 2 * M * (∫ ω, |X ω - X' ω| ∂μ) +
        2 * M * (∫ ω, |Y ω - Y' ω| ∂μ) := add_le_add h₁ h₂
    _ = _ := by ring

/-- All-good finite mixtures preserve the common conditional-mean variance term. -/
theorem covariance_bind_lower_of_common_means
    {H Ω : Type*} [Fintype H] [Fintype Ω]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (ν : PMF H) (law : H → PMF Ω) (X Y : Ω → ℝ) (Λ e₁ e₂ : H → ℝ)
    {a b M K C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hΛ : ∀ h, |Λ h| ≤ M) (he₁ : ∀ h, |e₁ h| ≤ K) (he₂ : ∀ h, |e₂ h| ≤ K)
    (hmeanX : ∀ h, (∫ ω, X ω ∂(law h).toMeasure) = a * Λ h + e₁ h)
    (hmeanY : ∀ h, (∫ ω, Y ω ∂(law h).toMeasure) = b * Λ h + e₂ h)
    (hcov : ∀ h, -C ≤ covariance X Y (law h).toMeasure) :
    -C + a * b * variance Λ ν.toMeasure - 2 * (a + b) * M * K - 2 * K ^ 2 ≤
      covariance X Y (ν.bind law).toMeasure := by
  have hc : -C ≤ ∫ h, covariance X Y (law h).toMeasure ∂ν.toMeasure := by
    have hh := integral_mono (integrable_const (-C))
      ((memLp_finite ν.toMeasure (fun h ↦ covariance X Y (law h).toMeasure)).integrable
        one_le_two) hcov
    simpa only [integral_const, probReal_univ, one_smul] using hh
  have hm := G2Moments.covariance_common_signal_lower ν.toMeasure Λ e₁ e₂
    (memLp_finite ν.toMeasure Λ) (memLp_finite ν.toMeasure e₁)
    (memLp_finite ν.toMeasure e₂) ha hb hM hK hΛ he₁ he₂
  have hmx : (fun h ↦ ∫ ω, X ω ∂(law h).toMeasure) = (fun h ↦ a * Λ h) + e₁ := by
    funext h
    exact hmeanX h
  have hmy : (fun h ↦ ∫ ω, Y ω ∂(law h).toMeasure) = (fun h ↦ b * Λ h) + e₂ := by
    funext h
    exact hmeanY h
  rw [covariance_bind, hmx, hmy]
  linarith

/-- A globally bounded rank has an integrated clipping error controlled by its global tail. -/
theorem integral_clip_error_le
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) {N cap : ℝ}
    (hcap : 0 ≤ cap) (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ N) :
    (∫ ω, |X ω - min (X ω) cap| ∂μ) ≤ N * μ.real {ω | cap < X ω} := by
  classical
  let bad : Set Ω := {ω | cap < X ω}
  have hm : MeasurableSet bad := measurableSet_lt measurable_const (measurable_of_finite X)
  have hp (ω : Ω) : |X ω - min (X ω) cap| ≤ bad.indicator (fun _ ↦ N) ω := by
    by_cases hb : cap < X ω
    · have hmem : ω ∈ bad := hb
      rw [Set.indicator_of_mem hmem, min_eq_right hb.le,
        abs_of_nonneg (sub_nonneg.mpr hb.le)]
      linarith [(hX ω).2]
    · have hmem : ω ∉ bad := hb
      rw [Set.indicator_of_notMem hmem, min_eq_left (le_of_not_gt hb), sub_self, abs_zero]
  calc
    _ ≤ ∫ ω, bad.indicator (fun _ ↦ N) ω ∂μ :=
      integral_mono ((memLp_finite μ (fun ω ↦ |X ω - min (X ω) cap|)).integrable one_le_two)
        ((integrable_const N).indicator hm) hp
    _ = N * μ.real {ω | cap < X ω} := by
      rw [integral_indicator_const N hm]
      simp only [smul_eq_mul, mul_comm, bad]

/-- Global clipping perturbation needs no bound on a conditional tail probability. -/
theorem covariance_clip_error_le
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ) {N cap : ℝ}
    (hN : 0 ≤ N) (hcap : 0 ≤ cap)
    (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ N) (hY : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ N) :
    |covariance X Y μ - covariance (fun ω ↦ min (X ω) cap) (fun ω ↦ min (Y ω) cap) μ| ≤
      2 * N ^ 2 * (μ.real {ω | cap < X ω} + μ.real {ω | cap < Y ω}) := by
  have hp := covariance_perturbation_le μ X Y (fun ω ↦ min (X ω) cap)
    (fun ω ↦ min (Y ω) cap) (memLp_finite μ X) (memLp_finite μ Y)
    (memLp_finite μ _) (memLp_finite μ _)
    (M := N) (fun ω ↦ by rw [abs_of_nonneg (hY ω).1]; exact (hY ω).2)
    (fun ω ↦ by
      rw [abs_of_nonneg (le_min (hX ω).1 hcap)]
      exact (min_le_left _ _).trans (hX ω).2)
  have hx := integral_clip_error_le μ X hcap hX
  have hy := integral_clip_error_le μ Y hcap hY
  have he := mul_le_mul_of_nonneg_left (add_le_add hx hy) (by positivity : 0 ≤ 2 * N)
  nlinarith

/-- A global union-tail bound controls the covariance error of both clipped ranks. -/
theorem covariance_clip_error_le_of_tail
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ) {N cap δ : ℝ}
    (hN : 0 ≤ N) (hcap : 0 ≤ cap)
    (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ N) (hY : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ N)
    (htail : μ.real {ω | cap < X ω ∨ cap < Y ω} ≤ δ) :
    |covariance X Y μ - covariance (fun ω ↦ min (X ω) cap) (fun ω ↦ min (Y ω) cap) μ| ≤
      4 * N ^ 2 * δ := by
  have hx : μ.real {ω | cap < X ω} ≤ δ :=
    (measureReal_mono (μ := μ) (fun _ h ↦ Or.inl h) (measure_ne_top _ _)).trans htail
  have hy : μ.real {ω | cap < Y ω} ≤ δ :=
    (measureReal_mono (μ := μ) (fun _ h ↦ Or.inr h) (measure_ne_top _ _)).trans htail
  have hp := covariance_clip_error_le μ X Y hN hcap hX hY
  have hh := mul_le_mul_of_nonneg_left (add_le_add hx hy) (by positivity : 0 ≤ 2 * N ^ 2)
  nlinarith

/-- Masking a bounded variable off a bad set has an `L¹` cost equal to its bound times bad mass. -/
theorem integral_mask_error_le
    {H : Type*} [Fintype H] [DecidableEq H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (μ : Measure H) [IsProbabilityMeasure μ] (good : Finset H) (X : H → ℝ)
    {M : ℝ} (hX : ∀ h, |X h| ≤ M) :
    (∫ h, |X h - (if h ∈ good then X h else 0)| ∂μ) ≤
      M * μ.real {h | h ∉ good} := by
  classical
  let bad : Set H := {h | h ∉ good}
  have hm : MeasurableSet bad := (Set.toFinite bad).measurableSet
  have hp (h : H) : |X h - (if h ∈ good then X h else 0)| ≤
      bad.indicator (fun _ ↦ M) h := by
    by_cases hh : h ∈ good
    · rw [ite_eq_left hh, sub_self, abs_zero,
        Set.indicator_of_notMem (show h ∉ bad by exact fun hn ↦ hn hh)]
    · rw [ite_eq_right hh, sub_zero, Set.indicator_of_mem (show h ∈ bad by exact hh)]
      exact hX h
  calc
    _ ≤ ∫ h, bad.indicator (fun _ ↦ M) h ∂μ :=
      integral_mono ((memLp_finite μ _).integrable one_le_two)
        ((integrable_const M).indicator hm) hp
    _ = M * μ.real {h | h ∉ good} := by
      rw [integral_indicator_const M hm]
      simp only [smul_eq_mul, mul_comm, bad]

/-- The covariance of means changes by at most a squared-bound times the bad-state mass. -/
theorem covariance_mask_error_le
    {H : Type*} [Fintype H] [DecidableEq H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (μ : Measure H) [IsProbabilityMeasure μ] (good : Finset H) (X Y : H → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hX : ∀ h, |X h| ≤ M) (hY : ∀ h, |Y h| ≤ M) :
    |covariance X Y μ - covariance (fun h ↦ if h ∈ good then X h else 0)
      (fun h ↦ if h ∈ good then Y h else 0) μ| ≤ 4 * M ^ 2 * μ.real {h | h ∉ good} := by
  classical
  have hmask (h : H) : |if h ∈ good then X h else 0| ≤ M := by
    split_ifs
    · exact hX h
    · simpa only [abs_zero] using hM
  have hp := covariance_perturbation_le μ X Y (fun h ↦ if h ∈ good then X h else 0)
    (fun h ↦ if h ∈ good then Y h else 0) (memLp_finite μ X) (memLp_finite μ Y)
    (memLp_finite μ _) (memLp_finite μ _) hY hmask
  have hx := integral_mask_error_le μ good X hX
  have hy := integral_mask_error_le μ good Y hY
  have he := mul_le_mul_of_nonneg_left (add_le_add hx hy) (by positivity : 0 ≤ 2 * M)
  nlinarith

/-- Nonnegative bounded random variables have means in the same interval. -/
theorem integral_bounds_of_nonnegative_bounded
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Integrable X μ) {M : ℝ}
    (hbound : ∀ ω, 0 ≤ X ω ∧ X ω ≤ M) :
    0 ≤ (∫ ω, X ω ∂μ) ∧ (∫ ω, X ω ∂μ) ≤ M := by
  constructor
  · exact integral_nonneg (f := X) (fun ω ↦ (hbound ω).1)
  · have hh := integral_mono hX (integrable_const M) (fun ω ↦ (hbound ω).2)
    simpa only [integral_const, probReal_univ, one_smul] using hh

/-- Nonnegative ranks bounded by `M` have covariance at least `-M²`. -/
theorem covariance_nonnegative_bounded_lower
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ M) (hY : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ M) :
    -(M ^ 2) ≤ covariance X Y μ := by
  have hx := integral_bounds_of_nonnegative_bounded μ X
    ((memLp_finite μ X).integrable one_le_two) hX
  have hy := integral_bounds_of_nonnegative_bounded μ Y
    ((memLp_finite μ Y).integrable one_le_two) hY
  have hp := integral_nonneg (μ := μ) (f := fun ω ↦ X ω * Y ω)
    (fun ω ↦ mul_nonneg (hX ω).1 (hY ω).1)
  have hm := mul_le_mul hx.2 hy.2 hy.1 hM
  rw [covariance_eq_sub (memLp_finite μ X) (memLp_finite μ Y)]
  simp only [Pi.mul_apply]
  nlinarith

/-- Separate good-state and bad-state lower bounds integrate with an explicit bad-mass cost. -/
theorem integral_lower_of_good_bad_bounds
    {H : Type*} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (μ : Measure H) [IsProbabilityMeasure μ] (good : Finset H) (Z : H → ℝ)
    {C D : ℝ} (hC : 0 ≤ C) (hgood : ∀ h ∈ good, -C ≤ Z h)
    (hbad : ∀ h, h ∉ good → -D ≤ Z h) :
    -C - D * μ.real {h | h ∉ good} ≤ ∫ h, Z h ∂μ := by
  classical
  let bad : Set H := {h | h ∉ good}
  have hm : MeasurableSet bad := (Set.toFinite bad).measurableSet
  have hi : Integrable (bad.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hm
  have hp (h : H) : -C - D * bad.indicator (fun _ ↦ (1 : ℝ)) h ≤ Z h := by
    by_cases hh : h ∈ good
    · rw [Set.indicator_of_notMem (show h ∉ bad by exact fun hn ↦ hn hh), mul_zero,
        sub_zero]
      exact hgood h hh
    · rw [Set.indicator_of_mem (show h ∈ bad by exact hh), mul_one]
      linarith [hbad h hh]
  calc
    -C - D * μ.real {h | h ∉ good} =
        ∫ h, -C - D * bad.indicator (fun _ ↦ (1 : ℝ)) h ∂μ := by
      rw [integral_sub (integrable_const (-C)) (hi.const_mul D),
        integral_const_mul, integral_indicator_const (1 : ℝ) hm]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_one, bad]
    _ ≤ ∫ h, Z h ∂μ :=
      integral_mono ((integrable_const (-C)).sub (hi.const_mul D))
        ((memLp_finite μ Z).integrable one_le_two) hp

/-- A finite mixture's global lower covariance survives bad latent states. Conditional means
are masked off the good set before applying the common-signal bound; their perturbation is
charged to bad mass rather than discarded. -/
theorem covariance_bind_lower_of_good_states
    {H Ω : Type*} [Fintype H] [DecidableEq H] [Fintype Ω]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (ν : PMF H) (law : H → PMF Ω) (good : Finset H) (X Y : Ω → ℝ)
    (Λ e₁ e₂ : H → ℝ) {a b M L K C : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hM : 0 ≤ M) (hL : 0 ≤ L) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ M) (hY : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ M)
    (hΛ : ∀ h, |Λ h| ≤ L) (he₁ : ∀ h, |e₁ h| ≤ K) (he₂ : ∀ h, |e₂ h| ≤ K)
    (hmeanX : ∀ h, (if h ∈ good then ∫ ω, X ω ∂(law h).toMeasure else 0) =
      a * Λ h + e₁ h)
    (hmeanY : ∀ h, (if h ∈ good then ∫ ω, Y ω ∂(law h).toMeasure else 0) =
      b * Λ h + e₂ h)
    (hcov : ∀ h ∈ good, -C ≤ covariance X Y (law h).toMeasure) :
    -C + a * b * variance Λ ν.toMeasure - 2 * (a + b) * L * K - 2 * K ^ 2 -
      5 * M ^ 2 * ν.toMeasure.real {h | h ∉ good} ≤
      covariance X Y (ν.bind law).toMeasure := by
  let mx : H → ℝ := fun h ↦ ∫ ω, X ω ∂(law h).toMeasure
  let my : H → ℝ := fun h ↦ ∫ ω, Y ω ∂(law h).toMeasure
  have hmx (h : H) : |mx h| ≤ M := by
    have hh := integral_bounds_of_nonnegative_bounded (law h).toMeasure X
      ((memLp_finite (law h).toMeasure X).integrable one_le_two) hX
    rw [abs_of_nonneg hh.1]
    exact hh.2
  have hmy (h : H) : |my h| ≤ M := by
    have hh := integral_bounds_of_nonnegative_bounded (law h).toMeasure Y
      ((memLp_finite (law h).toMeasure Y).integrable one_le_two) hY
    rw [abs_of_nonneg hh.1]
    exact hh.2
  have hi := integral_lower_of_good_bad_bounds ν.toMeasure good
    (fun h ↦ covariance X Y (law h).toMeasure) hC hcov
    (fun h _ ↦ covariance_nonnegative_bounded_lower (law h).toMeasure X Y hM hX hY)
  have hp := covariance_mask_error_le ν.toMeasure good mx my hM hmx hmy
  have hs := G2Moments.covariance_common_signal_lower ν.toMeasure Λ e₁ e₂
    (memLp_finite ν.toMeasure Λ) (memLp_finite ν.toMeasure e₁)
    (memLp_finite ν.toMeasure e₂) ha hb hL hK hΛ he₁ he₂
  have heqx : (fun h ↦ if h ∈ good then mx h else 0) = (fun h ↦ a * Λ h) + e₁ := by
    funext h
    exact hmeanX h
  have heqy : (fun h ↦ if h ∈ good then my h else 0) = (fun h ↦ b * Λ h) + e₂ := by
    funext h
    exact hmeanY h
  rw [heqx, heqy] at hp
  have hplo := (abs_le.mp hp).1
  rw [covariance_bind]
  change _ ≤ (∫ h, covariance X Y (law h).toMeasure ∂ν.toMeasure) +
    covariance mx my ν.toMeasure
  nlinarith

/-- Finite mixture event probabilities obey exact total expectation. -/
theorem real_measure_bind {H Ω : Type*} [Fintype H] [Fintype Ω]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (ν : PMF H) (law : H → PMF Ω) (event : Set Ω) :
    (ν.bind law).toMeasure.real event = ∫ h, (law h).toMeasure.real event ∂ν.toMeasure := by
  have hm : MeasurableSet event := (Set.toFinite event).measurableSet
  have hh := integral_bind ν law (event.indicator (fun _ ↦ (1 : ℝ)))
  simp_rw [integral_indicator_const (1 : ℝ) hm, smul_eq_mul, mul_one] at hh
  exact hh

/-- Integrated conditional-mean errors are bounded by the global coupled `L¹` error. -/
theorem integral_conditional_mean_error_le {H Ω : Type*} [Fintype H] [Fintype Ω]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (ν : PMF H) (law : H → PMF Ω) (X X' : Ω → ℝ) :
    (∫ h, |(∫ ω, X ω ∂(law h).toMeasure) -
      ∫ ω, X' ω ∂(law h).toMeasure| ∂ν.toMeasure) ≤
      ∫ ω, |X ω - X' ω| ∂(ν.bind law).toMeasure := by
  rw [integral_bind]
  apply integral_mono ((memLp_finite ν.toMeasure _).integrable one_le_two)
    ((memLp_finite ν.toMeasure _).integrable one_le_two)
  intro h
  dsimp only
  rw [← integral_sub ((memLp_finite (law h).toMeasure X).integrable one_le_two)
    ((memLp_finite (law h).toMeasure X').integrable one_le_two)]
  simpa only [Real.norm_eq_abs] using
    norm_integral_le_integral_norm (μ := (law h).toMeasure) (fun ω ↦ X ω - X' ω)

/-- A single global clipping tail bounds the average conditional-mean clipping error. -/
theorem integral_conditional_mean_clip_error_le
    {H Ω : Type*} [Fintype H] [Fintype Ω]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (ν : PMF H) (law : H → PMF Ω) (X : Ω → ℝ) {N cap : ℝ}
    (hcap : 0 ≤ cap) (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ N) :
    (∫ h, |(∫ ω, X ω ∂(law h).toMeasure) -
      ∫ ω, min (X ω) cap ∂(law h).toMeasure| ∂ν.toMeasure) ≤
        N * (ν.bind law).toMeasure.real {ω | cap < X ω} := by
  exact (integral_conditional_mean_error_le ν law X (fun ω ↦ min (X ω) cap)).trans
    (integral_clip_error_le (ν.bind law).toMeasure X hcap hX)

/-- Conditional covariance clipping errors are controlled only after integration. The bound
uses global clipping tails and assumes no pointwise conditional tail estimate. -/
theorem integral_conditional_covariance_clip_error_le
    {H Ω : Type*} [Fintype H] [Fintype Ω]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (ν : PMF H) (law : H → PMF Ω) (X Y : Ω → ℝ) {N cap : ℝ}
    (hN : 0 ≤ N) (hcap : 0 ≤ cap)
    (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ N) (hY : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ N) :
    (∫ h, |covariance X Y (law h).toMeasure -
      covariance (fun ω ↦ min (X ω) cap) (fun ω ↦ min (Y ω) cap) (law h).toMeasure|
        ∂ν.toMeasure) ≤
      2 * N ^ 2 * ((ν.bind law).toMeasure.real {ω | cap < X ω} +
        (ν.bind law).toMeasure.real {ω | cap < Y ω}) := by
  calc
    _ ≤ ∫ h, 2 * N ^ 2 * ((law h).toMeasure.real {ω | cap < X ω} +
        (law h).toMeasure.real {ω | cap < Y ω}) ∂ν.toMeasure := by
      apply integral_mono ((memLp_finite ν.toMeasure _).integrable one_le_two)
        ((memLp_finite ν.toMeasure _).integrable one_le_two)
      intro h
      exact covariance_clip_error_le (law h).toMeasure X Y hN hcap hX hY
    _ = _ := by
      rw [integral_const_mul, integral_add
        ((memLp_finite ν.toMeasure _).integrable one_le_two)
        ((memLp_finite ν.toMeasure _).integrable one_le_two),
        ← real_measure_bind ν law, ← real_measure_bind ν law]

/-- A global union-tail probability bounds the integrated conditional covariance correction. -/
theorem integral_conditional_covariance_clip_error_le_of_tail
    {H Ω : Type*} [Fintype H] [Fintype Ω]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (ν : PMF H) (law : H → PMF Ω) (X Y : Ω → ℝ) {N cap δ : ℝ}
    (hN : 0 ≤ N) (hcap : 0 ≤ cap)
    (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ N) (hY : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ N)
    (htail : (ν.bind law).toMeasure.real {ω | cap < X ω ∨ cap < Y ω} ≤ δ) :
    (∫ h, |covariance X Y (law h).toMeasure -
      covariance (fun ω ↦ min (X ω) cap) (fun ω ↦ min (Y ω) cap) (law h).toMeasure|
        ∂ν.toMeasure) ≤ 4 * N ^ 2 * δ := by
  have hx : (ν.bind law).toMeasure.real {ω | cap < X ω} ≤ δ :=
    (measureReal_mono (μ := (ν.bind law).toMeasure) (fun _ h ↦ Or.inl h)
      (measure_ne_top _ _)).trans htail
  have hy : (ν.bind law).toMeasure.real {ω | cap < Y ω} ≤ δ :=
    (measureReal_mono (μ := (ν.bind law).toMeasure) (fun _ h ↦ Or.inr h)
      (measure_ne_top _ _)).trans htail
  have hh := integral_conditional_covariance_clip_error_le ν law X Y hN hcap hX hY
  have hb := mul_le_mul_of_nonneg_left (add_le_add hx hy) (by positivity : 0 ≤ 2 * N ^ 2)
  nlinarith

/-- Approximate common conditional means may be compared only in integrated `L¹`.
The total covariance identity then transfers their common-signal lower bound. -/
theorem covariance_bind_lower_of_approximate_common_means
    {H Ω : Type*} [Fintype H] [Fintype Ω]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (ν : PMF H) (law : H → PMF Ω) (X Y : Ω → ℝ) (Λ e₁ e₂ : H → ℝ)
    {a b L K M C dx dy : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hL : 0 ≤ L) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hΛ : ∀ h, |Λ h| ≤ L) (he₁ : ∀ h, |e₁ h| ≤ K) (he₂ : ∀ h, |e₂ h| ≤ K)
    (hmeanY : ∀ h, |∫ ω, Y ω ∂(law h).toMeasure| ≤ M)
    (hrefX : ∀ h, |a * Λ h + e₁ h| ≤ M)
    (hcov : -C ≤ ∫ h, covariance X Y (law h).toMeasure ∂ν.toMeasure)
    (herrX : (∫ h, |(∫ ω, X ω ∂(law h).toMeasure) - (a * Λ h + e₁ h)|
      ∂ν.toMeasure) ≤ dx)
    (herrY : (∫ h, |(∫ ω, Y ω ∂(law h).toMeasure) - (b * Λ h + e₂ h)|
      ∂ν.toMeasure) ≤ dy) :
    -C + a * b * variance Λ ν.toMeasure - 2 * (a + b) * L * K - 2 * K ^ 2 -
      2 * M * (dx + dy) ≤ covariance X Y (ν.bind law).toMeasure := by
  let mx : H → ℝ := fun h ↦ ∫ ω, X ω ∂(law h).toMeasure
  let my : H → ℝ := fun h ↦ ∫ ω, Y ω ∂(law h).toMeasure
  let rx : H → ℝ := fun h ↦ a * Λ h + e₁ h
  let ry : H → ℝ := fun h ↦ b * Λ h + e₂ h
  have hp := covariance_perturbation_le ν.toMeasure mx my rx ry
    (memLp_finite ν.toMeasure _) (memLp_finite ν.toMeasure _)
    (memLp_finite ν.toMeasure _) (memLp_finite ν.toMeasure _) hmeanY hrefX
  have he := mul_le_mul_of_nonneg_left (add_le_add herrX herrY)
    (by positivity : 0 ≤ 2 * M)
  have hlo := (abs_le.mp hp).1
  have hs := G2Moments.covariance_common_signal_lower ν.toMeasure Λ e₁ e₂
    (memLp_finite ν.toMeasure Λ) (memLp_finite ν.toMeasure e₁)
    (memLp_finite ν.toMeasure e₂) ha hb hL hK hΛ he₁ he₂
  rw [covariance_bind]
  change _ ≤ (∫ h, covariance X Y (law h).toMeasure ∂ν.toMeasure) +
    covariance mx my ν.toMeasure
  change _ ≤ covariance rx ry ν.toMeasure at hs
  nlinarith

/-- Clipped conditional means compared with good-state original means incur only a global
clipping tail plus capped bad-state mass, never an uncapped bad-state cost. -/
theorem integral_conditional_mean_clip_mask_error_le
    {H Ω : Type*} [Fintype H] [DecidableEq H] [Fintype Ω]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (ν : PMF H) (law : H → PMF Ω) (good : Finset H) (X : Ω → ℝ) {N cap : ℝ}
    (hcap : 0 ≤ cap) (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ N) :
    (∫ h, |(∫ ω, min (X ω) cap ∂(law h).toMeasure) -
      (if h ∈ good then ∫ ω, X ω ∂(law h).toMeasure else 0)| ∂ν.toMeasure) ≤
      N * (ν.bind law).toMeasure.real {ω | cap < X ω} +
        cap * ν.toMeasure.real {h | h ∉ good} := by
  classical
  let m : H → ℝ := fun h ↦ ∫ ω, X ω ∂(law h).toMeasure
  let mc : H → ℝ := fun h ↦ ∫ ω, min (X ω) cap ∂(law h).toMeasure
  let bad : Set H := {h | h ∉ good}
  have hm : MeasurableSet bad := (Set.toFinite bad).measurableSet
  have hmc (h : H) : |mc h| ≤ cap := by
    have hh := integral_bounds_of_nonnegative_bounded (law h).toMeasure
      (fun ω ↦ min (X ω) cap) ((memLp_finite (law h).toMeasure _).integrable one_le_two)
      (fun ω ↦ ⟨le_min (hX ω).1 hcap, min_le_right _ _⟩)
    rw [abs_of_nonneg hh.1]
    exact hh.2
  have hp (h : H) : |mc h - (if h ∈ good then m h else 0)| ≤
      |mc h - m h| + bad.indicator (fun _ ↦ cap) h := by
    by_cases hh : h ∈ good
    · rw [ite_eq_left hh, Set.indicator_of_notMem (show h ∉ bad by exact fun hn ↦ hn hh),
        add_zero]
    · rw [ite_eq_right hh, sub_zero, Set.indicator_of_mem (show h ∈ bad by exact hh)]
      linarith [hmc h, abs_nonneg (mc h - m h)]
  have hi := integral_mono ((memLp_finite ν.toMeasure _).integrable one_le_two)
    ((memLp_finite ν.toMeasure _).integrable one_le_two) hp
  rw [integral_add ((memLp_finite ν.toMeasure _).integrable one_le_two)
    ((integrable_const cap).indicator hm), integral_indicator_const cap hm] at hi
  have he := integral_conditional_mean_clip_error_le ν law X hcap hX
  simp only [smul_eq_mul] at hi
  have he' : (∫ h, |mc h - m h| ∂ν.toMeasure) ≤
      N * (ν.bind law).toMeasure.real {ω | cap < X ω} := by
    simpa only [mc, m, abs_sub_comm] using he
  change (∫ h, |mc h - (if h ∈ good then m h else 0)| ∂ν.toMeasure) ≤ _
  change (∫ h, |mc h - (if h ∈ good then m h else 0)| ∂ν.toMeasure) ≤ _ at hi
  linarith

/-- Original good-state covariance lower bounds transfer to the average clipped covariance.
Only the integrated clipping error is charged; no conditional tail is asserted. -/
theorem integral_conditional_clipped_covariance_lower
    {H Ω : Type*} [Fintype H] [Fintype Ω]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (ν : PMF H) (law : H → PMF Ω) (good : Finset H) (X Y : Ω → ℝ)
    {N cap C : ℝ} (hN : 0 ≤ N) (hcap : 0 ≤ cap) (hC : 0 ≤ C)
    (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ N) (hY : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ N)
    (hcov : ∀ h ∈ good, -C ≤ covariance X Y (law h).toMeasure) :
    -C - cap ^ 2 * ν.toMeasure.real {h | h ∉ good} -
      2 * N ^ 2 * ((ν.bind law).toMeasure.real {ω | cap < X ω} +
        (ν.bind law).toMeasure.real {ω | cap < Y ω}) ≤
      ∫ h, covariance (fun ω ↦ min (X ω) cap) (fun ω ↦ min (Y ω) cap)
        (law h).toMeasure ∂ν.toMeasure := by
  let cv : H → ℝ := fun h ↦ covariance (fun ω ↦ min (X ω) cap)
    (fun ω ↦ min (Y ω) cap) (law h).toMeasure
  let er : H → ℝ := fun h ↦ |covariance X Y (law h).toMeasure - cv h|
  have hgood (h : H) (hh : h ∈ good) : -C ≤ cv h + er h := by
    have he := le_abs_self (covariance X Y (law h).toMeasure - cv h)
    have hc := hcov h hh
    change -C ≤ cv h + |covariance X Y (law h).toMeasure - cv h|
    linarith
  have hbad (h : H) (_hh : h ∉ good) : -(cap ^ 2) ≤ cv h + er h := by
    have hc := covariance_nonnegative_bounded_lower (law h).toMeasure
      (fun ω ↦ min (X ω) cap) (fun ω ↦ min (Y ω) cap) hcap
      (fun ω ↦ ⟨le_min (hX ω).1 hcap, min_le_right _ _⟩)
      (fun ω ↦ ⟨le_min (hY ω).1 hcap, min_le_right _ _⟩)
    have he : 0 ≤ er h := abs_nonneg _
    change -(cap ^ 2) ≤ cv h at hc
    linarith
  have hl := integral_lower_of_good_bad_bounds ν.toMeasure good
    (fun h ↦ cv h + er h) hC hgood hbad
  rw [integral_add ((memLp_finite ν.toMeasure cv).integrable one_le_two)
    ((memLp_finite ν.toMeasure er).integrable one_le_two)] at hl
  have he := integral_conditional_covariance_clip_error_le ν law X Y hN hcap hX hY
  change (∫ h, er h ∂ν.toMeasure) ≤ _ at he
  change _ ≤ ∫ h, cv h ∂ν.toMeasure
  linarith

/-- The complete finite-state clipping/deconditioning repair. Original good-state means and
covariances are used directly; only global clipping tails are charged. The conditional-mean
variance is retained and no future-event or pointwise conditional-tail estimate is assumed. -/
theorem covariance_bind_lower_via_clipping_good_states
    {H Ω : Type*} [Fintype H] [DecidableEq H] [Fintype Ω]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (ν : PMF H) (law : H → PMF Ω) (good : Finset H) (X Y : Ω → ℝ)
    (Λ e₁ e₂ : H → ℝ) {a b N cap L K C : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : 0 ≤ N) (hcap : 0 ≤ cap)
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ N) (hY : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ N)
    (hΛ : ∀ h, |Λ h| ≤ L) (he₁ : ∀ h, |e₁ h| ≤ K) (he₂ : ∀ h, |e₂ h| ≤ K)
    (hcapMean : a * L + K ≤ cap)
    (hmeanX : ∀ h, (if h ∈ good then ∫ ω, X ω ∂(law h).toMeasure else 0) =
      a * Λ h + e₁ h)
    (hmeanY : ∀ h, (if h ∈ good then ∫ ω, Y ω ∂(law h).toMeasure else 0) =
      b * Λ h + e₂ h)
    (hcov : ∀ h ∈ good, -C ≤ covariance X Y (law h).toMeasure) :
    -C + a * b * variance Λ ν.toMeasure - 2 * (a + b) * L * K - 2 * K ^ 2 -
      5 * cap ^ 2 * ν.toMeasure.real {h | h ∉ good} -
      (4 * N ^ 2 + 2 * cap * N) *
        ((ν.bind law).toMeasure.real {ω | cap < X ω} +
          (ν.bind law).toMeasure.real {ω | cap < Y ω}) ≤
      covariance X Y (ν.bind law).toMeasure := by
  let tx := (ν.bind law).toMeasure.real {ω | cap < X ω}
  let ty := (ν.bind law).toMeasure.real {ω | cap < Y ω}
  let bad := ν.toMeasure.real {h | h ∉ good}
  have hmeanClipY (h : H) : |∫ ω, min (Y ω) cap ∂(law h).toMeasure| ≤ cap := by
    have hh := integral_bounds_of_nonnegative_bounded (law h).toMeasure
      (fun ω ↦ min (Y ω) cap) ((memLp_finite (law h).toMeasure _).integrable one_le_two)
      (fun ω ↦ ⟨le_min (hY ω).1 hcap, min_le_right _ _⟩)
    rw [abs_of_nonneg hh.1]
    exact hh.2
  have href (h : H) : |a * Λ h + e₁ h| ≤ cap := by
    calc
      _ ≤ |a * Λ h| + |e₁ h| := abs_add_le _ _
      _ ≤ a * L + K := by
        rw [abs_mul, abs_of_nonneg ha]
        exact add_le_add (mul_le_mul_of_nonneg_left (hΛ h) ha) (he₁ h)
      _ ≤ cap := hcapMean
  have hi : -(C + cap ^ 2 * bad + 2 * N ^ 2 * (tx + ty)) ≤
      ∫ h, covariance (fun ω ↦ min (X ω) cap) (fun ω ↦ min (Y ω) cap)
        (law h).toMeasure ∂ν.toMeasure := by
    have hh := integral_conditional_clipped_covariance_lower ν law good X Y
      hN hcap hC hX hY hcov
    change -C - cap ^ 2 * bad - 2 * N ^ 2 * (tx + ty) ≤ _ at hh
    linarith
  have hx : (∫ h, |(∫ ω, min (X ω) cap ∂(law h).toMeasure) - (a * Λ h + e₁ h)|
      ∂ν.toMeasure) ≤ N * tx + cap * bad := by
    have hh := integral_conditional_mean_clip_mask_error_le ν law good X hcap hX
    simp_rw [hmeanX] at hh
    exact hh
  have hy : (∫ h, |(∫ ω, min (Y ω) cap ∂(law h).toMeasure) - (b * Λ h + e₂ h)|
      ∂ν.toMeasure) ≤ N * ty + cap * bad := by
    have hh := integral_conditional_mean_clip_mask_error_le ν law good Y hcap hY
    simp_rw [hmeanY] at hh
    exact hh
  have hclipped := covariance_bind_lower_of_approximate_common_means ν law
    (fun ω ↦ min (X ω) cap) (fun ω ↦ min (Y ω) cap) Λ e₁ e₂ ha hb hL hK hcap
    hΛ he₁ he₂ hmeanClipY href hi hx hy
  have hp := covariance_clip_error_le (ν.bind law).toMeasure X Y hN hcap hX hY
  change |covariance X Y (ν.bind law).toMeasure -
    covariance (fun ω ↦ min (X ω) cap) (fun ω ↦ min (Y ω) cap) (ν.bind law).toMeasure| ≤
      2 * N ^ 2 * (tx + ty) at hp
  have hlo := (abs_le.mp hp).1
  change -C + a * b * variance Λ ν.toMeasure - 2 * (a + b) * L * K - 2 * K ^ 2 -
    5 * cap ^ 2 * bad - (4 * N ^ 2 + 2 * cap * N) * (tx + ty) ≤ _
  nlinarith

end TieredMatching.G2Deconditioning
