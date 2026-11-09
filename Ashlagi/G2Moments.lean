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
# Lower-covariance moment reductions for proposal counts

The lemmas are abstract moment inequalities on probability spaces. They do not assert
any deferred-acceptance process estimate. In particular, common-state mixture means
retain their nonnegative common-signal variance rather than dropping that term.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Ashlagi
namespace G2Moments

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Adding nonnegative rest counts costs only the cross products of their means in a
lower covariance bound. No bound on the rest-rest product moment is required. -/
theorem covariance_add_nonnegative_lower
    (A B C D : Ω → ℝ) (hA : MemLp A 2 μ) (hB : MemLp B 2 μ)
    (hC : MemLp C 2 μ) (hD : MemLp D 2 μ)
    (hA0 : ∀ ω, 0 ≤ A ω) (hB0 : ∀ ω, 0 ≤ B ω)
    (hC0 : ∀ ω, 0 ≤ C ω) (hD0 : ∀ ω, 0 ≤ D ω) :
    covariance A C μ - ((∫ ω, A ω ∂μ) * (∫ ω, D ω ∂μ) +
      (∫ ω, B ω ∂μ) * (∫ ω, C ω ∂μ) +
      (∫ ω, B ω ∂μ) * (∫ ω, D ω ∂μ)) ≤ covariance (A + B) (C + D) μ := by
  have hp : (∫ ω, A ω * C ω ∂μ) ≤ ∫ ω, (A ω + B ω) * (C ω + D ω) ∂μ := by
    apply integral_mono (hA.integrable_mul hC) ((hA.add hB).integrable_mul (hC.add hD))
    intro ω
    exact mul_le_mul (le_add_of_nonneg_right (hB0 ω)) (le_add_of_nonneg_right (hD0 ω))
      (hC0 ω) (add_nonneg (hA0 ω) (hB0 ω))
  rw [covariance_eq_sub hA hC, covariance_eq_sub (hA.add hB) (hC.add hD)]
  simp only [Pi.mul_apply, Pi.add_apply] at *
  rw [integral_add (hA.integrable one_le_two) (hB.integrable one_le_two),
    integral_add (hC.integrable one_le_two) (hD.integrable one_le_two)]
  nlinarith

/-- The fixed-state lower bound is linear in the initial mean scale when rest means are bounded. -/
theorem covariance_add_nonnegative_lower_of_means
    (A B C D : Ω → ℝ) (hA : MemLp A 2 μ) (hB : MemLp B 2 μ)
    (hC : MemLp C 2 μ) (hD : MemLp D 2 μ)
    (hA0 : ∀ ω, 0 ≤ A ω) (hB0 : ∀ ω, 0 ≤ B ω)
    (hC0 : ∀ ω, 0 ≤ C ω) (hD0 : ∀ ω, 0 ≤ D ω)
    {M K E : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hAM : (∫ ω, A ω ∂μ) ≤ M) (hCM : (∫ ω, C ω ∂μ) ≤ M)
    (hBK : (∫ ω, B ω ∂μ) ≤ K) (hDK : (∫ ω, D ω ∂μ) ≤ K)
    (hcov : -E ≤ covariance A C μ) :
    -E - 2 * M * K - K ^ 2 ≤ covariance (A + B) (C + D) μ := by
  have hAB := covariance_add_nonnegative_lower μ A B C D hA hB hC hD
    hA0 hB0 hC0 hD0
  have ha0 := integral_nonneg (μ := μ) (f := A) hA0
  have hb0 := integral_nonneg (μ := μ) (f := B) hB0
  have hc0 := integral_nonneg (μ := μ) (f := C) hC0
  have hd0 := integral_nonneg (μ := μ) (f := D) hD0
  have hAD : (∫ ω, A ω ∂μ) * (∫ ω, D ω ∂μ) ≤ M * K :=
    mul_le_mul hAM hDK hd0 hM
  have hBC : (∫ ω, B ω ∂μ) * (∫ ω, C ω ∂μ) ≤ K * M :=
    mul_le_mul hBK hCM hc0 hK
  have hBD : (∫ ω, B ω ∂μ) * (∫ ω, D ω ∂μ) ≤ K * K :=
    mul_le_mul hBK hDK hd0 hK
  nlinarith

/-- Bounded variables have covariance bounded by twice the product of their bounds. -/
theorem abs_covariance_le_of_abs_le
    (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    {M K : ℝ} (hM : 0 ≤ M)
    (hXM : ∀ ω, |X ω| ≤ M) (hYK : ∀ ω, |Y ω| ≤ K) :
    |covariance X Y μ| ≤ 2 * M * K := by
  have hx : |∫ ω, X ω ∂μ| ≤ M := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := μ) (f := X)
        (ae_of_all _ fun ω ↦ by simpa only [Real.norm_eq_abs] using hXM ω)
  have hy : |∫ ω, Y ω ∂μ| ≤ K := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := μ) (f := Y)
        (ae_of_all _ fun ω ↦ by simpa only [Real.norm_eq_abs] using hYK ω)
  have hp : |∫ ω, X ω * Y ω ∂μ| ≤ M * K := by
    have hb : ∀ ω, ‖X ω * Y ω‖ ≤ M * K := fun ω ↦ by
      simpa only [Real.norm_eq_abs, abs_mul] using
        mul_le_mul (hXM ω) (hYK ω) (abs_nonneg _) hM
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω ↦ X ω * Y ω)
        (ae_of_all _ hb)
  rw [covariance_eq_sub hX hY]
  simp only [Pi.mul_apply]
  exact (abs_sub _ _).trans (by
    rw [abs_mul]
    have hxy : |∫ ω, X ω ∂μ| * |∫ ω, Y ω ∂μ| ≤ M * K :=
      mul_le_mul hx hy (abs_nonneg _) hM
    nlinarith)

/-- Common conditional means have a common-signal variance term. This identity makes
that term explicit before any error estimate is applied. -/
theorem covariance_common_signal_decomposition
    (Λ e₁ e₂ : Ω → ℝ) (hΛ : MemLp Λ 2 μ) (he₁ : MemLp e₁ 2 μ)
    (he₂ : MemLp e₂ 2 μ) (a b : ℝ) :
    covariance ((fun ω ↦ a * Λ ω) + e₁) ((fun ω ↦ b * Λ ω) + e₂) μ =
      a * b * variance Λ μ + a * covariance Λ e₂ μ + b * covariance e₁ Λ μ +
        covariance e₁ e₂ μ := by
  rw [covariance_add_left (hΛ.const_mul a) he₁ ((hΛ.const_mul b).add he₂),
    covariance_add_right (hΛ.const_mul a) (hΛ.const_mul b) he₂,
    covariance_add_right he₁ (hΛ.const_mul b) he₂,
    covariance_const_mul_left, covariance_const_mul_right,
    covariance_const_mul_left, covariance_const_mul_right,
    covariance_self hΛ.aemeasurable]
  ring

/-- Bounded errors in common conditional means cost only a linear term in the signal bound.
The common-signal variance is retained with its correct, nonnegative coefficient. -/
theorem covariance_common_signal_lower
    (Λ e₁ e₂ : Ω → ℝ) (hΛ : MemLp Λ 2 μ) (he₁ : MemLp e₁ 2 μ)
    (he₂ : MemLp e₂ 2 μ) {a b M K : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hΛM : ∀ ω, |Λ ω| ≤ M) (he₁K : ∀ ω, |e₁ ω| ≤ K)
    (he₂K : ∀ ω, |e₂ ω| ≤ K) :
    a * b * variance Λ μ - 2 * (a + b) * M * K - 2 * K ^ 2 ≤
      covariance ((fun ω ↦ a * Λ ω) + e₁) ((fun ω ↦ b * Λ ω) + e₂) μ := by
  have h₁ := (abs_le.mp (abs_covariance_le_of_abs_le μ Λ e₂ hΛ he₂ hM hΛM he₂K)).1
  have h₂ : -(2 * M * K) ≤ covariance e₁ Λ μ := by
    rw [covariance_comm]
    exact (abs_le.mp (abs_covariance_le_of_abs_le μ Λ e₁ hΛ he₁ hM hΛM he₁K)).1
  have h₃ := (abs_le.mp (abs_covariance_le_of_abs_le μ e₁ e₂ he₁ he₂ hK he₁K he₂K)).1
  rw [covariance_common_signal_decomposition μ Λ e₁ e₂ hΛ he₁ he₂ a b]
  have h₁' := mul_le_mul_of_nonneg_left h₁ ha
  have h₂' := mul_le_mul_of_nonneg_left h₂ hb
  nlinarith

/-- Inverse popularity coefficients in `[0,1]` give a uniform linear lower bound,
without requiring an upper bound on the common-signal variance. -/
theorem covariance_common_signal_lower_of_coefficients_le_one
    (Λ e₁ e₂ : Ω → ℝ) (hΛ : MemLp Λ 2 μ) (he₁ : MemLp e₁ 2 μ)
    (he₂ : MemLp e₂ 2 μ) {a b M K : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hΛM : ∀ ω, |Λ ω| ≤ M) (he₁K : ∀ ω, |e₁ ω| ≤ K)
    (he₂K : ∀ ω, |e₂ ω| ≤ K) :
    -4 * M * K - 2 * K ^ 2 ≤
      covariance ((fun ω ↦ a * Λ ω) + e₁) ((fun ω ↦ b * Λ ω) + e₂) μ := by
  have hl := covariance_common_signal_lower μ Λ e₁ e₂ hΛ he₁ he₂
    ha hb hM hK hΛM he₁K he₂K
  have hv : 0 ≤ a * b * variance Λ μ := mul_nonneg (mul_nonneg ha hb) (variance_nonneg _ _)
  have hm : 2 * (a + b) * M * K ≤ 4 * M * K := by
    have hh := mul_le_mul_of_nonneg_right (show a + b ≤ 2 by linarith) (mul_nonneg hM hK)
    nlinarith
  linarith

/-- Deleting nonnegative repetitions controls the ordinary total-count variance by the
raw total-count variance and the expected number of deleted steps. -/
theorem variance_le_of_nonnegative_le
    (S T : Ω → ℝ) (hS : MemLp S 2 μ) (hT : MemLp T 2 μ)
    (hS0 : ∀ ω, 0 ≤ S ω) (hST : ∀ ω, S ω ≤ T ω) :
    variance S μ ≤ variance T μ +
      2 * (∫ ω, T ω ∂μ) * (∫ ω, T ω - S ω ∂μ) := by
  have hp : (∫ ω, S ω * S ω ∂μ) ≤ ∫ ω, T ω * T ω ∂μ := by
    apply integral_mono (hS.integrable_mul hS) (hT.integrable_mul hT)
    intro ω
    exact mul_le_mul (hST ω) (hST ω) (hS0 ω) ((hS0 ω).trans (hST ω))
  rw [integral_sub (hT.integrable one_le_two) (hS.integrable one_le_two)]
  rw [variance_eq_sub hS, variance_eq_sub hT]
  simp only [Pi.pow_apply, pow_two] at *
  nlinarith [sq_nonneg ((∫ ω, T ω ∂μ) - ∫ ω, S ω ∂μ)]

/-- Quantitative raw-count moments imply an ordinary total-count variance bound. -/
theorem variance_le_of_nonnegative_le_of_moments
    (S T : Ω → ℝ) (hS : MemLp S 2 μ) (hT : MemLp T 2 μ)
    (hS0 : ∀ ω, 0 ≤ S ω) (hST : ∀ ω, S ω ≤ T ω)
    {V M R : ℝ} (hM : 0 ≤ M) (hvar : variance T μ ≤ V)
    (hmean : (∫ ω, T ω ∂μ) ≤ M) (hrest : (∫ ω, T ω - S ω ∂μ) ≤ R) :
    variance S μ ≤ V + 2 * M * R := by
  have hv := variance_le_of_nonnegative_le μ S T hS hT hS0 hST
  have hR0 : 0 ≤ ∫ ω, T ω - S ω ∂μ :=
    integral_nonneg (μ := μ) (f := fun ω ↦ T ω - S ω) fun ω ↦ sub_nonneg.mpr (hST ω)
  have hm := mul_le_mul hmean hrest hR0 hM
  nlinarith

/-- A lower cross covariance bounds the variance of one group by the variance of the whole. -/
theorem variance_left_le_of_covariance_lower
    (U V : Ω → ℝ) (hU : MemLp U 2 μ) (hV : MemLp V 2 μ)
    {K : ℝ} (hcov : -K ≤ covariance U V μ) :
    variance U μ ≤ variance (U + V) μ + 2 * K := by
  have heq := variance_add hU hV
  have hnonneg := variance_nonneg V μ
  linarith

/-- Uniform lower covariance bounds add over all pairs from two finite populations. -/
theorem covariance_sums_lower
    {ι κ : Type*} (s : Finset ι) (t : Finset κ) (X : ι → Ω → ℝ) (Y : κ → Ω → ℝ)
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hY : ∀ j ∈ t, MemLp (Y j) 2 μ)
    {K : ℝ} (hcov : ∀ i ∈ s, ∀ j ∈ t, -K ≤ covariance (X i) (Y j) μ) :
    -(s.card : ℝ) * (t.card : ℝ) * K ≤
      covariance (∑ i ∈ s, X i) (∑ j ∈ t, Y j) μ := by
  rw [covariance_sum_sum' hX hY]
  have hh := Finset.sum_le_sum fun i hi ↦ Finset.sum_le_sum fun j hj ↦ hcov i hi j hj
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_neg, neg_mul, mul_assoc] using hh

/-- Only cross-group lower covariance estimates are needed to concentrate a tier total.
Individual variance upper bounds or unconditional covariance upper bounds are not assumed. -/
theorem variance_group_le_total_of_cross_covariance_lower
    {ι κ : Type*} (s : Finset ι) (t : Finset κ) (X : ι → Ω → ℝ) (Y : κ → Ω → ℝ)
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hY : ∀ j ∈ t, MemLp (Y j) 2 μ)
    {K : ℝ} (hcov : ∀ i ∈ s, ∀ j ∈ t, -K ≤ covariance (X i) (Y j) μ) :
    variance (∑ i ∈ s, X i) μ ≤
      variance ((∑ i ∈ s, X i) + ∑ j ∈ t, Y j) μ +
        2 * (s.card : ℝ) * (t.card : ℝ) * K := by
  have hc := covariance_sums_lower μ s t X Y hX hY hcov
  have hv := variance_left_le_of_covariance_lower μ
    (∑ i ∈ s, X i) (∑ j ∈ t, Y j)
    (memLp_finsetSum' s hX) (memLp_finsetSum' t hY)
    (K := (s.card : ℝ) * (t.card : ℝ) * K) (by nlinarith [hc])
  nlinarith

/-- Uniformly close popularity-weighted means determine their total, with no covariance input. -/
theorem abs_sum_sub_signal_sum_inv_le
    {ι : Type*} (s : Finset ι) (β r : ι → ℝ) (ℓ K : ℝ)
    (hβ : ∀ i ∈ s, 0 < β i) (herr : ∀ i ∈ s, |β i * r i - ℓ| ≤ K) :
    |(∑ i ∈ s, r i) - ℓ * ∑ i ∈ s, (β i)⁻¹| ≤ K * ∑ i ∈ s, (β i)⁻¹ := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    |∑ i ∈ s, (r i - ℓ * (β i)⁻¹)| ≤
        ∑ i ∈ s, |r i - ℓ * (β i)⁻¹| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, K * (β i)⁻¹ := by
      apply Finset.sum_le_sum
      intro i hi
      have heq : r i - ℓ * (β i)⁻¹ = (β i * r i - ℓ) * (β i)⁻¹ := by
        field_simp [(hβ i hi).ne']
      rw [heq, abs_mul, abs_inv, abs_of_pos (hβ i hi)]
      exact mul_le_mul_of_nonneg_right (herr i hi) (inv_nonneg.mpr (hβ i hi).le)
    _ = K * ∑ i ∈ s, (β i)⁻¹ := (Finset.mul_sum ..).symm

/-- The common popularity-weighted mean is close to the total divided by reciprocal weights. -/
theorem abs_signal_sub_total_div_sum_inv_le
    {ι : Type*} (s : Finset ι) (β r : ι → ℝ) (ℓ K : ℝ)
    (hβ : ∀ i ∈ s, 0 < β i) (herr : ∀ i ∈ s, |β i * r i - ℓ| ≤ K)
    (hD : 0 < ∑ i ∈ s, (β i)⁻¹) :
    |ℓ - (∑ i ∈ s, r i) / (∑ i ∈ s, (β i)⁻¹)| ≤ K := by
  have hs := abs_sum_sub_signal_sum_inv_le s β r ℓ K hβ herr
  have heq : ℓ - (∑ i ∈ s, r i) / (∑ i ∈ s, (β i)⁻¹) =
      -((∑ i ∈ s, r i) - ℓ * ∑ i ∈ s, (β i)⁻¹) /
        (∑ i ∈ s, (β i)⁻¹) := by
    field_simp [hD.ne']
    ring
  rw [heq, abs_div, abs_neg, abs_of_pos hD]
  exact (div_le_iff₀ hD).2 hs

end G2Moments
end Ashlagi
