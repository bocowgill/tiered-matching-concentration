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

public import Ashlagi.G2Deconditioning
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Global mean and covariance reductions for finite mixtures

Good latent states control conditional moments. Bad-state costs are charged to their mass,
while clipping errors use tail probabilities under the global mixture law. The numerical
asymptotic reduction makes the resulting logarithmic covariance scale explicit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Ashlagi.MixtureBounds

/-- Masking a conditional mean costs the clipped bound on bad states and one global tail. -/
theorem integral_conditional_mean_mask_error_le
    {H Ω : Type*} [Fintype H] [DecidableEq H] [Fintype Ω]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (ν : PMF H) (law : H → PMF Ω) (good : Finset H) (X : Ω → ℝ) {N cap : ℝ}
    (hcap : 0 ≤ cap) (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ N) :
    (∫ h, |(∫ ω, X ω ∂(law h).toMeasure) -
      (if h ∈ good then ∫ ω, X ω ∂(law h).toMeasure else 0)| ∂ν.toMeasure) ≤
      cap * ν.toMeasure.real {h | h ∉ good} +
        N * (ν.bind law).toMeasure.real {ω | cap < X ω} := by
  classical
  let m : H → ℝ := fun h ↦ ∫ ω, X ω ∂(law h).toMeasure
  let mc : H → ℝ := fun h ↦ ∫ ω, min (X ω) cap ∂(law h).toMeasure
  let bad : Set H := {h | h ∉ good}
  have hm : MeasurableSet bad := (Set.toFinite bad).measurableSet
  have hmc (h : H) : mc h ≤ cap :=
    (G2Deconditioning.integral_bounds_of_nonnegative_bounded (law h).toMeasure
      (fun ω ↦ min (X ω) cap)
      ((G2Deconditioning.memLp_finite (law h).toMeasure _).integrable one_le_two)
      (fun ω ↦ ⟨le_min (hX ω).1 hcap, min_le_right _ _⟩)).2
  have hp (h : H) : |m h - (if h ∈ good then m h else 0)| ≤
      |m h - mc h| + bad.indicator (fun _ ↦ cap) h := by
    by_cases hh : h ∈ good
    · rw [ite_eq_left hh, sub_self, abs_zero,
        Set.indicator_of_notMem (show h ∉ bad by exact fun hn ↦ hn hh), add_zero]
      exact abs_nonneg _
    · rw [ite_eq_right hh, sub_zero,
        abs_of_nonneg (integral_nonneg (fun ω ↦ (hX ω).1)),
        Set.indicator_of_mem (show h ∈ bad by exact hh)]
      linarith [hmc h, le_abs_self (m h - mc h)]
  have hi := integral_mono ((G2Deconditioning.memLp_finite ν.toMeasure _).integrable
    one_le_two) ((G2Deconditioning.memLp_finite ν.toMeasure _).integrable one_le_two) hp
  rw [integral_add ((G2Deconditioning.memLp_finite ν.toMeasure _).integrable one_le_two)
    ((integrable_const cap).indicator hm), integral_indicator_const cap hm] at hi
  have he := G2Deconditioning.integral_conditional_mean_clip_error_le ν law X hcap hX
  change (∫ h, |m h - mc h| ∂ν.toMeasure) ≤ _ at he
  change (∫ h, |m h - (if h ∈ good then m h else 0)| ∂ν.toMeasure) ≤ _
  simp only [smul_eq_mul, bad] at hi
  linarith

/-- Good-state weighted means transfer globally using bad mass and global clipping tails. -/
theorem weighted_global_mean_difference_le
    {H Ω : Type*} [Fintype H] [DecidableEq H] [Fintype Ω]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (ν : PMF H) (law : H → PMF Ω) (good : Finset H) (X Y : Ω → ℝ)
    {β₁ β₂ B N cap K : ℝ} (hβ₁ : β₁ ∈ Set.Icc 0 B) (hβ₂ : β₂ ∈ Set.Icc 0 B)
    (hN : 0 ≤ N) (hcap : 0 ≤ cap) (hK : 0 ≤ K)
    (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ N) (hY : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ N)
    (hgood : ∀ h ∈ good, |β₁ * (∫ ω, X ω ∂(law h).toMeasure) -
      β₂ * (∫ ω, Y ω ∂(law h).toMeasure)| ≤ K) :
    |β₁ * (∫ ω, X ω ∂(ν.bind law).toMeasure) -
      β₂ * (∫ ω, Y ω ∂(ν.bind law).toMeasure)| ≤
      K + 2 * B * cap * ν.toMeasure.real {h | h ∉ good} +
        B * N * ((ν.bind law).toMeasure.real {ω | cap < X ω} +
          (ν.bind law).toMeasure.real {ω | cap < Y ω}) := by
  classical
  let mx : H → ℝ := fun h ↦ ∫ ω, X ω ∂(law h).toMeasure
  let my : H → ℝ := fun h ↦ ∫ ω, Y ω ∂(law h).toMeasure
  let dx : H → ℝ := fun h ↦ |mx h - (if h ∈ good then mx h else 0)|
  let dy : H → ℝ := fun h ↦ |my h - (if h ∈ good then my h else 0)|
  have hp (h : H) : |β₁ * mx h - β₂ * my h| ≤ K + β₁ * dx h + β₂ * dy h := by
    by_cases hh : h ∈ good
    · simpa only [dx, dy, ite_eq_left hh, sub_self, abs_zero, mul_zero, add_zero] using
        hgood h hh
    · have ha := abs_sub (β₁ * mx h) (β₂ * my h)
      rw [abs_mul, abs_mul, abs_of_nonneg hβ₁.1, abs_of_nonneg hβ₂.1] at ha
      simp only [dx, dy, ite_eq_right hh, sub_zero]
      linarith
  have hi := integral_mono ((G2Deconditioning.memLp_finite ν.toMeasure _).integrable
    one_le_two) ((G2Deconditioning.memLp_finite ν.toMeasure _).integrable one_le_two) hp
  rw [integral_add ((G2Deconditioning.memLp_finite ν.toMeasure _).integrable one_le_two)
    ((G2Deconditioning.memLp_finite ν.toMeasure _).integrable one_le_two),
    integral_add (integrable_const K)
      ((G2Deconditioning.memLp_finite ν.toMeasure _).integrable one_le_two),
    integral_const_mul, integral_const_mul] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  have hx := integral_conditional_mean_mask_error_le ν law good X hcap hX
  have hy := integral_conditional_mean_mask_error_le ν law good Y hcap hY
  change (∫ h, dx h ∂ν.toMeasure) ≤ _ at hx
  change (∫ h, dy h ∂ν.toMeasure) ≤ _ at hy
  have hx' := (mul_le_mul_of_nonneg_left hx hβ₁.1).trans
    (mul_le_mul_of_nonneg_right hβ₁.2 (by positivity))
  have hy' := (mul_le_mul_of_nonneg_left hy hβ₂.1).trans
    (mul_le_mul_of_nonneg_right hβ₂.2 (by positivity))
  have hn : |∫ h, β₁ * mx h - β₂ * my h ∂ν.toMeasure| ≤
      ∫ h, |β₁ * mx h - β₂ * my h| ∂ν.toMeasure := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (μ := ν.toMeasure) (fun h ↦ β₁ * mx h - β₂ * my h)
  rw [integral_sub ((G2Deconditioning.memLp_finite ν.toMeasure _).integrable one_le_two)
    ((G2Deconditioning.memLp_finite ν.toMeasure _).integrable one_le_two),
    integral_const_mul, integral_const_mul] at hn
  simp only [mx, my, ← G2Deconditioning.integral_bind ν law] at hn
  nlinarith

/-- Every fixed logarithmic power times a negative power of `n` tends to zero. -/
theorem tendsto_log_pow_mul_rpow_neg (k : ℕ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ ↦ (Real.log n) ^ k * (n : ℝ) ^ (-s)) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hr := ((isLittleO_log_rpow_rpow_atTop (k : ℝ) hs).comp_tendsto hnat)
  have hd := hr.tendsto_div_nhds_zero
  convert hd using 1
  ext n
  simp [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-- The exact clipping correction vanishes for polynomial bad mass and global tails. -/
theorem tendsto_covariance_clipping_correction
    (D E F : ℝ) {κ r : ℝ} (hκ : 0 < κ) (hr : 2 < r) :
    Tendsto (fun n : ℕ ↦
      5 * (D * (Real.log n) ^ 2) ^ 2 * (E * (n : ℝ) ^ (-κ)) +
        (4 * (n : ℝ) ^ 2 + 2 * (D * (Real.log n) ^ 2) * n) *
          (2 * F * (n : ℝ) ^ (-r))) atTop (𝓝 0) := by
  have hbad := tendsto_log_pow_mul_rpow_neg 4 hκ
  have hsq : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * (n : ℝ) ^ (-r)) atTop (𝓝 0) := by
    have ht := (tendsto_rpow_neg_atTop (by linarith : 0 < r - 2)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    change (n : ℝ) ^ (-(r - 2)) = (n : ℝ) ^ 2 * (n : ℝ) ^ (-r)
    rw [show -(r - 2) = (2 : ℝ) + (-r) by ring, Real.rpow_add hnpos, Real.rpow_two]
  have hcross : Tendsto
      (fun n : ℕ ↦ (Real.log n) ^ 2 * n * (n : ℝ) ^ (-r)) atTop (𝓝 0) := by
    apply (tendsto_log_pow_mul_rpow_neg 2 (by linarith : 0 < r - 1)).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [show -(r - 1) = (1 : ℝ) + (-r) by ring, Real.rpow_add hnpos, Real.rpow_one]
    ring
  convert ((hbad.const_mul (5 * D ^ 2 * E)).add (hsq.const_mul (8 * F))).add
    (hcross.const_mul (4 * D * F)) using 1
  · ext n
    ring
  · norm_num

/-- A fixed logarithmic lower-covariance coefficient after absorbing vanishing corrections. -/
def covarianceLogConstant (C₀ L₀ K : ℝ) : ℝ := C₀ + 4 * L₀ * K + 2 * K ^ 2 + 1

/-- The logarithmic covariance coefficient is positive for nonnegative input bounds. -/
theorem covarianceLogConstant_pos {C₀ L₀ K : ℝ}
    (hC₀ : 0 ≤ C₀) (hL₀ : 0 ≤ L₀) (hK : 0 ≤ K) :
    0 < covarianceLogConstant C₀ L₀ K := by
  unfold covarianceLogConstant
  positivity

/-- The clipping/deconditioning scalar bound is eventually a fixed logarithmic lower bound.
The nonnegative common-signal variance is retained in the input and then dropped. -/
theorem eventually_covariance_numeric_lower (C₀ L₀ K D E F : ℝ)
    (hL₀ : 0 ≤ L₀) (hK : 0 ≤ K) (hD : 0 ≤ D) {κ r : ℝ}
    (hκ : 0 < κ) (hr : 2 < r) :
    ∀ᶠ n : ℕ in atTop, ∀ (a b V δ tx ty z : ℝ),
      a ∈ Set.Icc 0 1 → b ∈ Set.Icc 0 1 → 0 ≤ V →
      δ ≤ E * (n : ℝ) ^ (-κ) →
      tx ≤ F * (n : ℝ) ^ (-r) → ty ≤ F * (n : ℝ) ^ (-r) →
      -C₀ * Real.log n + a * b * V - 2 * (a + b) * (L₀ * Real.log n) * K -
        2 * K ^ 2 - 5 * (D * (Real.log n) ^ 2) ^ 2 * δ -
          (4 * (n : ℝ) ^ 2 + 2 * (D * (Real.log n) ^ 2) * n) * (tx + ty) ≤ z →
      -(covarianceLogConstant C₀ L₀ K) * Real.log n ≤ z := by
  have he := (tendsto_covariance_clipping_correction D E F hκ hr).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have htlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hl := htlog.eventually_ge_atTop 1
  filter_upwards [he, hl] with n he hl a b V δ tx ty z ha hb hV hδ htx hty hz
  change 1 ≤ Real.log (n : ℝ) at hl
  have hlog : 0 ≤ Real.log n := by linarith
  have hbad := mul_le_mul_of_nonneg_left hδ
    (by positivity : 0 ≤ 5 * (D * (Real.log n) ^ 2) ^ 2)
  have hsum : tx + ty ≤ 2 * F * (n : ℝ) ^ (-r) := by linarith
  have htail := mul_le_mul_of_nonneg_left hsum
    (by positivity : 0 ≤ 4 * (n : ℝ) ^ 2 + 2 * (D * (Real.log n) ^ 2) * n)
  have herr := (add_le_add hbad htail).trans he.le
  have hvariance : 0 ≤ a * b * V := mul_nonneg (mul_nonneg ha.1 hb.1) hV
  have hmeans := mul_le_mul_of_nonneg_right (show 2 * (a + b) ≤ 4 by
    linarith [ha.2, hb.2]) (mul_nonneg (mul_nonneg hL₀ hlog) hK)
  have hconstant := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2 * K ^ 2 + 1)
  calc
    -(covarianceLogConstant C₀ L₀ K) * Real.log n ≤
        -C₀ * Real.log n - 4 * L₀ * K * Real.log n - 2 * K ^ 2 - 1 := by
      unfold covarianceLogConstant
      nlinarith only [hconstant]
    _ ≤ -C₀ * Real.log n + a * b * V - 2 * (a + b) * (L₀ * Real.log n) * K -
        2 * K ^ 2 - 5 * (D * (Real.log n) ^ 2) ^ 2 * δ -
          (4 * (n : ℝ) ^ 2 + 2 * (D * (Real.log n) ^ 2) * n) * (tx + ty) := by
      nlinarith only [hvariance, hmeans, herr]
    _ ≤ z := hz

end Ashlagi.MixtureBounds
