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

public import TieredMatching.FirstFresh
public import TieredMatching.CouponTail
public import TieredMatching.CouponMoments
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! # Lower tails for literal IID coupon hit counts

The finite-prefix Laplace transform is derived from the canonical product law. Exponential
Markov then gives quantitative small-hit bounds without an assumed binomial law or any
hypothesis about a deferred-acceptance process.
-/

@[expose] public section

namespace TieredMatching.CouponLowerTail

open MeasureTheory
open scoped NNReal ENNReal

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

open scoped Classical in
/-- Literal real-valued number of occurrences in a finite categorical sample. -/
noncomputable def count {ι : Type*} [Fintype ι] (w : α) (x : ι → α) : ℝ :=
  ∑ i, if x i = w then 1 else 0

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The finite-sample hit count is nonnegative. -/
theorem count_nonneg {ι : Type*} [Fintype ι] (w : α) (x : ι → α) : 0 ≤ count w x := by
  classical
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> norm_num

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
open scoped Classical in
/-- This real count is exactly the cardinality of the successful sample coordinates. -/
theorem count_eq_card {ι : Type*} [Fintype ι] (w : α) (x : ι → α) :
    count w x = ((Finset.univ.filter (fun i ↦ x i = w)).card : ℝ) := by
  classical
  simp [count, Finset.sum_boole]

/-- A finite hit count is a measurable statistic of its literal sample coordinates. -/
theorem measurable_count {ι : Type*} [Fintype ι] (w : α) : Measurable (count (ι := ι) w) := by
  classical
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_eq_fun (measurable_pi_apply i) measurable_const)
    measurable_const measurable_const

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
open scoped Classical in
/-- Exponentiating the negative hit count factors into coordinate rewards. -/
theorem exp_neg_count {ι : Type*} [Fintype ι] (w : α) (x : ι → α) (θ : ℝ) :
    Real.exp (-θ * count w x) = ∏ i, if x i = w then Real.exp (-θ) else 1 := by
  classical
  unfold count
  rw [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp

open scoped Classical in
/-- The exact one-draw categorical Laplace factor. -/
theorem integral_one_draw (p : PMF α) (w : α) (θ : ℝ) :
    (∫ a, (if a = w then Real.exp (-θ) else 1) ∂p.toMeasure) =
      1 - (p w).toReal + (p w).toReal * Real.exp (-θ) := by
  classical
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  have ht (a : α) : (p a).toReal * (if a = w then Real.exp (-θ) else 1) =
      (p a).toReal + (if a = w then (p a).toReal * (Real.exp (-θ) - 1) else 0) := by
    split_ifs <;> ring
  simp_rw [ht]
  rw [Finset.sum_add_distrib]
  have hs : ∑ a, (p a).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun a _ ↦ p.apply_ne_top a)]
    have hh : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
    rw [hh]
    rfl
  rw [hs]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- Exact finite-product Laplace transform, derived without a binomial-law premise. -/
theorem integral_laplace_finite {ι : Type*} [Fintype ι] (p : PMF α) (w : α) (θ : ℝ) :
    (∫ x : ι → α, Real.exp (-θ * count w x) ∂Measure.pi (fun _ ↦ p.toMeasure)) =
      (1 - (p w).toReal + (p w).toReal * Real.exp (-θ)) ^ Fintype.card ι := by
  classical
  simp_rw [exp_neg_count]
  rw [integral_fintype_prod_eq_pow (ι := ι) (fun a : α ↦
    if a = w then Real.exp (-θ) else 1), integral_one_draw]

/-- Literal hit count among the first `H` coordinates of the infinite IID stream. -/
noncomputable def hitCount (w : α) (H : ℕ) (x : ℕ → α) : ℝ :=
  count w ((Finset.range H).restrict x)

/-- The stream hit count is measurable. -/
theorem measurable_hitCount (w : α) (H : ℕ) : Measurable (hitCount w H) :=
  (measurable_count w).comp (by fun_prop)

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The literal prefix hit count is nonnegative. -/
theorem hitCount_nonneg (w : α) (H : ℕ) (x : ℕ → α) : 0 ≤ hitCount w H x :=
  count_nonneg _ _

open scoped Classical in
omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Literal stream hits also equal the ordinary sum over the natural-coordinate range. -/
theorem hitCount_eq_sum_range (w : α) (H : ℕ) (x : ℕ → α) :
    hitCount w H x = ∑ t ∈ Finset.range H, if x t = w then (1 : ℝ) else 0 := by
  exact Finset.sum_coe_sort (Finset.range H) (fun t ↦ if x t = w then (1 : ℝ) else 0)

open scoped Classical in
omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The hit count is the cardinality of successful literal natural-coordinate positions. -/
theorem hitCount_eq_card_range (w : α) (H : ℕ) (x : ℕ → α) :
    hitCount w H x = ((Finset.range H |>.filter (fun t ↦ x t = w)).card : ℝ) := by
  rw [hitCount_eq_sum_range]
  simp [Finset.sum_boole]

/-- The first `H` literal IID coordinates have exactly the finite product Laplace transform. -/
theorem integral_laplace (p : PMF α) (w : α) (H : ℕ) (θ : ℝ) :
    (∫ x, Real.exp (-θ * hitCount w H x) ∂FirstFresh.iidStream p) =
      (1 - (p w).toReal + (p w).toReal * Real.exp (-θ)) ^ H := by
  have hm : Measurable (fun x : ((i : Finset.range H) → α) ↦ Real.exp (-θ * count w x)) :=
    Real.measurable_exp.comp (measurable_const.mul (measurable_count w))
  change (∫ x, Real.exp (-θ * count w ((Finset.range H).restrict x))
    ∂FirstFresh.iidStream p) = _
  rw [← integral_map (show Measurable ((Finset.range H).restrict :
    (ℕ → α) → ((i : Finset.range H) → α)) from by fun_prop).aemeasurable
    hm.aestronglyMeasurable]
  rw [FirstFresh.iidStream, Measure.infinitePi_map_restrict, integral_laplace_finite]
  simp

/-- A nonnegative Laplace tilt gives an integrable bounded reward under the actual stream. -/
theorem integrable_laplace (p : PMF α) (w : α) (H : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun x ↦ Real.exp (-θ * hitCount w H x)) (FirstFresh.iidStream p) := by
  have hm : Measurable (fun x ↦ Real.exp (-θ * hitCount w H x)) :=
    Real.measurable_exp.comp (measurable_const.mul (measurable_hitCount w H))
  apply (integrable_const (μ := FirstFresh.iidStream p) (1 : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ) (hitCount_nonneg _ _ _)

/-- Exact-product Laplace transforms satisfy the standard exponential upper bound. -/
theorem integral_laplace_le (p : PMF α) (w : α) (H : ℕ) (θ : ℝ) :
    (∫ x, Real.exp (-θ * hitCount w H x) ∂FirstFresh.iidStream p) ≤
      Real.exp (-(p w).toReal * (1 - Real.exp (-θ)) * H) := by
  rw [integral_laplace]
  have hp : (p w).toReal ≤ 1 := by
    rw [← Coupon.singleton_real p w]
    exact measureReal_le_one
  have hbase : 0 ≤ 1 - (p w).toReal + (p w).toReal * Real.exp (-θ) :=
    add_nonneg (sub_nonneg.mpr hp) (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
  have hb : 1 - (p w).toReal + (p w).toReal * Real.exp (-θ) ≤
      Real.exp (-(p w).toReal * (1 - Real.exp (-θ))) := by
    have hh := Real.add_one_le_exp (-(p w).toReal * (1 - Real.exp (-θ)))
    nlinarith
  calc
    _ ≤ Real.exp (-(p w).toReal * (1 - Real.exp (-θ))) ^ H := pow_le_pow_left₀ hbase hb H
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- Exponential Markov lower-tail bound derived from the actual IID Laplace transform. -/
theorem lower_tail_le (p : PMF α) (w : α) (H : ℕ) (θ r : ℝ) (hθ : 0 ≤ θ) :
    (FirstFresh.iidStream p).real {x | hitCount w H x ≤ r} ≤
      Real.exp (θ * r - (p w).toReal * (1 - Real.exp (-θ)) * H) := by
  let f : (ℕ → α) → ℝ := fun x ↦ Real.exp (-θ * hitCount w H x)
  let ε : ℝ := Real.exp (-θ * r)
  have hε : 0 < ε := Real.exp_pos _
  have hsub : {x : ℕ → α | hitCount w H x ≤ r} ⊆ {x | ε ≤ f x} := by
    intro x hx
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hx (neg_nonpos.mpr hθ)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := FirstFresh.iidStream p) (f := f)
    (Filter.Eventually.of_forall fun x ↦ (Real.exp_pos _).le)
    (integrable_laplace p w H θ hθ) ε
  have hbound : (FirstFresh.iidStream p).real {x | hitCount w H x ≤ r} ≤
      (∫ x, f x ∂FirstFresh.iidStream p) / ε := by
    apply (le_div_iff₀ hε).mpr
    have hm := mul_le_mul_of_nonneg_right
      (measureReal_mono (μ := FirstFresh.iidStream p) hsub) hε.le
    nlinarith
  calc
    _ ≤ (∫ x, f x ∂FirstFresh.iidStream p) / ε := hbound
    _ ≤ Real.exp (-(p w).toReal * (1 - Real.exp (-θ)) * H) / ε :=
      div_le_div_of_nonneg_right (integral_laplace_le p w H θ) hε.le
    _ = _ := by
      dsimp [ε]
      rw [← Real.exp_sub]
      congr 1
      ring

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- A rational bound on the half-tilt is enough for a fixed explicit Chernoff constant. -/
theorem one_sub_exp_neg_half : (1 : ℝ) / 3 ≤ 1 - Real.exp (-(1 / 2 : ℝ)) := by
  have hh := Real.add_one_le_exp (1 / 2 : ℝ)
  have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-(1 / 2 : ℝ))).le
  have he : Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2 : ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith

/-- A literal IID coupon gets fewer than half its expected hits with probability at most
`exp(-p*H/12)`. The weak inequality includes the threshold's boundary. -/
theorem lower_tail_half_mean (p : PMF α) (w : α) (H : ℕ) :
    (FirstFresh.iidStream p).real {x | hitCount w H x ≤ (p w).toReal * H / 2} ≤
      Real.exp (-(p w).toReal * H / 12) := by
  apply (lower_tail_le p w H (1 / 2) ((p w).toReal * H / 2) (by norm_num)).trans
  apply Real.exp_le_exp.mpr
  have hpH : 0 ≤ (p w).toReal * (H : ℝ) := mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)
  have hh := mul_le_mul_of_nonneg_right one_sub_exp_neg_half hpH
  nlinarith

/-- Any deterministic lower bound on the actual mean supplies the same uniform small-hit tail. -/
theorem lower_tail_of_mean_lower (p : PMF α) (w : α) (H : ℕ) (L : ℝ)
    (hL : L ≤ (p w).toReal * H) :
    (FirstFresh.iidStream p).real {x | hitCount w H x ≤ L / 2} ≤ Real.exp (-L / 12) := by
  calc
    _ ≤ (FirstFresh.iidStream p).real {x | hitCount w H x ≤ (p w).toReal * H / 2} := by
      apply measureReal_mono (μ := FirstFresh.iidStream p)
      intro x hx
      change hitCount w H x ≤ L / 2 at hx
      change hitCount w H x ≤ (p w).toReal * H / 2
      exact hx.trans (by linarith)
    _ ≤ Real.exp (-(p w).toReal * H / 12) := lower_tail_half_mean p w H
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- Quantitative normalized-score small-hit input. The explicit horizon inequality is the
only deterministic rounding input: a horizon near `n*log n/(8*A)` eventually exceeds it. -/
theorem normalized_small_hit_tail (p : PMF α) (w : α) (H n : ℕ) (hn : 0 < n)
    (A : ℝ) (hA : 0 < A) (hp : 1 / (A * n) ≤ (p w).toReal)
    (hH : (n : ℝ) * Real.log n / (16 * A) ≤ H) :
    (FirstFresh.iidStream p).real {x | hitCount w H x ≤ Real.log n / (32 * A ^ 2)} ≤
      Real.exp (-Real.log n / (192 * A ^ 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hprod := mul_le_mul hp hH
    (div_nonneg (mul_nonneg hnR.le hlog) (by positivity : 0 ≤ 16 * A)) ENNReal.toReal_nonneg
  have heq : 1 / (A * n) * ((n : ℝ) * Real.log n / (16 * A)) =
      Real.log n / (16 * A ^ 2) := by
    field_simp
  rw [heq] at hprod
  have hh := lower_tail_of_mean_lower p w H (Real.log n / (16 * A ^ 2)) hprod
  have ht : Real.log n / (16 * A ^ 2) / 2 = Real.log n / (32 * A ^ 2) := by ring
  have he : -(Real.log n / (16 * A ^ 2)) / 12 = -Real.log n / (192 * A ^ 2) := by ring
  simpa only [ht, he] using hh

/-- The explicit exponential bound is exactly a negative power of the market size. -/
theorem normalized_small_hit_tail_rpow (p : PMF α) (w : α) (H n : ℕ) (hn : 0 < n)
    (A : ℝ) (hA : 0 < A) (hp : 1 / (A * n) ≤ (p w).toReal)
    (hH : (n : ℝ) * Real.log n / (16 * A) ≤ H) :
    (FirstFresh.iidStream p).real {x | hitCount w H x ≤ Real.log n / (32 * A ^ 2)} ≤
      (n : ℝ) ^ (-(1 / (192 * A ^ 2))) := by
  have he : Real.exp (-Real.log n / (192 * A ^ 2)) =
      (n : ℝ) ^ (-(1 / (192 * A ^ 2))) := by
    rw [Real.rpow_def_of_pos (show (0 : ℝ) < n by exact_mod_cast hn)]
    congr 1
    ring
  simpa only [he] using normalized_small_hit_tail p w H n hn A hA hp hH

/-- An explicit finite-size condition absorbs the floor in the source setup horizon. -/
theorem floor_setup_horizon_lower (n : ℕ) (A : ℝ) (hA : 0 < A)
    (hlarge : 16 * A ≤ (n : ℝ) * Real.log n) :
    (n : ℝ) * Real.log n / (16 * A) ≤
      (⌊(n : ℝ) * Real.log n / (8 * A)⌋₊ : ℝ) := by
  have hf := Nat.lt_floor_add_one ((n : ℝ) * Real.log n / (8 * A))
  have hx : 2 ≤ (n : ℝ) * Real.log n / (8 * A) :=
    (le_div_iff₀ (by positivity : 0 < 8 * A)).mpr (by linarith)
  have he : (n : ℝ) * Real.log n / (16 * A) =
      ((n : ℝ) * Real.log n / (8 * A)) / 2 := by ring
  rw [he]
  linarith

/-- Source-scale literal IID coupon lower tail, including deterministic floor rounding. -/
theorem floor_setup_small_hit_tail (p : PMF α) (w : α) (n : ℕ) (hn : 0 < n)
    (A : ℝ) (hA : 0 < A) (hp : 1 / (A * n) ≤ (p w).toReal)
    (hlarge : 16 * A ≤ (n : ℝ) * Real.log n) :
    (FirstFresh.iidStream p).real {x |
      hitCount w ⌊(n : ℝ) * Real.log n / (8 * A)⌋₊ x ≤ Real.log n / (32 * A ^ 2)} ≤
      (n : ℝ) ^ (-(1 / (192 * A ^ 2))) :=
  normalized_small_hit_tail_rpow p w _ n hn A hA hp (floor_setup_horizon_lower n A hA hlarge)

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Normalized public scores themselves imply the needed literal categorical mass bound. -/
theorem ofWeights_mass_lower [Nonempty α] (a : α → ℝ≥0) (ha : ∀ w, 1 ≤ a w)
    (A : ℝ) (hupper : ∀ w, (a w : ℝ) ≤ A) (w : α) :
    1 / (A * Fintype.card α) ≤ (RandomRanking.ofWeights a w).toReal := by
  have hpos : ∀ w, 0 < a w := fun w ↦ lt_of_lt_of_le (by norm_num) (ha w)
  have hW := CouponMoments.totalWeight_pos a hpos
  have hbound : CouponMoments.totalWeight a ≤ A * Fintype.card α := by
    simpa only [mul_comm] using CouponMoments.totalWeight_le_card_mul a A hupper
  exact (one_div_le_one_div_of_le hW hbound).trans (CouponMoments.ofWeights_real_ge_inv a ha w)

/-- Uniform source setup estimate for the actual normalized-score IID stream. The constants
`1/(32*A^2)` and `1/(192*A^2)` depend only on the score ceiling, not on tier shares. -/
theorem ofWeights_floor_small_hit_tail [Nonempty α] (a : α → ℝ≥0) (ha : ∀ w, 1 ≤ a w)
    (A : ℝ) (hA : 0 < A) (hupper : ∀ w, (a w : ℝ) ≤ A) (w : α)
    (hlarge : 16 * A ≤ (Fintype.card α : ℝ) * Real.log (Fintype.card α)) :
    (FirstFresh.iidStream (RandomRanking.ofWeights a)).real {x |
      hitCount w ⌊(Fintype.card α : ℝ) * Real.log (Fintype.card α) / (8 * A)⌋₊ x ≤
        Real.log (Fintype.card α) / (32 * A ^ 2)} ≤
      (Fintype.card α : ℝ) ^ (-(1 / (192 * A ^ 2))) :=
  floor_setup_small_hit_tail _ w _ Fintype.card_pos A hA
    (ofWeights_mass_lower a ha A hupper w) hlarge

/-- The explicit finite-size condition for the floored setup horizon holds eventually,
with a threshold depending only on the fixed score ceiling. -/
theorem eventually_setup_large (A : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, 16 * A ≤ (n : ℝ) * Real.log n := by
  have hn : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hl := Real.tendsto_log_atTop.comp hn
  filter_upwards [hn.eventually_ge_atTop (16 * A), hl.eventually_ge_atTop 1] with n hsize hlog
  have hnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  change 1 ≤ Real.log (n : ℝ) at hlog
  nlinarith

/-- The elementary logarithmic lower bound needed for early missing coupons. -/
theorem log_one_sub_lower {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    -2 * q ≤ Real.log (1 - q) := by
  have hpos : 0 < 1 - q := by linarith
  have hh := Real.one_sub_inv_le_log_of_pos hpos
  have he : 1 - (1 - q)⁻¹ = -q / (1 - q) := by field_simp; ring
  rw [he] at hh
  apply le_trans _ hh
  apply (le_div_iff₀ hpos).mpr
  nlinarith

/-- A coupon of mass at most one half stays missing with the elementary exponential lower bound. -/
theorem no_hit_lower {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (H : ℕ) :
    Real.exp (-2 * q * H) ≤ (1 - q) ^ H := by
  calc
    _ ≤ Real.exp ((H : ℝ) * Real.log (1 - q)) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right (log_one_sub_lower hq0 hq) (Nat.cast_nonneg H)
      nlinarith
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by linarith : 0 < 1 - q)]

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- In the setup horizon, every coupon whose mass is at most `A/n` is still missing
with probability at least `exp(-log n/4)`. -/
theorem setup_missing_probability_lower (p : PMF α) (w : α) (H n : ℕ) (hn : 0 < n)
    (A : ℝ) (hA : 0 < A) (hnA : 2 * A ≤ n) (hp : (p w).toReal ≤ A / n)
    (hH : (H : ℝ) ≤ (n : ℝ) * Real.log n / (8 * A)) :
    Real.exp (-Real.log n / 4) ≤ (1 - (p w).toReal) ^ H := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpHalf : (p w).toReal ≤ 1 / 2 := hp.trans ((div_le_iff₀ hnR).mpr (by linarith))
  have hprod := mul_le_mul hp hH (Nat.cast_nonneg H) (div_nonneg hA.le hnR.le)
  have he : A / n * ((n : ℝ) * Real.log n / (8 * A)) = Real.log n / 8 := by field_simp
  rw [he] at hprod
  exact (Real.exp_le_exp.mpr (by linarith)).trans (no_hit_lower ENNReal.toReal_nonneg hpHalf H)

/-- Exact finite-product missing-count mean is at least `n^(3/4)` during setup. -/
theorem setup_missing_mean_lower (n : ℕ) (hn : 0 < n) (p : PMF (Fin n)) (H : ℕ)
    (A : ℝ) (hA : 0 < A) (hnA : 2 * A ≤ n) (hp : ∀ w, (p w).toReal ≤ A / n)
    (hH : (H : ℝ) ≤ (n : ℝ) * Real.log n / (8 * A)) :
    (n : ℝ) ^ (3 / 4 : ℝ) ≤ ∫ x, Coupon.missingCount H x ∂Coupon.iidLaw p H := by
  rw [Coupon.integral_missingCount]
  have he : (n : ℝ) ^ (3 / 4 : ℝ) = (n : ℝ) * Real.exp (-Real.log n / 4) := by
    rw [Real.rpow_def_of_pos (show (0 : ℝ) < n by exact_mod_cast hn)]
    conv_rhs => rw [← Real.exp_log (show (0 : ℝ) < n by exact_mod_cast hn)]
    rw [← Real.exp_add]
    congr 1
    simp only [Real.log_exp]
    ring
  rw [he]
  calc
    _ = ∑ _w : Fin n, Real.exp (-Real.log n / 4) := by simp
    _ ≤ _ := Finset.sum_le_sum fun w _ ↦
      setup_missing_probability_lower p w H n hn A hA hnA (hp w) hH

/-- Generic one-sided Chebyshev form for a missing count with variance at most its mean. -/
theorem small_count_chebyshev {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : MemLp X 2 μ)
    (hmean : 4 ≤ ∫ x, X x ∂μ) (hvar : ProbabilityTheory.variance X μ ≤ ∫ x, X x ∂μ) :
    μ.real {x | X x ≤ 2} ≤ 4 / (∫ x, X x ∂μ) := by
  let M := ∫ x, X x ∂μ
  have hM : 0 < M := by dsimp [M]; linarith
  have hsub : {x | X x ≤ 2} ⊆ {x | M / 2 ≤ |X x - M|} := by
    intro x hx
    change X x ≤ 2 at hx
    change M / 2 ≤ |X x - M|
    have hh : -(X x - M) ≤ |X x - M| := neg_le_abs _
    dsimp [M] at *
    linarith
  have hh := ProbabilityTheory.meas_ge_le_variance_div_sq hX (by positivity : 0 < M / 2)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  rw [ENNReal.toReal_ofReal (div_nonneg (ProbabilityTheory.variance_nonneg _ _) (sq_nonneg _))]
    at hr
  calc
    _ ≤ μ.real {x | M / 2 ≤ |X x - M|} := measureReal_mono hsub
    _ ≤ ProbabilityTheory.variance X μ / (M / 2) ^ 2 := hr
    _ ≤ M / (M / 2) ^ 2 := div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ = 4 / M := by field_simp; ring

/-- Actual finite IID missing counts satisfy the source's `4/E` lower-tail estimate. -/
theorem missing_count_le_two (p : PMF α) (H : ℕ)
    (hmean : 4 ≤ ∫ x, Coupon.missingCount H x ∂Coupon.iidLaw p H) :
    (Coupon.iidLaw p H).real {x | Coupon.missingCount H x ≤ 2} ≤
      4 / (∫ x, Coupon.missingCount H x ∂Coupon.iidLaw p H) := by
  classical
  have hm : MemLp (Coupon.missingCount (α := α) H) 2 (Coupon.iidLaw p H) := by
    apply MemLp.of_bound Measurable.of_discrete.aestronglyMeasurable (Fintype.card α : ℝ)
    filter_upwards [] with x
    rw [Coupon.missingCount_eq_card, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast Finset.card_le_card (Finset.subset_univ (Coupon.missingCoupons H x))
  exact small_count_chebyshev _ _ hm hmean (Coupon.variance_missingCount_le_integral p H)

/-- Restrict the literal IID stream to its first `H` coordinates with `Fin H` indexing. -/
def samplePrefix (H : ℕ) (x : ℕ → α) (i : Fin H) : α := x i

omit [Fintype α] [MeasurableSingletonClass α] in
/-- Literal finite-prefix restriction is measurable. -/
theorem measurable_prefix (H : ℕ) : Measurable (samplePrefix (α := α) H) := by
  unfold samplePrefix
  fun_prop

omit [Fintype α] [MeasurableSingletonClass α] in
/-- The exact finite-prefix law of the actual IID stream is CouponTail's canonical product. -/
theorem map_prefix (p : PMF α) (H : ℕ) :
    (FirstFresh.iidStream p).map (samplePrefix H) = Coupon.iidLaw p H := by
  have hi := ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : ℕ ↦ p.toMeasure)
    (X := fun _ a ↦ a) (by fun_prop)
  have hf := ProbabilityTheory.iIndepFun.precomp (g := fun i : Fin H ↦ (i : ℕ))
    Fin.val_injective hi
  have hm := ProbabilityTheory.iIndepFun.map_fun_eq_pi_map
    (fun i : Fin H ↦ (measurable_pi_apply (i : ℕ)).aemeasurable) hf
  change (FirstFresh.iidStream p).map (fun x : ℕ → α ↦ fun i : Fin H ↦ x i) = _
  simpa only [FirstFresh.iidStream, Coupon.iidLaw, Measure.infinitePi_map_eval] using hm

/-- Literal missing-coupon count in an actual finite prefix of the infinite stream. -/
noncomputable def missingCount (H : ℕ) (x : ℕ → α) : ℝ := Coupon.missingCount H (samplePrefix H x)

/-- Exact expectation transfer from the actual stream to the finite product missing count. -/
theorem integral_missingCount (p : PMF α) (H : ℕ) :
    (∫ x, missingCount H x ∂FirstFresh.iidStream p) =
      ∫ y, Coupon.missingCount H y ∂Coupon.iidLaw p H := by
  change (∫ x, Coupon.missingCount H (samplePrefix H x) ∂FirstFresh.iidStream p) = _
  rw [← integral_map (measurable_prefix H).aemeasurable Measurable.of_discrete.aestronglyMeasurable,
    map_prefix]

/-- Exact lower-tail event transfer for literal missing counts. -/
theorem missingCount_probability (p : PMF α) (H : ℕ) (r : ℝ) :
    (FirstFresh.iidStream p).real {x | missingCount H x ≤ r} =
      (Coupon.iidLaw p H).real {y | Coupon.missingCount H y ≤ r} := by
  rw [measureReal_def, measureReal_def, ← map_prefix p H,
    Measure.map_apply (measurable_prefix H) (by exact (Set.toFinite _).measurableSet)]
  rfl

/-- The actual IID stream's missing-count expectation has the source setup lower bound. -/
theorem stream_setup_missing_mean_lower (n : ℕ) (hn : 0 < n) (p : PMF (Fin n)) (H : ℕ)
    (A : ℝ) (hA : 0 < A) (hnA : 2 * A ≤ n) (hp : ∀ w, (p w).toReal ≤ A / n)
    (hH : (H : ℝ) ≤ (n : ℝ) * Real.log n / (8 * A)) :
    (n : ℝ) ^ (3 / 4 : ℝ) ≤ ∫ x, missingCount H x ∂FirstFresh.iidStream p := by
  rw [integral_missingCount]
  exact setup_missing_mean_lower n hn p H A hA hnA hp hH

/-- Actual setup failure of having at most two unseen coupons is at most `4/n^(3/4)`. -/
theorem stream_setup_missing_le_two (n : ℕ) (hn : 0 < n) (p : PMF (Fin n)) (H : ℕ)
    (A : ℝ) (hA : 0 < A) (hnA : 2 * A ≤ n) (hp : ∀ w, (p w).toReal ≤ A / n)
    (hH : (H : ℝ) ≤ (n : ℝ) * Real.log n / (8 * A))
    (hlarge : 4 ≤ (n : ℝ) ^ (3 / 4 : ℝ)) :
    (FirstFresh.iidStream p).real {x | missingCount H x ≤ 2} ≤
      4 / (n : ℝ) ^ (3 / 4 : ℝ) := by
  rw [missingCount_probability]
  have hm := setup_missing_mean_lower n hn p H A hA hnA hp hH
  exact (missing_count_le_two p H (hlarge.trans hm)).trans
    (div_le_div_of_nonneg_left (by norm_num) (lt_of_lt_of_le (by norm_num) hlarge) hm)

/-- The source's floored setup horizon satisfies the deterministic early-time upper bound. -/
theorem floor_setup_horizon_upper (n : ℕ) (A : ℝ) (hA : 0 < A) :
    (⌊(n : ℝ) * Real.log n / (8 * A)⌋₊ : ℝ) ≤ (n : ℝ) * Real.log n / (8 * A) := by
  apply Nat.floor_le
  have hl : 0 ≤ (n : ℝ) * Real.log n := by
    by_cases hn : n = 0
    · simp [hn]
    · exact mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn))
  exact div_nonneg hl (by positivity)

/-- Missing-coupon setup lower tail at the exact source floor horizon. -/
theorem floor_setup_missing_le_two (n : ℕ) (hn : 0 < n) (p : PMF (Fin n))
    (A : ℝ) (hA : 0 < A) (hnA : 2 * A ≤ n) (hp : ∀ w, (p w).toReal ≤ A / n)
    (hlarge : 4 ≤ (n : ℝ) ^ (3 / 4 : ℝ)) :
    (FirstFresh.iidStream p).real {x |
      missingCount ⌊(n : ℝ) * Real.log n / (8 * A)⌋₊ x ≤ 2} ≤
      4 / (n : ℝ) ^ (3 / 4 : ℝ) :=
  stream_setup_missing_le_two n hn p _ A hA hnA hp (floor_setup_horizon_upper n A hA) hlarge

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Normalized scores also give the uniform categorical upper mass needed for missing coupons. -/
theorem ofWeights_mass_upper [Nonempty α] (a : α → ℝ≥0) (ha : ∀ w, 1 ≤ a w)
    (A : ℝ) (hupper : ∀ w, (a w : ℝ) ≤ A) (w : α) :
    (RandomRanking.ofWeights a w).toReal ≤ A / Fintype.card α := by
  have hpos : ∀ w, 0 < a w := fun w ↦ lt_of_lt_of_le (by norm_num) (ha w)
  have hW := CouponMoments.totalWeight_pos a hpos
  have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos (α := α)
  have hA : 0 ≤ A := (a w).coe_nonneg.trans (hupper w)
  have he : (RandomRanking.ofWeights a w).toReal = (a w : ℝ) / CouponMoments.totalWeight a := by
    apply (eq_div_iff hW.ne').mpr
    simpa only [mul_comm] using CouponMoments.ofWeights_weighted_mass a hpos w
  rw [he]
  exact (div_le_div_of_nonneg_right (hupper w) hW.le).trans
    (div_le_div_of_nonneg_left hA hn (CouponMoments.card_le_totalWeight a ha))

/-- The exact normalized-score stream satisfies the missing-count setup bound. -/
theorem ofWeights_floor_missing_le_two {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (ha : ∀ w, 1 ≤ a w) (A : ℝ) (hA : 0 < A) (hupper : ∀ w, (a w : ℝ) ≤ A)
    (hnA : 2 * A ≤ n) (hlarge : 4 ≤ (n : ℝ) ^ (3 / 4 : ℝ)) :
    (FirstFresh.iidStream (RandomRanking.ofWeights a)).real {x |
      missingCount ⌊(n : ℝ) * Real.log n / (8 * A)⌋₊ x ≤ 2} ≤
      4 / (n : ℝ) ^ (3 / 4 : ℝ) := by
  apply floor_setup_missing_le_two n (Nat.pos_of_ne_zero (NeZero.ne n)) _ A hA hnA _ hlarge
  intro w
  simpa only [Fintype.card_fin] using ofWeights_mass_upper a ha A hupper w

/-- Normalized-score literal stream missing expectation at the exact setup floor horizon. -/
theorem ofWeights_floor_missing_mean_lower {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (ha : ∀ w, 1 ≤ a w) (A : ℝ) (hA : 0 < A) (hupper : ∀ w, (a w : ℝ) ≤ A)
    (hnA : 2 * A ≤ n) :
    (n : ℝ) ^ (3 / 4 : ℝ) ≤
      ∫ x, missingCount ⌊(n : ℝ) * Real.log n / (8 * A)⌋₊ x
        ∂FirstFresh.iidStream (RandomRanking.ofWeights a) := by
  apply stream_setup_missing_mean_lower n (Nat.pos_of_ne_zero (NeZero.ne n)) _ _ A hA hnA
  · intro w
    simpa only [Fintype.card_fin] using ofWeights_mass_upper a ha A hupper w
  · exact floor_setup_horizon_upper n A hA

end TieredMatching.CouponLowerTail
