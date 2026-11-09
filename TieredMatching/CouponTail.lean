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

public import Mathlib

/-! # Missing coupons in a finite independent categorical sample

All estimates refer to the explicit finite product law. They make no assertion about a
randomly stopped deferred-acceptance process.
-/

@[expose] public section

namespace TieredMatching.Coupon

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The canonical law of `H` independent draws from a categorical PMF. -/
noncomputable def iidLaw (p : PMF α) (H : ℕ) : Measure (Fin H → α) :=
  Measure.pi fun _ ↦ p.toMeasure

instance (p : PMF α) (H : ℕ) : IsProbabilityMeasure (iidLaw p H) := by
  unfold iidLaw
  infer_instance

/-- A coupon is missing if none of the `H` draws equals it. -/
def missing (H : ℕ) (c : α) : Set (Fin H → α) := {x | ∀ t, x t ≠ c}

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- A missing-coupon event is a finite product box. -/
theorem missing_eq_pi (H : ℕ) (c : α) :
    missing H c = Set.univ.pi (fun _ ↦ ({c} : Set α)ᶜ) := by
  ext x
  simp [missing]

omit [Fintype α] in
/-- Missing-coupon events are measurable. -/
theorem measurableSet_missing (H : ℕ) (c : α) : MeasurableSet (missing H c) := by
  rw [missing_eq_pi]
  exact MeasurableSet.univ_pi fun _ ↦ (measurableSet_singleton c).compl

/-- The exact no-hit probability is the product of the one-draw no-hit probabilities. -/
theorem missing_measure (p : PMF α) (H : ℕ) (c : α) :
    iidLaw p H (missing H c) = (p.toMeasure ({c}ᶜ)) ^ H := by
  rw [missing_eq_pi, iidLaw, Measure.pi_pi]
  simp

omit [Fintype α] in
/-- The one-draw singleton probability equals its PMF mass. -/
theorem singleton_real (p : PMF α) (c : α) :
    p.toMeasure.real {c} = (p c).toReal := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton p c (measurableSet_singleton c)]

/-- The real-valued missing probability has the usual geometric form. -/
theorem missing_real (p : PMF α) (H : ℕ) (c : α) :
    (iidLaw p H).real (missing H c) = (1 - (p c).toReal) ^ H := by
  change (iidLaw p H (missing H c)).toReal = _
  rw [missing_measure, ENNReal.toReal_pow]
  change (p.toMeasure.real ({c}ᶜ)) ^ H = _
  rw [probReal_compl_eq_one_sub (measurableSet_singleton c), singleton_real]

/-- A lower bound on the one-draw mass gives an exponential no-hit bound. -/
theorem missing_real_le_exp (p : PMF α) (H : ℕ) (c : α) (pmin : ℝ)
    (hmin : pmin ≤ (p c).toReal) :
    (iidLaw p H).real (missing H c) ≤ Real.exp (-(H : ℝ) * pmin) := by
  rw [missing_real]
  have hc : (p c).toReal ≤ 1 := by
    rw [← singleton_real p c]
    exact measureReal_le_one
  have hbase : 1 - (p c).toReal ≤ Real.exp (-pmin) := by
    have h := Real.add_one_le_exp (-pmin)
    linarith
  calc
    (1 - (p c).toReal) ^ H ≤ Real.exp (-pmin) ^ H :=
      pow_le_pow_left₀ (sub_nonneg.mpr hc) hbase H
    _ = Real.exp (-(H : ℝ) * pmin) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- At least one coupon is absent from the finite sample. -/
def someMissing (H : ℕ) : Set (Fin H → α) := ⋃ c, missing H c

/-- The finite union bound for an unseen coupon, with exact individual probabilities. -/
theorem someMissing_real_le_sum (p : PMF α) (H : ℕ) :
    (iidLaw p H).real (someMissing H) ≤ ∑ c, (1 - (p c).toReal) ^ H := by
  simpa only [someMissing, missing_real] using
    measureReal_iUnion_fintype_le (μ := iidLaw p H) (missing H)

/-- A uniform lower mass gives the standard finite coupon-horizon exponential tail. -/
theorem someMissing_real_le_exp (p : PMF α) (H : ℕ) (pmin : ℝ)
    (hmin : ∀ c, pmin ≤ (p c).toReal) :
    (iidLaw p H).real (someMissing H) ≤
      (Fintype.card α : ℝ) * Real.exp (-(H : ℝ) * pmin) := by
  calc
    (iidLaw p H).real (someMissing H) ≤
        ∑ c, (iidLaw p H).real (missing H c) :=
      measureReal_iUnion_fintype_le (missing H)
    _ ≤ ∑ _c : α, Real.exp (-(H : ℝ) * pmin) :=
      Finset.sum_le_sum fun c _ ↦ missing_real_le_exp p H c pmin (hmin c)
    _ = _ := by simp

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Simultaneous absence of two coupons is a product box avoiding their union. -/
theorem missing_inter_eq_pi (H : ℕ) (c d : α) :
    missing H c ∩ missing H d = Set.univ.pi (fun _ ↦ ({c, d} : Set α)ᶜ) := by
  ext x
  simp [missing, forall_and]

/-- The exact joint no-hit measure, before conversion to real probabilities. -/
theorem missing_inter_measure (p : PMF α) (H : ℕ) (c d : α) :
    iidLaw p H (missing H c ∩ missing H d) = (p.toMeasure ({c, d}ᶜ)) ^ H := by
  rw [missing_inter_eq_pi, iidLaw, Measure.pi_pi]
  simp

omit [Fintype α] in
/-- Distinct singleton probabilities add. -/
theorem pair_real (p : PMF α) (c d : α) (hcd : c ≠ d) :
    p.toMeasure.real {c, d} = (p c).toReal + (p d).toReal := by
  rw [show ({c, d} : Set α) = ({c} : Set α) ∪ {d} by ext x; simp [or_comm]]
  rw [measureReal_union (by simp [hcd]) (measurableSet_singleton d),
    singleton_real, singleton_real]

/-- Two distinct coupons are simultaneously missing with probability `(1-pc-pd)^H`. -/
theorem missing_inter_real (p : PMF α) (H : ℕ) (c d : α) (hcd : c ≠ d) :
    (iidLaw p H).real (missing H c ∩ missing H d) =
      (1 - (p c).toReal - (p d).toReal) ^ H := by
  change (iidLaw p H (missing H c ∩ missing H d)).toReal = _
  rw [missing_inter_measure, ENNReal.toReal_pow]
  change (p.toMeasure.real ({c, d}ᶜ)) ^ H = _
  rw [probReal_compl_eq_one_sub (by measurability), pair_real p c d hcd,
    sub_add_eq_sub_sub]

/-- Missing events for distinct coupons have a joint probability at most the product. -/
theorem missing_inter_real_le_mul (p : PMF α) (H : ℕ) (c d : α) (hcd : c ≠ d) :
    (iidLaw p H).real (missing H c ∩ missing H d) ≤
      (iidLaw p H).real (missing H c) * (iidLaw p H).real (missing H d) := by
  have hsum : (p c).toReal + (p d).toReal ≤ 1 := by
    rw [← pair_real p c d hcd]
    exact measureReal_le_one
  rw [missing_inter_real p H c d hcd, missing_real, missing_real]
  calc
    (1 - (p c).toReal - (p d).toReal) ^ H ≤
        ((1 - (p c).toReal) * (1 - (p d).toReal)) ^ H := by
      apply pow_le_pow_left₀ (by linarith) _ H
      have hc : 0 ≤ (p c).toReal := ENNReal.toReal_nonneg
      have hd : 0 ≤ (p d).toReal := ENNReal.toReal_nonneg
      nlinarith [mul_nonneg hc hd]
    _ = _ := mul_pow _ _ H

/-- Real indicator that a named coupon is missing. -/
noncomputable def missingIndicator (H : ℕ) (c : α) : (Fin H → α) → ℝ :=
  (missing H c).indicator fun _ ↦ 1

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Missing indicators are idempotent under squaring. -/
theorem missingIndicator_sq (H : ℕ) (c : α) (x : Fin H → α) :
    missingIndicator H c x ^ 2 = missingIndicator H c x := by
  classical
  by_cases hx : x ∈ missing H c <;> simp [missingIndicator, hx]

omit [Fintype α] in
/-- Every missing indicator has a finite second moment under the iid law. -/
theorem memLp_missingIndicator (p : PMF α) (H : ℕ) (c : α) :
    MemLp (missingIndicator H c) 2 (iidLaw p H) := by
  exact (memLp_const (1 : ℝ)).indicator (measurableSet_missing H c).nullMeasurableSet

omit [Fintype α] in
/-- A missing indicator's expectation is its missing-event probability. -/
theorem integral_missingIndicator (p : PMF α) (H : ℕ) (c : α) :
    (∫ x, missingIndicator H c x ∂iidLaw p H) =
      (iidLaw p H).real (missing H c) := by
  simpa [missingIndicator, smul_eq_mul] using
    integral_indicator_const (μ := iidLaw p H) (1 : ℝ) (measurableSet_missing H c)

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The product of missing indicators is the indicator of joint absence. -/
theorem missingIndicator_mul (H : ℕ) (c d : α) :
    missingIndicator H c * missingIndicator H d =
      (missing H c ∩ missing H d).indicator (fun _ ↦ (1 : ℝ)) := by
  classical
  funext x
  by_cases hc : x ∈ missing H c <;> by_cases hd : x ∈ missing H d <;>
    simp [missingIndicator, hc, hd]

omit [Fintype α] in
/-- A product of missing indicators has the joint absence probability as its expectation. -/
theorem integral_missingIndicator_mul (p : PMF α) (H : ℕ) (c d : α) :
    (∫ x, missingIndicator H c x * missingIndicator H d x ∂iidLaw p H) =
      (iidLaw p H).real (missing H c ∩ missing H d) := by
  change (∫ x, (missingIndicator H c * missingIndicator H d) x ∂iidLaw p H) = _
  rw [missingIndicator_mul]
  simpa [smul_eq_mul] using integral_indicator_const (μ := iidLaw p H) (1 : ℝ)
    ((measurableSet_missing H c).inter (measurableSet_missing H d))

/-- Distinct missing-coupon indicators have nonpositive covariance. -/
theorem covariance_missingIndicator_nonpos (p : PMF α) (H : ℕ) (c d : α)
    (hcd : c ≠ d) :
    covariance (missingIndicator H c) (missingIndicator H d) (iidLaw p H) ≤ 0 := by
  rw [covariance_eq_sub (memLp_missingIndicator p H c) (memLp_missingIndicator p H d)]
  change (∫ x, missingIndicator H c x * missingIndicator H d x ∂iidLaw p H) -
    (∫ x, missingIndicator H c x ∂iidLaw p H) *
      (∫ x, missingIndicator H d x ∂iidLaw p H) ≤ 0
  rw [integral_missingIndicator_mul, integral_missingIndicator, integral_missingIndicator]
  exact sub_nonpos.mpr (missing_inter_real_le_mul p H c d hcd)

omit [Fintype α] in
/-- The variance of a missing indicator is at most its expectation. -/
theorem variance_missingIndicator_le_integral (p : PMF α) (H : ℕ) (c : α) :
    variance (missingIndicator H c) (iidLaw p H) ≤
      ∫ x, missingIndicator H c x ∂iidLaw p H := by
  rw [variance_eq_sub (memLp_missingIndicator p H c)]
  have hsq : missingIndicator H c ^ 2 = missingIndicator H c := by
    funext x
    exact missingIndicator_sq H c x
  rw [hsq]
  exact sub_le_self _ (sq_nonneg _)

/-- The real-valued number of coupons absent from the sample. -/
noncomputable def missingCount (H : ℕ) (x : Fin H → α) : ℝ :=
  ∑ c, missingIndicator H c x

/-- Expected missing coupons equal the sum of their exact no-hit probabilities. -/
theorem integral_missingCount (p : PMF α) (H : ℕ) :
    (∫ x, missingCount H x ∂iidLaw p H) = ∑ c, (1 - (p c).toReal) ^ H := by
  unfold missingCount
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun c _ ↦ by rw [integral_missingIndicator, missing_real]
  · intro c _
    exact (memLp_missingIndicator p H c).integrable (by norm_num)

/-- Nonpositive cross-covariances bound missing-count variance by its mean. -/
theorem variance_missingCount_le_integral (p : PMF α) (H : ℕ) :
    variance (missingCount H) (iidLaw p H) ≤
      ∫ x, missingCount H x ∂iidLaw p H := by
  classical
  change variance (fun x ↦ ∑ c, missingIndicator H c x) (iidLaw p H) ≤ _
  rw [variance_fun_sum (fun c ↦ memLp_missingIndicator p H c)]
  have hrow (c : α) :
      (∑ d, covariance (missingIndicator H c) (missingIndicator H d) (iidLaw p H)) ≤
        variance (missingIndicator H c) (iidLaw p H) := by
    calc
      _ ≤ ∑ d : α, if c = d then variance (missingIndicator H c) (iidLaw p H) else 0 := by
        apply Finset.sum_le_sum
        intro d _
        by_cases hcd : c = d
        · subst d
          rw [ite_eq_left rfl, covariance_self (memLp_missingIndicator p H c).aemeasurable]
        · rw [ite_eq_right hcd]
          exact covariance_missingIndicator_nonpos p H c d hcd
      _ = _ := by simp
  calc
    _ ≤ ∑ c, variance (missingIndicator H c) (iidLaw p H) :=
      Finset.sum_le_sum fun c _ ↦ hrow c
    _ ≤ ∑ c, ∫ x, missingIndicator H c x ∂iidLaw p H :=
      Finset.sum_le_sum fun c _ ↦ variance_missingIndicator_le_integral p H c
    _ = _ := by
      unfold missingCount
      rw [integral_finsetSum]
      intro c _
      exact (memLp_missingIndicator p H c).integrable (by norm_num)

/-- The finite set of coupon labels absent from a sample. -/
noncomputable def missingCoupons (H : ℕ) (x : Fin H → α) : Finset α := by
  classical
  exact Finset.univ.filter fun c ↦ x ∈ missing H c

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The real missing-count variable is exactly the cardinality of the absent labels. -/
theorem missingCount_eq_card (H : ℕ) (x : Fin H → α) :
    missingCount H x = ((missingCoupons H x).card : ℝ) := by
  classical
  simp [missingCount, missingIndicator, missingCoupons, Set.indicator, Finset.sum_boole]

end TieredMatching.Coupon
