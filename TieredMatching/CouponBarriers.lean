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

public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Harmonic barriers for exact coupon moment recurrences

The functions bounded here satisfy explicit finite-set Bellman equations. Identifying them
with an actual coupon process is a separate stochastic theorem. The harmonic function is
Mathlib's rational-valued `harmonic`, cast to the reals.
-/

@[expose] public section

namespace TieredMatching.CouponBarriers

/-- The harmonic mean upper barrier for `r` remaining coupons. -/
noncomputable def meanBarrier (W : ℝ) (r : ℕ) : ℝ := W * (harmonic r : ℝ)

/-- Partial reciprocal-square correction in the second-moment barrier. -/
noncomputable def squareSum (r : ℕ) : ℝ := ∑ i ∈ Finset.range r, 1 / ((i : ℝ) + 1) ^ 2

/-- The second-moment barrier with its exact geometric-waiting correction. -/
noncomputable def secondBarrier (W : ℝ) (r : ℕ) : ℝ :=
  meanBarrier W r ^ 2 + W ^ 2 * squareSum r - meanBarrier W r

@[simp] theorem meanBarrier_zero (W : ℝ) : meanBarrier W 0 = 0 := by
  simp [meanBarrier]

@[simp] theorem squareSum_zero : squareSum 0 = 0 := by simp [squareSum]

@[simp] theorem secondBarrier_zero (W : ℝ) : secondBarrier W 0 = 0 := by
  simp [secondBarrier]

/-- Mathlib's harmonic successor identity, transported to the real mean barrier. -/
theorem meanBarrier_succ (W : ℝ) (r : ℕ) :
    meanBarrier W (r + 1) = meanBarrier W r + W / ((r : ℝ) + 1) := by
  simp only [meanBarrier, harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast,
    Nat.cast_add, Nat.cast_one, Rat.cast_one, mul_add, div_eq_mul_inv]

/-- The reciprocal-square correction gains exactly its next summand. -/
theorem squareSum_succ (r : ℕ) :
    squareSum (r + 1) = squareSum r + 1 / ((r : ℝ) + 1) ^ 2 := by
  exact Finset.sum_range_succ _ _

/-- The exact increment used to compare the second Bellman equation with the barrier. -/
theorem secondBarrier_succ (W : ℝ) (r : ℕ) :
    secondBarrier W (r + 1) = secondBarrier W r +
      (2 * meanBarrier W (r + 1) - 1) * (W / ((r : ℝ) + 1)) := by
  simp only [secondBarrier, meanBarrier_succ, squareSum_succ, div_eq_mul_inv, ← inv_pow, one_mul]
  ring

/-- Harmonic mean barriers are nonnegative for a nonnegative waiting scale. -/
theorem meanBarrier_nonneg {W : ℝ} (hW : 0 ≤ W) (r : ℕ) : 0 ≤ meanBarrier W r := by
  have hh : 0 ≤ harmonic r := by unfold harmonic; positivity
  exact mul_nonneg hW (Rat.cast_nonneg.mpr hh)

/-- When `r+1 <= W`, the next harmonic mean barrier is at least one. -/
theorem one_le_meanBarrier_succ {W : ℝ} (r : ℕ) (hcard : (r : ℝ) + 1 ≤ W) :
    1 ≤ meanBarrier W (r + 1) := by
  have hW : 0 ≤ W := by have hr := Nat.cast_nonneg (α := ℝ) r; linarith
  have hm := meanBarrier_nonneg hW r
  have hr : 1 ≤ W / ((r : ℝ) + 1) := by
    apply (le_div_iff₀ (by positivity : 0 < (r : ℝ) + 1)).2
    simpa using hcard
  rw [meanBarrier_succ]
  linarith

/-- The reciprocal-square tail is bounded by adjacent reciprocal differences. -/
theorem inverse_square_le_telescope {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ^ 2 ≤ 1 / x - 1 / (x + 1) := by
  have heq : 1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by
    field_simp
    ring
  rw [heq]
  exact one_div_le_one_div_of_le (mul_pos hx (by linarith)) (by nlinarith)

/-- A finite telescoping bound for the reciprocal-square correction. -/
theorem squareSum_succ_le (r : ℕ) : squareSum (r + 1) ≤ 2 - 1 / ((r : ℝ) + 1) := by
  induction r with
  | zero => norm_num [squareSum]
  | succ r ih =>
    rw [squareSum_succ]
    have hh := inverse_square_le_telescope (show 0 < (r : ℝ) + 1 by positivity)
    simp only [Nat.cast_add, Nat.cast_one] at *
    linarith

/-- Every finite reciprocal-square correction is at most two. -/
theorem squareSum_le_two (r : ℕ) : squareSum r ≤ 2 := by
  cases r with
  | zero => norm_num
  | succ r =>
    have hh := squareSum_succ_le r
    have hp : 0 ≤ 1 / ((r : ℝ) + 1) := by positivity
    linarith

/-- A pointwise coupon-mass lower bound gives the exact cardinal lower bound on unseen mass. -/
theorem delta_lower {α : Type*} (R : Finset α) (π : α → ℝ) {W : ℝ}
    (hπ : ∀ q ∈ R, 1 / W ≤ π q) : (R.card : ℝ) / W ≤ ∑ q ∈ R, π q := by
  calc
    (R.card : ℝ) / W = ∑ _q ∈ R, 1 / W := by simp [div_eq_mul_inv]
    _ ≤ ∑ q ∈ R, π q := Finset.sum_le_sum hπ

/-- Exact mean Bellman equations imply the harmonic upper barrier. No cardinal-scale
restriction or unproved stochastic interpretation is needed for this mean inequality. -/
theorem mean_le_barrier {α : Type*} [DecidableEq α] (π : α → ℝ)
    (M : Finset α → ℝ) {W : ℝ} (hW : 0 < W) (hπ : ∀ q, 1 / W ≤ π q)
    (hzero : M ∅ = 0)
    (hstep : ∀ R : Finset α, R.Nonempty →
      (∑ q ∈ R, π q) * M R = 1 + ∑ q ∈ R, π q * M (R.erase q))
    (R : Finset α) : M R ≤ meanBarrier W R.card := by
  refine Finset.strongInductionOn R ?_
  intro R ih
  by_cases hR : R = ∅
  · simp only [hR, hzero, Finset.card_empty, meanBarrier_zero, le_refl]
  · have hne := Finset.nonempty_iff_ne_empty.mpr hR
    obtain ⟨r, hr⟩ : ∃ r, R.card = r + 1 :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Finset.card_pos.mpr hne))
    have hr0 : 0 < (r : ℝ) + 1 := by positivity
    have hd : ((r : ℝ) + 1) / W ≤ ∑ q ∈ R, π q := by
      simpa only [hr, Nat.cast_add, Nat.cast_one] using delta_lower R π (fun q _ ↦ hπ q)
    have hd0 : 0 < ∑ q ∈ R, π q := (div_pos hr0 hW).trans_le hd
    have hincr : 1 ≤ (∑ q ∈ R, π q) * (W / ((r : ℝ) + 1)) := by
      have hh := mul_le_mul_of_nonneg_right hd (div_nonneg hW.le hr0.le)
      have heq : (((r : ℝ) + 1) / W) * (W / ((r : ℝ) + 1)) = 1 := by field_simp
      rwa [heq] at hh
    have hterms : (∑ q ∈ R, π q * M (R.erase q)) ≤
        (∑ q ∈ R, π q) * meanBarrier W r := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro q hq
      have hi := ih (R.erase q) (Finset.erase_ssubset hq)
      have he : (R.erase q).card = r := by
        have hh := Finset.card_erase_add_one hq
        omega
      rw [he] at hi
      exact mul_le_mul_of_nonneg_left hi ((div_nonneg zero_le_one hW.le).trans (hπ q))
    rw [hr, meanBarrier_succ]
    apply (mul_le_mul_iff_right₀ hd0).mp
    have he := hstep R hne
    nlinarith

/-- If all coupons in a target remaining set have mass exactly `1/W`, its exact Bellman
mean is the harmonic barrier. No condition is imposed on coupons outside that target. -/
theorem mean_eq_barrier_of_equal_mass_on {α : Type*} [DecidableEq α]
    (π : α → ℝ) (M : Finset α → ℝ) {W : ℝ} (hW : 0 < W)
    (hzero : M ∅ = 0)
    (hstep : ∀ R : Finset α, R.Nonempty →
      (∑ q ∈ R, π q) * M R = 1 + ∑ q ∈ R, π q * M (R.erase q))
    (R : Finset α) (hequal : ∀ q ∈ R, π q = 1 / W) : M R = meanBarrier W R.card := by
  revert hequal
  refine Finset.strongInductionOn R ?_
  intro R ih hequal
  by_cases hR : R = ∅
  · simp only [hR, hzero, Finset.card_empty, meanBarrier_zero]
  · have hne := Finset.nonempty_iff_ne_empty.mpr hR
    obtain ⟨r, hr⟩ : ∃ r, R.card = r + 1 :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Finset.card_pos.mpr hne))
    have hr0 : 0 < (r : ℝ) + 1 := by positivity
    have hd : (∑ q ∈ R, π q) = ((r : ℝ) + 1) / W := by
      rw [Finset.sum_congr rfl hequal]
      simp only [Finset.sum_const, nsmul_eq_mul, hr, Nat.cast_add, Nat.cast_one]
      ring
    have hd0 : 0 < ∑ q ∈ R, π q := by rw [hd]; exact div_pos hr0 hW
    have hincr : (∑ q ∈ R, π q) * (W / ((r : ℝ) + 1)) = 1 := by
      rw [hd]
      field_simp
    have hterms : (∑ q ∈ R, π q * M (R.erase q)) =
        (∑ q ∈ R, π q) * meanBarrier W r := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      have hi := ih (R.erase q) (Finset.erase_ssubset hq)
        (fun v hv ↦ hequal v (Finset.mem_of_mem_erase hv))
      have he : (R.erase q).card = r := by
        have hh := Finset.card_erase_add_one hq
        omega
      rw [he] at hi
      rw [hi]
    rw [hr, meanBarrier_succ]
    apply mul_left_cancel₀ hd0.ne'
    have he := hstep R hne
    rw [hterms] at he
    nlinarith

/-- Exact first/second Bellman equations imply the second harmonic barrier. The local
cardinality bound makes each nonempty-state geometric waiting cost at least one. -/
theorem secondMoment_le_barrier {α : Type*} [DecidableEq α] (π : α → ℝ)
    (M V : Finset α → ℝ) {W : ℝ} (hW : 0 < W) (hπ : ∀ q, 1 / W ≤ π q)
    (hMzero : M ∅ = 0)
    (hMstep : ∀ R : Finset α, R.Nonempty →
      (∑ q ∈ R, π q) * M R = 1 + ∑ q ∈ R, π q * M (R.erase q))
    (hVzero : V ∅ = 0)
    (hVstep : ∀ R : Finset α, R.Nonempty →
      (∑ q ∈ R, π q) * V R = 2 * M R - 1 + ∑ q ∈ R, π q * V (R.erase q))
    (R : Finset α) (hcard : (R.card : ℝ) ≤ W) : V R ≤ secondBarrier W R.card := by
  revert hcard
  refine Finset.strongInductionOn R ?_
  intro R ih hcard
  by_cases hR : R = ∅
  · simp only [hR, hVzero, Finset.card_empty, secondBarrier_zero, le_refl]
  · have hne := Finset.nonempty_iff_ne_empty.mpr hR
    obtain ⟨r, hr⟩ : ∃ r, R.card = r + 1 :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Finset.card_pos.mpr hne))
    have hr0 : 0 < (r : ℝ) + 1 := by positivity
    have hcardr : (r : ℝ) + 1 ≤ W := by simpa only [hr, Nat.cast_add, Nat.cast_one] using hcard
    have hd : ((r : ℝ) + 1) / W ≤ ∑ q ∈ R, π q := by
      simpa only [hr, Nat.cast_add, Nat.cast_one] using delta_lower R π (fun q _ ↦ hπ q)
    have hd0 : 0 < ∑ q ∈ R, π q := (div_pos hr0 hW).trans_le hd
    have hincr : 1 ≤ (∑ q ∈ R, π q) * (W / ((r : ℝ) + 1)) := by
      have hh := mul_le_mul_of_nonneg_right hd (div_nonneg hW.le hr0.le)
      have heq : (((r : ℝ) + 1) / W) * (W / ((r : ℝ) + 1)) = 1 := by field_simp
      rwa [heq] at hh
    have hcost : 0 ≤ 2 * meanBarrier W (r + 1) - 1 := by
      have hh := one_le_meanBarrier_succ r hcardr
      linarith
    have hwait := mul_le_mul_of_nonneg_left hincr hcost
    have hterms : (∑ q ∈ R, π q * V (R.erase q)) ≤
        (∑ q ∈ R, π q) * secondBarrier W r := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro q hq
      have he : (R.erase q).card = r := by
        have hh := Finset.card_erase_add_one hq
        omega
      have hc : ((R.erase q).card : ℝ) ≤ W := by
        rw [he]
        linarith
      have hi := ih (R.erase q) (Finset.erase_ssubset hq) hc
      rw [he] at hi
      exact mul_le_mul_of_nonneg_left hi ((div_nonneg zero_le_one hW.le).trans (hπ q))
    have hm := mean_le_barrier π M hW hπ hMzero hMstep R
    rw [hr] at hm
    rw [hr, secondBarrier_succ]
    apply (mul_le_mul_iff_right₀ hd0).mp
    have he := hVstep R hne
    nlinarith

/-- A simple second-moment bound follows from the telescoping reciprocal-square estimate. -/
theorem secondMoment_le_meanBarrier_sq_add_two_mul_sq
    {α : Type*} [DecidableEq α] (π : α → ℝ) (M V : Finset α → ℝ)
    {W : ℝ} (hW : 0 < W) (hπ : ∀ q, 1 / W ≤ π q)
    (hMzero : M ∅ = 0)
    (hMstep : ∀ R : Finset α, R.Nonempty →
      (∑ q ∈ R, π q) * M R = 1 + ∑ q ∈ R, π q * M (R.erase q))
    (hVzero : V ∅ = 0)
    (hVstep : ∀ R : Finset α, R.Nonempty →
      (∑ q ∈ R, π q) * V R = 2 * M R - 1 + ∑ q ∈ R, π q * V (R.erase q))
    (R : Finset α) (hcard : (R.card : ℝ) ≤ W) :
    V R ≤ meanBarrier W R.card ^ 2 + 2 * W ^ 2 := by
  have hv := secondMoment_le_barrier π M V hW hπ hMzero hMstep hVzero hVstep R hcard
  have hh := mul_le_mul_of_nonneg_left (squareSum_le_two R.card) (sq_nonneg W)
  have hm := meanBarrier_nonneg hW.le R.card
  unfold secondBarrier at hv
  nlinarith

/-- The harmonic barrier has Mathlib's usual logarithmic upper bound. -/
theorem meanBarrier_le_one_add_log {W : ℝ} (hW : 0 ≤ W) (r : ℕ) :
    meanBarrier W r ≤ W * (1 + Real.log r) :=
  mul_le_mul_of_nonneg_left (harmonic_le_one_add_log r) hW

end TieredMatching.CouponBarriers
