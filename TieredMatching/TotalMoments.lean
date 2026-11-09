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

public import TieredMatching.RepeatMoments
public import TieredMatching.RankTail
public import TieredMatching.G2Moments

/-! # Uniform total proposal moments under the original PR profile law

Fixed public score bounds determine all asymptotic constants before the population varies.
The actual raw clock, predictable repeats, and exact PR rank tail are combined without
additional stochastic premises.
-/

@[expose] public section

namespace TieredMatching.TotalMoments

open MeasureTheory ProbabilityTheory StableMarriage Filter
open ContinuationAsymptotics
open scoped ENNReal NNReal Topology

/-- A fixed polynomial-tail clock cutoff. -/
noncomputable def clockCap (A : ℝ) (n : ℕ) : ℕ := globalCap (5 * A) n

/-- Fixed rank-tail coefficient for the repeat mean correction. -/
noncomputable def rankConstant (A B : ℝ) : ℝ := RankTail.rankCoefficient A B 4

/-- The actual per-man genuine counter cutoff. -/
noncomputable def rankCap (A B : ℝ) (n : ℕ) : ℕ := threshold (rankConstant A B) n

/-- A uniform coefficient for the actual discarded-repeat mean. -/
noncomputable def repeatConstant (A B : ℝ) : ℝ :=
  (5 * A + 1) * A * (rankConstant A B + 1) + 1

/-- The original raw source law for the PR's two public score vectors. -/
noncomputable abbrev rawLaw {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0) :=
  rawInputLaw (fun _ ↦ a) (fun m _ ↦ b m)

/-- The actual raw coupon clock has the elementary exponential upper tail. -/
theorem clock_tail_le_exp {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    {A : ℝ} (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ))
    (haA : ∀ w, (a w : ℝ) ≤ A) (hb : ∀ m, 0 < b m) (H : ℕ) :
    (rawLaw a b).real {z | H < GlobalDraws.rawClock z} ≤
      n * Real.exp (-(H : ℝ) / (A * n)) := by
  have ha : ∀ w, 1 ≤ a w := fun w ↦ by exact_mod_cast ha1 w
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hW := CouponMoments.totalWeight_pos a
    (fun w ↦ lt_of_lt_of_le (by norm_num) (ha w))
  have hWA : CouponMoments.totalWeight a ≤ A * n := by
    simpa [mul_comm] using CouponMoments.totalWeight_le_card_mul a A haA
  have hAn : 0 < A * n := mul_pos (by linarith) hn
  have hlo (w : Fin n) : 1 / (A * n) ≤ (RandomRanking.ofWeights a w).toReal := by
    exact (div_le_div_of_nonneg_left zero_le_one hW hWA).trans
      (by simpa [one_div] using CouponMoments.ofWeights_real_ge_inv a ha w)
  rw [rawLaw, Measure.real, RepeatMoments.clock_tail_measure_eq_coupon a (fun m _ ↦ b m)
    (fun m _ ↦ hb m) H]
  apply (CouponMoments.time_tail_le_sum (RandomRanking.ofWeights a) H).trans
  calc
    _ ≤ ∑ _w : Fin n, Real.exp (-(H : ℝ) / (A * n)) := by
      apply Finset.sum_le_sum
      intro w _
      have hp1 : (RandomRanking.ofWeights a w).toReal ≤ 1 := by
        exact_mod_cast ENNReal.toReal_mono ENNReal.one_ne_top
          ((RandomRanking.ofWeights a).coe_le_one w)
      apply (EmptySurvival.geometric_le_exp hp1 H).trans
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left (hlo w) (Nat.cast_nonneg H : (0 : ℝ) ≤ H)
      simpa only [div_eq_mul_inv, one_div, neg_mul, one_mul] using neg_le_neg hm
    _ = _ := by simp

/-- The chosen actual raw clock cap has error at most n^-4. -/
theorem clock_cap_tail {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    {A : ℝ} (hA : 1 ≤ A) (hlog : 0 ≤ Real.log n)
    (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) :
    (rawLaw a b).real {z | clockCap A n < GlobalDraws.rawClock z} ≤ 1 / (n : ℝ) ^ 4 := by
  have hn : 0 < n := NeZero.pos n
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hexp := global_exp_le (by linarith : 0 < A) hn hlog
    (show A * (5 : ℝ) ≤ 5 * A by linarith)
  have ht := clock_tail_le_exp a b hA ha1 haA hb (clockCap A n)
  apply ht.trans
  have hm := mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have he5 : Real.exp (-(5 : ℝ) * Real.log n) = 1 / (n : ℝ) ^ 5 := by
    simpa using exp_neg_nat_log hn 5
  rw [he5] at hm
  dsimp only [clockCap]
  convert hm using 1
  field_simp

/-- The raw terminal rank-cap error inherits the exact original PR maximum-rank tail. -/
theorem eventually_rank_cap_tail {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ [NeZero n] (a b : Fin n → ℝ≥0),
      (∀ w, 1 ≤ (a w : ℝ)) → (∀ w, (a w : ℝ) ≤ A) →
      (∀ m, 1 ≤ (b m : ℝ)) → (∀ m, (b m : ℝ) ≤ B) →
      (rawLaw a b).real (RepeatMoments.RankCap (rankCap A B n))ᶜ ≤ 5 / (n : ℝ) ^ 4 := by
  filter_upwards [RankTail.eventually_max_rank_tail hA hB (by norm_num : (0 : ℝ) ≤ 4)]
    with n ht _ a b ha1 haA hb1 hbB
  have ha : ∀ w, 0 < a w := fun w ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (ha1 w)
  have hb : ∀ m, 0 < b m := fun m ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (hb1 m)
  rw [rawLaw, RepeatMoments.rankCap_compl_real_eq_profile a (fun m _ ↦ b m) ha
    (fun m _ ↦ hb m)]
  have hm := RankTail.probability_mono (VisitBounds.profileLaw a b)
    (E := {p | ∃ m, rankCap A B n < (deferredAcceptance p).next m})
    (F := {p | ∃ m, rankCap A B n ≤ (deferredAcceptance p).next m}) (by
      rintro p ⟨m, hm⟩
      exact ⟨m, hm.le⟩)
  rw [← FiniteConditioning.eventMass_eq_toMeasure _ _ (by trivial)]
  have hr : (n : ℝ) ^ (-(4 : ℝ)) = 1 / (n : ℝ) ^ 4 := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), show (4 : ℝ) = (4 : ℕ) by norm_num,
      Real.rpow_natCast, one_div]
  exact hm.trans (by simpa only [rankCap, rankConstant, RankTail.rank, hr, div_eq_mul_inv,
    SurvivalKernel.probability, one_mul] using (ht a b ha1 haA hb1 hbB))

/-- The actual coupon second moment gives a uniform square-root bound on the log scale. -/
theorem clock_second_sqrt_le {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    {A : ℝ} (hA : 1 ≤ A) (hlog : 1 ≤ Real.log n)
    (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) :
    Real.sqrt (∫ z, (GlobalDraws.rawClock z : ℝ) ^ 2 ∂rawLaw a b) ≤
      3 * A * n * Real.log n := by
  have ha : ∀ w, 1 ≤ a w := fun w ↦ by exact_mod_cast ha1 w
  have hW0 : 0 ≤ CouponMoments.totalWeight a := by unfold CouponMoments.totalWeight; positivity
  have hWA : CouponMoments.totalWeight a ≤ A * n := by
    simpa [mul_comm] using CouponMoments.totalWeight_le_card_mul a A haA
  have hH0 : 0 ≤ (harmonic n : ℝ) := by
    have hh : (0 : ℚ) ≤ harmonic n := by unfold harmonic; positivity
    exact_mod_cast hh
  have hH : (harmonic n : ℝ) ≤ 2 * Real.log n :=
    (harmonic_le_one_add_log _).trans (by linarith)
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hm := GlobalDraws.rawClock_secondMoment_le a (fun m _ ↦ b m) ha (fun m _ ↦ hb m)
  apply hm.trans
  have hh : (CouponMoments.totalWeight a * (harmonic n : ℝ)) ^ 2 ≤
      (A * n * (2 * Real.log n)) ^ 2 := by
    gcongr
  have hw : CouponMoments.totalWeight a ^ 2 ≤ (A * n) ^ 2 := by gcongr
  have hL : 1 ≤ (Real.log n) ^ 2 := by nlinarith
  have hsq : 0 ≤ (A * (n : ℝ)) ^ 2 := sq_nonneg _
  nlinarith

/-- Rounding the fixed caps costs only fixed multiplicative constants on the log scale. -/
theorem capped_mean_term_le {n : ℕ} [NeZero n] {A D : ℝ}
    (hA : 1 ≤ A) (hD : 0 ≤ D) (hlog : 1 ≤ Real.log n) :
    (globalCap (5 * A) n : ℝ) * A * threshold D n / n ≤
      ((5 * A + 1) * A * (D + 1)) * (Real.log n) ^ 3 := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.pos n
  have hnc : (n : ℝ) ≠ 0 := by linarith
  have hh := Nat.ceil_lt_add_one (by positivity : 0 ≤ 5 * A * n * Real.log n)
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ D * (Real.log n) ^ 2)
  have hH : (globalCap (5 * A) n : ℝ) ≤ (5 * A + 1) * n * Real.log n := by
    dsimp only [globalCap]
    nlinarith
  have hC : (threshold D n : ℝ) ≤ (D + 1) * (Real.log n) ^ 2 := by
    dsimp only [threshold]
    nlinarith
  calc
    _ ≤ ((5 * A + 1) * n * Real.log n) * A * ((D + 1) * (Real.log n) ^ 2) / n := by
      gcongr
    _ = _ := by field_simp

/-- The combined actual cap-error correction is eventually at most one. -/
theorem cap_correction_le_one {n : ℕ} [NeZero n] {A : ℝ}
    (hA : 1 ≤ A) (hlog : 1 ≤ Real.log n) (hsmall : 9 * A * Real.log n ≤ n)
    {M δ : ℝ} (hM : Real.sqrt M ≤ 3 * A * n * Real.log n) (hδ : δ ≤ 6 / (n : ℝ) ^ 4) :
    Real.sqrt M * Real.sqrt δ ≤ 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn0 := hn.ne'
  have hs : Real.sqrt δ ≤ 3 / (n : ℝ) ^ 2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, hδ.trans ?_⟩
    apply (div_le_div_of_nonneg_right (by norm_num : (6 : ℝ) ≤ 9)
      (pow_nonneg hn.le 4)).trans_eq
    field_simp
    ring
  calc
    _ ≤ (3 * A * n * Real.log n) * (3 / (n : ℝ) ^ 2) :=
      mul_le_mul hM hs (Real.sqrt_nonneg _) (by positivity)
    _ = 9 * A * Real.log n / n := by field_simp; ring
    _ ≤ 1 := (div_le_one hn).mpr hsmall

/-- Uniform discarded repeats are O(log cubed), with constants fixed before n and scores. -/
theorem eventually_repeat_mean_le {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ [NeZero n] (a b : Fin n → ℝ≥0),
      (∀ w, 1 ≤ (a w : ℝ)) → (∀ w, (a w : ℝ) ≤ A) →
      (∀ m, 1 ≤ (b m : ℝ)) → (∀ m, (b m : ℝ) ≤ B) →
      (∫ z, (GlobalDraws.rawClock z : ℝ) - (numProposals (RawBridge.sourceProfile z) : ℝ)
        ∂rawLaw a b) ≤ repeatConstant A B * (Real.log n) ^ 3 := by
  have hAp : 0 < A := by linarith
  filter_upwards [eventually_rank_cap_tail hA hB, eventually_one_le_log,
    eventually_log_sq_le (by positivity : 0 < 1 / (9 * A))] with n hr hlog hsmall
  intro _ a b ha1 haA hb1 hbB
  have hb : ∀ m, 0 < b m := fun m ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (hb1 m)
  have hD := RankTail.rankCoefficient_pos hA hB (by norm_num : (0 : ℝ) ≤ 4)
  have ht := RepeatMoments.integral_difference_le a (fun m _ ↦ b m) (fun m _ ↦ hb m)
    hAp.le ha1 haA (rankCap A B n) (clockCap A n)
  have hδ : (rawLaw a b).real {z | clockCap A n < GlobalDraws.rawClock z} +
      (rawLaw a b).real (RepeatMoments.RankCap (rankCap A B n))ᶜ ≤ 6 / (n : ℝ) ^ 4 := by
    have h1 := clock_cap_tail a b hA (by linarith) ha1 haA hb
    have h2 := hr a b ha1 haA hb1 hbB
    calc
      _ ≤ 1 / (n : ℝ) ^ 4 + 5 / (n : ℝ) ^ 4 := add_le_add h1 h2
      _ = _ := by ring
  have hsmall' : 9 * A * Real.log n ≤ n := by
    have hl : Real.log n ≤ (Real.log n) ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ 9 * A)
    have he : 9 * A * (1 / (9 * A) * n) = (n : ℝ) := by field_simp
    rw [he] at hm
    nlinarith
  have hc := cap_correction_le_one hA hlog hsmall'
    (clock_second_sqrt_le a b hA hlog ha1 haA hb) hδ
  have hcap := capped_mean_term_le hA hD.le hlog
  have hL : 1 ≤ (Real.log n) ^ 3 := one_le_pow₀ hlog
  change _ ≤ _ at ht
  change _ ≤ _ at hcap
  dsimp only [clockCap, rankCap, rankConstant, rawLaw] at ht hc hcap ⊢
  dsimp only [repeatConstant, rankConstant]
  nlinarith

/-- Fixed loss from a positive fraction of minimum-score women. -/
noncomputable def minimumConstant (ρ : ℝ) : ℝ := 1 + |Real.log ρ|

/-- Actual raw mean bounds retain the exact total-weight coefficient. -/
theorem clock_mean_sandwich {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (hb : ∀ m, 0 < b m)
    {ρ : ℝ} (hρ : 0 < ρ) (hmin : ρ * n ≤ (CouponMoments.minimumCoupons a).card) :
    let W := CouponMoments.totalWeight a
    let M := ∫ z, (GlobalDraws.rawClock z : ℝ) ∂rawLaw a b
    0 ≤ M ∧ M ≤ W * (1 + Real.log n) ∧ W * (Real.log ρ + Real.log n) ≤ M := by
  dsimp only
  have ha : ∀ w, 1 ≤ a w := fun w ↦ by exact_mod_cast ha1 w
  have hap : ∀ w, 0 < a w := fun w ↦ lt_of_lt_of_le (by norm_num) (ha w)
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hW := (CouponMoments.totalWeight_pos a hap).le
  refine ⟨integral_nonneg (fun z ↦ Nat.cast_nonneg _), ?_, ?_⟩
  · rw [rawLaw, GlobalDraws.rawClock_integral_eq a _ (fun m _ ↦ hb m)]
    simpa using CouponMoments.mean_time_le_log a ha
  · have hl : Real.log ρ + Real.log n ≤
        Real.log ((CouponMoments.minimumCoupons a).card + 1 : ℕ) := by
      rw [← Real.log_mul hρ.ne' hn.ne']
      apply Real.log_le_log (mul_pos hρ hn)
      exact hmin.trans (by simp)
    have hlow := CouponMoments.log_le_mean_time a hap (CouponMoments.minimumCoupons a).card
      le_rfl
    rw [← GlobalDraws.rawClock_integral_eq a (fun m _ ↦ b m) (fun m _ ↦ hb m)
      (fun k ↦ (k : ℝ))] at hlow
    exact (mul_le_mul_of_nonneg_left hl hW).trans hlow

/-- Actual raw mean differs from W log n by at most a fixed linear error. -/
theorem clock_mean_abs_sub_le {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    {A ρ : ℝ} (ha1 : ∀ w, 1 ≤ (a w : ℝ))
    (haA : ∀ w, (a w : ℝ) ≤ A) (hb : ∀ m, 0 < b m)
    (hρ : 0 < ρ) (hmin : ρ * n ≤ (CouponMoments.minimumCoupons a).card) :
    |(∫ z, (GlobalDraws.rawClock z : ℝ) ∂rawLaw a b) -
      CouponMoments.totalWeight a * Real.log n| ≤ A * minimumConstant ρ * n := by
  have hs := clock_mean_sandwich a b ha1 hb hρ hmin
  dsimp only at hs
  have hW0 : 0 ≤ CouponMoments.totalWeight a := by unfold CouponMoments.totalWeight; positivity
  have hWA : CouponMoments.totalWeight a ≤ A * n := by
    simpa [mul_comm] using CouponMoments.totalWeight_le_card_mul a A haA
  have hlow := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log ρ)) hW0
  have hc : 0 ≤ minimumConstant ρ := by unfold minimumConstant; positivity
  apply (abs_le.mpr ⟨?_, ?_⟩).trans
    (show CouponMoments.totalWeight a * minimumConstant ρ ≤ A * minimumConstant ρ * n by
      nlinarith [mul_le_mul_of_nonneg_right hWA hc])
  · dsimp only [minimumConstant]
    nlinarith
  · dsimp only [minimumConstant]
    nlinarith [abs_nonneg (Real.log ρ)]

/-- Actual raw variance is O(n squared log n) under only a positive minimum-score fraction. -/
theorem clock_variance_le {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    {A ρ : ℝ} (hlog : 1 ≤ Real.log n)
    (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (hρ : 0 < ρ)
    (hmin : ρ * n ≤ (CouponMoments.minimumCoupons a).card) :
    variance (fun z ↦ (GlobalDraws.rawClock z : ℝ)) (rawLaw a b) ≤
      (2 + 4 * minimumConstant ρ) * A ^ 2 * (n : ℝ) ^ 2 * Real.log n := by
  have ha : ∀ w, 1 ≤ a w := fun w ↦ by exact_mod_cast ha1 w
  have hap : ∀ w, 0 < a w := fun w ↦ lt_of_lt_of_le (by norm_num) (ha w)
  have := Raw.isProbabilityMeasure_rawInputLaw (fun _ ↦ a) (fun m _ ↦ b m) (fun m _ ↦ hb m)
  let W := CouponMoments.totalWeight a
  let U := W * (harmonic n : ℝ)
  let M := ∫ z, (GlobalDraws.rawClock z : ℝ) ∂rawLaw a b
  let c := minimumConstant ρ
  have hW : 0 ≤ W := (CouponMoments.totalWeight_pos a hap).le
  have hWA : W ≤ A * n := by
    simpa [W, mul_comm] using CouponMoments.totalWeight_le_card_mul a A haA
  have hc : 1 ≤ c := by dsimp [c, minimumConstant]; linarith [abs_nonneg (Real.log ρ)]
  have hs := clock_mean_sandwich a b ha1 hb hρ hmin
  change 0 ≤ M ∧ M ≤ W * (1 + Real.log n) ∧ W * (Real.log ρ + Real.log n) ≤ M at hs
  have hMU : M ≤ U := (GlobalDraws.rawClock_mean_bounds a (fun m _ ↦ b m) ha
    (fun m _ ↦ hb m) 0 (Nat.zero_le _)).2
  have hU : U ≤ W * (1 + Real.log n) :=
    mul_le_mul_of_nonneg_left (harmonic_le_one_add_log _) hW
  have hgap : U - M ≤ W * c := by
    have hn := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log ρ)) hW
    dsimp only [c, minimumConstant]
    nlinarith [hs.2.2]
  have hsum : U + M ≤ 2 * W * (1 + Real.log n) := by linarith [hs.2.1]
  have hprod := mul_le_mul hgap hsum (by linarith : 0 ≤ U + M) (mul_nonneg hW (by linarith))
  have hm2 := GlobalDraws.rawClock_secondMoment_le a (fun m _ ↦ b m) ha (fun m _ ↦ hb m)
  unfold rawLaw
  rw [variance_eq_sub (GlobalDraws.rawClock_memLp a (fun m _ ↦ b m) hap (fun m _ ↦ hb m))]
  simp only [Pi.pow_apply]
  have hv : (∫ z, (GlobalDraws.rawClock z : ℝ) ^ 2 ∂rawLaw a b) - M ^ 2 ≤
      (2 + 4 * c) * W ^ 2 * Real.log n := by
    change (∫ z, (GlobalDraws.rawClock z : ℝ) ^ 2 ∂rawLaw a b) ≤ U ^ 2 + 2 * W ^ 2 at hm2
    have hn : 0 ≤ 2 * W ^ 2 * (1 + c) * (Real.log n - 1) := by positivity
    nlinarith
  apply hv.trans
  have hw : W ^ 2 ≤ (A * n) ^ 2 := by gcongr
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 2 + 4 * c)) (by linarith : 0 ≤ Real.log n)
  convert hm using 1
  ring

/-- Exact original-profile proposal totals are L2 under the actual raw source law. -/
theorem ordinary_memLp {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) :
    MemLp (fun z ↦ (numProposals (RawBridge.sourceProfile z) : ℝ)) 2 (rawLaw a b) := by
  apply (GlobalDraws.rawClock_memLp a (fun m _ ↦ b m) ha (fun m _ ↦ hb m)).mono'
    (((measurable_of_countable (fun p : Profile n ↦ (numProposals p : ℝ))).comp
      RepeatMoments.measurable_sourceProfile).aestronglyMeasurable)
  filter_upwards [GlobalDraws.ae_rawClock_decomposition a (fun m _ ↦ b m) ha
    (fun m _ ↦ hb m)] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  change (numProposals (RawBridge.sourceProfile z) : ℝ) ≤ (GlobalDraws.rawClock z : ℝ)
  exact_mod_cast (show numProposals (RawBridge.sourceProfile z) ≤ GlobalDraws.rawClock z by omega)

/-- The ordinary/raw variance comparison remains valid for an almost-sure deletion coupling. -/
theorem variance_le_of_ae_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S T : Ω → ℝ)
    (hS : MemLp S 2 μ) (hT : MemLp T 2 μ) (hS0 : ∀ ω, 0 ≤ S ω)
    (hST : ∀ᵐ ω ∂μ, S ω ≤ T ω) :
    variance S μ ≤ variance T μ +
      2 * (∫ ω, T ω ∂μ) * (∫ ω, T ω - S ω ∂μ) := by
  have hp : (∫ ω, S ω * S ω ∂μ) ≤ ∫ ω, T ω * T ω ∂μ := by
    apply integral_mono_ae (hS.integrable_mul hS) (hT.integrable_mul hT)
    filter_upwards [hST] with ω hω
    exact mul_le_mul hω hω (hS0 ω) ((hS0 ω).trans hω)
  rw [integral_sub (hT.integrable one_le_two) (hS.integrable one_le_two),
    variance_eq_sub hS, variance_eq_sub hT]
  simp only [Pi.pow_apply, pow_two] at *
  nlinarith [sq_nonneg ((∫ ω, T ω ∂μ) - ∫ ω, S ω ∂μ)]

/-- Fixed coefficient for the exact PR total mean error. -/
noncomputable def meanConstant (A B ρ : ℝ) : ℝ :=
  A * minimumConstant ρ + repeatConstant A B

/-- Fixed coefficient for the exact PR total variance. -/
noncomputable def varianceConstant (A B ρ : ℝ) : ℝ :=
  (2 + 4 * minimumConstant ρ) * A ^ 2 + 4 * A * repeatConstant A B

/-- All moment coefficients are positive for fixed admissible public score bounds. -/
theorem constants_pos {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (ρ : ℝ) :
    0 < repeatConstant A B ∧ 0 < meanConstant A B ρ ∧ 0 < varianceConstant A B ρ := by
  have hD := RankTail.rankCoefficient_pos hA hB (by norm_num : (0 : ℝ) ≤ 4)
  have hA0 : 0 < A := by linarith
  dsimp [repeatConstant, meanConstant, varianceConstant, minimumConstant, rankConstant]
  exact ⟨by positivity, by positivity, by positivity⟩

/-- Actual source-space ordinary moments follow from the already controlled repeat mean. -/
theorem ordinary_moments_of_repeat_bound {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    {A B ρ : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hρ : 0 < ρ)
    (hlog : 1 ≤ Real.log n) (hlog3 : (Real.log n) ^ 3 ≤ n)
    (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (hmin : ρ * n ≤ (CouponMoments.minimumCoupons a).card)
    (hrepeat : (∫ z, (GlobalDraws.rawClock z : ℝ) -
      (numProposals (RawBridge.sourceProfile z) : ℝ) ∂rawLaw a b) ≤
        repeatConstant A B * (Real.log n) ^ 3) :
    |(∫ z, (numProposals (RawBridge.sourceProfile z) : ℝ) ∂rawLaw a b) -
      CouponMoments.totalWeight a * Real.log n| ≤ meanConstant A B ρ * n ∧
    variance (fun z ↦ (numProposals (RawBridge.sourceProfile z) : ℝ)) (rawLaw a b) ≤
      varianceConstant A B ρ * (n : ℝ) ^ 2 * Real.log n := by
  have ha : ∀ w, 0 < a w := fun w ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (ha1 w)
  have hprob : IsProbabilityMeasure (rawLaw a b) :=
    Raw.isProbabilityMeasure_rawInputLaw (fun _ ↦ a) (fun m _ ↦ b m) (fun m _ ↦ hb m)
  have hS := ordinary_memLp a b ha hb
  have hT := GlobalDraws.rawClock_memLp a (fun m _ ↦ b m) ha (fun m _ ↦ hb m)
  have hST : ∀ᵐ z ∂rawLaw a b,
      (numProposals (RawBridge.sourceProfile z) : ℝ) ≤ (GlobalDraws.rawClock z : ℝ) := by
    filter_upwards [GlobalDraws.ae_rawClock_decomposition a (fun m _ ↦ b m) ha
      (fun m _ ↦ hb m)] with z hz
    exact_mod_cast (show numProposals (RawBridge.sourceProfile z) ≤ GlobalDraws.rawClock z by omega)
  have hR0 : 0 ≤ ∫ z, (GlobalDraws.rawClock z : ℝ) -
      (numProposals (RawBridge.sourceProfile z) : ℝ) ∂rawLaw a b :=
    integral_nonneg_of_ae (hST.mono fun z hz ↦ sub_nonneg.mpr hz)
  have hRC := (constants_pos hA hB ρ).1
  have hrepeatn := hrepeat.trans (mul_le_mul_of_nonneg_left hlog3 hRC.le)
  have hdiff := integral_sub (hT.integrable one_le_two) (hS.integrable one_le_two)
  have hmean := clock_mean_abs_sub_le a b ha1 haA hb hρ hmin
  dsimp only [rawLaw] at *
  constructor
  · rw [abs_le] at hmean ⊢
    dsimp only [meanConstant]
    constructor <;> nlinarith
  · have hv := variance_le_of_ae_le (rawLaw a b) _ _ hS hT (fun z ↦ Nat.cast_nonneg _) hST
    have hvT := clock_variance_le a b hlog ha1 haA hb hρ hmin
    have hs := clock_mean_sandwich a b ha1 hb hρ hmin
    dsimp only at hs
    have hWA : CouponMoments.totalWeight a ≤ A * n := by
      simpa [mul_comm] using CouponMoments.totalWeight_le_card_mul a A haA
    have hM : (∫ z, (GlobalDraws.rawClock z : ℝ) ∂rawLaw a b) ≤
        2 * A * n * Real.log n := by
      apply hs.2.1.trans
      calc
        _ ≤ A * n * (1 + Real.log n) := by gcongr
        _ ≤ _ := by
          have hm := mul_le_mul_of_nonneg_left (by linarith : 1 + Real.log n ≤ 2 * Real.log n)
            (by positivity : 0 ≤ A * n)
          simpa only [mul_assoc, mul_left_comm, mul_comm] using hm
    dsimp only [rawLaw] at *
    have hprod := mul_le_mul hM hrepeat hR0 (by positivity : 0 ≤ 2 * A * n * Real.log n)
    have hcor : 2 * (∫ z, (GlobalDraws.rawClock z : ℝ) ∂rawLaw a b) *
        (∫ z, (GlobalDraws.rawClock z : ℝ) - (numProposals (RawBridge.sourceProfile z) : ℝ)
          ∂rawLaw a b) ≤ 4 * A * repeatConstant A B * (n : ℝ) ^ 2 * Real.log n := by
      have hm := mul_le_mul_of_nonneg_left hlog3
        (by positivity : 0 ≤ 4 * A * repeatConstant A B * n * Real.log n)
      nlinarith
    dsimp only [varianceConstant]
    nlinarith

/-- The original profile projection preserves the unchanged PR market law. -/
theorem profile_measurePreserving {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) :
    MeasurePreserving RawBridge.sourceProfile (rawLaw a b) (VisitBounds.profileLaw a b).toMeasure :=
  ⟨RepeatMoments.measurable_sourceProfile,
    iid_raw_profile_law (fun _ ↦ a) (fun m _ ↦ b m) (fun _ ↦ ha) (fun m _ ↦ hb m)⟩

/-- Exact total means transport to the original finite PR profile probability space. -/
theorem ordinary_mean_eq_profile {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) :
    (∫ z, (numProposals (RawBridge.sourceProfile z) : ℝ) ∂rawLaw a b) =
      ∫ p, (numProposals p : ℝ) ∂(VisitBounds.profileLaw a b).toMeasure := by
  have hp := profile_measurePreserving a b ha hb
  have hf : Measurable (fun p : Profile n ↦ (numProposals p : ℝ)) := measurable_of_countable _
  rw [← integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable, hp.map_eq]

/-- Exact total variances transport to the original finite PR profile probability space. -/
theorem ordinary_variance_eq_profile {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) :
    variance (fun z ↦ (numProposals (RawBridge.sourceProfile z) : ℝ)) (rawLaw a b) =
      variance (fun p ↦ (numProposals p : ℝ)) (VisitBounds.profileLaw a b).toMeasure := by
  have hf : Measurable (fun p : Profile n ↦ (numProposals p : ℝ)) := measurable_of_countable _
  exact (profile_measurePreserving a b ha hb).variance_fun_comp
    (f := fun p : Profile n ↦ (numProposals p : ℝ)) hf.aemeasurable

/-- Uniform actual PR total mean and variance, with all constants fixed before population size. -/
theorem eventually_uniform_total_moments {A B ρ : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hρ : 0 < ρ) :
    ∀ᶠ n : ℕ in atTop, ∀ [NeZero n] (a b : Fin n → ℝ≥0),
      (∀ w, 1 ≤ (a w : ℝ)) → (∀ w, (a w : ℝ) ≤ A) →
      (∀ m, 1 ≤ (b m : ℝ)) → (∀ m, (b m : ℝ) ≤ B) →
      ρ * n ≤ (CouponMoments.minimumCoupons a).card →
      |(∫ p, (numProposals p : ℝ) ∂(VisitBounds.profileLaw a b).toMeasure) -
        CouponMoments.totalWeight a * Real.log n| ≤ meanConstant A B ρ * n ∧
      variance (fun p ↦ (numProposals p : ℝ)) (VisitBounds.profileLaw a b).toMeasure ≤
        varianceConstant A B ρ * (n : ℝ) ^ 2 * Real.log n := by
  have hlog3 := (Real.isLittleO_pow_log_id_atTop (n := 3)).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  filter_upwards [eventually_repeat_mean_le hA hB, eventually_one_le_log,
    hlog3.def zero_lt_one] with n hrepeat hlog hsmall
  intro _ a b ha1 haA hb1 hbB hmin
  have ha : ∀ w, 0 < a w := fun w ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (ha1 w)
  have hb : ∀ m, 0 < b m := fun m ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (hb1 m)
  have hL3 : (Real.log n) ^ 3 ≤ n := by
    simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs, one_mul,
      abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ Real.log n) _),
      abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using hsmall
  have hs := ordinary_moments_of_repeat_bound a b hA hB hρ hlog hL3 ha1 haA hb hmin
    (hrepeat a b ha1 haA hb1 hbB)
  rwa [ordinary_mean_eq_profile a b ha hb, ordinary_variance_eq_profile a b ha hb] at hs

end TieredMatching.TotalMoments
