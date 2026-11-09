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

public import Ashlagi.DestinationMartingale
public import Ashlagi.LabelSymmetry
public import Ashlagi.TotalMoments
public import Ashlagi.TierConcentration
public import Ashlagi.CouponLowerTail
public import Ashlagi.Transfer
public import Ashlagi.ProposalCounts
public import Ashlagi.G2Numerics
public import Ashlagi.G2Coefficients
public import Ashlagi.GlobalPairMoments
public import Ashlagi.G2Scaling

/-! # Fixed-woman proposal concentration from the exact raw process -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Ashlagi.G2Assembly

/-- The leading fixed-woman coefficient for an arbitrary proposer subset. -/
noncomputable def center {n : ℕ} (a b : Fin n → ℝ≥0) (J : Finset (Fin n))
    (w : Fin n) : ℝ := (a w : ℝ) * TierConcentration.share b J * Real.log n

/-- Multiplication by the exact categorical mass cancels the total public weight. -/
theorem destination_mul_target {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (J : Finset (Fin n)) (w : Fin n) :
    DestinationMartingale.destinationProbability a w * TierConcentration.target a b J =
      center a b J w := by
  have hw := CouponMoments.ofWeights_weighted_mass a ha w
  change CouponMoments.totalWeight a * DestinationMartingale.destinationProbability a w =
    (a w : ℝ) at hw
  unfold TierConcentration.target center
  calc
    _ = (CouponMoments.totalWeight a * DestinationMartingale.destinationProbability a w) *
      TierConcentration.share b J * Real.log n := by ring
    _ = _ := by rw [hw]

/-- A positive tier share gives a uniform logarithmic lower center at every woman. -/
theorem center_lower {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (J : Finset (Fin n)) (w : Fin n) {B ρ : ℝ} (hB : 0 < B) (hρ : 0 ≤ ρ)
    (ha1 : ∀ v, 1 ≤ (a v : ℝ)) (hb1 : ∀ m, 1 ≤ (b m : ℝ))
    (hbB : ∀ m, (b m : ℝ) ≤ B) (hcard : ρ * n ≤ J.card)
    (hlog : 0 ≤ Real.log n) : (ρ / B) * Real.log n ≤ center a b J w := by
  have hs := TierConcentration.share_lower b J hB hρ hb1 hbB hcard
  have hbs : 0 ≤ TierConcentration.share b J :=
    (div_nonneg hρ hB.le).trans hs
  unfold center
  apply mul_le_mul_of_nonneg_right _ hlog
  exact hs.trans (by nlinarith [ha1 w])

/-- The local and global repeat corrections in the raw destination-counting comparison. -/
noncomputable def repeatNoise {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0) (w : Fin n)
    (z : Raw.Sources n) : ℝ :=
  (LabelSymmetry.repeatAtWoman z w : ℝ) +
    (RandomRanking.ofWeights a w).toReal * (RepeatMoments.totalRepeats z : ℝ)

/-- Both repeat corrections are nonnegative. -/
theorem repeatNoise_nonneg {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0) (w : Fin n)
    (z : Raw.Sources n) : 0 ≤ repeatNoise a w z := by
  exact add_nonneg (Nat.cast_nonneg _) (mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _))

/-- The actual repeat correction is square integrable under the original raw law. -/
theorem repeatNoise_memLp {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (w : Fin n) :
    MemLp (repeatNoise a w) 2 (TotalMoments.rawLaw a b) :=
  (LabelSymmetry.repeatAtWoman_memLp a b ha hb w).add
    ((RepeatMoments.totalRepeats_memLp a (fun m _ ↦ b m) ha
      (fun m _ ↦ hb m)).const_mul _)

/-- Within a common-score class, the repeat correction is bounded by the total repeat mean. -/
theorem repeatNoise_mean_le {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (T : Finset (Fin n))
    (w : Fin n) (hw : w ∈ T) (hT : ∀ v ∈ T, a v = a w) :
    (∫ z, repeatNoise a w z ∂TotalMoments.rawLaw a b) ≤
      (1 / T.card + (RandomRanking.ofWeights a w).toReal) *
        ∫ z, (RepeatMoments.totalRepeats z : ℝ) ∂TotalMoments.rawLaw a b := by
  have := Raw.isProbabilityMeasure_rawInputLaw (fun _ ↦ a) (fun m _ ↦ b m)
    (fun m _ ↦ hb m)
  have : IsProbabilityMeasure (LabelSymmetry.sourceLaw a b) :=
    Raw.isProbabilityMeasure_rawInputLaw (fun _ ↦ a) (fun m _ ↦ b m) (fun m _ ↦ hb m)
  have hiw : Integrable (fun z ↦ (LabelSymmetry.repeatAtWoman z w : ℝ))
      (TotalMoments.rawLaw a b) :=
    (LabelSymmetry.repeatAtWoman_memLp a b ha hb w).integrable one_le_two
  have hir : Integrable (fun z ↦ (RepeatMoments.totalRepeats z : ℝ))
      (TotalMoments.rawLaw a b) :=
    (RepeatMoments.totalRepeats_memLp a (fun m _ ↦ b m) ha
      (fun m _ ↦ hb m)).integrable one_le_two
  have hmean : (∫ z, (LabelSymmetry.repeatAtWoman z w : ℝ) ∂TotalMoments.rawLaw a b) ≤
      (∫ z, (RepeatMoments.totalRepeats z : ℝ) ∂TotalMoments.rawLaw a b) / T.card :=
    LabelSymmetry.integral_repeatAtWoman_le_total_div_tier a b ha hb T w hw hT
  unfold repeatNoise
  rw [integral_add hiw (hir.const_mul _), integral_const_mul]
  calc
    _ ≤ (∫ z, (RepeatMoments.totalRepeats z : ℝ) ∂TotalMoments.rawLaw a b) / T.card +
        (RandomRanking.ofWeights a w).toReal *
          ∫ z, (RepeatMoments.totalRepeats z : ℝ) ∂TotalMoments.rawLaw a b :=
      add_le_add hmean le_rfl
    _ = _ := by ring

/-- Every fixed positive power of log is eventually below a fixed positive population power. -/
theorem eventually_log_power_le {c s : ℝ} (hc : 0 < c) (hs : 0 < s) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, (Real.log n) ^ k ≤ c * (n : ℝ) ^ s := by
  have hh := (isLittleO_log_rpow_rpow_atTop (s := s) (k : ℝ) hs).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  filter_upwards [hh.def hc, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  simpa only [Function.comp_apply, Real.rpow_natCast, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hlog k),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s)] using hn

/-- A linear-size equal-score class makes the expected repeat correction negligible. -/
theorem repeatNoise_mean_le_of_bounds {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (T : Finset (Fin n))
    (w : Fin n) (hw : w ∈ T) (hT : ∀ v ∈ T, a v = a w)
    {ρ A M : ℝ} (hρ : 0 < ρ) (hA : 0 ≤ A)
    (hcard : ρ * n ≤ (T.card : ℝ))
    (hq : (RandomRanking.ofWeights a w).toReal ≤ A / n)
    (hM : (∫ z, (RepeatMoments.totalRepeats z : ℝ) ∂TotalMoments.rawLaw a b) ≤ M) :
    (∫ z, repeatNoise a w z ∂TotalMoments.rawLaw a b) ≤
      ((1 / ρ + A) / n) * M := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hcard0 : (0 : ℝ) < T.card := (mul_pos hρ hn).trans_le hcard
  have hfactor : 1 / (T.card : ℝ) + (RandomRanking.ofWeights a w).toReal ≤
      (1 / ρ + A) / n := by
    calc
      _ ≤ 1 / (ρ * n) + A / n := add_le_add
        (one_div_le_one_div_of_le (mul_pos hρ hn) hcard) hq
      _ = _ := by field_simp
  have hR : 0 ≤ ∫ z, (RepeatMoments.totalRepeats z : ℝ) ∂TotalMoments.rawLaw a b :=
    integral_nonneg fun _ ↦ Nat.cast_nonneg _
  exact (repeatNoise_mean_le a b ha hb T w hw hT).trans
    ((mul_le_mul_of_nonneg_right hfactor hR).trans
      (mul_le_mul_of_nonneg_left hM (by positivity)))

/-- The raw repeat correction has a uniform log-cubed over n expectation. -/
theorem eventually_repeatNoise_mean_le {A B ρ : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hρ : 0 < ρ) :
    ∀ᶠ n : ℕ in atTop, ∀ [NeZero n] (a b : Fin n → ℝ≥0),
      (∀ w, 1 ≤ (a w : ℝ)) → (∀ w, (a w : ℝ) ≤ A) →
      (∀ m, 1 ≤ (b m : ℝ)) → (∀ m, (b m : ℝ) ≤ B) →
      ∀ (T : Finset (Fin n)) (w : Fin n), w ∈ T →
      (∀ v ∈ T, a v = a w) → ρ * n ≤ (T.card : ℝ) →
      (∫ z, repeatNoise a w z ∂TotalMoments.rawLaw a b) ≤
        (1 / ρ + A) * TotalMoments.repeatConstant A B * (Real.log n) ^ 3 / n := by
  filter_upwards [TotalMoments.eventually_repeat_mean_le hA hB] with n hR
  intro _ a b ha1 haA hb1 hbB T w hw hT hcard
  have ha : ∀ w, 0 < a w := fun w ↦ by
    exact_mod_cast lt_of_lt_of_le zero_lt_one (ha1 w)
  have hb : ∀ m, 0 < b m := fun m ↦ by
    exact_mod_cast lt_of_lt_of_le zero_lt_one (hb1 m)
  have hR' := hR a b ha1 haA hb1 hbB
  have heq := RepeatMoments.ae_difference_eq_totalRepeats a (fun m _ ↦ b m)
    ha (fun m _ ↦ hb m)
  rw [integral_congr_ae heq] at hR'
  have hq : (RandomRanking.ofWeights a w).toReal ≤ A / n := by
    simpa only [Fintype.card_fin] using CouponLowerTail.ofWeights_mass_upper a
      (fun v ↦ by exact_mod_cast ha1 v) A haA w
  have hh := repeatNoise_mean_le_of_bounds a b ha hb T w hw hT hρ
    (by linarith : 0 ≤ A) hcard hq hR'
  convert hh using 1
  ring

/-- Three actual count errors control the final normalized destination count. -/
theorem count_error_le {x rawX U rawU target q localR totalR : ℝ}
    (hq : 0 ≤ q) (hl : |x - rawX| ≤ localR) (ht : |rawU - U| ≤ totalR) :
    |x - q * target| ≤ |rawX - q * rawU| + q * |U - target| + localR + q * totalR := by
  calc
    _ ≤ |x - rawX| + |rawX - q * target| := abs_sub_le _ _ _
    _ ≤ localR + (|rawX - q * rawU| + |q * rawU - q * target|) :=
      add_le_add hl (abs_sub_le _ _ _)
    _ = localR + (|rawX - q * rawU| + q * |rawU - target|) := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hq]
    _ ≤ localR + (|rawX - q * rawU| + q * (totalR + |U - target|)) := by
      gcongr
      exact (abs_sub_le rawU U target).trans (add_le_add ht le_rfl)
    _ = _ := by ring

/-- A terminal count error is covered by a clock failure and three observable error events. -/
theorem deviation_probability_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (good : Set Ω) (X rawX U rawU noise : Ω → ℝ)
    {q target η : ℝ} (hq : 0 ≤ q)
    (hcount : ∀ᵐ ω ∂μ, ω ∈ good →
      |X ω - q * target| ≤ |rawX ω - q * rawU ω| + q * |U ω - target| + noise ω) :
    μ.real {ω | η * (q * target) < |X ω - q * target|} ≤ μ.real goodᶜ +
      μ.real {ω | η * (q * target) / 3 < |rawX ω - q * rawU ω|} +
      μ.real {ω | η * target / 3 < |U ω - target|} +
      μ.real {ω | η * (q * target) / 3 < noise ω} := by
  let E₀ := goodᶜ
  let E₁ := {ω | η * (q * target) / 3 < |rawX ω - q * rawU ω|}
  let E₂ := {ω | η * target / 3 < |U ω - target|}
  let E₃ := {ω | η * (q * target) / 3 < noise ω}
  have hsub : ∀ᵐ ω ∂μ, ω ∈ {ω | η * (q * target) < |X ω - q * target|} →
      ω ∈ ((E₀ ∪ E₁) ∪ E₂) ∪ E₃ := by
    filter_upwards [hcount] with ω hc
    intro hx
    by_contra hn
    have hg : ω ∈ good := by
      by_contra hng
      exact hn (Or.inl (Or.inl (Or.inl hng)))
    have h₁ : |rawX ω - q * rawU ω| ≤ η * (q * target) / 3 := by
      by_contra h
      exact hn (Or.inl (Or.inl (Or.inr (lt_of_not_ge h))))
    have h₂ : |U ω - target| ≤ η * target / 3 := by
      by_contra h
      exact hn (Or.inl (Or.inr (lt_of_not_ge h)))
    have h₃ : noise ω ≤ η * (q * target) / 3 := by
      by_contra h
      exact hn (Or.inr (lt_of_not_ge h))
    have hm := mul_le_mul_of_nonneg_left h₂ hq
    have he := hc hg
    nlinarith
  have hmono : μ.real {ω | η * (q * target) < |X ω - q * target|} ≤
      μ.real (((E₀ ∪ E₁) ∪ E₂) ∪ E₃) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  exact hmono.trans ((measureReal_union_le _ _).trans
    (add_le_add (measureReal_union_le _ _) le_rfl) |>.trans
      (add_le_add (add_le_add (measureReal_union_le _ _) le_rfl) le_rfl))

/-- The repeat event has its ordinary Markov bound under the actual source law. -/
theorem repeatNoise_tail_le {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (w : Fin n) {ε : ℝ} (hε : 0 < ε) :
    (TotalMoments.rawLaw a b).real {z | ε < repeatNoise a w z} ≤
      (∫ z, repeatNoise a w z ∂TotalMoments.rawLaw a b) / ε := by
  have := Raw.isProbabilityMeasure_rawInputLaw (fun _ ↦ a) (fun m _ ↦ b m)
    (fun m _ ↦ hb m)
  have hm := tailReal_le_integral_abs (TotalMoments.rawLaw a b) (repeatNoise a w)
    ((repeatNoise_memLp a b ha hb w).integrable one_le_two) hε
  have he : {z | ε < |repeatNoise a w z|} = {z | ε < repeatNoise a w z} := by
    ext z
    change (ε < |repeatNoise a w z|) ↔ ε < repeatNoise a w z
    rw [abs_of_nonneg (repeatNoise_nonneg a w z)]
  have hi : (∫ z, |repeatNoise a w z| ∂TotalMoments.rawLaw a b) =
      ∫ z, repeatNoise a w z ∂TotalMoments.rawLaw a b :=
    integral_congr_ae (Filter.Eventually.of_forall fun z ↦
      abs_of_nonneg (repeatNoise_nonneg a w z))
  rwa [he, hi] at hm

/-- The exact PR woman's count obeys the four-event estimate on the original raw source. -/
theorem source_deviation_probability_le {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (J : Finset (Fin n)) (w : Fin n)
    (H : ℕ) (η : ℝ) :
    let μ := TotalMoments.rawLaw a b
    let q := DestinationMartingale.destinationProbability a w
    let t := TierConcentration.target a b J
    μ.real {z | η * (q * t) <
        |(ProposalCounts.genuineWomanCount (RawBridge.sourceProfile z) J w : ℝ) - q * t|} ≤
      μ.real {z | H < GlobalDraws.rawClock z} +
      μ.real {z | η * (q * t) / 3 <
        |(DestinationMartingale.rawWomanTierCount (GlobalDraws.activeProtocol Finset.univ)
          J w H z : ℝ) - q * DestinationMartingale.rawTierCount
            (GlobalDraws.activeProtocol Finset.univ) J H z|} +
      μ.real {z | η * t / 3 < |TierConcentration.tierTotal J (RawBridge.sourceProfile z) - t|} +
      μ.real {z | η * (q * t) / 3 < repeatNoise a w z} := by
  have := Raw.isProbabilityMeasure_rawInputLaw (fun _ ↦ a) (fun m _ ↦ b m)
    (fun m _ ↦ hb m)
  let μ := TotalMoments.rawLaw a b
  let q := DestinationMartingale.destinationProbability a w
  let t := TierConcentration.target a b J
  have hq : 0 ≤ q := (DestinationMartingale.destinationProbability_mem_Icc a w).1
  have hcount : ∀ᵐ z ∂μ, z ∈ {z | GlobalDraws.rawClock z ≤ H} →
      |(ProposalCounts.genuineWomanCount (RawBridge.sourceProfile z) J w : ℝ) - q * t| ≤
        |(DestinationMartingale.rawWomanTierCount (GlobalDraws.activeProtocol Finset.univ)
          J w H z : ℝ) - q * DestinationMartingale.rawTierCount
            (GlobalDraws.activeProtocol Finset.univ) J H z| +
          q * |TierConcentration.tierTotal J (RawBridge.sourceProfile z) - t| +
            repeatNoise a w z := by
    filter_upwards [ProposalCounts.ae_deviation_transfer a b ha hb H] with z hz
    intro hH
    have he := hz hH J w q hq
    have ht := abs_sub_le
      (ProposalCounts.genuineWomanCount (RawBridge.sourceProfile z) J w : ℝ)
      (q * TierConcentration.tierTotal J (RawBridge.sourceProfile z)) (q * t)
    rw [← mul_sub, abs_mul, abs_of_nonneg hq] at ht
    dsimp only [repeatNoise, q, DestinationMartingale.destinationProbability] at he ht ⊢
    linarith
  have hh := deviation_probability_le μ {z | GlobalDraws.rawClock z ≤ H}
    (fun z ↦ (ProposalCounts.genuineWomanCount (RawBridge.sourceProfile z) J w : ℝ))
    (fun z ↦ (DestinationMartingale.rawWomanTierCount (GlobalDraws.activeProtocol Finset.univ)
      J w H z : ℝ))
    (fun z ↦ TierConcentration.tierTotal J (RawBridge.sourceProfile z))
    (fun z ↦ (DestinationMartingale.rawTierCount (GlobalDraws.activeProtocol Finset.univ)
      J H z : ℝ)) (repeatNoise a w) (target := t) (η := η) hq hcount
  have hcompl : {z : Raw.Sources n | GlobalDraws.rawClock z ≤ H}ᶜ =
      {z | H < GlobalDraws.rawClock z} := by
    ext z
    change ¬ GlobalDraws.rawClock z ≤ H ↔ H < GlobalDraws.rawClock z
    omega
  rwa [hcompl] at hh

/-- Every original-profile event has exactly the same probability on the raw source. -/
theorem profile_event_real {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (E : Set (StableMarriage.Profile n)) :
    (TotalMoments.rawLaw a b).real (RawBridge.sourceProfile ⁻¹' E) =
      (VisitBounds.profileLaw a b).toMeasure.real E := by
  have hmp := TotalMoments.profile_measurePreserving a b ha hb
  change ((TotalMoments.rawLaw a b) (RawBridge.sourceProfile ⁻¹' E)).toReal = _
  rw [hmp.measure_preimage (show MeasurableSet E from trivial).nullMeasurableSet]
  rfl

/-- All four error estimates concern the exact PR statistic and its original probability law. -/
theorem four_error_bound {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (J : Finset (Fin n)) (w : Fin n) {A C η : ℝ}
    (hA : 1 ≤ A) (ha1 : ∀ v, 1 ≤ (a v : ℝ)) (haA : ∀ v, (a v : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (hlog : 0 ≤ Real.log n) (hη : 0 < η)
    (ht : 0 < TierConcentration.target a b J) (hc : 0 < center a b J w)
    (hTier : (VisitBounds.profileLaw a b).toMeasure.real
      {p | η / 3 < |TierConcentration.tierTotal J p / TierConcentration.target a b J - 1|} ≤
        C / ((η / 3) ^ 2 * Real.log n)) :
    (VisitBounds.profileLaw a b).toMeasure.real
      {p | η * center a b J w <
        |(ProposalCounts.genuineWomanCount p J w : ℝ) - center a b J w|} ≤
      1 / (n : ℝ) ^ 4 +
        (TotalMoments.clockCap A n : ℝ) * DestinationMartingale.destinationProbability a w /
          (η * center a b J w / 3) ^ 2 + C / ((η / 3) ^ 2 * Real.log n) +
        (∫ z, repeatNoise a w z ∂TotalMoments.rawLaw a b) / (η * center a b J w / 3) := by
  have ha : ∀ v, 0 < a v := fun v ↦ by
    exact_mod_cast lt_of_lt_of_le zero_lt_one (ha1 v)
  let μ := TotalMoments.rawLaw a b
  let q := DestinationMartingale.destinationProbability a w
  let t := TierConcentration.target a b J
  let H := TotalMoments.clockCap A n
  let ε := η * center a b J w / 3
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hq : 0 ≤ q := (DestinationMartingale.destinationProbability_mem_Icc a w).1
  have : IsProbabilityMeasure μ :=
    Raw.isProbabilityMeasure_rawInputLaw (fun _ ↦ a) (fun m _ ↦ b m) (fun m _ ↦ hb m)
  have hbase := source_deviation_probability_le a b ha hb J w H η
  dsimp only at hbase
  rw [destination_mul_target a b ha J w] at hbase
  have hclock := TotalMoments.clock_cap_tail a b hA hlog ha1 haA hb
  have hraw := DestinationMartingale.raw_counts_deviation_measure_le a (fun m _ ↦ b m)
    (fun m _ ↦ hb m) (GlobalDraws.activeProtocol Finset.univ) J w H ε hε
  have hrawReal : μ.real {z | ε <
      |(DestinationMartingale.rawWomanTierCount (GlobalDraws.activeProtocol Finset.univ)
        J w H z : ℝ) - q * DestinationMartingale.rawTierCount
          (GlobalDraws.activeProtocol Finset.univ) J H z|} ≤ (H : ℝ) * q / ε ^ 2 := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hraw
    rw [ENNReal.toReal_ofReal (by positivity)] at hh
    have hsub : {z : Raw.Sources n | ε <
        |(DestinationMartingale.rawWomanTierCount (GlobalDraws.activeProtocol Finset.univ)
          J w H z : ℝ) - q * DestinationMartingale.rawTierCount
            (GlobalDraws.activeProtocol Finset.univ) J H z|} ⊆
        {z | ε ≤ |(DestinationMartingale.rawWomanTierCount
          (GlobalDraws.activeProtocol Finset.univ) J w H z : ℝ) - q *
            DestinationMartingale.rawTierCount (GlobalDraws.activeProtocol Finset.univ) J H z|} :=
      by
        intro z hz
        change ε < |(DestinationMartingale.rawWomanTierCount
          (GlobalDraws.activeProtocol Finset.univ) J w H z : ℝ) - q *
            DestinationMartingale.rawTierCount (GlobalDraws.activeProtocol Finset.univ) J H z|
          at hz
        change ε ≤ |(DestinationMartingale.rawWomanTierCount
          (GlobalDraws.activeProtocol Finset.univ) J w H z : ℝ) - q *
            DestinationMartingale.rawTierCount (GlobalDraws.activeProtocol Finset.univ) J H z|
        exact hz.le
    exact (measureReal_mono (μ := μ) hsub (measure_ne_top _ _)).trans hh
  have hTierRaw : μ.real {z | η * t / 3 <
      |TierConcentration.tierTotal J (RawBridge.sourceProfile z) - t|} ≤
        C / ((η / 3) ^ 2 * Real.log n) := by
    have hevent : {z : Raw.Sources n | η * t / 3 <
        |TierConcentration.tierTotal J (RawBridge.sourceProfile z) - t|} =
        RawBridge.sourceProfile ⁻¹'
          {p | η / 3 < |TierConcentration.tierTotal J p / t - 1|} := by
      rw [TierConcentration.relative_event_eq (TierConcentration.tierTotal J) ht]
      ext z
      change (η * t / 3 < |TierConcentration.tierTotal J (RawBridge.sourceProfile z) - t|) ↔
        (η / 3 * t < |TierConcentration.tierTotal J (RawBridge.sourceProfile z) - t|)
      rw [show η * t / 3 = η / 3 * t by ring]
    rw [hevent, profile_event_real a b ha hb]
    exact hTier
  have hnoise := repeatNoise_tail_le a b ha hb w hε
  have hbad : μ.real {z | η * center a b J w <
      |(ProposalCounts.genuineWomanCount (RawBridge.sourceProfile z) J w : ℝ) -
        center a b J w|} =
      (VisitBounds.profileLaw a b).toMeasure.real
        {p | η * center a b J w <
          |(ProposalCounts.genuineWomanCount p J w : ℝ) - center a b J w|} := by
    have he : RawBridge.sourceProfile ⁻¹'
        {p | η * center a b J w <
          |(ProposalCounts.genuineWomanCount p J w : ℝ) - center a b J w|} =
        {z | η * center a b J w <
          |(ProposalCounts.genuineWomanCount (RawBridge.sourceProfile z) J w : ℝ) -
            center a b J w|} := by ext z; rfl
    rw [← he]
    exact profile_event_real a b ha hb _
  rw [hbad] at hbase
  exact hbase.trans (add_le_add (add_le_add (add_le_add hclock hrawReal) hTierRaw) hnoise)

/-- Uniform G.2 for normalized score vectors under the original PR probability law.
All process moments, raw counts, repeat corrections, and clock estimates are discharged.
-/
theorem uniform_vector_g2 {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) : UniformVectorG2 A B := by
  obtain ⟨Km, Ccov, hKm, hCcov, hPair⟩ := GlobalPairMoments.uniform_pair_moments hA hB
  intro ρ hρ
  let cmin := ρ / B
  let Kclock := 5 * A + 1
  let Ct := 4 * (TotalMoments.varianceConstant A B ρ + 2 * Ccov) / cmin ^ 2
  let M := (1 / ρ + A) * TotalMoments.repeatConstant A B
  have hAp : 0 < A := by linarith
  have hBp : 0 < B := by linarith
  have hcmin : 0 < cmin := div_pos hρ hBp
  have hKclock : 0 < Kclock := by dsimp only [Kclock]; positivity
  have hCt : 0 ≤ Ct := by
    have hv := (TotalMoments.constants_pos hA hB ρ).2.2
    dsimp only [Ct]
    positivity
  have hM : 0 ≤ M := by
    have hr := (TotalMoments.constants_pos hA hB ρ).1
    dsimp only [M]
    positivity
  refine ⟨G2Numerics.errorConstant A Kclock Ct M cmin,
    G2Numerics.errorConstant_pos hA hKclock hCt hM hcmin, ?_⟩
  intro η hη hη1
  have hη3 : 0 < η / 3 := by positivity
  have hcubes : ∀ᶠ n : ℕ in atTop, (Real.log n) ^ 3 ≤ (n : ℝ) := by
    simpa only [one_mul, Real.rpow_one] using
      eventually_log_power_le (c := 1) (s := 1) zero_lt_one zero_lt_one 3
  have hfinal : ∀ᶠ n : ℕ in atTop, 2 ≤ n →
      ∀ (a b : Fin n → ℝ≥0),
        (∀ w, 1 ≤ (a w : ℝ)) → (∀ w, (a w : ℝ) ≤ A) →
        (∀ m, 1 ≤ (b m : ℝ)) → (∀ m, (b m : ℝ) ≤ B) →
        ρ * n ≤ ((CouponMoments.minimumCoupons a).card : ℝ) →
        ∀ J T : Finset (Fin n), ρ * n ≤ (J.card : ℝ) → ρ * n ≤ (T.card : ℝ) →
        (∀ x ∈ T, ∀ y ∈ T, a x = a y) → ∀ w ∈ T,
        (VisitBounds.profileLaw a b).toMeasure
          {p | |(ProposalCounts.genuineWomanCount p J w : ℝ) - center a b J w| >
            η * center a b J w} ≤
          ENNReal.ofReal (G2Numerics.errorConstant A Kclock Ct M cmin /
            (η ^ 2 * Real.log n)) := by
    filter_upwards [hPair,
      TierConcentration.eventually_tier_relative_deviation_le hA hB hρ hρ hKm.le hCcov.le hη3,
      eventually_repeatNoise_mean_le hA hB hρ,
      ContinuationAsymptotics.eventually_one_le_log, hcubes]
      with n hp ht hr hlog hcube
    intro hn2 a b ha1 haA hb1 hbB hmin J T hJ hT hsame w hw
    have : NeZero n := ⟨by omega⟩
    have hn : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have ha : ∀ v, 0 < a v := fun v ↦ by
      exact_mod_cast lt_of_lt_of_le zero_lt_one (ha1 v)
    have hb : ∀ m, 0 < b m := fun m ↦ by
      exact_mod_cast lt_of_lt_of_le zero_lt_one (hb1 m)
    obtain ⟨hpmean, hpcov⟩ := hp a b ha1 haA hb1 hbB
    have hTierBase := ht a b ha1 haA hb1 hbB hmin J hJ hpmean hpcov
    have hTier : (VisitBounds.profileLaw a b).toMeasure.real
        {p | η / 3 < |TierConcentration.tierTotal J p / TierConcentration.target a b J - 1|} ≤
          Ct / ((η / 3) ^ 2 * Real.log n) := by
      convert hTierBase using 1
      dsimp only [Ct, cmin]
      field_simp
    have hnoise := hr a b ha1 haA hb1 hbB T w hw (fun v hv ↦ hsame v hv w hw) hT
    change (∫ z, repeatNoise a w z ∂TotalMoments.rawLaw a b) ≤
      M * (Real.log n) ^ 3 / n at hnoise
    have hq : DestinationMartingale.destinationProbability a w ≤ A / n := by
      simpa only [DestinationMartingale.destinationProbability, Fintype.card_fin] using
        CouponLowerTail.ofWeights_mass_upper a
        (fun v ↦ by exact_mod_cast ha1 v) A haA w
    have hcenter := center_lower a b J w hBp hρ.le ha1 hb1 hbB hJ (by linarith)
    change cmin * Real.log n ≤ center a b J w at hcenter
    have hc : 0 < center a b J w := (by positivity : 0 < cmin * Real.log n).trans_le hcenter
    have htlow := TierConcentration.target_lower a b J hBp hρ.le
      (by linarith : 0 ≤ Real.log n) ha1 hb1 hbB hJ
    have htpos : 0 < TierConcentration.target a b J :=
      (by positivity : 0 < (ρ / B) * (n : ℝ) * Real.log n).trans_le htlow
    have hfinite := four_error_bound a b J w hA ha1 haA hb (by linarith) hη htpos hc hTier
    have hH := G2Numerics.clockCap_le (show 1 ≤ n by omega) hA hlog
    have hnum := G2Numerics.error_budget (C := Ct) hn hlog hcube hη hη1 hcmin hcenter hM
      hnoise (Nat.cast_nonneg (TotalMoments.clockCap A n)) hH hq hKclock hAp.le
    have hreal := hfinite.trans hnum
    have he := ENNReal.ofReal_le_ofReal hreal
    change ENNReal.ofReal ((VisitBounds.profileLaw a b).toMeasure
      {p | |(ProposalCounts.genuineWomanCount p J w : ℝ) - center a b J w| >
        η * center a b J w}).toReal ≤ _ at he
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)] at he
    exact he
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfinal
  refine ⟨N, ?_⟩
  intro n hn hn2
  exact hN n hn hn2

/-- Proposition G.2 has one quantitative bound uniform in every labeled market with tier
shares bounded below, for the exact arbitrary positive public scores in the PR.
-/
theorem uniform_g2_bound {I J : ℕ} (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (αmin : ℝ) (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (hmin : IsMinimumScore α αmin) : UniformG2Bound α β αmin := by
  obtain ⟨N⟩ := G2Scaling.exists_scoreNormalization α β αmin hα hβ hmin
  apply N.uniformG2Bound
  exact (uniform_vector_g2 N.one_le_A N.one_le_B).uniformG2Bound _ _
    (fun i ↦ (N.woman_bounds i).2) (fun j ↦ (N.man_bounds j).1)
    (fun j ↦ (N.man_bounds j).2) N.minimum_one

/-- The exact fixed-woman G.2 assertion follows for every tier sequence allowed by the
PR's rounding error at most one. Its uniform stochastic estimate is proved above.
-/
theorem proposition_g2 {I J : ℕ} (a : Fin I → ℝ) (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j) (hmin : IsMinimumScore α αmin)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (hw : ∀ n i, |(Fintype.card {w // womanTier n w = i} : ℝ) - n * a i| ≤ 1)
    (hm : ∀ n j, |(Fintype.card {m // manTier n m = j} : ℝ) - n * b j| ≤ 1)
    (i : Fin I) : PropositionG2 b α β αmin womanTier manTier i :=
  UniformG2Bound.propositionG2 a b α β αmin ha hb hα hβ hmin
    (uniform_g2_bound α β αmin hα hβ hmin) womanTier manTier hw hm i

end Ashlagi.G2Assembly
