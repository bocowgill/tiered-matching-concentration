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

public import Ashlagi.GlobalDraws
public import Ashlagi.RepeatBounds

/-! # Actual raw repeat moments by predictable cap removal

The actual raw coupon clock is decomposed using its exact ordinary PR profile. Repeats on
paths below both caps are controlled by the predictable compensator. The complementary
paths cost a Cauchy--Schwarz correction using the actual raw clock's second moment.
-/

@[expose] public section

namespace Ashlagi.RepeatMoments

open MeasureTheory StableMarriage
open scoped ENNReal NNReal

/-- Repeated-edge count increases exactly on an already present edge. -/
theorem repeatCount_cons {n : ℕ} (q : RawSemantics.Edge n) (L : List (RawSemantics.Edge n)) :
    RawSemantics.repeatCount (q :: L) = RawSemantics.repeatCount L +
      if q ∈ L.toFinset then 1 else 0 := by
  have hc := List.toFinset_card_le L
  simp only [RawSemantics.repeatCount, RawSemantics.distinctCount, List.length_cons,
    List.toFinset_cons]
  by_cases hq : q ∈ L.toFinset
  · rw [Finset.insert_eq_of_mem hq, ite_eq_left hq]
    omega
  · rw [Finset.card_insert_of_notMem hq, ite_eq_right hq]
    omega

/-- Every actual raw repeat tag is exactly an edge repetition in the erased-pause trace. -/
theorem repeatCount_observation {n : ℕ} (C : Raw.Protocol n) (h : List (Raw.Entry n))
    (hv : Raw.Valid C h) (z : Raw.Sources n) :
    RawSemantics.repeatCount (RawBridge.trace
      (Raw.observation C z.1 (Function.uncurry z.2) h :: h)) =
        RawSemantics.repeatCount (RawBridge.trace h) +
          if ∃ q, Raw.observation C z.1 (Function.uncurry z.2) h = some (q, none)
            then 1 else 0 := by
  classical
  have hseen : (RawBridge.trace h).toFinset = Raw.seenEdges h :=
    (RawBridge.trace_toFinset h).trans (Raw.seenEdges_eq_allEdges C h hv).symm
  cases he : Raw.observation C z.1 (Function.uncurry z.2) h with
  | none => simp [RawBridge.trace]
  | some e =>
    rcases e with ⟨q, tag⟩
    have ht := (Raw.observation_eq_iff C z.1 (Function.uncurry z.2) h _).mp he
    rw [RawBridge.trace, repeatCount_cons, hseen]
    cases tag with
    | none =>
      have hq : q ∈ Raw.seenEdges h := ht.2.1
      simp only [hq, Option.some.injEq, Prod.mk.injEq, and_true,
        exists_eq', ↓reduceIte]
    | some acc =>
      have hq : q ∉ Raw.seenEdges h := ht.2.1
      simp [hq]

/-- The predictable leaf's actual uncapped count equals the semantic trace repeat count. -/
theorem repeats_eq_trace_repeatCount {n : ℕ} (C : Raw.Protocol n) (t : ℕ)
    (z : Raw.Sources n) :
    RepeatBounds.repeats C t z =
      RawSemantics.repeatCount (RawBridge.trace (RawBridge.history C z t)) := by
  classical
  induction t with
  | zero => simp [RepeatBounds.repeats, RawBridge.history, Raw.transcript,
      RawBridge.trace, RawSemantics.repeatCount, RawSemantics.distinctCount]
  | succ t ih =>
    rw [RepeatBounds.repeats_eq_sum_observations, Finset.sum_range_succ,
      ← RepeatBounds.repeats_eq_sum_observations, ih]
    exact (repeatCount_observation C _ (Raw.valid_transcript C z.1
      (Function.uncurry z.2) t) z).symm

/-- Longer raw horizons can only add actual repeat indicators. -/
theorem repeats_mono {n : ℕ} (C : Raw.Protocol n) (s t : ℕ) (hst : s ≤ t)
    (z : Raw.Sources n) : RepeatBounds.repeats C s z ≤ RepeatBounds.repeats C t z := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hst)
    (fun _ _ _ ↦ Nat.zero_le _)

/-- Every reachable state's counter lies below the exact full-market PR terminal counter. -/
theorem reachable_next_le_pr {n : ℕ} (p : Profile n) (s : ProposalState n)
    (hs : Schedules.Reachable p Finset.univ s) (m : Fin n) :
    s.next m ≤ (deferredAcceptance p).next m := by
  by_contra hnot
  have hv := Schedules.reachable_valid p Finset.univ hs
  have hn : (deferredAcceptance p).next m < n :=
    lt_of_lt_of_le (lt_of_not_ge hnot) (hv.next_le m)
  let w := (p.manRank m).symm ⟨(deferredAcceptance p).next m, hn⟩
  have hp : HasProposed p s m w := by
    simp only [HasProposed, w, Equiv.apply_symm_apply]
    omega
  have ht := Schedules.reachable_proposals_subset_larger_terminal p (Finset.Subset.refl _)
    hs (Schedules.pr_terminal p).1 (Schedules.pr_terminal p).2 m w hp
  simp [HasProposed, w] at ht

/-- The exact terminal PR rank cap is a statistic of the original source profile. -/
def RankCap {n : ℕ} (cap : ℕ) : Set (Raw.Sources n) :=
  {z | ∀ m, (deferredAcceptance (RawBridge.sourceProfile z)).next m ≤ cap}

/-- Terminal rank control bounds every actual raw prefix counter, almost surely. -/
theorem ae_rankCap_implies_noCap {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hQ : ∀ m w, 0 < Q m w) (cap H : ℕ) :
    ∀ᵐ z ∂rawInputLaw (fun _ ↦ a) Q,
      z ∈ RankCap cap → z ∈ RepeatBounds.NoCap (GlobalDraws.activeProtocol Finset.univ) cap H := by
  filter_upwards [RawBridge.ae_reachable (fun _ ↦ a) Q (fun _ ↦ ha) hQ
    (GlobalDraws.activeProtocol Finset.univ) Finset.univ (RawBridge.supports_univ _)] with z hz
  intro hcap t _ m
  exact (reachable_next_le_pr _ _ (hz t) m).trans (hcap m)

/-- Actual completed-run repeats, as the nonnegative natural raw/ordinary count difference. -/
noncomputable def totalRepeats {n : ℕ} [NeZero n] (z : Raw.Sources n) : ℕ :=
  GlobalDraws.rawClock z - numProposals (RawBridge.sourceProfile z)

/-- The proved actual clock decomposition identifies total repeats with actual repeat tags. -/
theorem ae_totalRepeats_eq {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hQ : ∀ m w, 0 < Q m w) :
    ∀ᵐ z ∂rawInputLaw (fun _ ↦ a) Q,
      totalRepeats z = RepeatBounds.repeats (GlobalDraws.activeProtocol Finset.univ)
        (GlobalDraws.rawClock z) z := by
  filter_upwards [GlobalDraws.ae_rawClock_decomposition a Q ha hQ] with z hz
  rw [repeats_eq_trace_repeatCount]
  unfold totalRepeats
  omega

/-- The extracted original PR profile is a measurable function of the actual raw sources. -/
theorem measurable_sourceProfile {n : ℕ} : Measurable (RawBridge.sourceProfile (n := n)) :=
  measurable_mixedRankProfile IIDRanking.iidRank exponentialRank
    IIDRanking.measurableSet_iidRank_fiber measurableSet_exponentialRank_fiber

/-- Measurability of the actual raw completion clock. -/
theorem measurable_rawClock {n : ℕ} [NeZero n] : Measurable (GlobalDraws.rawClock (n := n)) :=
  CouponMoments.measurable_time.comp (GlobalDraws.measurable_sourceTape _
    (GlobalDraws.activeProtocol_pauseStable Finset.univ))

/-- Actual PR terminal rank-cap events are measurable. -/
theorem measurableSet_rankCap {n : ℕ} (cap : ℕ) : MeasurableSet (RankCap (n := n) cap) := by
  have hm : Measurable (fun p : Profile n ↦ decide (∀ m, (deferredAcceptance p).next m ≤ cap)) :=
    measurable_of_countable _
  simpa only [RankCap, Set.preimage, Set.mem_singleton_iff, Function.comp_apply,
    decide_eq_true_eq] using ((hm.comp measurable_sourceProfile) (measurableSet_singleton true))

/-- The nonnegative completed-run difference is measurable. -/
theorem measurable_totalRepeats {n : ℕ} [NeZero n] : Measurable (totalRepeats (n := n)) := by
  exact measurable_rawClock.sub
    ((measurable_of_countable numProposals).comp measurable_sourceProfile)

/-- Actual repeats are bounded by the actual raw clock on every source. -/
theorem totalRepeats_le_clock {n : ℕ} [NeZero n] (z : Raw.Sources n) :
    totalRepeats z ≤ GlobalDraws.rawClock z := Nat.sub_le _ _

/-- The actual real completed-run repeat count belongs to L2. -/
theorem totalRepeats_memLp {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hQ : ∀ m w, 0 < Q m w) :
    MemLp (fun z ↦ (totalRepeats z : ℝ)) 2 (rawInputLaw (fun _ ↦ a) Q) := by
  apply (GlobalDraws.rawClock_memLp a Q ha hQ).mono'
    ((measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp
      measurable_totalRepeats).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  change (totalRepeats z : ℝ) ≤ (GlobalDraws.rawClock z : ℝ)
  exact_mod_cast totalRepeats_le_clock z

/-- Cauchy--Schwarz bounds the expectation of a nonnegative L2 variable on an arbitrary event. -/
theorem integral_indicator_le_sqrt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (T : Ω → ℝ) (hT : MemLp T 2 μ)
    (hT0 : ∀ ω, 0 ≤ T ω) (E : Set Ω) (hE : MeasurableSet E) :
    (∫ ω, E.indicator T ω ∂μ) ≤
      Real.sqrt (∫ ω, T ω ^ 2 ∂μ) * Real.sqrt (μ.real E) := by
  have hI : MemLp (E.indicator (fun _ ↦ (1 : ℝ))) 2 μ :=
    (memLp_const (1 : ℝ)).indicator hE.nullMeasurableSet
  have hI0 : ∀ ω, 0 ≤ E.indicator (fun _ ↦ (1 : ℝ)) ω := by
    intro ω
    by_cases he : ω ∈ E <;> simp [he]
  have hb := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hT0) (Filter.Eventually.of_forall hI0)
    (by simpa using hT) (by simpa using hI)
  have hl : (fun ω ↦ T ω * E.indicator (fun _ ↦ (1 : ℝ)) ω) = E.indicator T := by
    funext ω
    by_cases he : ω ∈ E <;> simp [he]
  have hr : (fun ω ↦ (E.indicator (fun _ ↦ (1 : ℝ)) ω) ^ (2 : ℝ)) =
      E.indicator (fun _ ↦ (1 : ℝ)) := by
    funext ω
    by_cases he : ω ∈ E <;> simp [he]
  have hprob : (∫ ω, E.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ) = μ.real E := by
    exact integral_indicator_one hE
  rw [hl, hr, hprob] at hb
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using hb

/-- Both cap failures retained explicitly, under the actual original raw source law. -/
def Bad {n : ℕ} [NeZero n] (H cap : ℕ) : Set (Raw.Sources n) :=
  {z | H < GlobalDraws.rawClock z} ∪ (RankCap cap)ᶜ

/-- The actual cap failure event is measurable. -/
theorem measurableSet_bad {n : ℕ} [NeZero n] (H cap : ℕ) :
    MeasurableSet (Bad (n := n) H cap) :=
  (measurable_rawClock measurableSet_Ioi).union (measurableSet_rankCap cap).compl

/-- On paths below both caps, the completed-run count is dominated by the capped horizon count. -/
theorem ae_totalRepeats_le_capped {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hQ : ∀ m w, 0 < Q m w) (cap H : ℕ) :
    ∀ᵐ z ∂rawInputLaw (fun _ ↦ a) Q, z ∉ Bad H cap →
      totalRepeats z ≤ RepeatBounds.cappedRepeats
        (GlobalDraws.activeProtocol Finset.univ) cap H z := by
  filter_upwards [ae_totalRepeats_eq a Q ha hQ, ae_rankCap_implies_noCap a Q ha hQ cap H]
    with z hz hcap
  intro hgood
  have ht : GlobalDraws.rawClock z ≤ H := by
    have hn : ¬ H < GlobalDraws.rawClock z := fun hh ↦ hgood (Or.inl hh)
    omega
  have hr : z ∈ RankCap cap := by
    by_contra hnot
    exact hgood (Or.inr hnot)
  rw [hz, RepeatBounds.cappedRepeats_eq_repeats_of_no_cap _ cap H z (hcap hr)]
  exact repeats_mono _ _ H ht z

/-- Actual cap removal for completed-run repeats, retaining both original-law cap errors. -/
theorem integral_totalRepeats_le {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    {A : ℝ} (hA : 0 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ))
    (haA : ∀ w, (a w : ℝ) ≤ A) (cap H : ℕ) :
    let μ := rawInputLaw (fun _ ↦ a) Q
    (∫ z, (totalRepeats z : ℝ) ∂μ) ≤ (H : ℝ) * A * cap / n +
      Real.sqrt (∫ z, (GlobalDraws.rawClock z : ℝ) ^ 2 ∂μ) *
        Real.sqrt (μ.real {z | H < GlobalDraws.rawClock z} + μ.real (RankCap cap)ᶜ) := by
  dsimp only
  let μ := rawInputLaw (fun _ ↦ a) Q
  have := Raw.isProbabilityMeasure_rawInputLaw (fun _ ↦ a) Q hQ
  have ha : ∀ w, 0 < a w := fun w ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (ha1 w)
  have hT := GlobalDraws.rawClock_memLp a Q ha hQ
  have hR := totalRepeats_memLp a Q ha hQ
  have hC := RepeatBounds.integrable_cappedRepeats
    (GlobalDraws.activeProtocol Finset.univ) cap H μ
  have hB := (hT.integrable one_le_two).indicator (measurableSet_bad H cap)
  have hpoint : ∀ᵐ z ∂μ, (totalRepeats z : ℝ) ≤
      (RepeatBounds.cappedRepeats (GlobalDraws.activeProtocol Finset.univ) cap H z : ℝ) +
        (Bad H cap).indicator (fun z ↦ (GlobalDraws.rawClock z : ℝ)) z := by
    filter_upwards [ae_totalRepeats_le_capped a Q ha hQ cap H] with z hz
    by_cases hb : z ∈ Bad H cap
    · rw [Set.indicator_of_mem hb]
      have hr : (totalRepeats z : ℝ) ≤ (GlobalDraws.rawClock z : ℝ) := by
        exact_mod_cast totalRepeats_le_clock z
      exact hr.trans (le_add_of_nonneg_left (Nat.cast_nonneg _))
    · rw [Set.indicator_of_notMem hb, add_zero]
      exact_mod_cast hz hb
  have hmean := integral_mono_ae (hR.integrable one_le_two) (hC.add hB) hpoint
  simp only [Pi.add_apply] at hmean
  rw [integral_add hC hB] at hmean
  have hcap := RepeatBounds.integral_cappedRepeats_le_scores a Q hQ hA ha1 haA
    (GlobalDraws.activeProtocol Finset.univ) cap H
  have hbad := integral_indicator_le_sqrt μ (fun z ↦ (GlobalDraws.rawClock z : ℝ)) hT
    (fun z ↦ Nat.cast_nonneg _) (Bad H cap) (measurableSet_bad H cap)
  have hp : μ.real (Bad H cap) ≤
      μ.real {z | H < GlobalDraws.rawClock z} + μ.real (RankCap cap)ᶜ :=
    measureReal_union_le _ _
  have hcorr := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hp)
    (Real.sqrt_nonneg (∫ z, (GlobalDraws.rawClock z : ℝ) ^ 2 ∂μ))
  exact hmean.trans (add_le_add hcap (hbad.trans hcorr))

/-- Natural and real raw-minus-ordinary differences agree almost surely under the actual law. -/
theorem ae_difference_eq_totalRepeats {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hQ : ∀ m w, 0 < Q m w) :
    ∀ᵐ z ∂rawInputLaw (fun _ ↦ a) Q,
      (GlobalDraws.rawClock z : ℝ) - (numProposals (RawBridge.sourceProfile z) : ℝ) =
        (totalRepeats z : ℝ) := by
  filter_upwards [GlobalDraws.ae_rawClock_decomposition a Q ha hQ] with z hz
  have hle : numProposals (RawBridge.sourceProfile z) ≤ GlobalDraws.rawClock z := by omega
  rw [totalRepeats, Nat.cast_sub hle]

/-- The actual real raw-minus-ordinary difference has a finite second moment. -/
theorem difference_memLp {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hQ : ∀ m w, 0 < Q m w) :
    MemLp (fun z ↦ (GlobalDraws.rawClock z : ℝ) -
      (numProposals (RawBridge.sourceProfile z) : ℝ)) 2 (rawInputLaw (fun _ ↦ a) Q) :=
  (memLp_congr_ae (ae_difference_eq_totalRepeats a Q ha hQ)).mpr
    (totalRepeats_memLp a Q ha hQ)

/-- The requested actual raw/ordinary mean correction, with explicit clock/rank cap errors. -/
theorem integral_difference_le {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    {A : ℝ} (hA : 0 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ))
    (haA : ∀ w, (a w : ℝ) ≤ A) (cap H : ℕ) :
    let μ := rawInputLaw (fun _ ↦ a) Q
    (∫ z, (GlobalDraws.rawClock z : ℝ) -
      (numProposals (RawBridge.sourceProfile z) : ℝ) ∂μ) ≤ (H : ℝ) * A * cap / n +
        Real.sqrt (∫ z, (GlobalDraws.rawClock z : ℝ) ^ 2 ∂μ) *
          Real.sqrt (μ.real {z | H < GlobalDraws.rawClock z} + μ.real (RankCap cap)ᶜ) := by
  have ha : ∀ w, 0 < a w := fun w ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (ha1 w)
  dsimp only
  rw [integral_congr_ae (ae_difference_eq_totalRepeats a Q ha hQ)]
  exact integral_totalRepeats_le a Q hQ hA ha1 haA cap H

/-- Numerical moment and tail bounds can be substituted without disguising them as proved tails. -/
theorem integral_difference_le_of_bounds {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    {A : ℝ} (hA : 0 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ))
    (haA : ∀ w, (a w : ℝ) ≤ A) (cap H : ℕ) (B δclock δrank : ℝ)
    (hmoment : (∫ z, (GlobalDraws.rawClock z : ℝ) ^ 2 ∂rawInputLaw (fun _ ↦ a) Q) ≤ B)
    (hclock : (rawInputLaw (fun _ ↦ a) Q).real {z | H < GlobalDraws.rawClock z} ≤ δclock)
    (hrank : (rawInputLaw (fun _ ↦ a) Q).real (RankCap cap)ᶜ ≤ δrank) :
    (∫ z, (GlobalDraws.rawClock z : ℝ) - (numProposals (RawBridge.sourceProfile z) : ℝ)
      ∂rawInputLaw (fun _ ↦ a) Q) ≤
      (H : ℝ) * A * cap / n + Real.sqrt B * Real.sqrt (δclock + δrank) := by
  apply (integral_difference_le a Q hQ hA ha1 haA cap H).trans
  apply add_le_add le_rfl
  exact mul_le_mul (Real.sqrt_le_sqrt hmoment)
    (Real.sqrt_le_sqrt (add_le_add hclock hrank)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- The checked coupon second moment supplies the correction's moment factor automatically. -/
theorem integral_difference_le_coupon_bound {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    {A : ℝ} (hA : 0 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ))
    (haA : ∀ w, (a w : ℝ) ≤ A) (cap H : ℕ) (δclock δrank : ℝ)
    (hclock : (rawInputLaw (fun _ ↦ a) Q).real {z | H < GlobalDraws.rawClock z} ≤ δclock)
    (hrank : (rawInputLaw (fun _ ↦ a) Q).real (RankCap cap)ᶜ ≤ δrank) :
    (∫ z, (GlobalDraws.rawClock z : ℝ) - (numProposals (RawBridge.sourceProfile z) : ℝ)
      ∂rawInputLaw (fun _ ↦ a) Q) ≤ (H : ℝ) * A * cap / n +
        Real.sqrt ((CouponMoments.totalWeight a * (harmonic n : ℝ)) ^ 2 +
          2 * CouponMoments.totalWeight a ^ 2) * Real.sqrt (δclock + δrank) := by
  apply integral_difference_le_of_bounds a Q hQ hA ha1 haA cap H _ δclock δrank _ hclock hrank
  exact GlobalDraws.rawClock_secondMoment_le a Q (fun w ↦ by exact_mod_cast ha1 w) hQ

/-- The actual raw rank-cap error is exactly a finite original PR-profile probability. -/
theorem rankCap_compl_measure_eq_profile {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hQ : ∀ m w, 0 < Q m w) (cap : ℕ) :
    rawInputLaw (fun _ ↦ a) Q (RankCap cap)ᶜ =
      (RandomRanking.profile (fun _ ↦ a) Q).toMeasure
        {p | ∃ m, cap < (deferredAcceptance p).next m} := by
  have he : (RankCap cap)ᶜ = RawBridge.sourceProfile ⁻¹'
      {p : Profile n | ∃ m, cap < (deferredAcceptance p).next m} := by
    ext z
    simp [RankCap, not_forall]
  rw [he, ← Measure.map_apply measurable_sourceProfile (by trivial),
    show RawBridge.sourceProfile = mixedRankProfile IIDRanking.iidRank exponentialRank from rfl,
    iid_raw_profile_law (fun _ ↦ a) Q (fun _ ↦ ha) hQ]

/-- The rank-error equality in the real-probability form used by moment corrections. -/
theorem rankCap_compl_real_eq_profile {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hQ : ∀ m w, 0 < Q m w) (cap : ℕ) :
    (rawInputLaw (fun _ ↦ a) Q).real (RankCap cap)ᶜ =
      ((RandomRanking.profile (fun _ ↦ a) Q).toMeasure
        {p | ∃ m, cap < (deferredAcceptance p).next m}).toReal := by
  exact congrArg ENNReal.toReal (rankCap_compl_measure_eq_profile a Q ha hQ cap)

/-- The raw-clock error is exactly the corresponding weighted iid coupon tail. -/
theorem clock_tail_measure_eq_coupon {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0)
    (hQ : ∀ m w, 0 < Q m w) (H : ℕ) :
    rawInputLaw (fun _ ↦ a) Q {z | H < GlobalDraws.rawClock z} =
      FirstFresh.iidStream (RandomRanking.ofWeights a) {x | H < CouponMoments.time x} := by
  change rawInputLaw (fun _ ↦ a) Q (GlobalDraws.rawClock ⁻¹' Set.Ioi H) =
    FirstFresh.iidStream (RandomRanking.ofWeights a) (CouponMoments.time ⁻¹' Set.Ioi H)
  rw [← Measure.map_apply measurable_rawClock measurableSet_Ioi,
    GlobalDraws.rawClock_law a Q hQ,
    Measure.map_apply CouponMoments.measurable_time measurableSet_Ioi]

/-- The actual raw-minus-ordinary correction is integrable in the usual real sense. -/
theorem integrable_difference {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hQ : ∀ m w, 0 < Q m w) :
    Integrable (fun z ↦ (GlobalDraws.rawClock z : ℝ) -
      (numProposals (RawBridge.sourceProfile z) : ℝ)) (rawInputLaw (fun _ ↦ a) Q) := by
  have := Raw.isProbabilityMeasure_rawInputLaw (fun _ ↦ a) Q hQ
  exact (difference_memLp a Q ha hQ).integrable one_le_two

end Ashlagi.RepeatMoments
