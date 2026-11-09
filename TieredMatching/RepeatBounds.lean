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

public import TieredMatching.RawKernel
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # Predictable repeat bounds under the actual raw input law

The exact raw destination kernel is summed over finite visible prefixes. Each repeat before
the genuine counter cap has mass at most the number of tried destinations times the largest
categorical mass. No terminal-count independence or reference bout law is used.
-/

@[expose] public section

namespace TieredMatching.RepeatBounds

open MeasureTheory StableMarriage TieredMatching.Raw
open scoped ENNReal NNReal

/-- All possible finite words at the fixed raw time. -/
noncomputable def histories (n t : ℕ) : Finset (List (Raw.Entry n)) := by
  classical
  exact Finset.univ.image (fun f : Fin t → Raw.Entry n ↦ List.ofFn f)

/-- These finite words are exactly the histories of the indicated length. -/
theorem mem_histories {n t : ℕ} (h : List (Raw.Entry n)) :
    h ∈ histories n t ↔ h.length = t := by
  classical
  constructor
  · intro hh
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hh
    exact List.length_ofFn
  · intro hh
    subst t
    exact Finset.mem_image.mpr ⟨h.get, Finset.mem_univ _, List.ofFn_get h⟩

/-- The predictable cap observes only genuine distinct proposal counters in the current past. -/
def BelowCap {n : ℕ} (cap : ℕ) (h : List (Raw.Entry n)) : Prop :=
  ∀ m, (Raw.state h).next m ≤ cap

/-- Women already tried by a fixed man, as a visible finite set. -/
noncomputable def tried {n : ℕ} (h : List (Raw.Entry n)) (m : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun w ↦ (w, m) ∈ Raw.seenEdges h

/-- The number of tried women is bounded by the genuine proposal counter even for bad words. -/
theorem card_tried_le {n : ℕ} (h : List (Raw.Entry n)) (m : Fin n) :
    (tried h m).card ≤ (Raw.state h).next m := by
  have he : tried h m = (Ordinal.manOrder (Raw.ordinary h) m).toFinset := by
    ext w
    simp only [tried, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
    exact (Ordinal.mem_manOrder_iff_seenEdges (Raw.ordinary h) w m).symm
  rw [he]
  exact (List.toFinset_card_le _).trans_eq (Ordinal.length_manOrder _ _)

/-- The actual repeated-next-entry event jointly with precisely the current prefix. -/
def repeatBranch {n : ℕ} (C : Raw.Protocol n) (h : List (Raw.Entry n)) : Set (Raw.Sources n) :=
  ⋃ q : Arrival.Edge n, Raw.historyEvent C (some (q, none) :: h)

/-- Repeat branches are measurable literal finite prefix fibers. -/
theorem measurableSet_repeatBranch {n : ℕ} (C : Raw.Protocol n) (h : List (Raw.Entry n)) :
    MeasurableSet (repeatBranch C h) := by
  exact MeasurableSet.iUnion fun q ↦ Raw.measurableSet_historyEvent C _

/-- Literal repeated children are exactly the actual repeated observation at the parent. -/
theorem mem_repeatBranch {n : ℕ} (C : Raw.Protocol n) (h : List (Raw.Entry n))
    (z : Raw.Sources n) : z ∈ repeatBranch C h ↔
      z ∈ Raw.historyEvent C h ∧
        ∃ q, Raw.observation C z.1 (Function.uncurry z.2) h = some (q, none) := by
  simp only [repeatBranch, Set.mem_iUnion]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨hh, he⟩ := (Raw.inputTranscript_cons_iff C z h _).mp hq
    exact ⟨hh, q, he⟩
  · rintro ⟨hh, q, he⟩
    exact ⟨q, (Raw.inputTranscript_cons_iff C z h _).mpr ⟨hh, he⟩⟩

/-- A paused protocol creates no raw repeat. -/
theorem repeatBranch_of_paused {n : ℕ} (C : Raw.Protocol n) (h : List (Raw.Entry n))
    (hs : Raw.selected C h = none) : repeatBranch C h = ∅ := by
  ext z
  simp only [mem_repeatBranch, Set.mem_empty_iff_false, iff_false, not_and]
  intro _
  simp [Raw.observation, Raw.nextEdge, hs]

/-- Under a visible selected man, repeated children range only over his already tried women. -/
theorem repeatBranch_eq_union {n : ℕ} (C : Raw.Protocol n) (h : List (Raw.Entry n))
    (m : Fin n) (hs : Raw.selected C h = some m) :
    repeatBranch C h = ⋃ w ∈ tried h m, Raw.historyEvent C (some ((w, m), none) :: h) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨hh, ⟨w, k⟩, hobs⟩ := (mem_repeatBranch C h z).mp hz
    have hx := (Raw.observation_eq_iff C z.1 (Function.uncurry z.2) h _).mp hobs
    have he : Raw.nextEdge C z.1 h = some (w, k) := hx.1
    have hm := Raw.nextEdge_map_man C z.1 h
    rw [he, Option.map_some, hs] at hm
    have hkm : k = m := Option.some.inj hm
    subst k
    have hseen : (w, m) ∈ Raw.seenEdges h := hx.2.1
    exact Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr
      ⟨by simp [tried, hseen], (Raw.inputTranscript_cons_iff C z h _).mpr ⟨hh, hobs⟩⟩⟩
  · intro hz
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hz
    obtain ⟨_, he⟩ := Set.mem_iUnion.mp hw
    exact Set.mem_iUnion.mpr ⟨(w, m), he⟩

/-- Exact raw prefix disintegration bounds a capped local repeat mass. -/
theorem repeatBranch_measure_le {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    (πmax : ℝ≥0∞) (hπ : ∀ w, RandomRanking.ofWeights a w ≤ πmax)
    (C : Raw.Protocol n) (h : List (Raw.Entry n)) (cap : ℕ) (hc : BelowCap cap h) :
    rawInputLaw (fun _ ↦ a) Q (repeatBranch C h) ≤
      (cap : ℝ≥0∞) * πmax * rawInputLaw (fun _ ↦ a) Q (Raw.historyEvent C h) := by
  classical
  cases hs : Raw.selected C h with
  | none => simp [repeatBranch_of_paused C h hs]
  | some m =>
    rw [repeatBranch_eq_union C h m hs]
    calc
      _ ≤ ∑ w ∈ tried h m,
          rawInputLaw (fun _ ↦ a) Q (Raw.historyEvent C (some ((w, m), none) :: h)) :=
        measure_biUnion_finset_le _ _
      _ = ∑ w ∈ tried h m,
          RandomRanking.ofWeights a w *
            rawInputLaw (fun _ ↦ a) Q (Raw.historyEvent C h) := by
        apply Finset.sum_congr rfl
        intro w hw
        exact Raw.extend_repeat_measure _ Q hQ C h w m hs (by simpa [tried] using hw)
      _ ≤ ∑ _w ∈ tried h m, πmax * rawInputLaw (fun _ ↦ a) Q (Raw.historyEvent C h) := by
        exact Finset.sum_le_sum fun w _ ↦ mul_le_mul_of_nonneg_right (hπ w) zero_le
      _ = ((tried h m).card : ℝ≥0∞) * πmax *
          rawInputLaw (fun _ ↦ a) Q (Raw.historyEvent C h) := by simp [mul_assoc]
      _ ≤ _ := by
        have hcard : ((tried h m).card : ℝ≥0∞) ≤ (cap : ℝ≥0∞) := by
          exact_mod_cast (card_tried_le h m).trans (hc m)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcard zero_le) zero_le

open scoped Classical in
/-- A capped repeat at a fixed actual raw time, partitioned by its finite visible past. -/
def cappedStepEvent {n : ℕ} (C : Raw.Protocol n) (cap t : ℕ) : Set (Raw.Sources n) :=
  ⋃ h ∈ histories n t, if BelowCap cap h then repeatBranch C h else ∅

/-- The uncapped repeat event at a fixed actual raw time. -/
def repeatStepEvent {n : ℕ} (C : Raw.Protocol n) (t : ℕ) : Set (Raw.Sources n) :=
  ⋃ h ∈ histories n t, repeatBranch C h

/-- Capping is predictable and only removes actual repeated next entries. -/
theorem mem_cappedStepEvent {n : ℕ} (C : Raw.Protocol n) (cap t : ℕ)
    (z : Raw.Sources n) : z ∈ cappedStepEvent C cap t ↔
      BelowCap cap (Raw.inputTranscript C t z) ∧ z ∈ repeatStepEvent C t := by
  classical
  have hlen : (Raw.inputTranscript C t z).length = t := Raw.transcript_length _ _ _ _
  simp only [cappedStepEvent, repeatStepEvent, Set.mem_iUnion]
  constructor
  · rintro ⟨h, hh, hz⟩
    by_cases hc : BelowCap cap h
    · rw [ite_eq_left hc] at hz
      have he : Raw.inputTranscript C t z = h := by
        have := ((mem_repeatBranch C h z).mp hz).1
        simpa only [Raw.historyEvent, Set.mem_ofPred_eq, (mem_histories h).mp hh] using this
      exact ⟨he.symm ▸ hc, h, hh, hz⟩
    · simp [hc] at hz
  · rintro ⟨hc, h, hh, hz⟩
    have he : Raw.inputTranscript C t z = h := by
      have := ((mem_repeatBranch C h z).mp hz).1
      simpa only [Raw.historyEvent, Set.mem_ofPred_eq, (mem_histories h).mp hh] using this
    have hc' : BelowCap cap h := he ▸ hc
    exact ⟨h, hh, by rw [ite_eq_left hc']; exact hz⟩

/-- Finite visible-prefix disintegration: the length-t history fibers partition total mass. -/
theorem sum_history_measure {n : ℕ} [NeZero n]
    (P Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    (C : Raw.Protocol n) (t : ℕ) :
    (∑ h ∈ histories n t, rawInputLaw P Q (Raw.historyEvent C h)) = 1 := by
  classical
  have := Raw.isProbabilityMeasure_rawInputLaw P Q hQ
  have hd : (histories n t : Set (List (Raw.Entry n))).PairwiseDisjoint
      (Raw.historyEvent C) := by
    intro h hh k hk hne
    apply Set.disjoint_left.mpr
    intro z hzh hzk
    have heh : Raw.inputTranscript C t z = h := by
      simpa only [Raw.historyEvent, Set.mem_ofPred_eq, (mem_histories h).mp hh] using hzh
    have hek : Raw.inputTranscript C t z = k := by
      simpa only [Raw.historyEvent, Set.mem_ofPred_eq, (mem_histories k).mp hk] using hzk
    exact hne (heh.symm.trans hek)
  rw [← measure_biUnion_finset hd (fun h _ ↦ Raw.measurableSet_historyEvent C h)]
  have hu : (⋃ h ∈ histories n t, Raw.historyEvent C h) = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hl : (Raw.inputTranscript C t z).length = t := Raw.transcript_length _ _ _ _
    exact ⟨Raw.inputTranscript C t z, (mem_histories _).mpr hl, by
      change Raw.inputTranscript C (Raw.inputTranscript C t z).length z = _
      rw [hl]⟩
  rw [hu, measure_univ]

/-- Capped repeat events are measurable unions of literal visible-prefix events. -/
theorem measurableSet_cappedStepEvent {n : ℕ} (C : Raw.Protocol n) (cap t : ℕ) :
    MeasurableSet (cappedStepEvent C cap t) := by
  classical
  apply MeasurableSet.iUnion
  intro h
  apply MeasurableSet.iUnion
  intro _
  split_ifs
  · exact measurableSet_repeatBranch C h
  · exact MeasurableSet.empty

/-- Uncapped repeat events are measurable finite next-entry observations. -/
theorem measurableSet_repeatStepEvent {n : ℕ} (C : Raw.Protocol n) (t : ℕ) :
    MeasurableSet (repeatStepEvent C t) :=
  MeasurableSet.iUnion fun h ↦ MeasurableSet.iUnion fun _ ↦ measurableSet_repeatBranch C h

/-- The actual unconditional predictable one-step repeat bound follows by prefix disintegration. -/
theorem cappedStep_measure_le {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    (πmax : ℝ≥0∞) (hπ : ∀ w, RandomRanking.ofWeights a w ≤ πmax)
    (C : Raw.Protocol n) (cap t : ℕ) :
    rawInputLaw (fun _ ↦ a) Q (cappedStepEvent C cap t) ≤ (cap : ℝ≥0∞) * πmax := by
  classical
  calc
    _ ≤ ∑ h ∈ histories n t, rawInputLaw (fun _ ↦ a) Q
        (if BelowCap cap h then repeatBranch C h else ∅) := measure_biUnion_finset_le _ _
    _ ≤ ∑ h ∈ histories n t, (cap : ℝ≥0∞) * πmax *
        rawInputLaw (fun _ ↦ a) Q (Raw.historyEvent C h) := by
      apply Finset.sum_le_sum
      intro h _
      by_cases hc : BelowCap cap h
      · rw [ite_eq_left hc]
        exact repeatBranch_measure_le a Q hQ πmax hπ C h cap hc
      · simp [hc]
    _ = _ := by
      rw [← Finset.mul_sum, sum_history_measure _ Q hQ C t, mul_one]

open scoped Classical in
/-- The actual number of repeated raw draws whose predictable current counters are below cap. -/
noncomputable def cappedRepeats {n : ℕ} (C : Raw.Protocol n) (cap H : ℕ)
    (z : Raw.Sources n) : ℕ :=
  ∑ t ∈ Finset.range H, if z ∈ cappedStepEvent C cap t then 1 else 0

open scoped Classical in
/-- The actual repeated raw draws up to the fixed raw horizon, with no cap. -/
noncomputable def repeats {n : ℕ} (C : Raw.Protocol n) (H : ℕ) (z : Raw.Sources n) : ℕ :=
  ∑ t ∈ Finset.range H, if z ∈ repeatStepEvent C t then 1 else 0

/-- The ENNReal count is the finite sum of actual predictable repeat indicators. -/
theorem cast_cappedRepeats {n : ℕ} (C : Raw.Protocol n) (cap H : ℕ) (z : Raw.Sources n) :
    (cappedRepeats C cap H z : ℝ≥0∞) =
      ∑ t ∈ Finset.range H, (cappedStepEvent C cap t).indicator (fun _ ↦ (1 : ℝ≥0∞)) z := by
  classical
  simp only [cappedRepeats, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : z ∈ cappedStepEvent C cap t <;> simp [ht]

/-- The actual predictable capped-repeat count is measurable. -/
theorem measurable_cast_cappedRepeats {n : ℕ} (C : Raw.Protocol n) (cap H : ℕ) :
    Measurable (fun z ↦ (cappedRepeats C cap H z : ℝ≥0∞)) := by
  simp_rw [cast_cappedRepeats]
  apply Finset.measurable_sum
  intro t _
  exact measurable_const.indicator (measurableSet_cappedStepEvent C cap t)

/-- Actual expected capped repeats: finite history disintegration plus linearity. -/
theorem lintegral_cappedRepeats_le {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    (πmax : ℝ≥0∞) (hπ : ∀ w, RandomRanking.ofWeights a w ≤ πmax)
    (C : Raw.Protocol n) (cap H : ℕ) :
    (∫⁻ z, (cappedRepeats C cap H z : ℝ≥0∞) ∂rawInputLaw (fun _ ↦ a) Q) ≤
      (H : ℝ≥0∞) * cap * πmax := by
  simp_rw [cast_cappedRepeats]
  rw [lintegral_finsetSum _ (fun t _ ↦
    measurable_const.indicator (measurableSet_cappedStepEvent C cap t))]
  simp_rw [lintegral_indicator_const (measurableSet_cappedStepEvent C cap _), one_mul]
  calc
    _ ≤ ∑ _t ∈ Finset.range H, (cap : ℝ≥0∞) * πmax :=
      Finset.sum_le_sum fun t _ ↦ cappedStep_measure_le a Q hQ πmax hπ C cap t
    _ = _ := by simp [mul_assoc]

/-- Markov's inequality for actual capped repeats under the unchanged raw source law. -/
theorem measure_cappedRepeats_ge_le {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    (πmax : ℝ≥0∞) (hπ : ∀ w, RandomRanking.ofWeights a w ≤ πmax)
    (C : Raw.Protocol n) (cap H : ℕ) (ε : ℝ≥0∞) (hε : ε ≠ 0) (hεtop : ε ≠ ∞) :
    rawInputLaw (fun _ ↦ a) Q {z | ε ≤ (cappedRepeats C cap H z : ℝ≥0∞)} ≤
      ((H : ℝ≥0∞) * cap * πmax) / ε := by
  exact (meas_ge_le_lintegral_div (measurable_cast_cappedRepeats C cap H).aemeasurable
    hε hεtop).trans (ENNReal.div_le_div_right
      (lintegral_cappedRepeats_le a Q hQ πmax hπ C cap H) ε)

/-- On the visible no-cap event, the predictable capped count equals the actual repeat count. -/
theorem cappedRepeats_eq_repeats_of_no_cap {n : ℕ} (C : Raw.Protocol n) (cap H : ℕ)
    (z : Raw.Sources n)
    (hc : ∀ t < H, BelowCap cap (Raw.inputTranscript C t z)) :
    cappedRepeats C cap H z = repeats C H z := by
  classical
  apply Finset.sum_congr rfl
  intro t ht
  have he : z ∈ cappedStepEvent C cap t ↔ z ∈ repeatStepEvent C t := by
    rw [mem_cappedStepEvent, and_iff_right (hc t (Finset.mem_range.mp ht))]
  simp only [he]

/-- Scores in [1,A] force every actual categorical mass to be at most A/n. -/
theorem categorical_le_score_ratio {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    {A : ℝ} (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A) (w : Fin n) :
    RandomRanking.ofWeights a w ≤ ENNReal.ofReal (A / n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hsum : (n : ℝ) ≤ ∑ v, (a v : ℝ) := by
    simpa using (Finset.sum_le_sum (s := Finset.univ) (fun v _ ↦ ha1 v))
  have hsumpos : 0 < ∑ v, a v := by
    exact_mod_cast lt_of_lt_of_le hn hsum
  rw [RandomRanking.ofWeights_apply a (ne_of_gt hsumpos),
    ← ENNReal.coe_div (ne_of_gt hsumpos)]
  have hratio : (a w : ℝ) / (∑ v, a v : ℝ≥0) ≤ A / n := by
    rw [NNReal.coe_sum]
    apply (div_le_div_of_nonneg_left (a w).coe_nonneg hn hsum).trans
    exact div_le_div_of_nonneg_right (haA w) hn.le
  have he : ((a w / ∑ v, a v : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal ((a w : ℝ) / (∑ v, a v : ℝ≥0)) := by
    simpa only [NNReal.coe_div] using
      (ENNReal.ofReal_coe_nnreal (p := a w / ∑ v, a v)).symm
  rw [he]
  exact ENNReal.ofReal_le_ofReal hratio

/-- The actual PR score bound gives E(capped raw repeats)<=H*A*cap/n. -/
theorem lintegral_cappedRepeats_le_scores {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    {A : ℝ} (ha1 : ∀ w, 1 ≤ (a w : ℝ))
    (haA : ∀ w, (a w : ℝ) ≤ A) (C : Raw.Protocol n) (cap H : ℕ) :
    (∫⁻ z, (cappedRepeats C cap H z : ℝ≥0∞) ∂rawInputLaw (fun _ ↦ a) Q) ≤
      ENNReal.ofReal ((H : ℝ) * A * cap / n) := by
  have hb := lintegral_cappedRepeats_le a Q hQ (ENNReal.ofReal (A / n))
    (categorical_le_score_ratio a ha1 haA) C cap H
  have he : (H : ℝ≥0∞) * cap * ENNReal.ofReal (A / n) =
      ENNReal.ofReal ((H : ℝ) * A * cap / n) := by
    rw [show (H : ℝ) * A * cap / n = (H : ℝ) * cap * (A / n) by ring,
      ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg H) (Nat.cast_nonneg cap)),
      ENNReal.ofReal_mul (Nat.cast_nonneg H), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast]
  exact hb.trans_eq he

/-- Each actual raw time contributes at most one predictable repeat. -/
theorem cappedRepeats_le_horizon {n : ℕ} (C : Raw.Protocol n) (cap H : ℕ)
    (z : Raw.Sources n) : cappedRepeats C cap H z ≤ H := by
  classical
  calc
    _ ≤ ∑ _t ∈ Finset.range H, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro t _
      split_ifs <;> omega
    _ = _ := by simp

/-- The actual real capped-repeat count is measurable. -/
theorem measurable_cappedRepeats_real {n : ℕ} (C : Raw.Protocol n) (cap H : ℕ) :
    Measurable (fun z ↦ (cappedRepeats C cap H z : ℝ)) := by
  simpa using (measurable_cast_cappedRepeats C cap H).ennreal_toReal

/-- Bounded fixed-horizon capped repeats have an ordinary finite real expectation. -/
theorem integrable_cappedRepeats {n : ℕ} (C : Raw.Protocol n) (cap H : ℕ)
    (μ : Measure (Raw.Sources n)) [IsFiniteMeasure μ] :
    Integrable (fun z ↦ (cappedRepeats C cap H z : ℝ)) μ := by
  apply Integrable.of_bound (measurable_cappedRepeats_real C cap H).aestronglyMeasurable H
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast cappedRepeats_le_horizon C cap H z

/-- The standard real expectation form of the actual capped raw repeat estimate. -/
theorem integral_cappedRepeats_le_scores {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    {A : ℝ} (hA : 0 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ))
    (haA : ∀ w, (a w : ℝ) ≤ A) (C : Raw.Protocol n) (cap H : ℕ) :
    (∫ z, (cappedRepeats C cap H z : ℝ) ∂rawInputLaw (fun _ ↦ a) Q) ≤
      (H : ℝ) * A * cap / n := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun z ↦
    Nat.cast_nonneg (cappedRepeats C cap H z)))
    (measurable_cappedRepeats_real C cap H).aestronglyMeasurable]
  simp only [ENNReal.ofReal_natCast]
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (lintegral_cappedRepeats_le_scores a Q hQ ha1 haA C cap H)
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (H : ℝ) * A * cap / n)] using hb

/-- Actual score-based Markov bound; all past dependence is retained in the count. -/
theorem measure_cappedRepeats_ge_le_scores {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    {A : ℝ} (ha1 : ∀ w, 1 ≤ (a w : ℝ))
    (haA : ∀ w, (a w : ℝ) ≤ A) (C : Raw.Protocol n) (cap H : ℕ)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) (hεtop : ε ≠ ∞) :
    rawInputLaw (fun _ ↦ a) Q {z | ε ≤ (cappedRepeats C cap H z : ℝ≥0∞)} ≤
      ENNReal.ofReal ((H : ℝ) * A * cap / n) / ε := by
  exact (meas_ge_le_lintegral_div (measurable_cast_cappedRepeats C cap H).aemeasurable
    hε hεtop).trans (ENNReal.div_le_div_right
      (lintegral_cappedRepeats_le_scores a Q hQ ha1 haA C cap H) ε)

/-- The uncapped step event literally observes a repeated draw in the actual current history. -/
theorem mem_repeatStepEvent {n : ℕ} (C : Raw.Protocol n) (t : ℕ) (z : Raw.Sources n) :
    z ∈ repeatStepEvent C t ↔ ∃ q, Raw.observation C z.1 (Function.uncurry z.2)
      (Raw.inputTranscript C t z) = some (q, none) := by
  constructor
  · intro hz
    obtain ⟨h, hh⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hh, he⟩ := Set.mem_iUnion.mp hh
    obtain ⟨hp, q, hq⟩ := (mem_repeatBranch C h z).mp he
    have hhist : Raw.inputTranscript C t z = h := by
      simpa only [Raw.historyEvent, Set.mem_ofPred_eq, (mem_histories h).mp hh] using hp
    exact ⟨q, by simpa only [hhist] using hq⟩
  · rintro ⟨q, hq⟩
    have hl : (Raw.inputTranscript C t z).length = t := Raw.transcript_length _ _ _ _
    apply Set.mem_iUnion.mpr
    refine ⟨Raw.inputTranscript C t z, Set.mem_iUnion.mpr ⟨(mem_histories _).mpr hl, ?_⟩⟩
    apply (mem_repeatBranch C _ z).mpr
    refine ⟨?_, q, hq⟩
    change Raw.inputTranscript C (Raw.inputTranscript C t z).length z = _
    rw [hl]

/-- The actual uncapped count is the sum of raw repeat-tag observations, not a reference law. -/
theorem repeats_eq_sum_observations {n : ℕ} (C : Raw.Protocol n) (H : ℕ)
    (z : Raw.Sources n) :
    repeats C H z = ∑ t ∈ Finset.range H,
      if ∃ q, Raw.observation C z.1 (Function.uncurry z.2) (Raw.inputTranscript C t z) =
        some (q, none) then 1 else 0 := by
  classical
  simp only [repeats, mem_repeatStepEvent]

/-- The predictable cap only removes repeats. -/
theorem cappedRepeats_le_repeats {n : ℕ} (C : Raw.Protocol n) (cap H : ℕ)
    (z : Raw.Sources n) : cappedRepeats C cap H z ≤ repeats C H z := by
  classical
  apply Finset.sum_le_sum
  intro t _
  by_cases hc : z ∈ cappedStepEvent C cap t
  · have hr := ((mem_cappedStepEvent C cap t z).mp hc).2
    simp [hc, hr]
  · simp [hc]

/-- The actual raw process stays below the genuine counter cap through the chosen horizon. -/
def NoCap {n : ℕ} (C : Raw.Protocol n) (cap H : ℕ) : Set (Raw.Sources n) :=
  {z | ∀ t < H, BelowCap cap (Raw.inputTranscript C t z)}

/-- The actual uncapped tail is bounded by cap failure plus the predictable compensator tail. -/
theorem measure_repeats_ge_le_cap_failure {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    {A : ℝ} (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (C : Raw.Protocol n) (cap H : ℕ) (ε : ℝ≥0∞) (hε : ε ≠ 0) (hεtop : ε ≠ ∞) :
    rawInputLaw (fun _ ↦ a) Q {z | ε ≤ (repeats C H z : ℝ≥0∞)} ≤
      rawInputLaw (fun _ ↦ a) Q (NoCap C cap H)ᶜ +
        ENNReal.ofReal ((H : ℝ) * A * cap / n) / ε := by
  have hsub : {z | ε ≤ (repeats C H z : ℝ≥0∞)} ⊆ (NoCap C cap H)ᶜ ∪
      {z | ε ≤ (cappedRepeats C cap H z : ℝ≥0∞)} := by
    intro z hz
    by_cases hc : z ∈ NoCap C cap H
    · apply Or.inr
      change ε ≤ (cappedRepeats C cap H z : ℝ≥0∞)
      rwa [cappedRepeats_eq_repeats_of_no_cap C cap H z hc]
    · exact Or.inl hc
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl (measure_cappedRepeats_ge_le_scores a Q hQ ha1 haA C cap H ε hε hεtop)))

end TieredMatching.RepeatBounds
