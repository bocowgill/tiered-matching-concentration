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

public import TieredMatching.RepeatBounds
public import Mathlib.Probability.Moments.Variance

/-! # Centered raw destination counts at deterministic horizons

The exact raw-history destination kernel gives zero centered conditional means. Finite history
partitions and literal past visibility give orthogonality without terminal-count independence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TieredMatching.DestinationMartingale

open StableMarriage Raw RepeatBounds

/-- The categorical destination probability in real form. -/
noncomputable def destinationProbability {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (w : Fin n) : ℝ := (RandomRanking.ofWeights a w).toReal

/-- A past-visible real statistic at a fixed raw clock. -/
noncomputable def past {n : ℕ} (C : Raw.Protocol n) (t : ℕ)
    (f : List (Raw.Entry n) → ℝ) (z : Raw.Sources n) : ℝ := f (Raw.inputTranscript C t z)

/-- Every actual finite raw history belongs to its fixed-time finite history set. -/
theorem current_mem_histories {n : ℕ} (C : Raw.Protocol n) (t : ℕ) (z : Raw.Sources n) :
    Raw.inputTranscript C t z ∈ histories n t :=
  (mem_histories _).mpr (Raw.transcript_length _ _ _ _)

/-- The history fibers at a fixed raw clock cover the whole source space. -/
theorem union_historyEvent {n : ℕ} (C : Raw.Protocol n) (t : ℕ) :
    (⋃ h ∈ histories n t, Raw.historyEvent C h) = Set.univ := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  refine ⟨Raw.inputTranscript C t z, current_mem_histories C t z, ?_⟩
  change Raw.inputTranscript C (Raw.inputTranscript C t z).length z = _
  rw [show (Raw.inputTranscript C t z).length = t from Raw.transcript_length _ _ _ _]

/-- Distinct fixed-time actual histories have disjoint source fibers. -/
theorem disjoint_historyEvent {n : ℕ} (C : Raw.Protocol n) (t : ℕ) :
    (histories n t : Set (List (Raw.Entry n))).PairwiseDisjoint (Raw.historyEvent C) := by
  intro h hh k hk hne
  change Disjoint (Raw.historyEvent C h) (Raw.historyEvent C k)
  rw [Set.disjoint_left]
  intro z hz hkz
  have heh : Raw.inputTranscript C t z = h := by
    simpa only [Raw.historyEvent, Set.mem_ofPred_eq, (mem_histories h).mp hh] using hz
  have hek : Raw.inputTranscript C t z = k := by
    simpa only [Raw.historyEvent, Set.mem_ofPred_eq, (mem_histories k).mp hk] using hkz
  exact hne (heh.symm.trans hek)

/-- Exact integration over the finite partition of actual raw histories. -/
theorem integral_history_sum {n : ℕ} (μ : Measure (Raw.Sources n)) (C : Raw.Protocol n)
    (t : ℕ) (f : Raw.Sources n → ℝ) (hf : Integrable f μ) :
    (∫ z, f z ∂μ) = ∑ h ∈ histories n t, ∫ z in Raw.historyEvent C h, f z ∂μ := by
  rw [← integral_biUnion_finset (histories n t)
    (fun h _ ↦ Raw.measurableSet_historyEvent C h) (disjoint_historyEvent C t)
      (fun _ _ ↦ hf.integrableOn), union_historyEvent, setIntegral_univ]

/-- A point in a fixed-time history fiber has precisely that actual observed past. -/
theorem transcript_eq_on_history {n : ℕ} (C : Raw.Protocol n) (t : ℕ)
    (h : List (Raw.Entry n)) (hh : h ∈ histories n t) (z : Raw.Sources n)
    (hz : z ∈ Raw.historyEvent C h) : Raw.inputTranscript C t z = h := by
  simpa only [Raw.historyEvent, Set.mem_ofPred_eq, (mem_histories h).mp hh] using hz

/-- Every past-visible statistic is a finite sum of literal history indicators. -/
theorem past_eq_sum {n : ℕ} (C : Raw.Protocol n) (t : ℕ) (f : List (Raw.Entry n) → ℝ) :
    past C t f = fun z ↦ ∑ h ∈ histories n t, (Raw.historyEvent C h).indicator (fun _ ↦ f h) z := by
  classical
  funext z
  symm
  rw [Finset.sum_eq_single (Raw.inputTranscript C t z)]
  · have hz : z ∈ Raw.historyEvent C (Raw.inputTranscript C t z) := by
      change Raw.inputTranscript C (Raw.inputTranscript C t z).length z = _
      rw [show (Raw.inputTranscript C t z).length = t from Raw.transcript_length _ _ _ _]
    rw [Set.indicator_of_mem hz]
    rfl
  · intro h hh hne
    rw [Set.indicator_of_notMem]
    exact fun hz ↦ hne (transcript_eq_on_history C t h hh z hz).symm
  · intro hnot
    exact False.elim (hnot (current_mem_histories C t z))

/-- Past-visible statistics are measurable even for arbitrary history functions. -/
theorem measurable_past {n : ℕ} (C : Raw.Protocol n) (t : ℕ)
    (f : List (Raw.Entry n) → ℝ) : Measurable (past C t f) := by
  rw [past_eq_sum]
  exact Finset.measurable_sum _ (fun h _ ↦ measurable_const.indicator
    (Raw.measurableSet_historyEvent C h))

/-- Every fixed-time past-visible statistic is square integrable under a finite source measure. -/
theorem memLp_past {n : ℕ} (μ : Measure (Raw.Sources n)) [IsFiniteMeasure μ]
    (C : Raw.Protocol n) (t : ℕ) (f : List (Raw.Entry n) → ℝ) : MemLp (past C t f) 2 μ := by
  apply MemLp.of_bound (measurable_past C t f).aestronglyMeasurable
    (∑ h ∈ histories n t, |f h|)
  apply ae_of_all
  intro z
  simpa only [past, Real.norm_eq_abs] using Finset.single_le_sum
    (fun h _ ↦ abs_nonneg (f h)) (current_mem_histories C t z)

/-- Dropping the newest records of an actual raw transcript returns its literal older prefix. -/
theorem inputTranscript_drop {n : ℕ} (C : Raw.Protocol n) (z : Raw.Sources n)
    (s t : ℕ) (hst : s ≤ t) :
    (Raw.inputTranscript C t z).drop (t - s) = Raw.inputTranscript C s z := by
  induction t with
  | zero =>
    have hs : s = 0 := by omega
    subst s
    rfl
  | succ t ih =>
    by_cases hs : s = t + 1
    · subst s
      simp
    · have hst' : s ≤ t := by omega
      have hsub : t + 1 - s = (t - s) + 1 := by omega
      change (Raw.observation C z.1 (Function.uncurry z.2) (Raw.inputTranscript C t z) ::
        Raw.inputTranscript C t z).drop (t + 1 - s) = _
      rw [hsub, List.drop_succ_cons, ih hst']

open scoped Classical in
/-- Whether an actual raw edge comes from the chosen men's subset; pauses count zero. -/
def tierValue {n : ℕ} (J : Finset (Fin n)) : Option (Arrival.Edge n) → ℕ
  | none => 0
  | some (_, m) => if m ∈ J then 1 else 0

open scoped Classical in
/-- Whether an actual raw edge comes from that subset and visits the specified woman. -/
def womanValue {n : ℕ} (J : Finset (Fin n)) (w : Fin n) : Option (Arrival.Edge n) → ℕ
  | none => 0
  | some (v, m) => if m ∈ J ∧ v = w then 1 else 0

/-- One centered categorical destination increment; repeated proposals are included. -/
noncomputable def edgeValue {n : ℕ} (J : Finset (Fin n)) (w : Fin n) (q : ℝ)
    (e : Option (Arrival.Edge n)) : ℝ := (womanValue J w e : ℝ) - q * tierValue J e

/-- The actual next-edge centered increment after a fixed visible raw history. -/
noncomputable def localIncrement {n : ℕ} (C : Raw.Protocol n) (J : Finset (Fin n))
    (w : Fin n) (q : ℝ) (h : List (Raw.Entry n)) (z : Raw.Sources n) : ℝ :=
  edgeValue J w q (Raw.nextEdge C z.1 h)

/-- The centered increment at the actual raw clock t. -/
noncomputable def increment {n : ℕ} (C : Raw.Protocol n) (J : Finset (Fin n))
    (w : Fin n) (q : ℝ) (t : ℕ) (z : Raw.Sources n) : ℝ :=
  localIncrement C J w q (Raw.inputTranscript C t z) z

/-- A record retains exactly the edge used by the centered increment. -/
noncomputable def historyValue {n : ℕ} (J : Finset (Fin n)) (w : Fin n) (q : ℝ) :
    List (Raw.Entry n) → ℝ
  | [] => 0
  | entry :: _ => edgeValue J w q (entry.map Prod.fst)

/-- The observable raw record's edge projection is exactly the actual next edge. -/
theorem observation_map_edge {n : ℕ} (C : Raw.Protocol n) (streams : Fin n → ℕ → Fin n)
    (female : Arrival.Edge n → ℝ) (h : List (Raw.Entry n)) :
    (Raw.observation C streams female h).map Prod.fst = Raw.nextEdge C streams h := by
  cases he : Raw.nextEdge C streams h <;> simp [Raw.observation, he]

/-- An increment is already visible in the next actual raw transcript. -/
theorem increment_eq_past {n : ℕ} (C : Raw.Protocol n) (J : Finset (Fin n))
    (w : Fin n) (q : ℝ) (t : ℕ) :
    increment C J w q t = past C (t + 1) (historyValue J w q) := by
  funext z
  change edgeValue J w q (Raw.nextEdge C z.1 (Raw.inputTranscript C t z)) =
    edgeValue J w q ((Raw.observation C z.1 (Function.uncurry z.2)
      (Raw.inputTranscript C t z)).map Prod.fst)
  rw [observation_map_edge]

/-- Earlier centered increments are functions only of any later revealed history. -/
theorem increment_eq_later_past {n : ℕ} (C : Raw.Protocol n) (J : Finset (Fin n))
    (w : Fin n) (q : ℝ) (s t : ℕ) (hst : s < t) :
    increment C J w q s = past C t (fun h ↦ historyValue J w q (h.drop (t - (s + 1)))) := by
  rw [increment_eq_past]
  funext z
  simp only [past, inputTranscript_drop C z (s + 1) t (by omega)]

/-- Actual centered increments are square integrable at each finite time. -/
theorem memLp_increment {n : ℕ} (μ : Measure (Raw.Sources n)) [IsFiniteMeasure μ]
    (C : Raw.Protocol n) (J : Finset (Fin n)) (w : Fin n) (q : ℝ) (t : ℕ) :
    MemLp (increment C J w q t) 2 μ := by
  rw [increment_eq_past]
  exact memLp_past μ C (t + 1) _

/-- The real categorical mass lies in the unit interval. -/
theorem destinationProbability_mem_Icc {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (w : Fin n) : destinationProbability a w ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  exact ENNReal.toReal_le_of_le_ofReal (by simp) (by
    simpa using (PMF.coe_le_one (RandomRanking.ofWeights a) w))

/-- The next destination event after a fixed past. -/
def destinationEvent {n : ℕ} (C : Raw.Protocol n) (h : List (Raw.Entry n))
    (w m : Fin n) : Set (Raw.Sources n) := {z | Raw.nextEdge C z.1 h = some (w, m)}

/-- A selected next-destination event is a measurable, still-unread male coordinate. -/
theorem measurableSet_destinationEvent {n : ℕ} (C : Raw.Protocol n)
    (h : List (Raw.Entry n)) (w m : Fin n) (hs : Raw.selected C h = some m) :
    MeasurableSet (destinationEvent C h w m) := by
  have he : destinationEvent C h w m = {z | z.1 m (Raw.rawCounter h m) = w} := by
    ext z
    simp [destinationEvent, Raw.nextEdge, hs]
  rw [he]
  exact measurableSet_eq_fun ((measurable_pi_apply (Raw.rawCounter h m)).comp
    ((measurable_pi_apply m).comp measurable_fst)) measurable_const

/-- On a selected tier member, the local increment is the centered destination indicator. -/
theorem localIncrement_of_selected {n : ℕ} (C : Raw.Protocol n) (J : Finset (Fin n))
    (w : Fin n) (q : ℝ) (h : List (Raw.Entry n)) (m : Fin n)
    (hs : Raw.selected C h = some m) (hm : m ∈ J) :
    localIncrement C J w q h = fun z ↦
      (destinationEvent C h w m).indicator (fun _ ↦ (1 : ℝ)) z - q := by
  classical
  funext z
  by_cases he : z.1 m (Raw.rawCounter h m) = w
  · simp [localIncrement, edgeValue, womanValue, tierValue, Raw.nextEdge, hs, hm, he,
      destinationEvent, Set.indicator]
  · simp [localIncrement, edgeValue, womanValue, tierValue, Raw.nextEdge, hs, hm, he,
      destinationEvent, Set.indicator]

/-- A paused protocol creates no centered draw. -/
theorem localIncrement_of_paused {n : ℕ} (C : Raw.Protocol n) (J : Finset (Fin n))
    (w : Fin n) (q : ℝ) (h : List (Raw.Entry n)) (hs : Raw.selected C h = none) :
    localIncrement C J w q h = 0 := by
  funext z
  simp [localIncrement, Raw.nextEdge, hs, edgeValue, womanValue, tierValue]

/-- Selecting a man outside the fixed subset creates no centered tier draw. -/
theorem localIncrement_of_not_mem {n : ℕ} (C : Raw.Protocol n) (J : Finset (Fin n))
    (w : Fin n) (q : ℝ) (h : List (Raw.Entry n)) (m : Fin n)
    (hs : Raw.selected C h = some m) (hm : m ∉ J) :
    localIncrement C J w q h = 0 := by
  funext z
  simp [localIncrement, Raw.nextEdge, hs, edgeValue, womanValue, tierValue, hm]

/-- The fixed-history centered increment is square integrable. -/
theorem memLp_localIncrement {n : ℕ} (μ : Measure (Raw.Sources n)) [IsFiniteMeasure μ]
    (C : Raw.Protocol n) (J : Finset (Fin n)) (w : Fin n) (q : ℝ)
    (h : List (Raw.Entry n)) : MemLp (localIncrement C J w q h) 2 μ := by
  classical
  cases hs : Raw.selected C h with
  | none => rw [localIncrement_of_paused C J w q h hs]; exact memLp_const 0
  | some m =>
    by_cases hm : m ∈ J
    · rw [localIncrement_of_selected C J w q h m hs hm]
      exact ((memLp_const (1 : ℝ)).indicator
        (measurableSet_destinationEvent C h w m hs).nullMeasurableSet).sub (memLp_const q)
    · rw [localIncrement_of_not_mem C J w q h m hs hm]; exact memLp_const 0

/-- Real form of the exact fixed-history destination kernel. -/
theorem destination_joint_real {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) (C : Raw.Protocol n)
    (h : List (Raw.Entry n)) (w m : Fin n) (hs : Raw.selected C h = some m) :
    (rawInputLaw (fun _ ↦ a) Q).real (destinationEvent C h w m ∩ Raw.historyEvent C h) =
      destinationProbability a w * (rawInputLaw (fun _ ↦ a) Q).real (Raw.historyEvent C h) := by
  have he : destinationEvent C h w m ∩ Raw.historyEvent C h =
      {z | z ∈ Raw.historyEvent C h ∧ Raw.nextEdge C z.1 h = some (w, m)} := by
    ext z
    simp only [Set.mem_inter_iff, destinationEvent, Set.mem_ofPred_eq]
    exact and_comm
  simp only [Measure.real, he, Raw.next_destination_measure _ Q hQ C h w m hs,
    ENNReal.toReal_mul, destinationProbability]

/-- The destination indicator integrates to its categorical mass times the history mass. -/
theorem indicator_integral_history {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) (C : Raw.Protocol n)
    (h : List (Raw.Entry n)) (w m : Fin n) (hs : Raw.selected C h = some m) :
    (∫ z in Raw.historyEvent C h,
      (destinationEvent C h w m).indicator (fun _ ↦ (1 : ℝ)) z
      ∂rawInputLaw (fun _ ↦ a) Q) =
      destinationProbability a w * (rawInputLaw (fun _ ↦ a) Q).real (Raw.historyEvent C h) := by
  rw [integral_indicator_const _ (measurableSet_destinationEvent C h w m hs),
    measureReal_restrict_apply (measurableSet_destinationEvent C h w m hs), smul_eq_mul,
    mul_one]
  exact destination_joint_real a Q hQ C h w m hs

/-- The actual destination kernel gives zero centered mean on every literal raw-history fiber. -/
theorem local_mean_zero {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) (C : Raw.Protocol n)
    (J : Finset (Fin n)) (w : Fin n) (h : List (Raw.Entry n)) :
    (∫ z in Raw.historyEvent C h, localIncrement C J w (destinationProbability a w) h z
      ∂rawInputLaw (fun _ ↦ a) Q) = 0 := by
  have : IsProbabilityMeasure (rawInputLaw (fun _ ↦ a) Q) :=
    Raw.isProbabilityMeasure_rawInputLaw _ Q hQ
  classical
  cases hs : Raw.selected C h with
  | none => rw [localIncrement_of_paused C J w _ h hs]; simp
  | some m =>
    by_cases hm : m ∈ J
    · rw [localIncrement_of_selected C J w _ h m hs hm, integral_sub]
      · rw [indicator_integral_history a Q hQ C h w m hs, setIntegral_const, smul_eq_mul]
        ring
      · exact ((integrable_const (1 : ℝ)).indicator
          (measurableSet_destinationEvent C h w m hs)).integrableOn
      · exact integrable_const _
    · rw [localIncrement_of_not_mem C J w _ h m hs hm]; simp

/-- The exact fixed-history second moment when a man from the subset is selected. -/
theorem local_second_moment {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) (C : Raw.Protocol n)
    (J : Finset (Fin n)) (w : Fin n) (h : List (Raw.Entry n)) (m : Fin n)
    (hs : Raw.selected C h = some m) (hm : m ∈ J) :
    (∫ z in Raw.historyEvent C h, (localIncrement C J w (destinationProbability a w) h z)^2
      ∂rawInputLaw (fun _ ↦ a) Q) =
      destinationProbability a w * (1 - destinationProbability a w) *
        (rawInputLaw (fun _ ↦ a) Q).real (Raw.historyEvent C h) := by
  have : IsProbabilityMeasure (rawInputLaw (fun _ ↦ a) Q) :=
    Raw.isProbabilityMeasure_rawInputLaw _ Q hQ
  classical
  let q := destinationProbability a w
  let I : Raw.Sources n → ℝ := (destinationEvent C h w m).indicator (fun _ ↦ 1)
  have hI : Integrable I (rawInputLaw (fun _ ↦ a) Q) :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_destinationEvent C h w m hs)
  have he : (fun z ↦ (localIncrement C J w q h z)^2) =
      fun z ↦ (1 - 2 * q) * I z + q^2 := by
    rw [localIncrement_of_selected C J w q h m hs hm]
    funext z
    by_cases hz : z ∈ destinationEvent C h w m <;> simp [I, hz]
    ring
  rw [he, integral_add (hI.const_mul _).integrableOn (integrable_const _),
    integral_const_mul, indicator_integral_history a Q hQ C h w m hs,
    setIntegral_const, smul_eq_mul]
  dsimp [q]
  ring

/-- A local second moment is bounded by the categorical mass times its history mass. -/
theorem local_second_moment_le {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) (C : Raw.Protocol n)
    (J : Finset (Fin n)) (w : Fin n) (h : List (Raw.Entry n)) :
    (∫ z in Raw.historyEvent C h, (localIncrement C J w (destinationProbability a w) h z)^2
      ∂rawInputLaw (fun _ ↦ a) Q) ≤
      destinationProbability a w * (rawInputLaw (fun _ ↦ a) Q).real (Raw.historyEvent C h) := by
  classical
  have hq := (destinationProbability_mem_Icc a w).1
  have hmass : 0 ≤ (rawInputLaw (fun _ ↦ a) Q).real (Raw.historyEvent C h) :=
    ENNReal.toReal_nonneg
  cases hs : Raw.selected C h with
  | none => rw [localIncrement_of_paused C J w _ h hs]; simp; positivity
  | some m =>
    by_cases hm : m ∈ J
    · rw [local_second_moment a Q hQ C J w h m hs hm]
      exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (destinationProbability a w)])
        hmass
    · rw [localIncrement_of_not_mem C J w _ h m hs hm]; simp; positivity

/-- Multiplication by any visible past statistic preserves the zero mean of the next draw. -/
theorem past_mul_increment_integral_zero {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) (C : Raw.Protocol n)
    (J : Finset (Fin n)) (w : Fin n) (t : ℕ) (f : List (Raw.Entry n) → ℝ) :
    (∫ z, past C t f z * increment C J w (destinationProbability a w) t z
      ∂rawInputLaw (fun _ ↦ a) Q) = 0 := by
  have : IsProbabilityMeasure (rawInputLaw (fun _ ↦ a) Q) :=
    Raw.isProbabilityMeasure_rawInputLaw _ Q hQ
  rw [integral_history_sum _ C t (fun z ↦ past C t f z *
    increment C J w (destinationProbability a w) t z)
    ((memLp_past _ C t f).integrable_mul (memLp_increment _ C J w _ t))]
  apply Finset.sum_eq_zero
  intro h hh
  calc
    _ = ∫ z in Raw.historyEvent C h,
        f h * localIncrement C J w (destinationProbability a w) h z
        ∂rawInputLaw (fun _ ↦ a) Q := by
      apply setIntegral_congr_fun (Raw.measurableSet_historyEvent C h)
      intro z hz
      change f (Raw.inputTranscript C t z) *
        localIncrement C J w _ (Raw.inputTranscript C t z) z = _
      rw [transcript_eq_on_history C t h hh z hz]
    _ = 0 := by rw [integral_const_mul, local_mean_zero a Q hQ C J w h, mul_zero]

/-- Each actual centered raw destination increment has mean zero. -/
theorem increment_integral_zero {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) (C : Raw.Protocol n)
    (J : Finset (Fin n)) (w : Fin n) (t : ℕ) :
    (∫ z, increment C J w (destinationProbability a w) t z
      ∂rawInputLaw (fun _ ↦ a) Q) = 0 := by
  simpa [past] using past_mul_increment_integral_zero a Q hQ C J w t (fun _ ↦ 1)

/-- Distinct actual raw increments are orthogonal because the earlier draw is past-visible. -/
theorem increment_cross_integral_zero {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) (C : Raw.Protocol n)
    (J : Finset (Fin n)) (w : Fin n) (s t : ℕ) (hst : s ≠ t) :
    (∫ z, increment C J w (destinationProbability a w) s z *
      increment C J w (destinationProbability a w) t z ∂rawInputLaw (fun _ ↦ a) Q) = 0 := by
  rcases lt_or_gt_of_ne hst with hlt | hlt
  · rw [increment_eq_later_past C J w _ s t hlt]
    exact past_mul_increment_integral_zero a Q hQ C J w t _
  · rw [show (fun z ↦ increment C J w (destinationProbability a w) s z *
        increment C J w (destinationProbability a w) t z) =
        (fun z ↦ increment C J w (destinationProbability a w) t z *
          increment C J w (destinationProbability a w) s z) from funext (fun _ ↦ mul_comm _ _)]
    rw [increment_eq_later_past C J w _ t s hlt]
    exact past_mul_increment_integral_zero a Q hQ C J w s _

/-- The finite history masses also sum to one in real form. -/
theorem sum_history_real {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) (C : Raw.Protocol n) (t : ℕ) :
    ∑ h ∈ histories n t, (rawInputLaw (fun _ ↦ a) Q).real (Raw.historyEvent C h) = 1 := by
  have : IsProbabilityMeasure (rawInputLaw (fun _ ↦ a) Q) :=
    Raw.isProbabilityMeasure_rawInputLaw _ Q hQ
  have he := congrArg ENNReal.toReal (sum_history_measure (fun _ ↦ a) Q hQ C t)
  rw [ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _)] at he
  exact he

/-- The second moment of a single actual raw increment is at most the destination mass. -/
theorem increment_second_moment_le {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) (C : Raw.Protocol n)
    (J : Finset (Fin n)) (w : Fin n) (t : ℕ) :
    (∫ z, (increment C J w (destinationProbability a w) t z)^2
      ∂rawInputLaw (fun _ ↦ a) Q) ≤ destinationProbability a w := by
  have : IsProbabilityMeasure (rawInputLaw (fun _ ↦ a) Q) :=
    Raw.isProbabilityMeasure_rawInputLaw _ Q hQ
  have h2 := memLp_increment (rawInputLaw (fun _ ↦ a) Q) C J w
    (destinationProbability a w) t
  rw [integral_history_sum _ C t _ h2.integrable_sq]
  calc
    _ ≤ ∑ h ∈ histories n t, destinationProbability a w *
        (rawInputLaw (fun _ ↦ a) Q).real (Raw.historyEvent C h) := by
      apply Finset.sum_le_sum
      intro h hh
      calc
        _ = ∫ z in Raw.historyEvent C h,
            (localIncrement C J w (destinationProbability a w) h z)^2
            ∂rawInputLaw (fun _ ↦ a) Q := by
          apply setIntegral_congr_fun (Raw.measurableSet_historyEvent C h)
          intro z hz
          change (localIncrement C J w _ (Raw.inputTranscript C t z) z)^2 = _
          rw [transcript_eq_on_history C t h hh z hz]
        _ ≤ _ := local_second_moment_le a Q hQ C J w h
    _ = _ := by rw [← Finset.mul_sum, sum_history_real a Q hQ C t, mul_one]

/-- The centered raw destination total up to a deterministic raw horizon. -/
noncomputable def centeredSum {n : ℕ} (C : Raw.Protocol n) (J : Finset (Fin n))
    (w : Fin n) (q : ℝ) (H : ℕ) (z : Raw.Sources n) : ℝ :=
  ∑ t ∈ Finset.range H, increment C J w q t z

/-- A finite actual centered total is square integrable. -/
theorem memLp_centeredSum {n : ℕ} (μ : Measure (Raw.Sources n)) [IsFiniteMeasure μ]
    (C : Raw.Protocol n) (J : Finset (Fin n)) (w : Fin n) (q : ℝ) (H : ℕ) :
    MemLp (centeredSum C J w q H) 2 μ :=
  memLp_finsetSum _ (fun t _ ↦ memLp_increment μ C J w q t)

/-- An actual centered destination total has zero mean at each deterministic horizon. -/
theorem centeredSum_integral_zero {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) (C : Raw.Protocol n)
    (J : Finset (Fin n)) (w : Fin n) (H : ℕ) :
    (∫ z, centeredSum C J w (destinationProbability a w) H z
      ∂rawInputLaw (fun _ ↦ a) Q) = 0 := by
  have : IsProbabilityMeasure (rawInputLaw (fun _ ↦ a) Q) :=
    Raw.isProbabilityMeasure_rawInputLaw _ Q hQ
  change (∫ z, ∑ t ∈ Finset.range H,
    increment C J w (destinationProbability a w) t z ∂rawInputLaw (fun _ ↦ a) Q) = 0
  rw [integral_finsetSum (Finset.range H) (fun t _ ↦
    (memLp_increment _ C J w (destinationProbability a w) t).integrable (by norm_num))]
  simp only [increment_integral_zero a Q hQ C J w, Finset.sum_const_zero]

/-- The centered past total is orthogonal to the next actual centered raw draw. -/
theorem centeredSum_mul_next_integral_zero {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) (C : Raw.Protocol n)
    (J : Finset (Fin n)) (w : Fin n) (H : ℕ) :
    (∫ z, centeredSum C J w (destinationProbability a w) H z *
      increment C J w (destinationProbability a w) H z ∂rawInputLaw (fun _ ↦ a) Q) = 0 := by
  have : IsProbabilityMeasure (rawInputLaw (fun _ ↦ a) Q) :=
    Raw.isProbabilityMeasure_rawInputLaw _ Q hQ
  simp only [centeredSum, Finset.sum_mul]
  rw [integral_finsetSum (Finset.range H)
    (f := fun t z ↦ increment C J w (destinationProbability a w) t z *
      increment C J w (destinationProbability a w) H z) (fun t _ ↦
    (memLp_increment _ C J w _ t).integrable_mul (memLp_increment _ C J w _ H))]
  apply Finset.sum_eq_zero
  intro t ht
  exact increment_cross_integral_zero a Q hQ C J w t H (Nat.ne_of_lt (Finset.mem_range.mp ht))

/-- Orthogonality makes the second moment of the actual total the sum of its diagonal moments. -/
theorem centeredSum_second_moment_eq {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) (C : Raw.Protocol n)
    (J : Finset (Fin n)) (w : Fin n) (H : ℕ) :
    (∫ z, (centeredSum C J w (destinationProbability a w) H z)^2
      ∂rawInputLaw (fun _ ↦ a) Q) =
      ∑ t ∈ Finset.range H, ∫ z, (increment C J w (destinationProbability a w) t z)^2
        ∂rawInputLaw (fun _ ↦ a) Q := by
  have : IsProbabilityMeasure (rawInputLaw (fun _ ↦ a) Q) :=
    Raw.isProbabilityMeasure_rawInputLaw _ Q hQ
  induction H with
  | zero => simp [centeredSum]
  | succ H ih =>
    have hs := memLp_centeredSum (rawInputLaw (fun _ ↦ a) Q) C J w
      (destinationProbability a w) H
    have hd := memLp_increment (rawInputLaw (fun _ ↦ a) Q) C J w
      (destinationProbability a w) H
    have hs2 := hs.integrable_sq
    have hd2 := hd.integrable_sq
    have hsd : Integrable (fun z ↦ centeredSum C J w (destinationProbability a w) H z *
        increment C J w (destinationProbability a w) H z)
        (rawInputLaw (fun _ ↦ a) Q) := hs.integrable_mul hd
    have he : (fun z ↦ (centeredSum C J w (destinationProbability a w) (H + 1) z)^2) =
        fun z ↦ (centeredSum C J w (destinationProbability a w) H z)^2 +
          2 * (centeredSum C J w (destinationProbability a w) H z *
            increment C J w (destinationProbability a w) H z) +
              (increment C J w (destinationProbability a w) H z)^2 := by
      funext z
      simp only [centeredSum, Finset.sum_range_succ]
      ring
    rw [he, integral_add (f := fun z ↦
        (centeredSum C J w (destinationProbability a w) H z)^2 +
          2 * (centeredSum C J w (destinationProbability a w) H z *
            increment C J w (destinationProbability a w) H z))
        (g := fun z ↦ (increment C J w (destinationProbability a w) H z)^2)
        (hs2.add (hsd.const_mul 2)) hd2,
      integral_add hs2 (hsd.const_mul 2), integral_const_mul,
      centeredSum_mul_next_integral_zero a Q hQ C J w H, mul_zero, add_zero, ih,
      Finset.sum_range_succ]

/-- The actual raw centered total has second moment at most horizon times destination mass. -/
theorem centeredSum_second_moment_le {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) (C : Raw.Protocol n)
    (J : Finset (Fin n)) (w : Fin n) (H : ℕ) :
    (∫ z, (centeredSum C J w (destinationProbability a w) H z)^2
      ∂rawInputLaw (fun _ ↦ a) Q) ≤ (H : ℝ) * destinationProbability a w := by
  rw [centeredSum_second_moment_eq a Q hQ C J w H]
  calc
    _ ≤ ∑ _t ∈ Finset.range H, destinationProbability a w :=
      Finset.sum_le_sum fun t _ ↦ increment_second_moment_le a Q hQ C J w t
    _ = _ := by simp

/-- All raw draws made by the chosen men up to a fixed horizon, including repeats. -/
noncomputable def rawTierCount {n : ℕ} (C : Raw.Protocol n) (J : Finset (Fin n))
    (H : ℕ) (z : Raw.Sources n) : ℕ :=
  ∑ t ∈ Finset.range H, tierValue J (Raw.nextEdge C z.1 (Raw.inputTranscript C t z))

/-- All raw draws from the chosen men to one woman, including repeats. -/
noncomputable def rawWomanTierCount {n : ℕ} (C : Raw.Protocol n) (J : Finset (Fin n))
    (w : Fin n) (H : ℕ) (z : Raw.Sources n) : ℕ :=
  ∑ t ∈ Finset.range H, womanValue J w (Raw.nextEdge C z.1 (Raw.inputTranscript C t z))

/-- A raw record adds one subset draw precisely when its proposing man lies in the subset. -/
theorem rawCounter_sum_cons {n : ℕ} (J : Finset (Fin n)) (h : List (Raw.Entry n))
    (entry : Raw.Entry n) :
    (∑ m ∈ J, Raw.rawCounter (entry :: h) m) =
      (∑ m ∈ J, Raw.rawCounter h m) + tierValue J (entry.map Prod.fst) := by
  classical
  cases entry with
  | none => simp [Raw.rawCounter, Raw.drawOrder, tierValue]
  | some entry =>
    rcases entry with ⟨⟨v, k⟩, tag⟩
    simp [Raw.rawCounter_record, Finset.sum_add_distrib, tierValue]

/-- A raw record adds one occurrence at its destination precisely for the chosen men's subset. -/
theorem drawOrder_count_sum_cons {n : ℕ} (J : Finset (Fin n)) (w : Fin n)
    (h : List (Raw.Entry n)) (entry : Raw.Entry n) :
    (∑ m ∈ J, (Raw.drawOrder (entry :: h) m).count w) =
      (∑ m ∈ J, (Raw.drawOrder h m).count w) + womanValue J w (entry.map Prod.fst) := by
  classical
  cases entry with
  | none => simp [Raw.drawOrder, womanValue]
  | some entry =>
    rcases entry with ⟨⟨v, k⟩, tag⟩
    have he (m : Fin n) :
        (Raw.drawOrder (some ((v, k), tag) :: h) m).count w =
          (Raw.drawOrder h m).count w + if k = m ∧ v = w then 1 else 0 := by
      by_cases hm : k = m <;>
        simp [Raw.drawOrder, hm, List.count_append, List.count_singleton]
    simp only [he, Finset.sum_add_distrib, Option.map_some, womanValue]
    by_cases hv : v = w <;> simp [hv]

/-- The time-sum tier count is exactly the total number of consumed male stream coordinates. -/
theorem rawTierCount_eq_rawCounter_sum {n : ℕ} (C : Raw.Protocol n)
    (J : Finset (Fin n)) (H : ℕ) (z : Raw.Sources n) :
    rawTierCount C J H z = ∑ m ∈ J, Raw.rawCounter (Raw.inputTranscript C H z) m := by
  induction H with
  | zero => simp [rawTierCount, Raw.inputTranscript, Raw.transcript, Raw.rawCounter, Raw.drawOrder]
  | succ H ih =>
    change (∑ t ∈ Finset.range (H + 1),
      tierValue J (Raw.nextEdge C z.1 (Raw.inputTranscript C t z))) =
        ∑ m ∈ J, Raw.rawCounter (Raw.observation C z.1 (Function.uncurry z.2)
          (Raw.inputTranscript C H z) :: Raw.inputTranscript C H z) m
    rw [Finset.sum_range_succ, rawCounter_sum_cons, observation_map_edge]
    exact congrArg (fun k ↦ k + tierValue J
      (Raw.nextEdge C z.1 (Raw.inputTranscript C H z))) ih

/-- The time-sum woman count is exactly her multiplicity in the actual male draw lists. -/
theorem rawWomanTierCount_eq_drawOrder_count_sum {n : ℕ} (C : Raw.Protocol n)
    (J : Finset (Fin n)) (w : Fin n) (H : ℕ) (z : Raw.Sources n) :
    rawWomanTierCount C J w H z =
      ∑ m ∈ J, (Raw.drawOrder (Raw.inputTranscript C H z) m).count w := by
  induction H with
  | zero => simp [rawWomanTierCount, Raw.inputTranscript, Raw.transcript, Raw.drawOrder]
  | succ H ih =>
    change (∑ t ∈ Finset.range (H + 1),
      womanValue J w (Raw.nextEdge C z.1 (Raw.inputTranscript C t z))) =
        ∑ m ∈ J, (Raw.drawOrder (Raw.observation C z.1 (Function.uncurry z.2)
          (Raw.inputTranscript C H z) :: Raw.inputTranscript C H z) m).count w
    rw [Finset.sum_range_succ, drawOrder_count_sum_cons, observation_map_edge]
    exact congrArg (fun k ↦ k + womanValue J w
      (Raw.nextEdge C z.1 (Raw.inputTranscript C H z))) ih

/-- The centered total is exactly the two literal raw counts centered by destination mass. -/
theorem centeredSum_eq_counts {n : ℕ} (C : Raw.Protocol n) (J : Finset (Fin n))
    (w : Fin n) (q : ℝ) (H : ℕ) (z : Raw.Sources n) :
    centeredSum C J w q H z =
      (rawWomanTierCount C J w H z : ℝ) - q * rawTierCount C J H z := by
  simp only [centeredSum, increment, localIncrement, edgeValue, rawWomanTierCount,
    rawTierCount, Nat.cast_sum, Finset.sum_sub_distrib, Finset.mul_sum]

/-- A deterministic-horizon concentration bound for actual raw woman-by-tier destination counts. -/
theorem raw_counts_deviation_measure_le {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) (C : Raw.Protocol n)
    (J : Finset (Fin n)) (w : Fin n) (H : ℕ) (r : ℝ) (hr : 0 < r) :
    rawInputLaw (fun _ ↦ a) Q {z |
      r ≤ |(rawWomanTierCount C J w H z : ℝ) -
        destinationProbability a w * rawTierCount C J H z|} ≤
      ENNReal.ofReal ((H : ℝ) * destinationProbability a w / r^2) := by
  have : IsProbabilityMeasure (rawInputLaw (fun _ ↦ a) Q) :=
    Raw.isProbabilityMeasure_rawInputLaw _ Q hQ
  have hs := memLp_centeredSum (rawInputLaw (fun _ ↦ a) Q) C J w
    (destinationProbability a w) H
  have hmean := centeredSum_integral_zero a Q hQ C J w H
  have hv : Var[centeredSum C J w (destinationProbability a w) H;
      rawInputLaw (fun _ ↦ a) Q] ≤ (H : ℝ) * destinationProbability a w := by
    rw [variance_eq_sub hs, hmean, zero_pow (by norm_num), sub_zero]
    exact centeredSum_second_moment_le a Q hQ C J w H
  have hc := meas_ge_le_variance_div_sq hs hr
  change rawInputLaw (fun _ ↦ a) Q {z |
    r ≤ |centeredSum C J w (destinationProbability a w) H z -
      (∫ x, centeredSum C J w (destinationProbability a w) H x
        ∂rawInputLaw (fun _ ↦ a) Q)|} ≤ _ at hc
  rw [hmean] at hc
  simp only [sub_zero, centeredSum_eq_counts] at hc
  exact hc.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hv (sq_nonneg r)))

/-- The logarithmic scale needed for Proposition G.2, at an arbitrary deterministic raw horizon. -/
theorem raw_counts_log_deviation_measure_le {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) (C : Raw.Protocol n)
    (J : Finset (Fin n)) (w : Fin n) (H : ℕ) (η : ℝ) (hη : 0 < η) (hn : 1 < n) :
    rawInputLaw (fun _ ↦ a) Q {z |
      η * Real.log n ≤ |(rawWomanTierCount C J w H z : ℝ) -
        destinationProbability a w * rawTierCount C J H z|} ≤
      ENNReal.ofReal ((H : ℝ) * destinationProbability a w / (η^2 * (Real.log n)^2)) := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  simpa only [mul_pow] using
    raw_counts_deviation_measure_le a Q hQ C J w H (η * Real.log n) (mul_pos hη hlog)

/-- A logarithmic clock bound and an order-one-over-market destination mass give the G.2 scale. -/
theorem raw_counts_log_deviation_le_of_clock_bound {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    (C : Raw.Protocol n) (J : Finset (Fin n)) (w : Fin n) (H : ℕ)
    (η K B : ℝ) (hη : 0 < η) (hK : 0 ≤ K) (hn : 1 < n)
    (hH : (H : ℝ) ≤ K * n * Real.log n) (hq : destinationProbability a w ≤ B / n) :
    rawInputLaw (fun _ ↦ a) Q {z |
      η * Real.log n ≤ |(rawWomanTierCount C J w H z : ℝ) -
        destinationProbability a w * rawTierCount C J H z|} ≤
      ENNReal.ofReal (K * B / (η^2 * Real.log n)) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hn)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hnum : (H : ℝ) * destinationProbability a w ≤ K * B * Real.log n := by
    calc
      _ ≤ (K * n * Real.log n) * destinationProbability a w :=
        mul_le_mul_of_nonneg_right hH (destinationProbability_mem_Icc a w).1
      _ ≤ (K * n * Real.log n) * (B / n) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      _ = _ := by field_simp
  have he : (K * B * Real.log n) / (η^2 * (Real.log n)^2) =
      K * B / (η^2 * Real.log n) := by
    field_simp
  exact (raw_counts_log_deviation_measure_le a Q hQ C J w H η hη hn).trans
    (ENNReal.ofReal_le_ofReal ((div_le_div_of_nonneg_right hnum (by positivity)).trans_eq he))

end TieredMatching.DestinationMartingale
