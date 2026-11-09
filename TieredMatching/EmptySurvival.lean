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

public import TieredMatching.ProfileHistories

/-! # Ordinary protocol tails for initially empty women

The conditional one-step hazard is derived from the original weighted ranking law.
Work conservation excludes protocol pauses while an empty woman remains. No independent
proposal sequence or conditioning on a future terminal event is used.
-/

@[expose] public section

namespace TieredMatching.EmptySurvival

open StableMarriage TieredMatching.Ordinal Protocols FiniteConditioning ProfileHistories
open scoped ENNReal NNReal

/-- The unchanged original PR profile law. -/
noncomputable def market {n : ℕ} (a b : Fin n → ℝ≥0) : PMF (Profile n) :=
  RandomRanking.profile (fun _ w ↦ a w) (fun m _ ↦ b m)

/-- Every supported continuation prefix selects a genuine proposer until all women are held. -/
def WorkConserving {n : ℕ} (μ : PMF (Profile n)) (C : Protocol n)
    (h0 : List (Entry n)) : Prop :=
  ∀ h, h0.IsSuffix h → eventMass μ (event C h) ≠ 0 →
    (∃ w, (recordState h).held w = none) → selected C h ≠ none

/-- The same original profile continued for a fixed number of ordinary protocol steps. -/
noncomputable def advance {n : ℕ} (C : Protocol n) (p : Profile n) :
    ℕ → List (Entry n) → List (Entry n)
  | 0, h => h
  | s + 1, h => advance C p s (nextObservation C h p :: h)

/-- Future empty status is a Boolean statistic of the original profile. -/
noncomputable def missing {n : ℕ} (C : Protocol n) (s : ℕ) (h : List (Entry n))
    (w : Fin n) (p : Profile n) : Bool :=
  decide ((recordState (advance C p s h)).held w = none)

/-- Its distribution is derived from the actual visible-history conditional profile law. -/
noncomputable def missingLaw {n : ℕ} (μ : PMF (Profile n)) (C : Protocol n)
    (s : ℕ) (h : List (Entry n)) (w : Fin n) : PMF Bool :=
  (lawAt μ C h).map (missing C s h w)

/-- A positive visible-history event has a genuine original-profile realization. -/
theorem exists_profile {n : ℕ} (μ : PMF (Profile n)) (C : Protocol n)
    (h : List (Entry n)) (hh : eventMass μ (event C h) ≠ 0) :
    ∃ p, profileTranscript C p h.length = h := by
  obtain ⟨p, hp⟩ := (lawAt μ C h).support_nonempty
  have hs : p ∈ (condition μ (event C h)).support := hp
  rw [support_condition _ _ hh] at hs
  exact ⟨p, hs.1⟩

/-- An empty woman is absent from every selected man's already exposed prefix. -/
theorem empty_unseen {n : ℕ} (μ : PMF (Profile n)) (C : Protocol n)
    (h : List (Entry n)) (hh : eventMass μ (event C h) ≠ 0)
    (w : Fin n) (hw : (recordState h).held w = none) (m : Fin n) : w ∉ manOrder h m := by
  obtain ⟨p, hp⟩ := exists_profile μ C h hh
  exact VisitBounds.empty_unseen_of_history C p h hp w hw m

/-- Exact residual-weight next-destination law under the actual conditional history law. -/
theorem destination_probability {n : ℕ} (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (C : Protocol n)
    (h : List (Entry n)) (hh : eventMass (market a b) (event C h) ≠ 0)
    (w m : Fin n) (hs : selected C h = some m) (hw : w ∉ manOrder h m) :
    eventMass (lawAt (market a b) C h) {p | nextEdge C p.manRank h = some (w, m)} =
      ((a w / ∑ v with v ∉ manOrder h m, a v : ℝ≥0) : ℝ≥0∞) := by
  apply conditional_event_of_joint_factor _ _ _ hh
  rw [eventMass_eq_toMeasure _ _ (by trivial), eventMass_eq_toMeasure _ _ (by trivial)]
  exact profile_next_destination_measure _ _ (fun _ w ↦ ha w) (fun m _ ↦ hb m) C h w m hs hw

/-- Scores in [1,A] give an ordinary-step empty-destination hazard of at least 1/(A*n). -/
theorem empty_destination_lower {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0)
    {A : ℝ} (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ))
    (haA : ∀ w, (a w : ℝ) ≤ A) (hb : ∀ m, 0 < b m) (C : Protocol n)
    (h : List (Entry n)) (hh : eventMass (market a b) (event C h) ≠ 0)
    (m : Fin n) (hs : selected C h = some m) (w : Fin n)
    (hw : (recordState h).held w = none) :
    1 / (A * n) ≤
      (eventMass (lawAt (market a b) C h) {p | nextEdge C p.manRank h = some (w, m)}).toReal := by
  classical
  have ha : ∀ w, 0 < a w := fun w ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (ha1 w)
  have hu := empty_unseen (market a b) C h hh w hw m
  rw [destination_probability a b ha hb C h hh w m hs hu, ENNReal.coe_toReal,
    NNReal.coe_div, NNReal.coe_sum]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < ∑ v with v ∉ manOrder h m, (a v : ℝ) := by
    apply Finset.sum_pos'
    · intro v hv
      exact (a v).coe_nonneg
    · exact ⟨w, by simp [hu], lt_of_lt_of_le zero_lt_one (ha1 w)⟩
  have hsum : (∑ v with v ∉ manOrder h m, (a v : ℝ)) ≤ A * n := by
    calc
      _ ≤ ∑ v : Fin n, (a v : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun v _ _ ↦ (a v).coe_nonneg)
      _ ≤ ∑ _ : Fin n, A := Finset.sum_le_sum fun v _ ↦ haA v
      _ = A * n := by simp [mul_comm]
  exact (div_le_div_of_nonneg_right (ha1 w) (mul_nonneg (by linarith) hn'.le)).trans
    (div_le_div_of_nonneg_left (a w).coe_nonneg hden hsum)

/-- A record never creates a new empty woman, including rejection and pause records. -/
theorem empty_cons_subset {n : ℕ} (h : List (Entry n)) (e : Entry n) :
    VisitBounds.emptyWomen (e :: h) ⊆ VisitBounds.emptyWomen h := by
  cases e with
  | none => exact fun _ hw ↦ hw
  | some e =>
    rcases e with ⟨⟨w, m⟩, acc⟩
    cases acc
    · exact fun _ hw ↦ hw
    · rw [VisitBounds.emptyWomen_cons_true]
      exact Finset.erase_subset _ _

/-- Once a woman is held, all subsequent actual protocol steps keep her held. -/
theorem empty_advance_subset {n : ℕ} (C : Protocol n) (p : Profile n)
    (s : ℕ) (h : List (Entry n)) :
    VisitBounds.emptyWomen (advance C p s h) ⊆ VisitBounds.emptyWomen h := by
  induction s generalizing h with
  | zero => exact fun _ hw ↦ hw
  | succ s ih => exact (ih _).trans (empty_cons_subset h _)

/-- The actual missing-status law obeys the literal conditional next-entry tower. -/
theorem missingLaw_succ {n : ℕ} (μ : PMF (Profile n)) (C : Protocol n)
    (s : ℕ) (h : List (Entry n)) (w : Fin n) (hh : eventMass μ (event C h) ≠ 0) :
    missingLaw μ C (s + 1) h w =
      (nextLaw μ C h).bind fun e ↦ missingLaw μ C s (e :: h) w := by
  apply map_next_lawAt_congr μ C h hh
  intro e he p hp
  simp only [missing, advance, child_support_next μ C h e hh he p hp]

/-- No further steps give exactly the visible current empty status. -/
theorem missingLaw_zero {n : ℕ} (μ : PMF (Profile n)) (C : Protocol n)
    (h : List (Entry n)) (w : Fin n) :
    missingLaw μ C 0 h w = PMF.pure (decide ((recordState h).held w = none)) := by
  change (lawAt μ C h).map (Function.const (Profile n)
    (decide ((recordState h).held w = none))) = _
  exact PMF.map_const _ _

/-- For an empty woman, the actual next record fills her exactly when she is its destination. -/
theorem missing_one_eq {n : ℕ} (C : Protocol n) (h : List (Entry n)) (w m : Fin n)
    (hs : selected C h = some m) (hw : (recordState h).held w = none) (p : Profile n) :
    missing C 1 h w p = !decide (nextEdge C p.manRank h = some (w, m)) := by
  classical
  have hn := (selected_some_spec C h m hs).1
  simp only [missing, advance, nextObservation, Protocols.observation, nextEdge, hs, dite_eq_left hn,
    Option.map_some, recordState, recordStep]
  by_cases hv : (p.manRank m).symm ⟨(recordState h).next m, hn⟩ = w
  · simp [hv, accept, hw]
  · have hv' : w ≠ (p.manRank m).symm ⟨(recordState h).next m, hn⟩ := Ne.symm hv
    simp only [hv, Prod.mk.injEq, and_true, Option.some.injEq, decide_false, Bool.not_false,
      decide_eq_true_eq]
    split <;> simp_all

/-- The next-step failure-to-remain-empty mass equals the exact next-destination mass. -/
theorem missing_one_filled {n : ℕ} (μ : PMF (Profile n)) (C : Protocol n)
    (h : List (Entry n)) (w m : Fin n) (hs : selected C h = some m)
    (hw : (recordState h).held w = none) :
    missingLaw μ C 1 h w false =
      eventMass (lawAt μ C h) {p | nextEdge C p.manRank h = some (w, m)} := by
  unfold missingLaw
  rw [← eventMass_observation_fiber]
  congr 1
  ext p
  simp [missing_one_eq C h w m hs hw p]

/-- Local one-step survival is derived from the ordinary PR kernel and public score bounds. -/
theorem missing_one_le {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0)
    {A : ℝ} (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ))
    (haA : ∀ w, (a w : ℝ) ≤ A) (hb : ∀ m, 0 < b m) (C : Protocol n)
    (h : List (Entry n)) (hh : eventMass (market a b) (event C h) ≠ 0)
    (m : Fin n) (hs : selected C h = some m) (w : Fin n)
    (hw : (recordState h).held w = none) :
    (missingLaw (market a b) C 1 h w true).toReal ≤ 1 - 1 / (A * n) := by
  have ht : missingLaw (market a b) C 1 h w false +
      missingLaw (market a b) C 1 h w true = 1 := by
    simpa [tsum_fintype, add_comm] using (missingLaw (market a b) C 1 h w).tsum_coe
  have htr : (missingLaw (market a b) C 1 h w false).toReal +
      (missingLaw (market a b) C 1 h w true).toReal = 1 := by
    rw [← ENNReal.toReal_add ((missingLaw (market a b) C 1 h w).apply_ne_top false)
      ((missingLaw (market a b) C 1 h w).apply_ne_top true), ht]
    rfl
  have hl := empty_destination_lower hn a b hA ha1 haA hb C h hh m hs w hw
  rw [← missing_one_filled (market a b) C h w m hs hw] at hl
  linarith

/-- A visibly held woman cannot contribute positive future empty probability. -/
theorem missingLaw_of_not_empty {n : ℕ} (μ : PMF (Profile n)) (C : Protocol n)
    (s : ℕ) (h : List (Entry n)) (w : Fin n) (hw : (recordState h).held w ≠ none) :
    missingLaw μ C s h w = PMF.pure false := by
  have heq : missing C s h w = Function.const (Profile n) false := by
    funext p
    have hne : (recordState (advance C p s h)).held w ≠ none := by
      intro hempty
      have hm : w ∈ VisitBounds.emptyWomen (advance C p s h) := by
        simp [VisitBounds.emptyWomen, hempty]
      have hm' := empty_advance_subset C p s h hm
      exact hw (by simpa [VisitBounds.emptyWomen] using hm')
    simp [missing, hne]
  simp [missingLaw, heq, PMF.map_const]

/-- Finite next-history disintegration yields the actual one-step empty probability. -/
theorem one_step_sum {n : ℕ} (μ : PMF (Profile n)) (C : Protocol n)
    (h : List (Entry n)) (w : Fin n) (hh : eventMass μ (event C h) ≠ 0) :
    (∑ e, (nextLaw μ C h e).toReal *
      (if (recordState (e :: h)).held w = none then (1 : ℝ) else 0)) =
      (missingLaw μ C 1 h w true).toReal := by
  classical
  rw [show 1 = 0 + 1 from rfl, missingLaw_succ μ C 0 h w hh, toReal_bind_apply]
  apply Finset.sum_congr rfl
  intro e _
  rw [missingLaw_zero]
  by_cases he : (recordState (e :: h)).held w = none <;> simp [he, PMF.pure_apply]

/-- Actual ordinary-step conditional tail; the local hazard is proved, not postulated. -/
theorem missing_probability_le {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0)
    {A : ℝ} (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ))
    (haA : ∀ w, (a w : ℝ) ≤ A) (hb : ∀ m, 0 < b m) (C : Protocol n)
    (h0 : List (Entry n)) (hwork : WorkConserving (market a b) C h0)
    (s : ℕ) (h : List (Entry n)) (hbase : h0.IsSuffix h)
    (hh : eventMass (market a b) (event C h) ≠ 0) (w : Fin n) :
    (missingLaw (market a b) C s h w true).toReal ≤
      if (recordState h).held w = none then (1 - 1 / (A * n)) ^ s else 0 := by
  classical
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hAn : 1 ≤ A * n := by nlinarith
  have hr : 0 ≤ 1 - 1 / (A * n) := by
    have hp : 0 < A * n := by linarith
    have hi : 1 / (A * n) ≤ 1 := (div_le_one hp).mpr hAn
    linarith
  induction s generalizing h with
  | zero =>
    rw [missingLaw_zero]
    by_cases hw : (recordState h).held w = none <;> simp [hw, PMF.pure_apply]
  | succ s ih =>
    by_cases hw : (recordState h).held w = none
    · rw [ite_eq_left hw, missingLaw_succ _ C s h w hh, toReal_bind_apply]
      obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp (hwork h hbase hh ⟨w, hw⟩)
      calc
        _ ≤ ∑ e, (nextLaw (market a b) C h e).toReal *
            (if (recordState (e :: h)).held w = none then (1 - 1 / (A * n)) ^ s else 0) := by
          apply Finset.sum_le_sum
          intro e _
          by_cases he : nextLaw (market a b) C h e = 0
          · simp [he]
          · exact mul_le_mul_of_nonneg_left
              (ih (e :: h) (hbase.trans (List.suffix_cons e h))
                (child_nonnull _ C h e hh he)) ENNReal.toReal_nonneg
        _ = (missingLaw (market a b) C 1 h w true).toReal *
            (1 - 1 / (A * n)) ^ s := by
          rw [← one_step_sum (market a b) C h w hh, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro e _
          split_ifs <;> ring
        _ ≤ (1 - 1 / (A * n)) * (1 - 1 / (A * n)) ^ s :=
          mul_le_mul_of_nonneg_right
            (missing_one_le hn a b hA ha1 haA hb C h hh m hm w hw) (pow_nonneg hr _)
        _ = _ := by rw [pow_succ]; ring
    · rw [ite_eq_right hw, missingLaw_of_not_empty _ C (s + 1) h w hw]
      simp [PMF.pure_apply]

/-- Continuing a realized history gives the literal later transcript of the same profile. -/
theorem advance_eq_transcript {n : ℕ} (C : Protocol n) (p : Profile n)
    (s : ℕ) (h : List (Entry n)) (hp : profileTranscript C p h.length = h) :
    advance C p s h = profileTranscript C p (h.length + s) := by
  induction s generalizing h with
  | zero => simpa [advance] using hp.symm
  | succ s ih =>
    have hp' : profileTranscript C p (nextObservation C h p :: h).length =
        nextObservation C h p :: h := by
      change Protocols.observation C p.manRank (profilePriorities p)
        (profileTranscript C p h.length) :: profileTranscript C p h.length = _
      rw [hp]
      rfl
    rw [advance, ih _ hp']
    congr 1
    simp only [List.length_cons]
    omega

/-- The future missing law uses the literal later ordinary transcript on conditional support. -/
theorem missingLaw_eq_transcript {n : ℕ} (μ : PMF (Profile n)) (C : Protocol n)
    (s : ℕ) (h : List (Entry n)) (w : Fin n) (hh : eventMass μ (event C h) ≠ 0) :
    missingLaw μ C s h w = (lawAt μ C h).map
      (fun p ↦ decide ((recordState (profileTranscript C p (h.length + s))).held w = none)) := by
  apply StoppedProcess.Process.map_congr_support
  intro p hp
  have he : p ∈ (condition μ (event C h)).support := hp
  rw [support_condition _ _ hh] at he
  simp only [missing, advance_eq_transcript C p s h he.1]

/-- The single-woman tail as an actual conditional ordinary-transcript event. -/
theorem empty_probability_le {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0)
    {A : ℝ} (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ))
    (haA : ∀ w, (a w : ℝ) ≤ A) (hb : ∀ m, 0 < b m) (C : Protocol n)
    (h0 : List (Entry n)) (hwork : WorkConserving (market a b) C h0)
    (hh : eventMass (market a b) (event C h0) ≠ 0) (w : Fin n) (s : ℕ) :
    (eventMass (lawAt (market a b) C h0)
      {p | (recordState (profileTranscript C p (h0.length + s))).held w = none}).toReal ≤
      if (recordState h0).held w = none then (1 - 1 / (A * n)) ^ s else 0 := by
  have he : eventMass (lawAt (market a b) C h0)
      {p | (recordState (profileTranscript C p (h0.length + s))).held w = none} =
        missingLaw (market a b) C s h0 w true := by
    rw [missingLaw_eq_transcript _ C s h0 w hh, ← eventMass_observation_fiber]
    congr 1
    ext p
    simp
  rw [he]
  exact missing_probability_le hn a b hA ha1 haA hb C h0 hwork s h0 ⟨[], rfl⟩ hh w

/-- Finite real expectations commute with finite sums. -/
theorem expectation_finset_sum {Ω ι : Type*} [Fintype Ω] (μ : PMF Ω)
    (F : Finset ι) (f : ι → Ω → ℝ) :
    VisitBounds.expectation μ (fun p ↦ ∑ i ∈ F, f i p) =
      ∑ i ∈ F, VisitBounds.expectation μ (f i) := by
  simp only [VisitBounds.expectation, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The initially empty set contains every later empty woman on a realized prefix. -/
theorem endpoint_empty_subset {n : ℕ} (C : Protocol n) (p : Profile n)
    (h : List (Entry n)) (hp : profileTranscript C p h.length = h) (s : ℕ) :
    VisitBounds.emptyWomen (profileTranscript C p (h.length + s)) ⊆ VisitBounds.emptyWomen h := by
  rw [← advance_eq_transcript C p s h hp]
  exact empty_advance_subset C p s h

/-- Union over only the initially empty women bounds actual global noncompletion. -/
theorem incomplete_probability_le {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0)
    {A : ℝ} (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ))
    (haA : ∀ w, (a w : ℝ) ≤ A) (hb : ∀ m, 0 < b m) (C : Protocol n)
    (h0 : List (Entry n)) (hwork : WorkConserving (market a b) C h0)
    (hh : eventMass (market a b) (event C h0) ≠ 0) (s : ℕ) :
    (eventMass (lawAt (market a b) C h0)
      {p | ∃ w, (recordState (profileTranscript C p (h0.length + s))).held w = none}).toReal ≤
      (VisitBounds.emptyWomen h0).card * (1 - 1 / (A * n)) ^ s := by
  classical
  let E : Set (Profile n) :=
    {p | ∃ w, (recordState (profileTranscript C p (h0.length + s))).held w = none}
  let F : Fin n → Set (Profile n) := fun w ↦
    {p | (recordState (profileTranscript C p (h0.length + s))).held w = none}
  rw [← VisitBounds.expectation_indicator_one]
  change VisitBounds.expectation _ (E.indicator (fun _ ↦ (1 : ℝ))) ≤ _
  calc
    _ ≤ VisitBounds.expectation (lawAt (market a b) C h0)
        (fun p ↦ ∑ w ∈ VisitBounds.emptyWomen h0, (F w).indicator (fun _ ↦ (1 : ℝ)) p) := by
      apply VisitBounds.expectation_mono_support
      intro p hp
      have he : p ∈ (condition (market a b) (event C h0)).support := hp
      rw [support_condition _ _ hh] at he
      by_cases hpE : p ∈ E
      · obtain ⟨w, hw⟩ := hpE
        have hwF : p ∈ F w := hw
        have hw0 : w ∈ VisitBounds.emptyWomen h0 := by
          apply endpoint_empty_subset C p h0 he.1 s
          simp [VisitBounds.emptyWomen, hw]
        rw [Set.indicator_of_mem (show p ∈ E from ⟨w, hw⟩)]
        exact le_trans (by simp [Set.indicator_of_mem hwF])
          (Finset.single_le_sum (fun v _ ↦ by
            simp only [Set.indicator_apply]; split_ifs <;> norm_num) hw0)
      · rw [Set.indicator_of_notMem hpE]
        exact Finset.sum_nonneg fun v _ ↦ by
          simp only [Set.indicator_apply]; split_ifs <;> norm_num
    _ = ∑ w ∈ VisitBounds.emptyWomen h0,
        (eventMass (lawAt (market a b) C h0) (F w)).toReal := by
      rw [expectation_finset_sum]
      apply Finset.sum_congr rfl
      intro w _
      exact VisitBounds.expectation_indicator_one _ _
    _ ≤ ∑ _w ∈ VisitBounds.emptyWomen h0, (1 - 1 / (A * n)) ^ s := by
      apply Finset.sum_le_sum
      intro w hw
      have he : (recordState h0).held w = none := by
        simpa [VisitBounds.emptyWomen] using hw
      simpa only [F, ite_eq_left he] using
        empty_probability_le hn a b hA ha1 haA hb C h0 hwork hh w s
    _ = _ := by simp

/-- The elementary exponential comparison for the ordinary-step geometric tail. -/
theorem geometric_le_exp {x : ℝ} (hx : x ≤ 1) (s : ℕ) :
    (1 - x) ^ s ≤ Real.exp (-(s : ℝ) * x) := by
  calc
    _ ≤ Real.exp (-x) ^ s := by
      apply pow_le_pow_left₀ (by linarith)
      linarith [Real.add_one_le_exp (-x)]
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- With at most k initially empty women, the actual ordinary completion tail is geometric. -/
theorem incomplete_probability_le_geometric {n : ℕ} (hn : 0 < n)
    (a b : Fin n → ℝ≥0) {A : ℝ} (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ))
    (haA : ∀ w, (a w : ℝ) ≤ A) (hb : ∀ m, 0 < b m) (C : Protocol n)
    (h0 : List (Entry n)) (hwork : WorkConserving (market a b) C h0)
    (hh : eventMass (market a b) (event C h0) ≠ 0) (s k : ℕ)
    (hk : (VisitBounds.emptyWomen h0).card ≤ k) :
    (eventMass (lawAt (market a b) C h0)
      {p | ∃ w, (recordState (profileTranscript C p (h0.length + s))).held w = none}).toReal ≤
      k * (1 - 1 / (A * n)) ^ s := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hAn : 1 ≤ A * n := by nlinarith
  have hr : 0 ≤ 1 - 1 / (A * n) := by
    have hp : 0 < A * n := by linarith
    have hi := (div_le_one hp).mpr hAn
    linarith
  exact (incomplete_probability_le hn a b hA ha1 haA hb C h0 hwork hh s).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (pow_nonneg hr _))

/-- The actual ordinary completion tail has exponential scale A*n, conditionally only on past. -/
theorem incomplete_probability_le_exp {n : ℕ} (hn : 0 < n)
    (a b : Fin n → ℝ≥0) {A : ℝ} (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ))
    (haA : ∀ w, (a w : ℝ) ≤ A) (hb : ∀ m, 0 < b m) (C : Protocol n)
    (h0 : List (Entry n)) (hwork : WorkConserving (market a b) C h0)
    (hh : eventMass (market a b) (event C h0) ≠ 0) (s k : ℕ)
    (hk : (VisitBounds.emptyWomen h0).card ≤ k) :
    (eventMass (lawAt (market a b) C h0)
      {p | ∃ w, (recordState (profileTranscript C p (h0.length + s))).held w = none}).toReal ≤
      k * Real.exp (-(s : ℝ) / (A * n)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hAn : 1 ≤ A * n := by nlinarith
  have hx : 1 / (A * n) ≤ 1 := (div_le_one (by linarith : 0 < A * n)).mpr hAn
  have hg := geometric_le_exp hx s
  have hexp : -(s : ℝ) * (1 / (A * n)) = -(s : ℝ) / (A * n) := by ring
  rw [hexp] at hg
  exact (incomplete_probability_le_geometric hn a b hA ha1 haA hb C h0 hwork hh s k hk).trans
    (mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg k))

end TieredMatching.EmptySurvival
