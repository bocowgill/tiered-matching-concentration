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
public import TieredMatching.VisitBounds
public import TieredMatching.CompetingHazards

/-! # Actual protected-destination safety under the original profile law

Finite backward induction uses the actual conditional profile tower and the score-weighted
next-destination inequality. Stops and protocol pauses are safe outcomes.
-/

@[expose] public section

namespace TieredMatching.ActualCompeting

open StableMarriage TieredMatching.Ordinal Protocols ProfileHistories FiniteConditioning
open CompetingHazards
open scoped ENNReal NNReal

/-- A finite actual continuation is safe if no proposal reaches the protected destination.
The visible stop rule, finite fuel limit, and protocol pauses all count as safe. -/
noncomputable def safeFuel {n : ℕ} (stop : List (Entry n) → Bool) (C : Protocol n)
    (target : Fin n) : ℕ → List (Entry n) → Profile n → Bool
  | 0, _, _ => true
  | fuel + 1, h, p => if stop h then true else
      match nextObservation C h p with
      | none => true
      | some (q, accepted) => if q.1 = target then false else
          safeFuel stop C target fuel (some (q, accepted) :: h) p

/-- Its literal probability under the original profile law conditioned on the visible prefix. -/
noncomputable def safeProbability {n : ℕ} (μ : PMF (Profile n))
    (stop : List (Entry n) → Bool) (C : Protocol n) (target : Fin n) (fuel : ℕ)
    (h : List (Entry n)) : ℝ :=
  VisitBounds.expectation (lawAt μ C h)
    (fun p ↦ if safeFuel stop C target fuel h p then 1 else 0)

/-- Every nonnull history has a genuine profile realizing precisely its ordinal records. -/
theorem exists_profile {n : ℕ} (μ : PMF (Profile n)) (C : Protocol n)
    (h : List (Entry n)) (hh : eventMass μ (event C h) ≠ 0) :
    ∃ p, profileTranscript C p h.length = h := by
  obtain ⟨p, hp⟩ := (lawAt μ C h).support_nonempty
  have hs : p ∈ (condition μ (event C h)).support := hp
  rw [support_condition _ _ hh] at hs
  exact ⟨p, hs.1⟩

/-- At an actually possible history with no empty women, every protocol is paused. -/
theorem selected_none_of_empty_zero {n : ℕ} (μ : PMF (Profile n)) (C : Protocol n)
    (h : List (Entry n)) (hh : eventMass μ (event C h) ≠ 0)
    (hz : (VisitBounds.emptyWomen h).card = 0) : selected C h = none := by
  classical
  obtain ⟨p, hp⟩ := exists_profile μ C h hh
  cases hs : selected C h with
  | none => rfl
  | some m =>
    obtain ⟨w, hw⟩ := VisitBounds.exists_empty_of_selected C p h hp m hs
    have hm : w ∈ VisitBounds.emptyWomen h := by simp [VisitBounds.emptyWomen, hw]
    have he : VisitBounds.emptyWomen h = ∅ := Finset.card_eq_zero.mp hz
    simp [he] at hm

/-- The original joint visit comparison becomes the same conditional comparison on a
nonnull visible history, including arbitrary suspensions. -/
theorem conditional_visit_le_empty {n : ℕ} (a b : Fin n → ℝ≥0)
    (ha1 : ∀ w, 1 ≤ a w) (hb : ∀ m, 0 < b m) (A : ℝ≥0)
    (haA : ∀ w, a w ≤ A) (C : Protocol n) (h : List (Entry n))
    (hh : eventMass (VisitBounds.profileLaw a b) (event C h) ≠ 0) (target : Fin n) :
    eventMass (lawAt (VisitBounds.profileLaw a b) C h) (VisitBounds.visitEvent C h target) ≤
      (A : ℝ≥0∞) * eventMass (lawAt (VisitBounds.profileLaw a b) C h)
        (VisitBounds.emptyHitEvent C h) := by
  have hv : event C h ∩ VisitBounds.visitEvent C h target =
      VisitBounds.visitEvent C h target := by
    apply Set.inter_eq_right.mpr
    rintro p ⟨m, hm⟩
    exact hm.1
  have he : event C h ∩ VisitBounds.emptyHitEvent C h = VisitBounds.emptyHitEvent C h := by
    apply Set.inter_eq_right.mpr
    rintro p ⟨w, m, _, hm⟩
    exact hm.1
  rw [lawAt, conditional_event_eq_div _ _ _ hh, conditional_event_eq_div _ _ _ hh, hv, he]
  have hmass (E : Set (Profile n)) :
      eventMass (VisitBounds.profileLaw a b) E = (VisitBounds.profileLaw a b).toMeasure E :=
    eventMass_eq_toMeasure _ _ (by trivial)
  simp_rw [hmass]
  have hi := ENNReal.div_le_div_right
    (VisitBounds.actual_visit_measure_le_emptyHit a b ha1 hb A haA C h target)
    ((VisitBounds.profileLaw a b).toMeasure (event C h))
  simpa only [ENNReal.div_eq_inv_mul, mul_assoc, mul_left_comm] using hi

/-- The next record is classified by its destination's current visible state. -/
noncomputable def kind {n : ℕ} (h : List (Entry n)) (target : Fin n) :
    Entry n → Destination := by
  classical
  exact fun entry ↦ match entry with
    | none => .neutral
    | some (q, _) => if q.1 = target then .target else
        if (recordState h).held q.1 = none then .empty else .neutral

/-- Total real mass of a destination class for any finite observation space. -/
noncomputable def classMass {R : Type*} [Fintype R] (law : PMF R)
    (classify : R → Destination) (d : Destination) : ℝ :=
  ∑ r, if classify r = d then (law r).toReal else 0

/-- The local weighted-reward identity is independent of the finite labels used for branches. -/
theorem weighted_reward {R : Type*} [Fintype R] (law : PMF R)
    (classify : R → Destination) (A : ℝ) (k : ℕ) :
    (∑ r, (law r).toReal * reward A k (classify r)) =
      CompetingHazards.potential A (k + 1) +
        (CompetingHazards.potential A k - CompetingHazards.potential A (k + 1)) *
          classMass law classify .empty -
            CompetingHazards.potential A (k + 1) * classMass law classify .target := by
  classical
  have ht (r : R) : (law r).toReal * reward A k (classify r) =
      CompetingHazards.potential A (k + 1) * (law r).toReal +
      (CompetingHazards.potential A k - CompetingHazards.potential A (k + 1)) *
        (if classify r = .empty then (law r).toReal else 0) -
      CompetingHazards.potential A (k + 1) *
        (if classify r = .target then (law r).toReal else 0) := by
    cases classify r <;> simp [reward] <;> ring
  have hsum : ∑ r, (law r).toReal = 1 := by
    have he := VisitBounds.expectation_const law 1
    simpa only [VisitBounds.expectation, mul_one] using he
  simp_rw [ht]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, hsum]
  simp only [classMass, mul_one]

/-- The exact local competing-hazard inequality makes the safe potential subharmonic. -/
theorem potential_le_weighted_reward {R : Type*} [Fintype R] {A : ℝ} (hA : 0 ≤ A)
    (law : PMF R) (classify : R → Destination) (k : ℕ)
    (hazard : classMass law classify .target ≤ A * classMass law classify .empty) :
    CompetingHazards.potential A (k + 1) ≤ ∑ r, (law r).toReal * reward A k (classify r) := by
  rw [weighted_reward, potential_difference hA]
  have hi := mul_le_mul_of_nonneg_left hazard (potential_pos hA (k + 1)).le
  nlinarith

/-- Real expectation commutes with the pushforward of a finite probability law. -/
theorem expectation_map {R Ω : Type*} [Fintype R] [Fintype Ω] (μ : PMF Ω)
    (f : Ω → R) (g : R → ℝ) :
    VisitBounds.expectation (μ.map f) g = VisitBounds.expectation μ (fun p ↦ g (f p)) := by
  rw [PMF.map, ProfileHistories.expectation_bind]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  unfold VisitBounds.expectation
  rw [Finset.sum_eq_single (f p)]
  · simp [PMF.pure_apply]
  · intro r _ hr
    simp [PMF.pure_apply, hr]
  · simp

/-- The observed next-record class has exactly its conditional indicator expectation. -/
theorem next_classMass {n : ℕ} (μ : PMF (Profile n)) (C : Protocol n)
    (h : List (Entry n)) (target : Fin n) (d : Destination) :
    classMass (nextLaw μ C h) (kind h target) d =
      VisitBounds.expectation (lawAt μ C h)
        (fun p ↦ if kind h target (nextObservation C h p) = d then 1 else 0) := by
  classical
  calc
    _ = VisitBounds.expectation (nextLaw μ C h)
        (fun e ↦ if kind h target e = d then 1 else 0) := by
      unfold classMass VisitBounds.expectation
      apply Finset.sum_congr rfl
      intro e _
      split_ifs with hd <;> simp [hd]
    _ = _ := expectation_map (lawAt μ C h) (nextObservation C h) _

/-- A target-class next record is exactly an actual next edge to the target woman. -/
theorem next_kind_target {n : ℕ} (C : Protocol n) (h : List (Entry n))
    (target : Fin n) (p : Profile n) :
    kind h target (nextObservation C h p) = .target ↔
      ∃ m, nextEdge C p.manRank h = some (target, m) := by
  classical
  cases hn : nextEdge C p.manRank h with
  | none => simp [nextObservation, Protocols.observation, hn, kind]
  | some q =>
    rcases q with ⟨w, m⟩
    by_cases hw : w = target
    · subst w
      simp [nextObservation, Protocols.observation, hn, kind]
    · by_cases he : (recordState h).held w = none <;>
        simp [nextObservation, Protocols.observation, hn, kind, hw, he]

/-- Because the protected woman is held, an empty-class record is exactly an actual edge
to one of the currently empty women. -/
theorem next_kind_empty {n : ℕ} (C : Protocol n) (h : List (Entry n))
    (target : Fin n) (hheld : ∃ u, (recordState h).held target = some u) (p : Profile n) :
    kind h target (nextObservation C h p) = .empty ↔
      ∃ w m, (recordState h).held w = none ∧ nextEdge C p.manRank h = some (w, m) := by
  classical
  obtain ⟨u, hu⟩ := hheld
  cases hn : nextEdge C p.manRank h with
  | none => simp [nextObservation, Protocols.observation, hn, kind]
  | some q =>
    rcases q with ⟨w, m⟩
    by_cases hw : w = target
    · subst w
      simp [nextObservation, Protocols.observation, hn, kind, hu]
    · by_cases he : (recordState h).held w = none
      · simp [nextObservation, Protocols.observation, hn, kind, hw, he]
      · simp [nextObservation, Protocols.observation, hn, kind, hw, he]

/-- Conditional class masses equal the original PR's actual conditional visit events. -/
theorem classMass_event {n : ℕ} (μ : PMF (Profile n)) (C : Protocol n)
    (h : List (Entry n)) (hh : eventMass μ (event C h) ≠ 0) (target : Fin n)
    (hheld : ∃ u, (recordState h).held target = some u) :
    classMass (nextLaw μ C h) (kind h target) .target =
      (eventMass (lawAt μ C h) (VisitBounds.visitEvent C h target)).toReal ∧
    classMass (nextLaw μ C h) (kind h target) .empty =
      (eventMass (lawAt μ C h) (VisitBounds.emptyHitEvent C h)).toReal := by
  classical
  have hsupport (p : Profile n) (hp : lawAt μ C h p ≠ 0) :
      profileTranscript C p h.length = h := by
    have hs : p ∈ (condition μ (event C h)).support := hp
    rw [support_condition _ _ hh] at hs
    exact hs.1
  have hexpect (d : Destination) (E : Set (Profile n))
      (heq : ∀ p, lawAt μ C h p ≠ 0 →
        (kind h target (nextObservation C h p) = d ↔ p ∈ E)) :
      classMass (nextLaw μ C h) (kind h target) d = (eventMass (lawAt μ C h) E).toReal := by
    rw [next_classMass, ← VisitBounds.expectation_indicator_one]
    unfold VisitBounds.expectation
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : lawAt μ C h p = 0
    · simp [hp]
    · congr 1
      simp only [Set.indicator_apply]
      exact if_congr (heq p hp) rfl rfl
  constructor
  · apply hexpect
    intro p hp
    rw [next_kind_target]
    simp only [VisitBounds.visitEvent, VisitBounds.edgeEvent, Set.mem_ofPred_eq, hsupport p hp,
      true_and]
  · apply hexpect
    intro p hp
    rw [next_kind_empty C h target hheld]
    simp only [VisitBounds.emptyHitEvent, VisitBounds.edgeEvent, Set.mem_ofPred_eq,
      hsupport p hp, true_and]

/-- The actual original-profile transition law satisfies the competing hazard inequality;
no local hazard assumption is supplied by a client. -/
theorem actual_hazard {n : ℕ} (a b : Fin n → ℝ≥0) {A : ℝ} (hA : 1 ≤ A)
    (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (C : Protocol n) (h : List (Entry n))
    (hh : eventMass (VisitBounds.profileLaw a b) (event C h) ≠ 0) (target : Fin n)
    (hheld : ∃ u, (recordState h).held target = some u) :
    classMass (nextLaw (VisitBounds.profileLaw a b) C h) (kind h target) .target ≤
      A * classMass (nextLaw (VisitBounds.profileLaw a b) C h) (kind h target) .empty := by
  let AN : ℝ≥0 := ⟨A, by linarith⟩
  have ha1' : ∀ w, 1 ≤ a w := fun w ↦ by exact_mod_cast ha1 w
  have haA' : ∀ w, a w ≤ AN := fun w ↦ by exact_mod_cast haA w
  have hi := conditional_visit_le_empty a b ha1' hb AN haA' C h hh target
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp)
    (eventMass_ne_top _ _)) hi
  rcases classMass_event (VisitBounds.profileLaw a b) C h hh target hheld with ⟨ht, he⟩
  rw [ht, he]
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal] at hr
  exact hr

/-- The branch value uses the same original profile in the literal child history. -/
noncomputable def branchValue {n : ℕ} (μ : PMF (Profile n)) (stop : List (Entry n) → Bool)
    (C : Protocol n) (target : Fin n) (fuel : ℕ) (h : List (Entry n)) : Entry n → ℝ
  | none => 1
  | some (q, accepted) => if q.1 = target then 0 else
      safeProbability μ stop C target fuel (some (q, accepted) :: h)

/-- The exact conditional profile tower supplies the actual safe-probability recursion. -/
theorem safeProbability_succ {n : ℕ} (μ : PMF (Profile n)) (stop : List (Entry n) → Bool)
    (C : Protocol n) (target : Fin n) (fuel : ℕ) (h : List (Entry n))
    (hh : eventMass μ (event C h) ≠ 0) (hs : stop h = false) :
    safeProbability μ stop C target (fuel + 1) h =
      ∑ e, (nextLaw μ C h e).toReal * branchValue μ stop C target fuel h e := by
  unfold safeProbability
  rw [expectation_next_lawAt_congr μ C h hh _
    (fun e p ↦ match e with
      | none => (1 : ℝ)
      | some (q, accepted) => if q.1 = target then 0 else
          if safeFuel stop C target fuel (some (q, accepted) :: h) p then 1 else 0) (by
      intro e he p hp
      rw [show safeFuel stop C target (fuel + 1) h p =
        (if stop h then true else match nextObservation C h p with
        | none => true
        | some (q, accepted) => if q.1 = target then false else
            safeFuel stop C target fuel (some (q, accepted) :: h) p) from rfl]
      rw [hs, child_support_next μ C h e hh he p hp]
      cases e with
      | none => rfl
      | some e =>
        rcases e with ⟨q, accepted⟩
        by_cases hq : q.1 = target <;> simp [hq])]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  cases e with
  | none => exact VisitBounds.expectation_const _ 1
  | some e =>
    rcases e with ⟨q, accepted⟩
    by_cases hq : q.1 = target
    · simp only [hq, ↓reduceIte, branchValue, VisitBounds.expectation_const]
    · simp only [hq, ↓reduceIte, branchValue, safeProbability]

/-- Positive next-record mass has an actual profile whose next observation is that record. -/
theorem observation_of_branch {n : ℕ} (μ : PMF (Profile n)) (C : Protocol n)
    (h : List (Entry n)) (e : Entry n) (he : nextLaw μ C h e ≠ 0) :
    ∃ p, nextObservation C h p = e := by
  obtain ⟨p, _, hp⟩ := (PMF.mem_support_map_iff (nextObservation C h) (lawAt μ C h) e).mp he
  exact ⟨p, hp⟩

/-- A supported hit on an empty woman is always accepted; its empty count falls by one.
Every other genuine supported record leaves the empty count unchanged. -/
theorem child_empty_card {n : ℕ} (μ : PMF (Profile n)) (C : Protocol n)
    (h : List (Entry n)) (q : Arrival.Edge n) (accepted : Bool)
    (he : nextLaw μ C h (some (q, accepted)) ≠ 0) :
    (VisitBounds.emptyWomen (some (q, accepted) :: h)).card =
      if (recordState h).held q.1 = none then (VisitBounds.emptyWomen h).card - 1 else
        (VisitBounds.emptyWomen h).card := by
  classical
  obtain ⟨p, hp⟩ := observation_of_branch μ C h (some (q, accepted)) he
  have ha := ((observation_eq_some_iff C p.manRank (profilePriorities p) h q accepted).mp hp).2
  by_cases hempty : (recordState h).held q.1 = none
  · have ht : accepted = true := by
      rw [accept, hempty] at ha
      exact ha.symm
    rw [ht, ite_eq_left hempty]
    rcases q with ⟨w, m⟩
    rw [VisitBounds.emptyWomen_cons_true, Finset.card_erase_of_mem]
    simp [VisitBounds.emptyWomen, hempty]
  · rw [ite_eq_right hempty]
    have hw : q.1 ∉ VisitBounds.emptyWomen h := by simp [VisitBounds.emptyWomen, hempty]
    cases accepted with
    | false => rfl
    | true =>
      rcases q with ⟨w, m⟩
      rw [VisitBounds.emptyWomen_cons_true, Finset.erase_eq_of_notMem hw]

/-- A record directed elsewhere leaves the protected woman's actual holder unchanged. -/
theorem child_target_held {n : ℕ} (h : List (Entry n)) (target : Fin n)
    (hheld : ∃ u, (recordState h).held target = some u) (q : Arrival.Edge n)
    (accepted : Bool) (hqt : q.1 ≠ target) :
    ∃ u, (recordState (some (q, accepted) :: h)).held target = some u := by
  obtain ⟨u, hu⟩ := hheld
  refine ⟨u, ?_⟩
  cases accepted <;> simp [recordState, recordStep, Ne.symm hqt, hu]

/-- The finite-fuel base event has probability one. -/
theorem safeProbability_zero {n : ℕ} (μ : PMF (Profile n)) (stop : List (Entry n) → Bool)
    (C : Protocol n) (target : Fin n) (h : List (Entry n)) :
    safeProbability μ stop C target 0 h = 1 := by
  simp only [safeProbability, safeFuel, ↓reduceIte, VisitBounds.expectation_const]

/-- Every visible stopping rule is an immediate safe event. -/
theorem safeProbability_stopped {n : ℕ} (μ : PMF (Profile n))
    (stop : List (Entry n) → Bool) (C : Protocol n) (target : Fin n) (fuel : ℕ)
    (h : List (Entry n)) (hs : stop h = true) :
    safeProbability μ stop C target (fuel + 1) h = 1 := by
  simp only [safeProbability, safeFuel, hs, ↓reduceIte, VisitBounds.expectation_const]

/-- A protocol pause is an immediate safe event, independently of the visible cap rule. -/
theorem safeProbability_paused {n : ℕ} (μ : PMF (Profile n))
    (stop : List (Entry n) → Bool) (C : Protocol n) (target : Fin n) (fuel : ℕ)
    (h : List (Entry n)) (hpause : selected C h = none) :
    safeProbability μ stop C target (fuel + 1) h = 1 := by
  have hn (p : Profile n) : nextObservation C h p = none := by
    simp only [nextObservation, Protocols.observation, nextEdge, hpause, Option.map_none]
  simp only [safeProbability, safeFuel, hn]
  have heq : (fun _ : Profile n ↦ if (if stop h then true else true) then (1 : ℝ) else 0) =
      fun _ ↦ 1 := by funext p; cases stop h <;> rfl
  rw [heq, VisitBounds.expectation_const]

/-- Actual capped safety is at least `(A+1)` to the negative current empty count.
This follows from the original profile law, its actual conditional tower, and public score bounds.
The protocol and visible stop rule are arbitrary; a protected woman must currently be held. -/
theorem potential_le_safeProbability {n : ℕ} (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (stop : List (Entry n) → Bool) (C : Protocol n)
    (target : Fin n) (fuel : ℕ) (h : List (Entry n))
    (hh : eventMass (VisitBounds.profileLaw a b) (event C h) ≠ 0)
    (hheld : ∃ u, (recordState h).held target = some u) :
    CompetingHazards.potential A (VisitBounds.emptyWomen h).card ≤
      safeProbability (VisitBounds.profileLaw a b) stop C target fuel h := by
  classical
  have hAnonneg : 0 ≤ A := by linarith
  induction fuel generalizing h with
  | zero =>
    rw [safeProbability_zero]
    exact potential_le_one hAnonneg _
  | succ fuel ih =>
    by_cases hs : stop h = true
    · rw [safeProbability_stopped _ stop C target fuel h hs]
      exact potential_le_one hAnonneg _
    · have hs' : stop h = false := Bool.eq_false_iff.mpr hs
      by_cases hz : (VisitBounds.emptyWomen h).card = 0
      · rw [safeProbability_paused _ stop C target fuel h
          (selected_none_of_empty_zero _ C h hh hz)]
        exact potential_le_one hAnonneg _
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hz
        rw [safeProbability_succ _ stop C target fuel h hh hs', hk]
        calc
          _ ≤ ∑ e, (nextLaw (VisitBounds.profileLaw a b) C h e).toReal *
              reward A k (kind h target e) :=
            potential_le_weighted_reward hAnonneg _ _ k
              (actual_hazard a b hA ha1 haA hb C h hh target hheld)
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro e _
            by_cases he : nextLaw (VisitBounds.profileLaw a b) C h e = 0
            · simp only [he, ENNReal.toReal_zero, zero_mul, le_refl]
            · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
              cases e with
              | none =>
                simp only [kind, reward, branchValue]
                exact potential_le_one hAnonneg _
              | some e =>
                rcases e with ⟨q, accepted⟩
                by_cases hqt : q.1 = target
                · simp only [kind, ite_eq_left hqt, reward, branchValue, le_refl]
                · have hchild := child_nonnull (VisitBounds.profileLaw a b) C h
                    (some (q, accepted)) hh he
                  have hheld' := child_target_held h target hheld q accepted hqt
                  have hi := ih (some (q, accepted) :: h) hchild hheld'
                  have hc := child_empty_card (VisitBounds.profileLaw a b) C h q accepted he
                  by_cases hempty : (recordState h).held q.1 = none
                  · rw [ite_eq_left hempty, hk] at hc
                    have hc' : (VisitBounds.emptyWomen (some (q, accepted) :: h)).card = k := by
                      omega
                    rw [hc'] at hi
                    simpa only [kind, ite_eq_right hqt, ite_eq_left hempty, reward, branchValue] using hi
                  · rw [ite_eq_right hempty, hk] at hc
                    rw [hc] at hi
                    simpa only [kind, ite_eq_right hqt, ite_eq_right hempty, reward, branchValue] using hi

/-- With at most two empty women, the actual finite safety probability has the source's
uniform lower bound `(A+1)⁻²`, with no independent eventual-survival variable. -/
theorem two_empty_le_safeProbability {n : ℕ} (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (stop : List (Entry n) → Bool) (C : Protocol n)
    (target : Fin n) (fuel : ℕ) (h : List (Entry n))
    (hh : eventMass (VisitBounds.profileLaw a b) (event C h) ≠ 0)
    (hheld : ∃ u, (recordState h).held target = some u)
    (hk : (VisitBounds.emptyWomen h).card ≤ 2) :
    CompetingHazards.potential A 2 ≤
      safeProbability (VisitBounds.profileLaw a b) stop C target fuel h := by
  apply le_trans _ (potential_le_safeProbability a b hA ha1 haA hb stop C target fuel h hh hheld)
  exact pow_le_pow_of_le_one (inv_nonneg.mpr (by linarith))
    ((inv_le_one₀ (by linarith : 0 < A + 1)).mpr (by linarith)) hk

/-- The actual success indicator expectation is precisely its conditional event mass. -/
theorem safeProbability_eq_eventMass {n : ℕ} (μ : PMF (Profile n))
    (stop : List (Entry n) → Bool) (C : Protocol n) (target : Fin n) (fuel : ℕ)
    (h : List (Entry n)) :
    safeProbability μ stop C target fuel h =
      (eventMass (lawAt μ C h) {p | safeFuel stop C target fuel h p = true}).toReal := by
  rw [← VisitBounds.expectation_indicator_one]
  unfold safeProbability
  congr 1
  funext p
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]

/-- The same literal safety event under the conditional probability measure. -/
theorem safeProbability_eq_measure {n : ℕ} (μ : PMF (Profile n))
    (stop : List (Entry n) → Bool) (C : Protocol n) (target : Fin n) (fuel : ℕ)
    (h : List (Entry n)) :
    safeProbability μ stop C target fuel h =
      ((lawAt μ C h).toMeasure {p | safeFuel stop C target fuel h p = true}).toReal := by
  rw [safeProbability_eq_eventMass, eventMass_eq_toMeasure _ _ (by trivial)]

/-- Direct actual-profile expectation form of the protected-destination safety bound. -/
theorem potential_le_safeExpectation {n : ℕ} (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (stop : List (Entry n) → Bool) (C : Protocol n)
    (target : Fin n) (fuel : ℕ) (h : List (Entry n))
    (hh : eventMass (VisitBounds.profileLaw a b) (event C h) ≠ 0)
    (hheld : ∃ u, (recordState h).held target = some u) :
    CompetingHazards.potential A (VisitBounds.emptyWomen h).card ≤
      VisitBounds.expectation (lawAt (VisitBounds.profileLaw a b) C h)
        (fun p ↦ if safeFuel stop C target fuel h p then 1 else 0) :=
  potential_le_safeProbability a b hA ha1 haA hb stop C target fuel h hh hheld

/-- Actual conditional measure form, without a finite-tree compilation premise. -/
theorem ofReal_potential_le_safeMeasure {n : ℕ} (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (stop : List (Entry n) → Bool) (C : Protocol n)
    (target : Fin n) (fuel : ℕ) (h : List (Entry n))
    (hh : eventMass (VisitBounds.profileLaw a b) (event C h) ≠ 0)
    (hheld : ∃ u, (recordState h).held target = some u) :
    ENNReal.ofReal (CompetingHazards.potential A (VisitBounds.emptyWomen h).card) ≤
      (lawAt (VisitBounds.profileLaw a b) C h).toMeasure
        {p | safeFuel stop C target fuel h p = true} := by
  apply ENNReal.ofReal_le_of_le_toReal
  rw [← safeProbability_eq_measure]
  exact potential_le_safeProbability a b hA ha1 haA hb stop C target fuel h hh hheld

/-- The protected-target failure event is bounded by the complementary safe potential. -/
theorem failureMeasure_le_one_sub_potential {n : ℕ} (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (stop : List (Entry n) → Bool) (C : Protocol n)
    (target : Fin n) (fuel : ℕ) (h : List (Entry n))
    (hh : eventMass (VisitBounds.profileLaw a b) (event C h) ≠ 0)
    (hheld : ∃ u, (recordState h).held target = some u) :
    ((lawAt (VisitBounds.profileLaw a b) C h).toMeasure
      {p | safeFuel stop C target fuel h p = false}).toReal ≤
        1 - CompetingHazards.potential A (VisitBounds.emptyWomen h).card := by
  classical
  let ν := lawAt (VisitBounds.profileLaw a b) C h
  have hfalse : (ν.toMeasure {p | safeFuel stop C target fuel h p = false}).toReal =
      VisitBounds.expectation ν (fun p ↦ if safeFuel stop C target fuel h p = false then
        (1 : ℝ) else 0) := by
    rw [← eventMass_eq_toMeasure _ _ (by trivial), ← VisitBounds.expectation_indicator_one]
    congr 1
    funext p
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  have hsum : VisitBounds.expectation ν
      (fun p ↦ if safeFuel stop C target fuel h p = false then (1 : ℝ) else 0) +
        safeProbability (VisitBounds.profileLaw a b) stop C target fuel h = 1 := by
    calc
      _ = VisitBounds.expectation ν (fun _ ↦ 1) := by
        change VisitBounds.expectation ν
          (fun p ↦ if safeFuel stop C target fuel h p = false then (1 : ℝ) else 0) +
            VisitBounds.expectation ν
              (fun p ↦ if safeFuel stop C target fuel h p then 1 else 0) = _
        unfold VisitBounds.expectation
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p _
        dsimp only
        cases hf : safeFuel stop C target fuel h p <;> simp
      _ = 1 := VisitBounds.expectation_const ν 1
  have hi := potential_le_safeProbability a b hA ha1 haA hb stop C target fuel h hh hheld
  change (ν.toMeasure _).toReal ≤ _
  rw [hfalse]
  linarith

end TieredMatching.ActualCompeting
