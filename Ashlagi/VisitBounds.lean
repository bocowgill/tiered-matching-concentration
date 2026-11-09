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

public import Ashlagi.ProtocolKernel
public import Ashlagi.FiniteConditioning
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! # Visits and accepted challenges in actual ordinal protocol continuations

The transition comparisons condition only on the visible ordinal history under the original
finite PR profile law. There is no IID destination assumption and no conditioning on a future
terminal proposal count.
-/

@[expose] public section

namespace Ashlagi.VisitBounds

open StableMarriage MeasureTheory Ashlagi.Ordinal Ashlagi.Protocols
open scoped NNReal ENNReal

/-- The exact original profile law with flat per-woman and per-man scores. -/
noncomputable def profileLaw {n : ℕ} (a b : Fin n → ℝ≥0) : PMF (Profile n) :=
  RandomRanking.profile (fun _ w ↦ a w) (fun m _ ↦ b m)

/-- A fixed visible transcript under an arbitrary ordinal proposer protocol. -/
def historyEvent {n : ℕ} (C : Protocol n) (h : List (Entry n)) : Set (Profile n) :=
  {p | profileTranscript C p h.length = h}

/-- A specified next genuine edge, jointly with the visible history. -/
def edgeEvent {n : ℕ} (C : Protocol n) (h : List (Entry n)) (w m : Fin n) :
    Set (Profile n) :=
  {p | profileTranscript C p h.length = h ∧ nextEdge C p.manRank h = some (w, m)}

/-- The next edge reaches this woman, with any selected proposer. -/
def visitEvent {n : ℕ} (C : Protocol n) (h : List (Entry n)) (w : Fin n) :
    Set (Profile n) := {p | ∃ m, p ∈ edgeEvent C h w m}

/-- The next genuine edge hits a currently empty woman. -/
def emptyHitEvent {n : ℕ} (C : Protocol n) (h : List (Entry n)) : Set (Profile n) :=
  {p | ∃ w m, (recordState h).held w = none ∧ p ∈ edgeEvent C h w m}

/-- Comparing a destination with one available score-at-least-one empty destination needs
only the exact residual weighted kernel. Suppressing an already seen target only helps. -/
theorem edge_measure_le_score_mul {n : ℕ} (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (A : ℝ≥0)
    (hupper : ∀ w, a w ≤ A) (C : Protocol n) (h : List (Entry n))
    (w e m : Fin n) (hs : selected C h = some m)
    (he : e ∉ manOrder h m) (heone : 1 ≤ a e) :
    (profileLaw a b).toMeasure (edgeEvent C h w m) ≤
      (A : ℝ≥0∞) * (profileLaw a b).toMeasure (edgeEvent C h e m) := by
  classical
  change (RandomRanking.profile (fun _ w ↦ a w) (fun m _ ↦ b m)).toMeasure
    {p | profileTranscript C p h.length = h ∧ nextEdge C p.manRank h = some (w, m)} ≤ _
  rw [profile_next_destination_kernel _ _ (fun _ w ↦ ha w) (fun m _ ↦ hb m) C h w m hs]
  change _ ≤ (A : ℝ≥0∞) *
    (RandomRanking.profile (fun _ w ↦ a w) (fun m _ ↦ b m)).toMeasure
      {p | profileTranscript C p h.length = h ∧ nextEdge C p.manRank h = some (e, m)}
  rw [profile_next_destination_measure _ _ (fun _ w ↦ ha w) (fun m _ ↦ hb m)
    C h e m hs he]
  by_cases hw : w ∈ manOrder h m
  · simp [hw]
  · rw [ite_eq_right hw, ← mul_assoc]
    apply mul_le_mul_left
    have hn : a w ≤ A * a e := by
      calc
        a w ≤ A := hupper w
        _ = A * 1 := by simp
        _ ≤ A * a e := mul_le_mul_right heone A
    have hdiv := div_le_div_of_nonneg_right hn
      (show (0 : ℝ≥0) ≤ ∑ v with v ∉ manOrder h m, a v from zero_le)
    rw [mul_div_assoc] at hdiv
    exact_mod_cast hdiv

/-- With the selected proposer fixed, the next woman's event is exactly that edge event. -/
theorem visitEvent_eq_edgeEvent {n : ℕ} (C : Protocol n) (h : List (Entry n))
    (w m : Fin n) (hs : selected C h = some m) : visitEvent C h w = edgeEvent C h w m := by
  ext p
  constructor
  · rintro ⟨k, hk⟩
    have hm := nextEdge_map_man C p.manRank h
    rw [hk.2, Option.map_some, hs] at hm
    have he : k = m := Option.some.inj hm
    subst k
    exact hk
  · intro hp
    exact ⟨m, hp⟩

/-- A genuine edge to an empty woman is one of the next-empty-hit outcomes. -/
theorem edgeEvent_subset_emptyHitEvent {n : ℕ} (C : Protocol n) (h : List (Entry n))
    (e m : Fin n) (he : (recordState h).held e = none) :
    edgeEvent C h e m ⊆ emptyHitEvent C h := fun _ hp ↦ ⟨e, m, he, hp⟩

/-- The actual PR joint next-visit inequality whenever one empty woman remains unseen by
the selected man. No positive history mass is required for this joint-event formulation. -/
theorem visit_measure_le_emptyHit {n : ℕ} (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (A : ℝ≥0)
    (hupper : ∀ w, a w ≤ A) (C : Protocol n) (h : List (Entry n))
    (w e m : Fin n) (hs : selected C h = some m)
    (he : e ∉ manOrder h m) (hempty : (recordState h).held e = none) (heone : 1 ≤ a e) :
    (profileLaw a b).toMeasure (visitEvent C h w) ≤
      (A : ℝ≥0∞) * (profileLaw a b).toMeasure (emptyHitEvent C h) := by
  rw [visitEvent_eq_edgeEvent C h w m hs]
  exact (edge_measure_le_score_mul a b ha hb A hupper C h w e m hs he heone).trans
    (mul_le_mul_right (measure_mono (edgeEvent_subset_emptyHitEvent C h e m hempty)) _)

/-- An actually observed empty woman has never been queried by any man. -/
theorem empty_unseen_of_history {n : ℕ} (C : Protocol n) (p : Profile n)
    (h : List (Entry n)) (hp : profileTranscript C p h.length = h)
    (e : Fin n) (he : (recordState h).held e = none) (m : Fin n) : e ∉ manOrder h m := by
  have hrow : RowFiber h e (fun k ↦ profilePriorities p (e, k)) :=
    ((Protocols.transcript_eq_iff C p.manRank (profilePriorities p) h.length h).mp hp).2.2 e
  rw [mem_manOrder_iff_seenEdges]
  exact rowFiber_no_holder_no_seen h e _ hrow he m

/-- Whenever an actual protocol can select a proposer, some woman is still empty.
This follows from the reachable state's injective holdings, even with suspended entrants. -/
theorem exists_empty_of_selected {n : ℕ} (C : Protocol n) (p : Profile n)
    (h : List (Entry n)) (hp : profileTranscript C p h.length = h)
    (m : Fin n) (hs : selected C h = some m) : ∃ e, (recordState h).held e = none := by
  classical
  by_contra hempty
  have hex (w : Fin n) : ∃ k, (recordState h).held w = some k := by
    cases hh : (recordState h).held w with
    | none => exact False.elim (hempty ⟨w, hh⟩)
    | some k => exact ⟨k, rfl⟩
  choose f hf using hex
  have hr := profileTranscript_reachable C p Finset.univ h.length (uses_univ C _)
  rw [hp] at hr
  have hv := Schedules.reachable_valid p Finset.univ hr
  have hinj : Function.Injective f := by
    intro u v heq
    exact hv.held_injective u v (f u) (hf u) (by simpa [heq] using hf v)
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective hinj m
  exact (selected_some_spec C h m hs).2 w (by simpa [hw] using hf w)

/-- Pausing a protocol gives no genuine next visit. -/
theorem visitEvent_eq_empty_of_paused {n : ℕ} (C : Protocol n) (h : List (Entry n))
    (w : Fin n) (hs : selected C h = none) : visitEvent C h w = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro p ⟨m, _, hm⟩
  have he := nextEdge_map_man C p.manRank h
  rw [hm, Option.map_some, hs] at he
  contradiction

/-- The actual PR joint visit-to-empty-hit comparison holds at every visible history,
including null histories, complete states, and arbitrary pauses. -/
theorem actual_visit_measure_le_emptyHit {n : ℕ} (a b : Fin n → ℝ≥0)
    (ha1 : ∀ w, 1 ≤ a w) (hb : ∀ m, 0 < b m) (A : ℝ≥0)
    (hupper : ∀ w, a w ≤ A) (C : Protocol n) (h : List (Entry n)) (w : Fin n) :
    (profileLaw a b).toMeasure (visitEvent C h w) ≤
      (A : ℝ≥0∞) * (profileLaw a b).toMeasure (emptyHitEvent C h) := by
  classical
  by_cases hex : ∃ p, profileTranscript C p h.length = h
  · obtain ⟨p, hp⟩ := hex
    cases hs : selected C h with
    | none => rw [visitEvent_eq_empty_of_paused C h w hs, measure_empty]; exact zero_le
    | some m =>
      obtain ⟨e, he⟩ := exists_empty_of_selected C p h hp m hs
      exact visit_measure_le_emptyHit a b
        (fun v ↦ lt_of_lt_of_le (by norm_num) (ha1 v)) hb A hupper C h w e m hs
        (empty_unseen_of_history C p h hp e he m) he (ha1 e)
  · have he : visitEvent C h w = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro p ⟨m, hm⟩
      exact hex ⟨p, hm.1⟩
    rw [he, measure_empty]
    exact zero_le

/-- Under a nonnull visible history, the exact next-visit inequality is a conditional
hazard inequality under FiniteConditioning's actual conditional profile law. -/
theorem conditional_visit_le_emptyHit {n : ℕ} (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (A : ℝ≥0)
    (hupper : ∀ w, a w ≤ A) (C : Protocol n) (h : List (Entry n))
    (w e m : Fin n) (hs : selected C h = some m)
    (he : e ∉ manOrder h m) (hempty : (recordState h).held e = none) (heone : 1 ≤ a e)
    (hpos : FiniteConditioning.eventMass (profileLaw a b) (historyEvent C h) ≠ 0) :
    FiniteConditioning.eventMass
      (FiniteConditioning.condition (profileLaw a b) (historyEvent C h)) (visitEvent C h w) ≤
      (A : ℝ≥0∞) * FiniteConditioning.eventMass
        (FiniteConditioning.condition (profileLaw a b) (historyEvent C h)) (emptyHitEvent C h) := by
  have hv : historyEvent C h ∩ visitEvent C h w = visitEvent C h w := by
    apply Set.inter_eq_right.mpr
    rintro p ⟨k, hk⟩
    exact hk.1
  have hevent : historyEvent C h ∩ emptyHitEvent C h = emptyHitEvent C h := by
    apply Set.inter_eq_right.mpr
    rintro p ⟨v, k, _, hk⟩
    exact hk.1
  rw [FiniteConditioning.conditional_event_eq_div _ _ _ hpos,
    FiniteConditioning.conditional_event_eq_div _ _ _ hpos, hv, hevent]
  have hmass (E : Set (Profile n)) :
      FiniteConditioning.eventMass (profileLaw a b) E = (profileLaw a b).toMeasure E :=
    FiniteConditioning.eventMass_eq_toMeasure _ _ (by trivial)
  simp_rw [hmass]
  have hh := ENNReal.div_le_div_right
    (visit_measure_le_emptyHit a b ha hb A hupper C h w e m hs he hempty heone)
    (FiniteConditioning.eventMass (profileLaw a b) (historyEvent C h))
  rw [hmass] at hh
  simpa only [ENNReal.div_eq_inv_mul, mul_assoc, mul_left_comm] using hh

/-- Total score of distinct men who have already proposed to the specified woman. -/
noncomputable def gamma {n : ℕ} (b : Fin n → ℝ≥0) (h : List (Entry n)) (w : Fin n) : ℝ :=
  ∑ k : SeenMen h w, (b k.val : ℝ)

/-- A next accepted challenge to a specified woman and proposer, jointly with visible past. -/
def acceptedEdgeEvent {n : ℕ} (C : Protocol n) (h : List (Entry n)) (w m : Fin n) :
    Set (Profile n) :=
  {p | profileTranscript C p h.length = h ∧ nextEdge C p.manRank h = some (w, m) ∧
    accept (profilePriorities p) (recordState h) (w, m) = true}

/-- A past-only lower bound on accumulated score bounds an actual accepted challenge.
No terminal visit count, future event, or unobserved priority is conditioned on. -/
theorem acceptedEdge_measure_le_visit {n : ℕ} (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m)
    (C : Protocol n) (h : List (Entry n)) (w m : Fin n) (B g : ℝ)
    (hg : 0 < g) (hB : (b m : ℝ) ≤ B) (hgamma : g ≤ gamma b h w) :
    (profileLaw a b).toMeasure (acceptedEdgeEvent C h w m) ≤
      ENNReal.ofReal (B / g) * (profileLaw a b).toMeasure (edgeEvent C h w m) := by
  change (RandomRanking.profile (fun _ w ↦ a w) (fun m _ ↦ b m)).toMeasure
    {p | profileTranscript C p h.length = h ∧ nextEdge C p.manRank h = some (w, m) ∧
      accept (profilePriorities p) (recordState h) (w, m) = true} ≤ _
  rw [Protocols.profile_next_acceptance_measure _ _ (fun _ w ↦ ha w) (fun m _ ↦ hb m)]
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  change (b m : ℝ) / ((b m : ℝ) + gamma b h w) ≤ B / g
  calc
    _ ≤ (b m : ℝ) / g := div_le_div_of_nonneg_left (b m).coe_nonneg hg
      (by have hh := (b m).coe_nonneg; linarith)
    _ ≤ _ := div_le_div_of_nonneg_right hB hg.le

/-- Real expectation under a finite probability law, with no measurability side conditions. -/
noncomputable def expectation {Ω : Type*} [Fintype Ω] (law : PMF Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, (law ω).toReal * f ω

/-- A finite visible-history fiber's contribution to a real expectation. -/
noncomputable def fiberExpectation {Ω R : Type*} [Fintype Ω] (law : PMF Ω)
    (observe : Ω → R) (r : R) (f : Ω → ℝ) : ℝ := by
  classical
  exact ∑ ω with observe ω = r, (law ω).toReal * f ω

open scoped Classical in
/-- Finite observations disintegrate every real expectation by their actual fibers. -/
theorem expectation_eq_sum_fibers {Ω R : Type*} [Fintype Ω] (law : PMF Ω)
    (observe : Ω → R) (f : Ω → ℝ) :
    expectation law f = ∑ r ∈ Finset.univ.image observe, fiberExpectation law observe r f := by
  classical
  symm
  exact Finset.sum_fiberwise_of_maps_to (fun ω _ ↦ Finset.mem_image.mpr
    ⟨ω, Finset.mem_univ _, rfl⟩) (fun ω ↦ (law ω).toReal * f ω)

open scoped Classical in
/-- Fiber comparisons can be summed with any restriction measurable from the visible past.
This is the predictable-step summation principle; future counts never enter its mask. -/
theorem expectation_masked_le {Ω R : Type*} [Fintype Ω] (law : PMF Ω)
    (observe : Ω → R) (mask : R → Prop) (f g : Ω → ℝ) (A : ℝ)
    (hlocal : ∀ r ∈ Finset.univ.image observe, mask r →
      fiberExpectation law observe r f ≤ A * fiberExpectation law observe r g) :
    expectation law (fun ω ↦ if mask (observe ω) then f ω else 0) ≤
      A * expectation law (fun ω ↦ if mask (observe ω) then g ω else 0) := by
  classical
  have hfiber (r : R) (F : Ω → ℝ) :
      fiberExpectation law observe r (fun ω ↦ if mask (observe ω) then F ω else 0) =
        if mask r then fiberExpectation law observe r F else 0 := by
    unfold fiberExpectation
    calc
      _ = ∑ ω with observe ω = r,
          if mask r then (law ω).toReal * F ω else 0 := by
        apply Finset.sum_congr rfl
        intro ω hω
        have he := (Finset.mem_filter.mp hω).2
        simp only [he]
        split_ifs <;> simp
      _ = _ := by rw [Finset.sum_ite_irrel]; simp
  rw [expectation_eq_sum_fibers, expectation_eq_sum_fibers, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  rw [hfiber, hfiber]
  by_cases hm : mask r
  · simpa only [hm, ite_true] using hlocal r hr hm
  · simp [hm]

/-- Finite real expectations agree with the actual PMF measure integral. -/
theorem expectation_eq_integral {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (law : PMF Ω) (f : Ω → ℝ) :
    expectation law f = ∫ ω, f ω ∂law.toMeasure := by
  rw [PMF.integral_eq_sum]
  rfl

/-- Finite conditional expectation satisfies the exact joint-mass identity. -/
theorem history_mass_mul_expectation {Ω : Type*} [Fintype Ω] (law : PMF Ω)
    (s : Set Ω) (f : Ω → ℝ) :
    (FiniteConditioning.eventMass law s).toReal *
      expectation (FiniteConditioning.condition law s) f =
        expectation law (s.indicator f) := by
  classical
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  have he := congrArg ENNReal.toReal (FiniteConditioning.eventMass_mul_condition law s ω)
  rw [ENNReal.toReal_mul] at he
  by_cases hω : ω ∈ s
  · simpa only [Set.indicator_of_mem hω, mul_assoc] using congrArg (fun z : ℝ ↦ z * f ω) he
  · simp only [Set.indicator_of_notMem hω, ENNReal.toReal_zero] at he ⊢
    rw [← mul_assoc, he, zero_mul, mul_zero]

/-- Currently empty women, a statistic of visible ordinal records alone. -/
noncomputable def emptyWomen {n : ℕ} (h : List (Entry n)) : Finset (Fin n) :=
  Finset.univ.filter fun w ↦ (recordState h).held w = none

/-- A genuine next visit to the fixed woman at a deterministic protocol time. -/
def isVisit {n : ℕ} (C : Protocol n) (p : Profile n) (t : ℕ) (w : Fin n) : Prop :=
  ∃ m, nextEdge C p.manRank (profileTranscript C p t) = some (w, m)

/-- A genuine next hit on a woman who is currently empty. -/
def isEmptyHit {n : ℕ} (C : Protocol n) (p : Profile n) (t : ℕ) : Prop :=
  ∃ w m, (recordState (profileTranscript C p t)).held w = none ∧
    nextEdge C p.manRank (profileTranscript C p t) = some (w, m)

open scoped Classical in
/-- The bounded real visit indicator; protocol pauses contribute zero. -/
noncomputable def visitReward {n : ℕ} (C : Protocol n) (p : Profile n) (t : ℕ)
    (w : Fin n) : ℝ := if isVisit C p t w then 1 else 0

open scoped Classical in
/-- The bounded real empty-hit indicator. -/
noncomputable def emptyReward {n : ℕ} (C : Protocol n) (p : Profile n) (t : ℕ) : ℝ :=
  if isEmptyHit C p t then 1 else 0

/-- Accepting a recorded proposal removes precisely its destination from the empty set. -/
theorem emptyWomen_cons_true {n : ℕ} (h : List (Entry n)) (w m : Fin n) :
    emptyWomen (some ((w, m), true) :: h) = (emptyWomen h).erase w := by
  classical
  ext v
  simp only [emptyWomen, Finset.mem_filter, Finset.mem_univ, true_and,
    recordState, recordStep, ite_true, Finset.mem_erase]
  by_cases hv : v = w
  · subst v
    simp
  · simp [hv]

/-- A rejection changes no woman's empty/nonempty status. -/
theorem emptyWomen_cons_false {n : ℕ} (h : List (Entry n)) (w m : Fin n) :
    emptyWomen (some ((w, m), false) :: h) = emptyWomen h := by
  rfl

/-- A pause changes no woman's empty/nonempty status. -/
theorem emptyWomen_cons_none {n : ℕ} (h : List (Entry n)) : emptyWomen (none :: h) = emptyWomen h :=
  rfl

/-- The actual next record has exactly one empty-to-held transition if and only if its
genuine destination is empty. Empty women can never be created by a later proposal. -/
theorem empty_card_step {n : ℕ} (C : Protocol n) (p : Profile n) (t : ℕ) :
    ((emptyWomen (profileTranscript C p t)).card : ℝ) =
      emptyReward C p t + ((emptyWomen (profileTranscript C p (t + 1))).card : ℝ) := by
  classical
  let h := profileTranscript C p t
  change ((emptyWomen h).card : ℝ) = emptyReward C p t +
    ((emptyWomen (Protocols.observation C p.manRank (profilePriorities p) h :: h)).card : ℝ)
  cases hn : nextEdge C p.manRank h with
  | none =>
    have hh : ¬isEmptyHit C p t := by
      change ¬∃ w m, (recordState h).held w = none ∧
        nextEdge C p.manRank h = some (w, m)
      simp [hn]
    simp [Protocols.observation, hn, emptyWomen_cons_none, emptyReward, hh]
  | some q =>
    obtain ⟨w, m⟩ := q
    by_cases hempty : (recordState h).held w = none
    · have hh : isEmptyHit C p t := ⟨w, m, hempty, hn⟩
      have ha : accept (profilePriorities p) (recordState h) (w, m) = true := by
        simp [accept, hempty]
      have hw : w ∈ emptyWomen h := by simp [emptyWomen, hempty]
      simp only [Protocols.observation, hn, Option.map_some, ha, emptyWomen_cons_true,
        emptyReward, ite_eq_left hh]
      have hcard := Finset.card_erase_add_one hw
      exact_mod_cast (show (emptyWomen h).card = 1 + ((emptyWomen h).erase w).card by omega)
    · have hh : ¬isEmptyHit C p t := by
        rintro ⟨v, k, hv, hvk⟩
        change nextEdge C p.manRank h = some (v, k) at hvk
        rw [hn] at hvk
        have he := Option.some.inj hvk
        have hew : w = v := congrArg Prod.fst he
        subst v
        exact hempty hv
      have hw : w ∉ emptyWomen h := by simp [emptyWomen, hempty]
      cases ha : accept (profilePriorities p) (recordState h) (w, m) <;>
        simp [Protocols.observation, hn, ha, emptyWomen_cons_true, emptyWomen_cons_false,
          Finset.erase_eq_of_notMem hw, emptyReward, hh]

/-- The finite future number of genuine hits on previously empty women. -/
noncomputable def emptyHitCount {n : ℕ} (C : Protocol n) (p : Profile n) (start H : ℕ) : ℝ :=
  ∑ t ∈ Finset.range H, emptyReward C p (start + t)

/-- Empty-hit counting telescopes pathwise, including every possible protocol pause. -/
theorem emptyHitCount_add_remaining {n : ℕ} (C : Protocol n) (p : Profile n) (start H : ℕ) :
    emptyHitCount C p start H + ((emptyWomen (profileTranscript C p (start + H))).card : ℝ) =
      ((emptyWomen (profileTranscript C p start)).card : ℝ) := by
  induction H with
  | zero => simp [emptyHitCount]
  | succ H ih =>
    rw [emptyHitCount, Finset.sum_range_succ]
    have hs := empty_card_step C p (start + H)
    change emptyHitCount C p start H + emptyReward C p (start + H) +
      ((emptyWomen (profileTranscript C p (start + (H + 1)))).card : ℝ) = _
    have he : start + (H + 1) = start + H + 1 := by omega
    rw [he]
    linarith

/-- At most the initial number of empty women can be hit for the first time. -/
theorem emptyHitCount_le_initial {n : ℕ} (C : Protocol n) (p : Profile n) (start H : ℕ) :
    emptyHitCount C p start H ≤ ((emptyWomen (profileTranscript C p start)).card : ℝ) := by
  have hh := emptyHitCount_add_remaining C p start H
  have hn := Nat.cast_nonneg (α := ℝ) (emptyWomen (profileTranscript C p (start + H))).card
  linarith

/-- A finite indicator-fiber expectation is exactly the real joint-event probability. -/
theorem fiber_indicator_eq_eventMass {Ω R : Type*} [Fintype Ω] (law : PMF Ω)
    (observe : Ω → R) (r : R) (E : Set Ω) :
    fiberExpectation law observe r (E.indicator (fun _ ↦ (1 : ℝ))) =
      (FiniteConditioning.eventMass law ({ω | observe ω = r} ∩ E)).toReal := by
  classical
  unfold fiberExpectation FiniteConditioning.eventMass
  rw [tsum_fintype, ENNReal.toReal_sum (fun ω _ ↦ by
    by_cases h : ω ∈ ({ω | observe ω = r} ∩ E)
    · simpa only [Set.indicator_of_mem h] using law.apply_ne_top ω
    · simp [Set.indicator_of_notMem h])]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases ho : observe ω = r <;> by_cases he : ω ∈ E <;>
    simp [ho, he, Set.indicator]

/-- The next-visit reward's exact visible-fiber expectation under the original PR law. -/
theorem fiber_visitReward {n : ℕ} (law : PMF (Profile n)) (C : Protocol n)
    (t : ℕ) (h : List (Entry n)) (hlen : h.length = t) (w : Fin n) :
    fiberExpectation law (fun p ↦ profileTranscript C p t) h (fun p ↦ visitReward C p t w) =
      (law.toMeasure (visitEvent C h w)).toReal := by
  have hfun : (fun p ↦ visitReward C p t w) =
      {p | isVisit C p t w}.indicator (fun _ ↦ (1 : ℝ)) := by
    classical
    funext p
    simp [visitReward, Set.indicator]
  rw [hfun, fiber_indicator_eq_eventMass, FiniteConditioning.eventMass_eq_toMeasure _ _
    (by trivial)]
  congr 1
  apply congrArg law.toMeasure
  ext p
  constructor
  · rintro ⟨hh, m, hm⟩
    change profileTranscript C p t = h at hh
    refine ⟨m, ?_, ?_⟩
    · simpa only [hlen] using hh
    · simpa only [hh] using hm
  · rintro ⟨m, hh, hm⟩
    have hh' : profileTranscript C p t = h := by simpa only [hlen] using hh
    exact ⟨hh', m, by simpa only [hh'] using hm⟩

/-- The next-empty-hit reward has the exact visible-fiber joint-event expectation. -/
theorem fiber_emptyReward {n : ℕ} (law : PMF (Profile n)) (C : Protocol n)
    (t : ℕ) (h : List (Entry n)) (hlen : h.length = t) :
    fiberExpectation law (fun p ↦ profileTranscript C p t) h (fun p ↦ emptyReward C p t) =
      (law.toMeasure (emptyHitEvent C h)).toReal := by
  have hfun : (fun p ↦ emptyReward C p t) =
      {p | isEmptyHit C p t}.indicator (fun _ ↦ (1 : ℝ)) := by
    classical
    funext p
    simp [emptyReward, Set.indicator]
  rw [hfun, fiber_indicator_eq_eventMass, FiniteConditioning.eventMass_eq_toMeasure _ _
    (by trivial)]
  congr 1
  apply congrArg law.toMeasure
  ext p
  constructor
  · rintro ⟨hh, v, m, hv, hm⟩
    change profileTranscript C p t = h at hh
    refine ⟨v, m, ?_, ?_, ?_⟩
    · simpa only [hh] using hv
    · simpa only [hlen] using hh
    · simpa only [hh] using hm
  · rintro ⟨v, m, hv, hh, hm⟩
    have hh' : profileTranscript C p t = h := by simpa only [hlen] using hh
    exact ⟨hh', v, m, by simpa only [hh'] using hv, by simpa only [hh'] using hm⟩

/-- Each actual visible-history fiber satisfies the predictable visit comparison. -/
theorem fiber_visit_le_empty {n : ℕ} (a b : Fin n → ℝ≥0)
    (ha1 : ∀ w, 1 ≤ a w) (hb : ∀ m, 0 < b m) (A : ℝ≥0)
    (hupper : ∀ w, a w ≤ A) (C : Protocol n) (t : ℕ)
    (h : List (Entry n)) (hlen : h.length = t) (w : Fin n) :
    fiberExpectation (profileLaw a b) (fun p ↦ profileTranscript C p t) h
      (fun p ↦ visitReward C p t w) ≤
      (A : ℝ) * fiberExpectation (profileLaw a b) (fun p ↦ profileTranscript C p t) h
        (fun p ↦ emptyReward C p t) := by
  rw [fiber_visitReward _ _ _ _ hlen, fiber_emptyReward _ _ _ _ hlen]
  have hh := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _))
    (actual_visit_measure_le_emptyHit a b ha1 hb A hupper C h w)
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using hh

/-- Dropping the newly added records recovers exactly the actual visible initial history. -/
theorem profileTranscript_drop {n : ℕ} (C : Protocol n) (p : Profile n) (start H : ℕ) :
    (profileTranscript C p (start + H)).drop H = profileTranscript C p start := by
  induction H with
  | zero => simp
  | succ H ih =>
    change (Protocols.observation C p.manRank (profilePriorities p)
      (profileTranscript C p (start + H)) :: profileTranscript C p (start + H)).drop (H + 1) = _
    simpa only [List.drop_succ_cons] using ih

/-- A predictable one-step inequality remains valid after fixing any initial visible history. -/
theorem joint_step_visit_le_empty {n : ℕ} (a b : Fin n → ℝ≥0)
    (ha1 : ∀ w, 1 ≤ a w) (hb : ∀ m, 0 < b m) (A : ℝ≥0)
    (hupper : ∀ w, a w ≤ A) (C : Protocol n) (h0 : List (Entry n)) (t : ℕ) (w : Fin n) :
    expectation (profileLaw a b) ((historyEvent C h0).indicator
      (fun p ↦ visitReward C p (h0.length + t) w)) ≤
      (A : ℝ) * expectation (profileLaw a b) ((historyEvent C h0).indicator
        (fun p ↦ emptyReward C p (h0.length + t))) := by
  classical
  have hh := expectation_masked_le (profileLaw a b)
    (fun p ↦ profileTranscript C p (h0.length + t)) (fun h ↦ h.drop t = h0)
    (fun p ↦ visitReward C p (h0.length + t) w)
    (fun p ↦ emptyReward C p (h0.length + t)) (A : ℝ) (fun h _ _ ↦ by
      by_cases hlen : h.length = h0.length + t
      · exact fiber_visit_le_empty a b ha1 hb A hupper C _ h hlen w
      · have heq (F : Profile n → ℝ) :
            fiberExpectation (profileLaw a b)
              (fun p ↦ profileTranscript C p (h0.length + t)) h F = 0 := by
          unfold fiberExpectation
          rw [Finset.sum_filter]
          apply Finset.sum_eq_zero
          intro p _
          by_cases he : profileTranscript C p (h0.length + t) = h
          · have hl : h.length = h0.length + t := by
              rw [← he]
              exact Protocols.transcript_length C p.manRank (profilePriorities p) _
            exact False.elim (hlen hl)
          · simp [he]
        rw [heq, heq, mul_zero])
  simpa [expectation, profileTranscript_drop, Set.indicator_apply, historyEvent] using hh

/-- Finite expectations preserve inequalities on the actual probability support. -/
theorem expectation_mono_support {Ω : Type*} [Fintype Ω] (law : PMF Ω) (f g : Ω → ℝ)
    (h : ∀ ω ∈ law.support, f ω ≤ g ω) : expectation law f ≤ expectation law g := by
  unfold expectation
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : law ω = 0
  · simp [hp]
  · exact mul_le_mul_of_nonneg_left (h ω hp) ENNReal.toReal_nonneg

/-- Constants have their usual expectation under a finite probability law. -/
theorem expectation_const {Ω : Type*} [Fintype Ω] (law : PMF Ω) (c : ℝ) :
    expectation law (fun _ ↦ c) = c := by
  unfold expectation
  rw [← Finset.sum_mul]
  have hs : ∑ ω, (law ω).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun ω _ ↦ law.apply_ne_top ω)]
    have he : ∑ ω, law ω = 1 := by simpa only [tsum_fintype] using law.tsum_coe
    rw [he]
    rfl
  rw [hs, one_mul]

/-- Nonnull visible conditioning preserves any joint indicator-expectation comparison. -/
theorem conditional_expectation_le {Ω : Type*} [Fintype Ω] (law : PMF Ω) (E : Set Ω)
    (hE : FiniteConditioning.eventMass law E ≠ 0) (f g : Ω → ℝ) (A : ℝ)
    (hjoint : expectation law (E.indicator f) ≤ A * expectation law (E.indicator g)) :
    expectation (FiniteConditioning.condition law E) f ≤
      A * expectation (FiniteConditioning.condition law E) g := by
  have hp : 0 < (FiniteConditioning.eventMass law E).toReal :=
    ENNReal.toReal_pos hE (FiniteConditioning.eventMass_ne_top law E)
  apply (mul_le_mul_iff_right₀ hp).mp
  rw [history_mass_mul_expectation]
  calc
    _ ≤ A * expectation law (E.indicator g) := hjoint
    _ = _ := by rw [← history_mass_mul_expectation]; ring

/-- Finite sums of future indicators commute with actual finite expectations. -/
theorem expectation_indicator_sum {Ω ι : Type*} [Fintype Ω] (law : PMF Ω)
    (E : Set Ω) (s : Finset ι) (f : ι → Ω → ℝ) :
    expectation law (E.indicator (fun ω ↦ ∑ i ∈ s, f i ω)) =
      ∑ i ∈ s, expectation law (E.indicator (f i)) := by
  classical
  have he (ω : Ω) : E.indicator (fun ω ↦ ∑ i ∈ s, f i ω) ω =
      ∑ i ∈ s, E.indicator (f i) ω := by
    by_cases hω : ω ∈ E <;> simp [Set.indicator, hω]
  simp only [expectation, he, Finset.mul_sum]
  exact Finset.sum_comm

/-- Finite future genuine visits to one fixed woman. -/
noncomputable def visitCount {n : ℕ} (C : Protocol n) (p : Profile n)
    (start H : ℕ) (w : Fin n) : ℝ := ∑ t ∈ Finset.range H, visitReward C p (start + t) w

/-- Summing exact predictable next-step inequalities gives the finite future visit bound
relative to actual empty hits, after fixing only the initial visible history. -/
theorem conditional_visitCount_le_emptyHitCount {n : ℕ} (a b : Fin n → ℝ≥0)
    (ha1 : ∀ w, 1 ≤ a w) (hb : ∀ m, 0 < b m) (A : ℝ≥0)
    (hupper : ∀ w, a w ≤ A) (C : Protocol n) (h0 : List (Entry n))
    (hpos : FiniteConditioning.eventMass (profileLaw a b) (historyEvent C h0) ≠ 0)
    (H : ℕ) (w : Fin n) :
    expectation (FiniteConditioning.condition (profileLaw a b) (historyEvent C h0))
      (fun p ↦ visitCount C p h0.length H w) ≤
      (A : ℝ) * expectation
        (FiniteConditioning.condition (profileLaw a b) (historyEvent C h0))
        (fun p ↦ emptyHitCount C p h0.length H) := by
  apply conditional_expectation_le _ _ hpos
  change expectation _ ((historyEvent C h0).indicator
    (fun p ↦ ∑ t ∈ Finset.range H, visitReward C p (h0.length + t) w)) ≤
      (A : ℝ) * expectation _ ((historyEvent C h0).indicator
        (fun p ↦ ∑ t ∈ Finset.range H, emptyReward C p (h0.length + t)))
  rw [expectation_indicator_sum, expectation_indicator_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun t _ ↦ joint_step_visit_le_empty a b ha1 hb A hupper C h0 t w

/-- Under the exact nonnull initial visible fiber, finite future empty hits are bounded by
the initial empty count; this is a pathwise fact rather than a conditioning assumption. -/
theorem conditional_emptyHitCount_le_initial {n : ℕ} (a b : Fin n → ℝ≥0)
    (C : Protocol n) (h0 : List (Entry n))
    (hpos : FiniteConditioning.eventMass (profileLaw a b) (historyEvent C h0) ≠ 0)
    (H k : ℕ) (hk : (emptyWomen h0).card ≤ k) :
    expectation (FiniteConditioning.condition (profileLaw a b) (historyEvent C h0))
      (fun p ↦ emptyHitCount C p h0.length H) ≤ k := by
  rw [← expectation_const (FiniteConditioning.condition (profileLaw a b) (historyEvent C h0))
    (k : ℝ)]
  apply expectation_mono_support
  intro p hp
  have hs := FiniteConditioning.support_condition (profileLaw a b) (historyEvent C h0) hpos
  have hh : profileTranscript C p h0.length = h0 := (hs ▸ hp).1
  have hb := emptyHitCount_le_initial C p h0.length H
  rw [hh] at hb
  exact hb.trans (by exact_mod_cast hk)

/-- Actual finite-horizon expected visits are at most `A*k` when initially at most `k`
women are empty. Partial schedules and arbitrary pauses are allowed. -/
theorem expected_visitCount_le {n : ℕ} (a b : Fin n → ℝ≥0)
    (ha1 : ∀ w, 1 ≤ a w) (hb : ∀ m, 0 < b m) (A : ℝ≥0)
    (hupper : ∀ w, a w ≤ A) (C : Protocol n) (h0 : List (Entry n))
    (hpos : FiniteConditioning.eventMass (profileLaw a b) (historyEvent C h0) ≠ 0)
    (H k : ℕ) (hk : (emptyWomen h0).card ≤ k) (w : Fin n) :
    expectation (FiniteConditioning.condition (profileLaw a b) (historyEvent C h0))
      (fun p ↦ visitCount C p h0.length H w) ≤ (A : ℝ) * k := by
  exact (conditional_visitCount_le_emptyHitCount a b ha1 hb A hupper C h0 hpos H w).trans
    (mul_le_mul_of_nonneg_left (conditional_emptyHitCount_le_initial a b C h0 hpos H k hk)
      A.coe_nonneg)

/-- Seen edges in a suffix were already seen in the full newest-first history. -/
theorem seenEdges_drop_subset {n : ℕ} (h : List (Entry n)) (t : ℕ) :
    seenEdges (h.drop t) ⊆ seenEdges h := by
  induction t generalizing h with
  | zero => exact Finset.Subset.refl _
  | succ t ih =>
    cases h with
    | nil => simp [seenEdges]
    | cons entry h =>
      simpa only [List.drop_succ_cons] using (ih h).trans (seenEdges_tail_subset entry h)

/-- Accumulated distinct-proposer score is a finite sum over seen men. -/
theorem gamma_eq_filter {n : ℕ} (b : Fin n → ℝ≥0) (h : List (Entry n)) (w : Fin n) :
    gamma b h w = ∑ m ∈ Finset.univ.filter (fun m ↦ (w, m) ∈ seenEdges h), (b m : ℝ) := by
  classical
  exact (Finset.sum_subtype _ (by simp) (fun m ↦ (b m : ℝ))).symm

/-- A past-only accumulated score lower bound persists through all future records. -/
theorem gamma_drop_le {n : ℕ} (b : Fin n → ℝ≥0) (h : List (Entry n)) (w : Fin n) (t : ℕ) :
    gamma b (h.drop t) w ≤ gamma b h w := by
  classical
  rw [gamma_eq_filter, gamma_eq_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      seenEdges_drop_subset h t (Finset.mem_filter.mp hm).2⟩
  · intro m _ _
    exact (b m).coe_nonneg

/-- A next accepted challenge to the fixed woman, jointly with the current visible history. -/
def acceptedVisitEvent {n : ℕ} (C : Protocol n) (h : List (Entry n)) (w : Fin n) :
    Set (Profile n) := {p | ∃ m, p ∈ acceptedEdgeEvent C h w m}

/-- Fixing the visible selected man also fixes the proposer of any accepted challenge. -/
theorem acceptedVisitEvent_eq_edge {n : ℕ} (C : Protocol n) (h : List (Entry n))
    (w m : Fin n) (hs : selected C h = some m) :
    acceptedVisitEvent C h w = acceptedEdgeEvent C h w m := by
  ext p
  constructor
  · rintro ⟨k, hk⟩
    have hm := nextEdge_map_man C p.manRank h
    rw [hk.2.1, Option.map_some, hs] at hm
    have he : k = m := Option.some.inj hm
    subst k
    exact hk
  · exact fun hp ↦ ⟨m, hp⟩

/-- The exact accepted-challenge joint hazard is bounded by current visit probability. -/
theorem actual_accepted_measure_le_visit {n : ℕ} (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m)
    (C : Protocol n) (h : List (Entry n)) (w : Fin n) (B g : ℝ)
    (hg : 0 < g) (hB : ∀ m, (b m : ℝ) ≤ B) (hgamma : g ≤ gamma b h w) :
    (profileLaw a b).toMeasure (acceptedVisitEvent C h w) ≤
      ENNReal.ofReal (B / g) * (profileLaw a b).toMeasure (visitEvent C h w) := by
  cases hs : selected C h with
  | none =>
    have he : acceptedVisitEvent C h w = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro p ⟨m, hp⟩
      have hv : p ∈ visitEvent C h w := ⟨m, hp.1, hp.2.1⟩
      rw [visitEvent_eq_empty_of_paused C h w hs] at hv
      exact hv
    rw [he, measure_empty]
    exact zero_le
  | some m =>
    rw [acceptedVisitEvent_eq_edge C h w m hs, visitEvent_eq_edgeEvent C h w m hs]
    exact acceptedEdge_measure_le_visit a b ha hb C h w m B g hg (hB m) hgamma

/-- The actual next accepted-challenge predicate at a deterministic protocol time. -/
def isAcceptedVisit {n : ℕ} (C : Protocol n) (p : Profile n) (t : ℕ) (w : Fin n) : Prop :=
  ∃ m, nextEdge C p.manRank (profileTranscript C p t) = some (w, m) ∧
    accept (profilePriorities p) (recordState (profileTranscript C p t)) (w, m) = true

open scoped Classical in
/-- Accepted-challenge indicator; all rejected proposals and protocol pauses contribute zero. -/
noncomputable def acceptedReward {n : ℕ} (C : Protocol n) (p : Profile n) (t : ℕ)
    (w : Fin n) : ℝ := if isAcceptedVisit C p t w then 1 else 0

/-- The actual accepted reward has the exact visible-fiber joint-event expectation. -/
theorem fiber_acceptedReward {n : ℕ} (law : PMF (Profile n)) (C : Protocol n)
    (t : ℕ) (h : List (Entry n)) (hlen : h.length = t) (w : Fin n) :
    fiberExpectation law (fun p ↦ profileTranscript C p t) h (fun p ↦ acceptedReward C p t w) =
      (law.toMeasure (acceptedVisitEvent C h w)).toReal := by
  have hfun : (fun p ↦ acceptedReward C p t w) =
      {p | isAcceptedVisit C p t w}.indicator (fun _ ↦ (1 : ℝ)) := by
    classical
    funext p
    simp [acceptedReward, Set.indicator]
  rw [hfun, fiber_indicator_eq_eventMass, FiniteConditioning.eventMass_eq_toMeasure _ _
    (by trivial)]
  congr 1
  apply congrArg law.toMeasure
  ext p
  constructor
  · rintro ⟨hh, m, hm, ha⟩
    change profileTranscript C p t = h at hh
    exact ⟨m, by simpa only [hlen] using hh, by simpa only [hh] using hm,
      by simpa only [hh] using ha⟩
  · rintro ⟨m, hh, hm, ha⟩
    have hh' : profileTranscript C p t = h := by simpa only [hlen] using hh
    exact ⟨hh', m, by simpa only [hh'] using hm, by simpa only [hh'] using ha⟩

/-- Current accumulated score controls the actual accepted-challenge fiber expectation. -/
theorem fiber_accepted_le_visit {n : ℕ} (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (C : Protocol n) (t : ℕ)
    (h : List (Entry n)) (hlen : h.length = t) (w : Fin n) (B g : ℝ)
    (hg : 0 < g) (hB : ∀ m, (b m : ℝ) ≤ B) (hgamma : g ≤ gamma b h w) :
    fiberExpectation (profileLaw a b) (fun p ↦ profileTranscript C p t) h
      (fun p ↦ acceptedReward C p t w) ≤
      (B / g) * fiberExpectation (profileLaw a b) (fun p ↦ profileTranscript C p t) h
        (fun p ↦ visitReward C p t w) := by
  rw [fiber_acceptedReward _ _ _ _ hlen, fiber_visitReward _ _ _ _ hlen]
  have hB0 : 0 ≤ B := (b w).coe_nonneg.trans (hB w)
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (actual_accepted_measure_le_visit a b ha hb C h w B g hg hB hgamma)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_nonneg hB0 hg.le)] using hh

/-- A visible transcript with the wrong deterministic length has zero fiber contribution. -/
theorem fiber_wrong_length {n : ℕ} (law : PMF (Profile n)) (C : Protocol n) (t : ℕ)
    (h : List (Entry n)) (hlen : h.length ≠ t) (F : Profile n → ℝ) :
    fiberExpectation law (fun p ↦ profileTranscript C p t) h F = 0 := by
  classical
  unfold fiberExpectation
  rw [Finset.sum_filter]
  apply Finset.sum_eq_zero
  intro p _
  by_cases he : profileTranscript C p t = h
  · have hl : h.length = t := by
      rw [← he]
      exact Protocols.transcript_length C p.manRank (profilePriorities p) _
    exact False.elim (hlen hl)
  · simp [he]

/-- The initial lower bound on seen score yields the accepted-versus-visit comparison at
every later step, using only restrictions measurable from that step's visible past. -/
theorem joint_step_accepted_le_visit {n : ℕ} (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (C : Protocol n)
    (h0 : List (Entry n)) (t : ℕ) (w : Fin n) (B g : ℝ)
    (hg : 0 < g) (hB : ∀ m, (b m : ℝ) ≤ B) (hgamma : g ≤ gamma b h0 w) :
    expectation (profileLaw a b) ((historyEvent C h0).indicator
      (fun p ↦ acceptedReward C p (h0.length + t) w)) ≤
      (B / g) * expectation (profileLaw a b) ((historyEvent C h0).indicator
        (fun p ↦ visitReward C p (h0.length + t) w)) := by
  classical
  have hh := expectation_masked_le (profileLaw a b)
    (fun p ↦ profileTranscript C p (h0.length + t)) (fun h ↦ h.drop t = h0)
    (fun p ↦ acceptedReward C p (h0.length + t) w)
    (fun p ↦ visitReward C p (h0.length + t) w) (B / g) (fun h _ hmask ↦ by
      by_cases hlen : h.length = h0.length + t
      · apply fiber_accepted_le_visit a b ha hb C _ h hlen w B g hg hB
        have hpast : g ≤ gamma b (h.drop t) w := by simpa only [hmask] using hgamma
        exact hpast.trans (gamma_drop_le b h w t)
      · rw [fiber_wrong_length _ _ _ _ hlen, fiber_wrong_length _ _ _ _ hlen, mul_zero])
  simpa [expectation, profileTranscript_drop, Set.indicator_apply, historyEvent] using hh

/-- The finite actual number of accepted challenges to a specified woman. -/
noncomputable def acceptedCount {n : ℕ} (C : Protocol n) (p : Profile n)
    (start H : ℕ) (w : Fin n) : ℝ :=
  ∑ t ∈ Finset.range H, acceptedReward C p (start + t) w

/-- Actual conditional expected accepted challenges are at most `B/g` times expected visits. -/
theorem conditional_acceptedCount_le_visitCount {n : ℕ} (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (C : Protocol n)
    (h0 : List (Entry n))
    (hpos : FiniteConditioning.eventMass (profileLaw a b) (historyEvent C h0) ≠ 0)
    (H : ℕ) (w : Fin n) (B g : ℝ) (hg : 0 < g) (hB : ∀ m, (b m : ℝ) ≤ B)
    (hgamma : g ≤ gamma b h0 w) :
    expectation (FiniteConditioning.condition (profileLaw a b) (historyEvent C h0))
      (fun p ↦ acceptedCount C p h0.length H w) ≤
      (B / g) * expectation (FiniteConditioning.condition (profileLaw a b) (historyEvent C h0))
        (fun p ↦ visitCount C p h0.length H w) := by
  apply conditional_expectation_le _ _ hpos
  change expectation _ ((historyEvent C h0).indicator
    (fun p ↦ ∑ t ∈ Finset.range H, acceptedReward C p (h0.length + t) w)) ≤
      (B / g) * expectation _ ((historyEvent C h0).indicator
        (fun p ↦ ∑ t ∈ Finset.range H, visitReward C p (h0.length + t) w))
  rw [expectation_indicator_sum, expectation_indicator_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun t _ ↦ joint_step_accepted_le_visit a b ha hb C h0 t w B g
    hg hB hgamma

/-- Exact source rest-phase input: at most `A*k*B/g` accepted challenges in finite future
horizon, with no conditioning on a future proposal count. -/
theorem expected_acceptedCount_le {n : ℕ} (a b : Fin n → ℝ≥0)
    (ha1 : ∀ w, 1 ≤ a w) (hb : ∀ m, 0 < b m) (A : ℝ≥0)
    (hupper : ∀ w, a w ≤ A) (C : Protocol n) (h0 : List (Entry n))
    (hpos : FiniteConditioning.eventMass (profileLaw a b) (historyEvent C h0) ≠ 0)
    (H k : ℕ) (hk : (emptyWomen h0).card ≤ k) (w : Fin n) (B g : ℝ)
    (hg : 0 < g) (hB : ∀ m, (b m : ℝ) ≤ B) (hgamma : g ≤ gamma b h0 w) :
    expectation (FiniteConditioning.condition (profileLaw a b) (historyEvent C h0))
      (fun p ↦ acceptedCount C p h0.length H w) ≤ (A : ℝ) * k * B / g := by
  have hB0 : 0 ≤ B := (b w).coe_nonneg.trans (hB w)
  calc
    _ ≤ (B / g) * expectation
        (FiniteConditioning.condition (profileLaw a b) (historyEvent C h0))
        (fun p ↦ visitCount C p h0.length H w) :=
      conditional_acceptedCount_le_visitCount a b
        (fun v ↦ lt_of_lt_of_le (by norm_num) (ha1 v)) hb C h0 hpos H w B g hg hB hgamma
    _ ≤ (B / g) * ((A : ℝ) * k) := mul_le_mul_of_nonneg_left
      (expected_visitCount_le a b ha1 hb A hupper C h0 hpos H k hk w) (div_nonneg hB0 hg.le)
    _ = _ := by ring

/-- Every finite accepted-reward sum is nonnegative. -/
theorem acceptedCount_nonneg {n : ℕ} (C : Protocol n) (p : Profile n)
    (start H : ℕ) (w : Fin n) : 0 ≤ acceptedCount C p start H w := by
  classical
  apply Finset.sum_nonneg
  intro t _
  simp only [acceptedReward]
  split_ifs <;> norm_num

/-- If no accepted proposal reaches this woman at the current step, her holder is unchanged. -/
theorem held_step_eq_of_not_accepted {n : ℕ} (C : Protocol n) (p : Profile n)
    (t : ℕ) (w : Fin n) (hno : ¬isAcceptedVisit C p t w) :
    (recordState (profileTranscript C p (t + 1))).held w =
      (recordState (profileTranscript C p t)).held w := by
  classical
  let h := profileTranscript C p t
  change (recordStep (recordState h)
    (Protocols.observation C p.manRank (profilePriorities p) h)).held w = _
  cases hn : nextEdge C p.manRank h with
  | none => simp [Protocols.observation, hn, recordStep, h]
  | some q =>
    obtain ⟨v, m⟩ := q
    cases ha : accept (profilePriorities p) (recordState h) (v, m) with
    | false => simp [Protocols.observation, hn, ha, recordStep, h]
    | true =>
      have hw : w ≠ v := by
        intro he
        subst v
        exact hno ⟨m, hn, ha⟩
      simp [Protocols.observation, hn, ha, recordStep, hw, h]

/-- Displacement by a finite horizon means the initial holder is absent at some observed
time no later than that horizon, rather than merely absent at its final time. -/
def displacedBy {n : ℕ} (C : Protocol n) (p : Profile n) (start H : ℕ)
    (w u : Fin n) : Prop :=
  ∃ t ≤ H, (recordState (profileTranscript C p (start + t))).held w ≠ some u

/-- An actual displacement necessarily has an accepted challenge at that woman. -/
theorem exists_accepted_of_displaced {n : ℕ} (C : Protocol n) (p : Profile n)
    (start H : ℕ) (w u : Fin n)
    (hheld : (recordState (profileTranscript C p start)).held w = some u)
    (hdisp : displacedBy C p start H w u) :
    ∃ t < H, isAcceptedVisit C p (start + t) w := by
  induction H with
  | zero =>
    obtain ⟨t, ht, hh⟩ := hdisp
    have he : t = 0 := by omega
    simp [he, hheld] at hh
  | succ H ih =>
    obtain ⟨t, ht, hh⟩ := hdisp
    by_cases htle : t ≤ H
    · obtain ⟨s, hs, ha⟩ := ih ⟨t, htle, hh⟩
      exact ⟨s, by omega, ha⟩
    · have he : t = H + 1 := by omega
      subst t
      by_cases hold : (recordState (profileTranscript C p (start + H))).held w = some u
      · have ha : isAcceptedVisit C p (start + H) w := by
          by_contra hno
          have hs := held_step_eq_of_not_accepted C p (start + H) w hno
          rw [hold] at hs
          exact hh (by simpa [Nat.add_assoc] using hs)
        exact ⟨H, by omega, ha⟩
      · obtain ⟨s, hs, ha⟩ := ih ⟨H, le_rfl, hold⟩
        exact ⟨s, by omega, ha⟩

/-- The pathwise displacement indicator is bounded by the actual accepted-challenge count. -/
theorem displacement_indicator_le_count {n : ℕ} (C : Protocol n) (p : Profile n)
    (start H : ℕ) (w u : Fin n)
    (hheld : (recordState (profileTranscript C p start)).held w = some u) :
    {p | displacedBy C p start H w u}.indicator (fun _ ↦ (1 : ℝ)) p ≤
      acceptedCount C p start H w := by
  classical
  by_cases hd : displacedBy C p start H w u
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hd]
    obtain ⟨t, ht, ha⟩ := exists_accepted_of_displaced C p start H w u hheld hd
    have hterm : acceptedReward C p (start + t) w = 1 := by simp [acceptedReward, ha]
    rw [← hterm]
    unfold acceptedCount
    exact Finset.single_le_sum (f := fun s ↦ acceptedReward C p (start + s) w) (fun s _ ↦ by
      simp only [acceptedReward]
      split_ifs <;> norm_num) (Finset.mem_range.mpr ht)
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hd]
    exact acceptedCount_nonneg C p start H w

/-- Indicator expectation is the actual finite event's real probability. -/
theorem expectation_indicator_one {Ω : Type*} [Fintype Ω] (law : PMF Ω) (E : Set Ω) :
    expectation law (E.indicator (fun _ ↦ (1 : ℝ))) =
      (FiniteConditioning.eventMass law E).toReal := by
  rw [← history_mass_mul_expectation, expectation_const, mul_one]

/-- The source's future-displacement bound under the exact PR conditional visible law. -/
theorem displacement_probability_le {n : ℕ} (a b : Fin n → ℝ≥0)
    (ha1 : ∀ w, 1 ≤ a w) (hb : ∀ m, 0 < b m) (A : ℝ≥0)
    (hupper : ∀ w, a w ≤ A) (C : Protocol n) (h0 : List (Entry n))
    (hpos : FiniteConditioning.eventMass (profileLaw a b) (historyEvent C h0) ≠ 0)
    (H k : ℕ) (hk : (emptyWomen h0).card ≤ k) (w u : Fin n)
    (hheld : (recordState h0).held w = some u) (B g : ℝ)
    (hg : 0 < g) (hB : ∀ m, (b m : ℝ) ≤ B) (hgamma : g ≤ gamma b h0 w) :
    (FiniteConditioning.eventMass
      (FiniteConditioning.condition (profileLaw a b) (historyEvent C h0))
      {p | displacedBy C p h0.length H w u}).toReal ≤ (A : ℝ) * k * B / g := by
  rw [← expectation_indicator_one]
  apply le_trans _ (expected_acceptedCount_le a b ha1 hb A hupper C h0 hpos H k hk w B g
    hg hB hgamma)
  apply expectation_mono_support
  intro p hp
  have hs := FiniteConditioning.support_condition (profileLaw a b) (historyEvent C h0) hpos
  have hh : profileTranscript C p h0.length = h0 := (hs ▸ hp).1
  exact displacement_indicator_le_count C p h0.length H w u (by simpa only [hh] using hheld)

/-- The finite future actual visit count is integrable under the exact conditional profile law. -/
theorem integrable_visitCount {n : ℕ} (a b : Fin n → ℝ≥0) (C : Protocol n)
    (h0 : List (Entry n)) (H : ℕ) (w : Fin n) :
    Integrable (fun p ↦ visitCount C p h0.length H w)
      (FiniteConditioning.condition (profileLaw a b) (historyEvent C h0)).toMeasure :=
  Integrable.of_finite

/-- The finite future accepted-challenge count is integrable under the same actual law. -/
theorem integrable_acceptedCount {n : ℕ} (a b : Fin n → ℝ≥0) (C : Protocol n)
    (h0 : List (Entry n)) (H : ℕ) (w : Fin n) :
    Integrable (fun p ↦ acceptedCount C p h0.length H w)
      (FiniteConditioning.condition (profileLaw a b) (historyEvent C h0)).toMeasure :=
  Integrable.of_finite

end Ashlagi.VisitBounds
