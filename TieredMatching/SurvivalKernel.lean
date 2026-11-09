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

public import TieredMatching.HazardMoments
public import TieredMatching.ProfileHistories

/-! # Actual finite-history survival recursions

Conditional next-success envelopes are integrated over actual observation fibers. Null fibers
carry zero observation mass, and no unconditional survival recurrence is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace TieredMatching.SurvivalKernel

open FiniteConditioning

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Actual real probability of a finite-law event. -/
noncomputable def probability (μ : PMF Ω) (S : Set Ω) : ℝ := (eventMass μ S).toReal

/-- Discrete conditional-event notation agrees with the actual probability measure. -/
theorem probability_eq_real (μ : PMF Ω) (S : Set Ω) :
    probability μ S = μ.toMeasure.real S := by
  rw [probability, eventMass_eq_toMeasure μ S (Set.toFinite S).measurableSet]
  rfl

omit [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- Real probabilities are nonnegative. -/
theorem probability_nonneg (μ : PMF Ω) (S : Set Ω) : 0 ≤ probability μ S :=
  ENNReal.toReal_nonneg

/-- The certain event has probability one. -/
theorem probability_univ (μ : PMF Ω) : probability μ Set.univ = 1 := by
  rw [probability_eq_real, probReal_univ]

/-- The impossible event has probability zero. -/
theorem probability_empty (μ : PMF Ω) : probability μ ∅ = 0 := by
  rw [probability_eq_real]
  simp

/-- Complement probabilities are exact for the actual finite conditional laws. -/
theorem probability_compl (μ : PMF Ω) (S : Set Ω) :
    probability μ Sᶜ = 1 - probability μ S := by
  rw [probability_eq_real, probability_eq_real,
    measureReal_compl (Set.toFinite S).measurableSet, probReal_univ]

/-- Event identities need hold only on points of positive actual probability. -/
theorem probability_congr_support (μ : PMF Ω) (S T : Set Ω)
    (hST : ∀ ω, μ ω ≠ 0 → (ω ∈ S ↔ ω ∈ T)) :
    probability μ S = probability μ T := by
  rw [probability_eq_real, probability_eq_real]
  apply congrArg ENNReal.toReal
  apply μ.toMeasure_apply_eq_of_inter_support_eq (Set.toFinite S).measurableSet
    (Set.toFinite T).measurableSet
  ext ω
  change (ω ∈ S ∧ μ ω ≠ 0) ↔ (ω ∈ T ∧ μ ω ≠ 0)
  by_cases hp : μ ω = 0
  · simp [hp]
  · exact and_congr (hST ω hp) Iff.rfl

omit [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- A positive conditioned point belongs to its literal observed fiber and the original support. -/
theorem condition_fiber_support {R : Type*} (μ : PMF Ω) (observe : Ω → R) (r : R)
    (hr : eventMass μ {ω | observe ω = r} ≠ 0) (ω : Ω)
    (hω : condition μ {ω | observe ω = r} ω ≠ 0) : μ ω ≠ 0 ∧ observe ω = r := by
  have hs : ω ∈ (condition μ {ω | observe ω = r}).support := hω
  rw [support_condition μ _ hr] at hs
  exact ⟨hs.2, hs.1⟩

/-- Exact finite observation disintegration of every real event probability. -/
theorem probability_disintegrate {R : Type*} [Fintype R] (μ : PMF Ω)
    (observe : Ω → R) (S : Set Ω) :
    probability μ S = ∑ r, ((μ.map observe) r).toReal *
      probability (condition μ {ω | observe ω = r}) S := by
  classical
  let : MeasurableSpace R := ⊤
  have hint (ν : PMF Ω) : (∫ ω, S.indicator (fun _ ↦ (1 : ℝ)) ω ∂ν.toMeasure) =
      probability ν S := by
    rw [integral_indicator_const 1 (Set.toFinite S).measurableSet, probability_eq_real]
    simp
  have hh := G2Deconditioning.integral_bind (μ.map observe)
    (fun r ↦ condition μ {ω | observe ω = r}) (S.indicator (fun _ ↦ (1 : ℝ)))
  rw [bind_condition_eq, hint, PMF.integral_eq_sum] at hh
  simpa only [hint, smul_eq_mul] using hh

/-- Literal conditional next-success probabilities imply the actual one-step survival bounds.
The current survival event is known from the revealed observation, and the next survival event
is exactly current survival without that next success, both only on the original support.
-/
theorem survival_step_finite {R : Type*} [Fintype R] (μ : PMF Ω) (A : Ω → ℕ)
    (observe : Ω → R) (alive : Set R) (success : Set Ω) (t : ℕ) (p δ : ℝ)
    (hknown : ∀ ω, μ ω ≠ 0 → (t < A ω ↔ observe ω ∈ alive))
    (hstep : ∀ ω, μ ω ≠ 0 → (t + 1 < A ω ↔ t < A ω ∧ ω ∉ success))
    (hhazard : ∀ r, eventMass μ {ω | observe ω = r} ≠ 0 → r ∈ alive →
      p - δ ≤ probability (condition μ {ω | observe ω = r}) success ∧
        probability (condition μ {ω | observe ω = r}) success ≤ p + δ) :
    (1 - p - δ) * HazardMoments.survival μ A t ≤ HazardMoments.survival μ A (t + 1) ∧
      HazardMoments.survival μ A (t + 1) ≤ (1 - p + δ) * HazardMoments.survival μ A t := by
  classical
  let S : Set Ω := {ω | t < A ω}
  let T : Set Ω := {ω | t + 1 < A ω}
  let K (r : R) := condition μ {ω | observe ω = r}
  let w (r : R) := ((μ.map observe) r).toReal
  have hcond (r : R) (hr : eventMass μ {ω | observe ω = r} ≠ 0) :
      (1 - p - δ) * probability (K r) S ≤ probability (K r) T ∧
        probability (K r) T ≤ (1 - p + δ) * probability (K r) S := by
    have hsupp (ω : Ω) (hω : K r ω ≠ 0) := condition_fiber_support μ observe r hr ω hω
    by_cases ha : r ∈ alive
    · have hS : probability (K r) S = 1 := by
        rw [← probability_univ (K r)]
        apply probability_congr_support
        intro ω hω
        have hh := hsupp ω hω
        simpa only [S, Set.mem_ofPred_eq, Set.mem_univ, iff_true] using
          (hknown ω hh.1).mpr (hh.2 ▸ ha)
      have hT : probability (K r) T = probability (K r) successᶜ := by
        apply probability_congr_support
        intro ω hω
        have hh := hsupp ω hω
        have hsurv : t < A ω := (hknown ω hh.1).mpr (hh.2 ▸ ha)
        simpa only [T, Set.mem_ofPred_eq, Set.mem_compl_iff, hsurv, true_and] using hstep ω hh.1
      rw [hS, hT, probability_compl, mul_one, mul_one]
      have hh := hhazard r hr ha
      constructor <;> linarith
    · have hS : probability (K r) S = 0 := by
        rw [← probability_empty (K r)]
        apply probability_congr_support
        intro ω hω
        have hh := hsupp ω hω
        have hn : ¬t < A ω := fun h ↦ ha (hh.2 ▸ (hknown ω hh.1).mp h)
        simp only [S, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact hn
      have hT : probability (K r) T = 0 := by
        rw [← probability_empty (K r)]
        apply probability_congr_support
        intro ω hω
        have hh := hsupp ω hω
        have hn : ¬t < A ω := fun h ↦ ha (hh.2 ▸ (hknown ω hh.1).mp h)
        simp only [T, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro ht
        exact hn (by omega)
      simp only [hS, hT, mul_zero, le_refl, and_self]
  have hlow : (1 - p - δ) * probability μ S ≤ probability μ T := by
    rw [probability_disintegrate μ observe S, probability_disintegrate μ observe T,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    by_cases hr : eventMass μ {ω | observe ω = r} = 0
    · have hz : (μ.map observe) r = 0 := by rw [← eventMass_observation_fiber]; exact hr
      simp only [hz, ENNReal.toReal_zero, zero_mul, mul_zero, le_refl]
    · have hh := mul_le_mul_of_nonneg_left (hcond r hr).1
        (show 0 ≤ w r from ENNReal.toReal_nonneg)
      dsimp only [K, w] at hh
      nlinarith
  have hupp : probability μ T ≤ (1 - p + δ) * probability μ S := by
    rw [probability_disintegrate μ observe S, probability_disintegrate μ observe T,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    by_cases hr : eventMass μ {ω | observe ω = r} = 0
    · have hz : (μ.map observe) r = 0 := by rw [← eventMass_observation_fiber]; exact hr
      simp only [hz, ENNReal.toReal_zero, zero_mul, mul_zero, le_refl]
    · have hh := mul_le_mul_of_nonneg_left (hcond r hr).2
        (show 0 ≤ w r from ENNReal.toReal_nonneg)
      dsimp only [K, w] at hh
      nlinarith
  simpa only [probability_eq_real, S, T, HazardMoments.survival] using And.intro hlow hupp

/-- Exact survival recursion for arbitrary actual history labels with finite source range. -/
theorem survival_step_of_history_success {R : Type*} (μ : PMF Ω) (A : Ω → ℕ)
    (observe : Ω → R) (alive : Set R) (success : Set Ω) (t : ℕ) (p δ : ℝ)
    (hknown : ∀ ω, μ ω ≠ 0 → (t < A ω ↔ observe ω ∈ alive))
    (hstep : ∀ ω, μ ω ≠ 0 → (t + 1 < A ω ↔ t < A ω ∧ ω ∉ success))
    (hhazard : ∀ r, eventMass μ {ω | observe ω = r} ≠ 0 → r ∈ alive →
      p - δ ≤ probability (condition μ {ω | observe ω = r}) success ∧
        probability (condition μ {ω | observe ω = r}) success ≤ p + δ) :
    (1 - p - δ) * HazardMoments.survival μ A t ≤ HazardMoments.survival μ A (t + 1) ∧
      HazardMoments.survival μ A (t + 1) ≤ (1 - p + δ) * HazardMoments.survival μ A t := by
  classical
  let O := Set.range observe
  let : Fintype O := (Set.finite_range observe).fintype
  let obs : Ω → O := fun ω ↦ ⟨observe ω, ⟨ω, rfl⟩⟩
  let good : Set O := Subtype.val ⁻¹' alive
  apply survival_step_finite μ A obs good success t p δ hknown hstep
  intro r hr hg
  have hfiber : {ω | obs ω = r} = {ω | observe ω = r.val} := by
    ext ω
    change (obs ω = r) ↔ observe ω = r.val
    exact Subtype.ext_iff
  rw [hfiber] at hr ⊢
  exact hhazard r.val hr hg

/-- Visibility on actual history fibers supplies the alive predicate. -/
theorem survival_step_of_visible_success {R : Type*} (μ : PMF Ω) (A : Ω → ℕ)
    (observe : Ω → R) (success : Set Ω) (t : ℕ) (p δ : ℝ)
    (hvisible : ∀ ω ω', μ ω ≠ 0 → μ ω' ≠ 0 → observe ω = observe ω' →
      (t < A ω ↔ t < A ω'))
    (hstep : ∀ ω, μ ω ≠ 0 → (t + 1 < A ω ↔ t < A ω ∧ ω ∉ success))
    (hhazard : ∀ r, eventMass μ {ω | observe ω = r} ≠ 0 →
      (∃ ω, μ ω ≠ 0 ∧ observe ω = r ∧ t < A ω) →
      p - δ ≤ probability (condition μ {ω | observe ω = r}) success ∧
        probability (condition μ {ω | observe ω = r}) success ≤ p + δ) :
    (1 - p - δ) * HazardMoments.survival μ A t ≤ HazardMoments.survival μ A (t + 1) ∧
      HazardMoments.survival μ A (t + 1) ≤ (1 - p + δ) * HazardMoments.survival μ A t := by
  let alive : Set R := {r | ∃ ω, μ ω ≠ 0 ∧ observe ω = r ∧ t < A ω}
  apply survival_step_of_history_success μ A observe alive success t p δ ?_ hstep hhazard
  intro ω hω
  constructor
  · intro hs
    exact ⟨ω, hω, rfl, hs⟩
  · rintro ⟨ω', hω', heq, hs⟩
    exact (hvisible ω ω' hω hω' heq.symm).mpr hs

omit [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- A positive current-law observation branch has a nonnull original refined event. -/
theorem refined_event_nonnull {R : Type*} (μ : PMF Ω) (setup : Set Ω)
    (hsetup : eventMass μ setup ≠ 0) (observe : Ω → R) (r : R)
    (hr : ((condition μ setup).map observe) r ≠ 0) :
    eventMass μ (setup ∩ {ω | observe ω = r}) ≠ 0 := by
  rw [← eventMass_mul_conditional_event, eventMass_observation_fiber]
  exact mul_ne_zero hsetup hr

omit [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- Literal refined-prefix conditioning agrees with sequential conditioning on nonnull branches. -/
theorem condition_refined_event {R : Type*} (μ : PMF Ω) (setup : Set Ω)
    (hsetup : eventMass μ setup ≠ 0) (observe : Ω → R) (child : R → Set Ω) (r : R)
    (hr : ((condition μ setup).map observe) r ≠ 0)
    (hrefine : child r = setup ∩ {ω | observe ω = r}) :
    condition (condition μ setup) {ω | observe ω = r} = condition μ (child r) := by
  rw [hrefine]
  exact StoppedProcess.condition_inter μ setup _
    (refined_event_nonnull μ setup hsetup observe r hr)

omit [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- Actual observation disintegration may use literal original-law refined-prefix conditionals.
Refinement is required only on positive observation branches; null default laws have zero weight.
-/
theorem bind_refined_condition {R : Type*} (μ : PMF Ω) (setup : Set Ω)
    (hsetup : eventMass μ setup ≠ 0) (observe : Ω → R) (child : R → Set Ω)
    (hrefine : ∀ r, ((condition μ setup).map observe) r ≠ 0 →
      child r = setup ∩ {ω | observe ω = r}) :
    ((condition μ setup).map observe).bind (fun r ↦ condition μ (child r)) =
      condition μ setup := by
  calc
    _ = ((condition μ setup).map observe).bind
        (fun r ↦ condition (condition μ setup) {ω | observe ω = r}) := by
      apply StoppedProcess.bind_congr_support
      intro r hr
      exact (condition_refined_event μ setup hsetup observe child r hr (hrefine r hr)).symm
    _ = condition μ setup := bind_condition_eq _ _

omit [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- Every future observable inherits the exact actual-history refined conditional tower. -/
theorem map_refined_condition {R B : Type*} (μ : PMF Ω) (setup : Set Ω)
    (hsetup : eventMass μ setup ≠ 0) (observe : Ω → R) (child : R → Set Ω)
    (hrefine : ∀ r, ((condition μ setup).map observe) r ≠ 0 →
      child r = setup ∩ {ω | observe ω = r}) (f : Ω → B) :
    (condition μ setup).map f = ((condition μ setup).map observe).bind
      (fun r ↦ (condition μ (child r)).map f) := by
  rw [← PMF.map_bind, bind_refined_condition μ setup hsetup observe child hrefine]

omit [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- Positive conditional refined-prefix support carries the original history label exactly. -/
theorem refined_support_observation {R : Type*} (μ : PMF Ω) (setup : Set Ω)
    (hsetup : eventMass μ setup ≠ 0) (observe : Ω → R) (child : R → Set Ω) (r : R)
    (hr : ((condition μ setup).map observe) r ≠ 0)
    (hrefine : child r = setup ∩ {ω | observe ω = r}) (ω : Ω)
    (hω : condition μ (child r) ω ≠ 0) : observe ω = r := by
  have hs : ω ∈ (condition μ (child r)).support := hω
  have hn : eventMass μ (child r) ≠ 0 := by
    rw [hrefine]
    exact refined_event_nonnull μ setup hsetup observe r hr
  rw [support_condition μ _ hn, hrefine] at hs
  exact hs.1.2

omit [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- The stopping-history/original-outcome joint law equals its positive-prefix disintegration. -/
theorem joint_refined_condition {R : Type*} (μ : PMF Ω) (setup : Set Ω)
    (hsetup : eventMass μ setup ≠ 0) (observe : Ω → R) (child : R → Set Ω)
    (hrefine : ∀ r, ((condition μ setup).map observe) r ≠ 0 →
      child r = setup ∩ {ω | observe ω = r}) :
    ((condition μ setup).map observe).bind
        (fun r ↦ (condition μ (child r)).map (Prod.mk r)) =
      (condition μ setup).map (fun ω ↦ (observe ω, ω)) := by
  calc
    _ = ((condition μ setup).map observe).bind
        (fun r ↦ (condition μ (child r)).map (fun ω ↦ (observe ω, ω))) := by
      apply StoppedProcess.bind_congr_support
      intro r hr
      apply StoppedProcess.Process.map_congr_support
      intro ω hω
      have he := refined_support_observation μ setup hsetup observe child r hr
        (hrefine r hr) ω hω
      exact Prod.ext he.symm rfl
    _ = (((condition μ setup).map observe).bind (fun r ↦ condition μ (child r))).map
        (fun ω ↦ (observe ω, ω)) := (PMF.map_bind _ _ _).symm
    _ = _ := by rw [bind_refined_condition μ setup hsetup observe child hrefine]

/-- A finite PMF almost surely lies in its positive support. -/
theorem ae_positive_support (μ : PMF Ω) : ∀ᵐ ω ∂μ.toMeasure, μ ω ≠ 0 := by
  rw [ae_iff]
  apply (μ.toMeasure_apply_eq_zero_iff (Set.toFinite _).measurableSet).mpr
  rw [Set.disjoint_left]
  intro ω hω hn
  exact hn hω

/-- Conditional expectation bounds need hold only on positive conditional outcomes. -/
theorem integral_bounds_support (μ : PMF Ω) (f : Ω → ℝ) (N : ℝ)
    (hbound : ∀ ω, μ ω ≠ 0 → 0 ≤ f ω ∧ f ω ≤ N) :
    0 ≤ (∫ ω, f ω ∂μ.toMeasure) ∧ (∫ ω, f ω ∂μ.toMeasure) ≤ N := by
  have hb : ∀ᵐ ω ∂μ.toMeasure, 0 ≤ f ω ∧ f ω ≤ N :=
    (ae_positive_support μ).mono fun ω hω ↦ hbound ω hω
  constructor
  · exact integral_nonneg_of_ae (hb.mono fun _ h ↦ h.1)
  · have hi := integral_mono_ae
      ((G2Deconditioning.memLp_finite μ.toMeasure f).integrable one_le_two)
      (integrable_const N) (hb.mono fun _ h ↦ h.2)
    simpa only [integral_const, probReal_univ, one_smul] using hi

/-- Stopping-history covariance bounds require no mean or boundedness assertions on null labels.
Both first-count and future-count bounds are required only on the actual joint-law support.
-/
theorem initial_covariance_lower_support {H : Type*} [Fintype H] [MeasurableSpace H]
    [MeasurableSingletonClass H] (ν : PMF H) (law : H → PMF Ω)
    (A1 : H → ℝ) (A2 : H → Ω → ℝ) (N M ε c cap : ℝ)
    (hN : 0 ≤ N) (hε : 0 ≤ ε)
    (hA1 : ∀ h, ν h ≠ 0 → 0 ≤ A1 h ∧ A1 h ≤ N)
    (hA2 : ∀ h, ν h ≠ 0 → ∀ ω, law h ω ≠ 0 → 0 ≤ A2 h ω ∧ A2 h ω ≤ N)
    (hc : 0 ≤ c ∧ c ≤ N) (hmean : (∫ h, A1 h ∂ν.toMeasure) ≤ M)
    (hclose : ∀ h, ν h ≠ 0 → A1 h ≤ cap →
      |(∫ ω, A2 h ω ∂(law h).toMeasure) - c| ≤ ε) :
    -2 * M * ε - 2 * N ^ 2 * ν.toMeasure.real {h | cap < A1 h} ≤
      ProbabilityTheory.covariance (fun z : H × Ω ↦ A1 z.1) (fun z ↦ A2 z.1 z.2)
        (HazardMoments.historyFuture ν law).toMeasure := by
  classical
  let X : H → ℝ := fun h ↦ if ν h = 0 then 0 else A1 h
  let Y : H → ℝ := fun h ↦ ∫ ω, A2 h ω ∂(law h).toMeasure
  let Y' : H → ℝ := fun h ↦ if ν h = 0 then c else Y h
  have hX : ∀ h, 0 ≤ X h ∧ X h ≤ N := by
    intro h
    by_cases hh : ν h = 0
    · simp only [X, ite_eq_left hh, le_refl, true_and]
      exact hN
    · simpa only [X, ite_eq_right hh] using hA1 h hh
  have hY : ∀ h, 0 ≤ Y' h ∧ Y' h ≤ N := by
    intro h
    by_cases hh : ν h = 0
    · simpa only [Y', ite_eq_left hh] using hc
    · simpa only [Y', ite_eq_right hh, Y] using
        integral_bounds_support (law h) (A2 h) N (hA2 h hh)
  have hXae : X =ᵐ[ν.toMeasure] A1 := by
    filter_upwards [ae_positive_support ν] with h hh
    simp only [X, ite_eq_right hh]
  have hYae : Y' =ᵐ[ν.toMeasure] Y := by
    filter_upwards [ae_positive_support ν] with h hh
    simp only [Y', ite_eq_right hh]
  have hXM : (∫ h, X h ∂ν.toMeasure) ≤ M := by
    rw [integral_congr_ae hXae]
    exact hmean
  have hclose' (h : H) (hh : h ∈ {h | A1 h ≤ cap}) : |Y' h - c| ≤ ε := by
    by_cases hn : ν h = 0
    · simpa only [Y', ite_eq_left hn, sub_self, abs_zero] using hε
    · simpa only [Y', ite_eq_right hn, Y] using hclose h hn hh
  have hcov : ProbabilityTheory.covariance X Y' ν.toMeasure =
      ProbabilityTheory.covariance A1 Y ν.toMeasure := by
    unfold ProbabilityTheory.covariance
    rw [integral_congr_ae hXae, integral_congr_ae hYae]
    apply integral_congr_ae
    filter_upwards [hXae, hYae] with h hx hy
    rw [hx, hy]
  rw [HazardMoments.covariance_historyFuture]
  have hh := HazardMoments.covariance_lower_of_close_on_good ν X Y' {h | A1 h ≤ cap}
    N M ε c hN hε hX hY hc hXM hclose'
  have heq : ({h | A1 h ≤ cap} : Set H)ᶜ = {h | cap < A1 h} := by ext h; simp
  rw [heq, hcov] at hh
  exact hh

/-- Every actual finite-law event has probability at most one. -/
theorem probability_le_one (μ : PMF Ω) (S : Set Ω) : probability μ S ≤ 1 := by
  rw [probability_eq_real, ← probReal_univ (μ := μ.toMeasure)]
  exact measureReal_mono (Set.subset_univ S)

/-- A good-history conditional bound transfers to the original finite law with the bad mass paid. -/
theorem probability_le_conditional_finite {R : Type*} [Fintype R] (μ : PMF Ω)
    (observe : Ω → R) (good : Set R) (E : Set Ω) (δ : ℝ) (hδ : 0 ≤ δ)
    (hbound : ∀ r, eventMass μ {ω | observe ω = r} ≠ 0 → r ∈ good →
      probability (condition μ {ω | observe ω = r}) E ≤ δ) :
    probability μ E ≤ δ + probability μ {ω | observe ω ∉ good} := by
  classical
  let : MeasurableSpace R := ⊤
  let ν := μ.map observe
  let K (r : R) := condition μ {ω | observe ω = r}
  have hdis : probability μ E = ∫ r, probability (K r) E ∂ν.toMeasure := by
    rw [PMF.integral_eq_sum]
    simpa only [smul_eq_mul] using probability_disintegrate μ observe E
  have hp : ∀ᵐ r ∂ν.toMeasure, probability (K r) E ≤
      δ + goodᶜ.indicator (fun _ ↦ (1 : ℝ)) r := by
    filter_upwards [ae_positive_support ν] with r hr
    have hn : eventMass μ {ω | observe ω = r} ≠ 0 := by
      rwa [eventMass_observation_fiber]
    by_cases hg : r ∈ good
    · have hnot : r ∉ goodᶜ := by simpa using hg
      rw [Set.indicator_of_notMem hnot, add_zero]
      exact hbound r hn hg
    · have hmem : r ∈ goodᶜ := hg
      rw [Set.indicator_of_mem hmem]
      exact (probability_le_one (K r) E).trans (by linarith)
  have hi (f : R → ℝ) : Integrable f ν.toMeasure :=
    (G2Deconditioning.memLp_finite ν.toMeasure f).integrable one_le_two
  have hh := integral_mono_ae (hi _) (hi _) hp
  rw [integral_add (hi _) (hi _), integral_const,
    integral_indicator_const 1 (Set.toFinite goodᶜ).measurableSet] at hh
  simp only [probReal_univ, smul_eq_mul, mul_one, one_mul] at hh
  have hbad : ν.toMeasure.real goodᶜ = probability μ {ω | observe ω ∉ good} := by
    rw [probability_eq_real, measureReal_def, measureReal_def,
      ← PMF.toMeasure_map observe μ (measurable_of_finite observe),
      Measure.map_apply (measurable_of_finite observe) (Set.toFinite goodᶜ).measurableSet]
    rfl
  rw [← hdis, hbad] at hh
  exact hh

/-- Bounds on actual nonnull good observation fibers hold unconditionally up to bad mass.
The observation type may be an arbitrary history-list type; only its actual finite range is used.
-/
theorem probability_le_of_conditional_on_good {R : Type*} (μ : PMF Ω)
    (observe : Ω → R) (good : Set R) (E : Set Ω) (δ : ℝ) (hδ : 0 ≤ δ)
    (hbound : ∀ r, eventMass μ {ω | observe ω = r} ≠ 0 → r ∈ good →
      probability (condition μ {ω | observe ω = r}) E ≤ δ) :
    probability μ E ≤ δ + probability μ {ω | observe ω ∉ good} := by
  classical
  let O := Set.range observe
  let : Fintype O := (Set.finite_range observe).fintype
  let obs : Ω → O := fun ω ↦ ⟨observe ω, ⟨ω, rfl⟩⟩
  let good0 : Set O := Subtype.val ⁻¹' good
  apply probability_le_conditional_finite μ obs good0 E δ hδ
  intro r hr hg
  have hfiber : {ω | obs ω = r} = {ω | observe ω = r.val} := by
    ext ω
    change (obs ω = r) ↔ observe ω = r.val
    exact Subtype.ext_iff
  rw [hfiber] at hr ⊢
  exact hbound r.val hr hg

end TieredMatching.SurvivalKernel
