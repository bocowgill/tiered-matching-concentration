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

public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! # Exact conditioning and observation disintegration for finite DA histories -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace TieredMatching.FiniteConditioning

/-- The mass of a discrete event, before normalization. -/
noncomputable def eventMass {Ω : Type*} (p : PMF Ω) (s : Set Ω) : ℝ≥0∞ :=
  ∑' a, s.indicator p a

/-- Conditioning on a null event uses the original law. Its branch weight is zero,
so this choice does not affect any of the disintegration identities. -/
noncomputable def condition {Ω : Type*} (p : PMF Ω) (s : Set Ω) : PMF Ω := by
  classical
  exact if hs : eventMass p s = 0 then p else
    PMF.normalize (s.indicator p) hs (p.tsum_coe_indicator_ne_top s)

/-- Every event under a PMF has finite mass. -/
theorem eventMass_ne_top {Ω : Type*} (p : PMF Ω) (s : Set Ω) : eventMass p s ≠ ∞ :=
  p.tsum_coe_indicator_ne_top s

/-- Multiplying a conditional point mass by its branch probability recovers the joint mass. -/
theorem eventMass_mul_condition {Ω : Type*} (p : PMF Ω) (s : Set Ω) (a : Ω) :
    eventMass p s * condition p s a = s.indicator p a := by
  classical
  by_cases hs : eventMass p s = 0
  · have ha : s.indicator p a = 0 := ENNReal.tsum_eq_zero.mp hs a
    simp only [hs, zero_mul, ha]
  · simp only [condition, dite_eq_right hs]
    change eventMass p s * (s.indicator p a * (eventMass p s)⁻¹) = _
    calc
      eventMass p s * (s.indicator p a * (eventMass p s)⁻¹) =
          s.indicator p a * (eventMass p s * (eventMass p s)⁻¹) := by ac_rfl
      _ = s.indicator p a := by
        rw [ENNReal.mul_inv_cancel hs (eventMass_ne_top p s), mul_one]

/-- An observation's PMF mass is its exact preimage-event mass. -/
theorem eventMass_observation_fiber {Ω R : Type*} (p : PMF Ω) (observe : Ω → R) (r : R) :
    eventMass p {a | observe a = r} = (p.map observe) r := by
  classical
  rw [PMF.map_apply]
  unfold eventMass
  congr 1
  funext a
  simp only [Set.indicator_apply, mem_ofPred_eq, eq_comm]

open scoped Classical in
/-- The observation law times its conditional law is the exact joint point mass. -/
theorem observation_mul_condition {Ω R : Type*} (p : PMF Ω) (observe : Ω → R)
    (r : R) (a : Ω) :
    (p.map observe) r * condition p {a | observe a = r} a =
      if observe a = r then p a else 0 := by
  classical
  rw [← eventMass_observation_fiber, eventMass_mul_condition]
  simp only [Set.indicator_apply, mem_ofPred_eq]

/-- Splitting by any observation and then using its conditional law recovers the original law. -/
theorem bind_condition_eq {Ω R : Type*} (p : PMF Ω) (observe : Ω → R) :
    (p.map observe).bind (fun r ↦ condition p {a | observe a = r}) = p := by
  classical
  ext a
  rw [PMF.bind_apply]
  simp_rw [observation_mul_condition]
  simp [eq_comm]

/-- Conditional event probabilities satisfy the exact joint-event identity. -/
theorem eventMass_mul_conditional_event {Ω : Type*} (p : PMF Ω) (s t : Set Ω) :
    eventMass p s * eventMass (condition p s) t = eventMass p (s ∩ t) := by
  classical
  unfold eventMass at ⊢
  rw [← ENNReal.tsum_mul_left]
  congr 1
  funext a
  by_cases ht : a ∈ t
  · simpa only [eventMass, Set.indicator_apply, Set.mem_inter_iff, ht, and_true, ite_true]
      using eventMass_mul_condition p s a
  · simp only [Set.indicator_apply, Set.mem_inter_iff, ht, and_false, ite_false, mul_zero]

/-- On a nonnull event, conditioning is the usual ratio of joint and marginal masses. -/
theorem conditional_event_eq_div {Ω : Type*} (p : PMF Ω) (s t : Set Ω)
    (hs : eventMass p s ≠ 0) :
    eventMass (condition p s) t = eventMass p (s ∩ t) / eventMass p s :=
  (ENNReal.eq_div_iff hs (eventMass_ne_top p s)).2 (eventMass_mul_conditional_event p s t)

/-- An exact joint-event transition law gives the exact conditional hazard on every
nonnull history. Zero histories are handled separately by disintegration. -/
theorem conditional_event_of_joint_factor {Ω : Type*} (p : PMF Ω) (s t : Set Ω)
    (hs : eventMass p s ≠ 0) (q : ℝ≥0∞)
    (hjoint : eventMass p (s ∩ t) = q * eventMass p s) :
    eventMass (condition p s) t = q := by
  rw [conditional_event_eq_div p s t hs, hjoint,
    ENNReal.mul_div_cancel_right hs (eventMass_ne_top p s)]

/-- Discrete event masses agree with the probability measure on measurable events. -/
theorem eventMass_eq_toMeasure {Ω : Type*} [MeasurableSpace Ω] (p : PMF Ω)
    (s : Set Ω) (hs : MeasurableSet s) : eventMass p s = p.toMeasure s :=
  (p.toMeasure_apply hs).symm

/-- Conditioning on a nonnull event removes exactly the points outside that event. -/
theorem support_condition {Ω : Type*} (p : PMF Ω) (s : Set Ω)
    (hs : eventMass p s ≠ 0) : (condition p s).support = s ∩ p.support := by
  classical
  ext a
  have heq : condition p s a = 0 ↔ s.indicator p a = 0 := by
    constructor
    · intro ha
      have h := eventMass_mul_condition p s a
      rw [ha, mul_zero] at h
      exact h.symm
    · intro ha
      have h := (eventMass_mul_condition p s a).trans ha
      exact (mul_eq_zero.mp h).resolve_left hs
  simp only [PMF.mem_support_iff, Set.mem_inter_iff]
  exact (not_congr heq).trans Set.indicator_apply_ne_zero

end TieredMatching.FiniteConditioning
