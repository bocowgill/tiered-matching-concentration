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

public import TieredMatching.Sandwich
public import Mathlib.MeasureTheory.Measure.Basic

/-! # The prefix sandwich outside null sets of tied exponential priorities -/

@[expose] public section

namespace TieredMatching

open MeasureTheory

/-- The sandwich needs absence of ties and winner properties only almost everywhere.
This form applies to continuous priorities on their original product probability space. -/
theorem measure_tier_disagreement_le {Ω J β : Type*} [MeasurableSpace Ω] [PartialOrder β]
    (μ : Measure Ω) (f : Ω → J × ℕ → β) (actual : Ω → J → ℕ)
    (lower central upper : J → ℕ) (a c u : Ω → J × ℕ)
    (hlc : ∀ j, lower j ≤ central j) (hcu : ∀ j, central j ≤ upper j)
    (ha : ∀ᵐ ω ∂μ, a ω ∈ prefixSet (actual ω))
    (hc : ∀ᵐ ω ∂μ, c ω ∈ prefixSet central)
    (ha_min : ∀ᵐ ω ∂μ, IsMinOn (f ω) (prefixSet (actual ω)) (a ω))
    (hc_min : ∀ᵐ ω ∂μ, IsMinOn (f ω) (prefixSet central) (c ω))
    (hu_min : ∀ᵐ ω ∂μ, IsMinOn (f ω) (prefixSet upper) (u ω))
    (hf : ∀ᵐ ω ∂μ, Set.InjOn (f ω) (prefixSet upper)) :
    μ {ω | (a ω).1 ≠ (c ω).1} ≤
      μ {ω | ¬ ∀ j, lower j ≤ actual ω j ∧ actual ω j ≤ upper j} +
        μ {ω | u ω ∉ prefixSet lower} := by
  classical
  apply le_trans (measure_mono_ae ?_) (measure_union_le _ _)
  filter_upwards [ha, hc, ha_min, hc_min, hu_min, hf] with ω ha hc ha_min hc_min hu_min hf
  intro hne
  by_cases hgood : ∀ j, lower j ≤ actual ω j ∧ actual ω j ≤ upper j
  · by_cases hlow : u ω ∈ prefixSet lower
    · exact False.elim (hne (congrArg Prod.fst
        (prefix_min_eq (fun j ↦ (hgood j).1) hlc (fun j ↦ (hgood j).2) hcu
          ha hc hlow ha_min hc_min hu_min hf)))
    · exact Or.inr hlow
  · exact Or.inl hgood

end TieredMatching
