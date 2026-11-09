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

public import Mathlib

/-! # Measure-preserving choices of transformations during adaptive exposure -/

@[expose] public section

namespace TieredMatching

open MeasureTheory Set Function

/-- Apply the transformation indexed by the current observable choice. -/
def selectedTransform {ι Ω : Type*} (choose : Ω → ι) (T : ι → Ω → Ω) (ω : Ω) : Ω :=
  T (choose ω) ω

/-- A selected transformation's preimage splits over the choice fibers. -/
theorem selectedTransform_preimage {ι Ω : Type*} (choose : Ω → ι) (T : ι → Ω → Ω)
    (s : Set Ω) :
    selectedTransform choose T ⁻¹' s = ⋃ i, {ω | choose ω = i} ∩ (T i ⁻¹' s) := by
  ext ω
  simp [selectedTransform]

/-- Measurable choices among countably many measurable maps remain measurable. -/
theorem measurable_selectedTransform {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (choose : Ω → ι) (T : ι → Ω → Ω)
    (hchoose : ∀ i, MeasurableSet {ω | choose ω = i}) (hT : ∀ i, Measurable (T i)) :
    Measurable (selectedTransform choose T) := by
  intro s hs
  rw [selectedTransform_preimage]
  exact MeasurableSet.iUnion fun i ↦ (hchoose i).inter (hT i hs)

/-- Selecting a measure-preserving transformation preserves the law when each choice fiber
is invariant under its selected transformation. This permits choices based on exposed values. -/
theorem measurePreserving_selectedTransform {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (choose : Ω → ι) (T : ι → Ω → Ω)
    (hchoose : ∀ i, MeasurableSet {ω | choose ω = i})
    (hT : ∀ i, MeasurePreserving (T i) μ μ)
    (hinv : ∀ i, T i ⁻¹' {ω | choose ω = i} = {ω | choose ω = i}) :
    MeasurePreserving (selectedTransform choose T) μ μ := by
  classical
  have hmeas := measurable_selectedTransform choose T hchoose (fun i ↦ (hT i).measurable)
  refine ⟨hmeas, Measure.ext fun s hs ↦ ?_⟩
  rw [Measure.map_apply hmeas hs, selectedTransform_preimage]
  have hdisj (U : ι → Set Ω) : Pairwise (onFun Disjoint
      (fun i ↦ {ω | choose ω = i} ∩ U i)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    exact hij (hi.1.symm.trans hj.1)
  rw [measure_iUnion (hdisj _) (fun i ↦ (hchoose i).inter ((hT i).measurable hs))]
  have hi (i : ι) : μ ({ω | choose ω = i} ∩ (T i ⁻¹' s)) =
      μ ({ω | choose ω = i} ∩ s) := by
    calc
      _ = μ (T i ⁻¹' ({ω | choose ω = i} ∩ s)) := by
        rw [Set.preimage_inter, hinv i]
      _ = _ := (hT i).measure_preimage ((hchoose i).inter hs).nullMeasurableSet
  simp_rw [hi]
  rw [← measure_iUnion (hdisj (fun _ ↦ s)) (fun i ↦ (hchoose i).inter hs)]
  congr 1
  ext ω
  simp

/-- Swapping two coordinates with equal marginal laws preserves a finite product measure. -/
theorem measurePreserving_swapCoordinates {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace α] (μ : ι → Measure α) [∀ i, SigmaFinite (μ i)] (a b : ι)
    (hab : μ a = μ b) :
    MeasurePreserving (fun x : ι → α ↦ x ∘ Equiv.swap a b) (Measure.pi μ) (Measure.pi μ) := by
  have hμ : (fun i ↦ μ (Equiv.swap a b i)) = μ := by
    funext i
    by_cases ha : i = a
    · subst i
      simpa using hab.symm
    · by_cases hb : i = b
      · subst i
        simpa using hab
      · simp [Equiv.swap_apply_of_ne_of_ne ha hb]
  have h := measurePreserving_piCongrLeft (α := fun _ : ι ↦ α) μ (Equiv.swap a b)
  rw [hμ] at h
  convert h using 1
  funext x i
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

end TieredMatching
