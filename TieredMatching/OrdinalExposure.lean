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

public import TieredMatching.ExponentialOrder

/-! # Exponential exposure conditional on ordinal information -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TieredMatching

/-- An ordinal event is unchanged when every clock is translated by the same amount. -/
def TranslationInvariant {ι : Type*} (E : Set (ι → ℝ)) : Prop :=
  ∀ (x : ι → ℝ) (a : ℝ), (fun i ↦ x i - a) ∈ E ↔ x ∈ E

/-- Simultaneous memorylessness for any finite index type. -/
theorem exponential_finite_tail_translate {ι : Type*} [Fintype ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (a : ℝ) (ha : 0 ≤ a) :
    Measure.map (fun x : ι → ℝ ↦ fun i ↦ x i - a)
      ((Measure.pi fun i ↦ expMeasure (r i)).restrict (univ.pi fun _ ↦ Ioi a)) =
      (∏ i, ENNReal.ofReal (Real.exp (-(r i * a)))) •
        Measure.pi (fun i ↦ expMeasure (r i)) := by
  have (i : ι) : IsProbabilityMeasure (expMeasure (r i)) :=
    isProbabilityMeasure_expMeasure (hr i)
  rw [Measure.restrict_pi_pi]
  rw [Measure.pi_map_pi (fun i ↦
    (show Measurable (fun x : ℝ ↦ x - a) by fun_prop).aemeasurable)]
  simp_rw [expMeasure_tail_translate (hr _) ha]
  exact pi_smul_finite (fun i ↦ expMeasure (r i)) _ (fun _ ↦ ENNReal.ofReal_ne_top)

/-- A common lower threshold factors from any measurable translation-invariant event. -/
theorem exponential_ordinal_above {ι : Type*} [Fintype ι] (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (E : Set (ι → ℝ)) (hE : MeasurableSet E) (hshift : TranslationInvariant E)
    (a : ℝ) (ha : 0 ≤ a) :
    (Measure.pi fun i ↦ expMeasure (r i)) {x | (∀ i, a < x i) ∧ x ∈ E} =
      (∏ i, ENNReal.ofReal (Real.exp (-(r i * a)))) *
        (Measure.pi fun i ↦ expMeasure (r i)) E := by
  have hmap := exponential_finite_tail_translate r hr a ha
  have hm : Measurable (fun x : ι → ℝ ↦ fun i ↦ x i - a) := by fun_prop
  have h := congrArg (fun μ : Measure (ι → ℝ) ↦ μ E) hmap
  rw [Measure.map_apply hm hE, Measure.restrict_apply (hE.preimage hm),
    Measure.smul_apply] at h
  have heq : (fun x : ι → ℝ ↦ fun i ↦ x i - a) ⁻¹' E ∩
      univ.pi (fun _ ↦ Ioi a) = {x | (∀ i, a < x i) ∧ x ∈ E} := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_univ_pi, mem_Ioi, mem_ofPred_eq]
    rw [hshift x a, and_comm]
  simpa only [heq, smul_eq_mul] using h

/-- A fresh exponential clock wins against a finite old collection with the usual
rate ratio even after conditioning on any measurable ordinal event in that collection. -/
theorem exponential_race_on_ordinal_event {ι : Type*} [Fintype ι] (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) (b : ℝ) (hb : 0 < b)
    (E : Set (ι → ℝ)) (hE : MeasurableSet E) (hshift : TranslationInvariant E) :
    ((expMeasure b).prod (Measure.pi fun i ↦ expMeasure (r i)))
      {z | (∀ i, z.1 < z.2 i) ∧ z.2 ∈ E} =
      ENNReal.ofReal (b / (b + ∑ i, r i)) *
        (Measure.pi fun i ↦ expMeasure (r i)) E := by
  have (i : ι) : IsProbabilityMeasure (expMeasure (r i)) :=
    isProbabilityMeasure_expMeasure (hr i)
  have : IsProbabilityMeasure (expMeasure b) := isProbabilityMeasure_expMeasure hb
  have hm : MeasurableSet {z : ℝ × (ι → ℝ) |
      (∀ i, z.1 < z.2 i) ∧ z.2 ∈ E} := by
    apply MeasurableSet.inter
    · have hi (i : ι) : MeasurableSet {z : ℝ × (ι → ℝ) | z.1 < z.2 i} :=
        measurableSet_lt measurable_fst ((measurable_pi_apply i).comp measurable_snd)
      have heq : {z : ℝ × (ι → ℝ) | ∀ i, z.1 < z.2 i} =
          ⋂ i, {z : ℝ × (ι → ℝ) | z.1 < z.2 i} := by
        ext z
        simp
      change MeasurableSet {z : ℝ × (ι → ℝ) | ∀ i, z.1 < z.2 i}
      rw [heq]
      exact MeasurableSet.iInter hi
    · exact hE.preimage measurable_snd
  rw [Measure.prod_apply hm]
  have hsection (a : ℝ) (ha : 0 ≤ a) :
      (Measure.pi fun i ↦ expMeasure (r i))
        (Prod.mk a ⁻¹' {z | (∀ i, z.1 < z.2 i) ∧ z.2 ∈ E}) =
      ENNReal.ofReal (Real.exp (-((∑ i, r i) * a))) *
        (Measure.pi fun i ↦ expMeasure (r i)) E := by
    change (Measure.pi fun i ↦ expMeasure (r i))
      {x | (∀ i, a < x i) ∧ x ∈ E} = _
    rw [exponential_ordinal_above r hr E hE hshift a ha]
    congr 1
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ (Real.exp_pos _).le),
      ← Real.exp_sum]
    congr 1
    rw [Finset.sum_neg_distrib, Finset.sum_mul]
  rw [lintegral_congr_ae ((ae_nonneg_expMeasure hb).mono fun a ha ↦ hsection a ha)]
  rw [lintegral_mul_const _ (by fun_prop),
    expMeasure_laplace hb (Finset.sum_nonneg fun i _ ↦ (hr i).le)]

/-- A fresh coordinate and any disjoint finite collection retain their independent marginal law. -/
theorem measurePreserving_fresh_and_old {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace α] (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p] (fresh : ι) (hfresh : ¬ p fresh) :
    MeasurePreserving (fun x : ι → α ↦ (x fresh, fun i : {i // p i} ↦ x i))
      (Measure.pi μ) ((μ fresh).prod (Measure.pi fun i : {i // p i} ↦ μ i)) := by
  let outside : {i // ¬ p i} := ⟨fresh, hfresh⟩
  have hsplit := measurePreserving_piEquivPiSubtypeProd μ p
  have heval := measurePreserving_eval (fun i : {i // ¬ p i} ↦ μ i) outside
  have h := Measure.measurePreserving_swap.comp
    (((MeasurePreserving.id (Measure.pi fun i : {i // p i} ↦ μ i)).prod heval).comp hsplit)
  exact h

/-- In the full independent array, an unobserved coordinate has the exact race probability
against the seen coordinates, conditional on any measurable ordinal event of the seen values. -/
theorem exponential_fresh_wins_on_ordinal_event {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (p : ι → Prop) [DecidablePred p]
    (fresh : ι) (hfresh : ¬ p fresh) (E : Set ({i // p i} → ℝ))
    (hE : MeasurableSet E) (hshift : TranslationInvariant E) :
    (Measure.pi fun i ↦ expMeasure (r i))
      {x | (∀ i : {i // p i}, x fresh < x i) ∧ (fun i : {i // p i} ↦ x i) ∈ E} =
      ENNReal.ofReal (r fresh / (r fresh + ∑ i : {i // p i}, r i)) *
        (Measure.pi fun i : {i // p i} ↦ expMeasure (r i)) E := by
  have (i : ι) : IsProbabilityMeasure (expMeasure (r i)) :=
    isProbabilityMeasure_expMeasure (hr i)
  have hmp := measurePreserving_fresh_and_old (fun i ↦ expMeasure (r i)) p fresh hfresh
  have hm : MeasurableSet {z : ℝ × ({i // p i} → ℝ) |
      (∀ i, z.1 < z.2 i) ∧ z.2 ∈ E} := by
    apply MeasurableSet.inter
    · have hi (i : {i // p i}) :
          MeasurableSet {z : ℝ × ({i // p i} → ℝ) | z.1 < z.2 i} :=
        measurableSet_lt measurable_fst ((measurable_pi_apply i).comp measurable_snd)
      have heq : {z : ℝ × ({i // p i} → ℝ) | ∀ i, z.1 < z.2 i} =
          ⋂ i, {z : ℝ × ({i // p i} → ℝ) | z.1 < z.2 i} := by
        ext z
        simp
      change MeasurableSet {z : ℝ × ({i // p i} → ℝ) | ∀ i, z.1 < z.2 i}
      rw [heq]
      exact MeasurableSet.iInter hi
    · exact hE.preimage measurable_snd
  have h := exponential_race_on_ordinal_event (fun i : {i // p i} ↦ r i)
    (fun i ↦ hr i) (r fresh) (hr fresh) E hE hshift
  rw [← hmp.map_eq, Measure.map_apply hmp.measurable hm] at h
  exact h

end TieredMatching
