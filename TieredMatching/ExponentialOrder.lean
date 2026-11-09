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

public import TieredMatching.Model
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Data.Fin.Tuple.Sort

/-! # Exponential clocks and the exact weighted ranking law -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace TieredMatching

/-- The distribution function of a positive-rate exponential measure. -/
theorem expMeasure_Iic {r : ℝ} (hr : 0 < r) (x : ℝ) :
    expMeasure r (Iic x) = ENNReal.ofReal (if 0 ≤ x then 1 - Real.exp (-(r * x)) else 0) := by
  let := isProbabilityMeasure_expMeasure hr
  rw [← ofReal_cdf, cdf_expMeasure_eq hr]

/-- Exponential memorylessness as an identity of translated tail measures. -/
theorem expMeasure_tail_translate {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    Measure.map (fun x : ℝ ↦ x - a) ((expMeasure r).restrict (Ioi a)) =
      ENNReal.ofReal (Real.exp (-(r * a))) • expMeasure r := by
  let := isProbabilityMeasure_expMeasure hr
  apply Measure.ext_of_Iic
  intro x
  have hm : Measurable (fun x : ℝ ↦ x - a) := by fun_prop
  rw [Measure.map_apply hm measurableSet_Iic,
    Measure.restrict_apply (by measurability)]
  have hset : (fun t : ℝ ↦ t - a) ⁻¹' Iic x ∩ Ioi a = Ioc a (a + x) := by
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioi, mem_Ioc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [hset, Measure.smul_apply]
  by_cases hx : 0 ≤ x
  · conv_lhs => rw [← measure_cdf (expMeasure r), StieltjesFunction.measure_Ioc]
    rw [cdf_expMeasure_eq hr, cdf_expMeasure_eq hr, expMeasure_Iic hr]
    simp only [ha, hx, add_nonneg ha hx, ite_true, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [show -(r * (a + x)) = -(r * a) + -(r * x) by ring, Real.exp_add]
    ring
  · rw [Ioc_eq_empty (by linarith), measure_empty, expMeasure_Iic hr]
    simp [hx]

/-- The Laplace transform of a positive-rate exponential measure. -/
theorem expMeasure_laplace {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-(s * x))) ∂expMeasure r) =
      ENNReal.ofReal (r / (r + s)) := by
  have hrs : 0 < r + s := by linarith
  have hmPDF (t : ℝ) : Measurable (exponentialPDF t) :=
    (measurable_exponentialPDFReal t).ennreal_ofReal
  have hm : Measurable (fun x : ℝ ↦ ENNReal.ofReal (Real.exp (-(s * x)))) := by fun_prop
  change (∫⁻ x, ENNReal.ofReal (Real.exp (-(s * x)))
    ∂volume.withDensity (exponentialPDF r)) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (hmPDF r) hm]
  have heq (x : ℝ) : exponentialPDF r x * ENNReal.ofReal (Real.exp (-(s * x))) =
      ENNReal.ofReal (r / (r + s)) * exponentialPDF (r + s) x := by
    by_cases hx : 0 ≤ x
    · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx,
        ← ENNReal.ofReal_mul (mul_nonneg hr.le (Real.exp_pos _).le),
        ← ENNReal.ofReal_mul (div_nonneg hr.le hrs.le)]
      congr 1
      rw [show -((r + s) * x) = -(r * x) + -(s * x) by ring, Real.exp_add]
      field_simp
    · rw [exponentialPDF_of_neg (lt_of_not_ge hx),
        exponentialPDF_of_neg (lt_of_not_ge hx)]
      simp
  simp only [Pi.mul_apply]
  simp_rw [heq]
  rw [lintegral_const_mul _ (hmPDF (r + s)), lintegral_exponentialPDF_eq_one hrs]
  exact mul_one _

/-- Finite product measures commute with finite coordinatewise scalar factors. -/
theorem pi_smul_finite {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (μ i)]
    (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ∞) :
    Measure.pi (fun i ↦ c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  let _ (i : ι) : IsFiniteMeasure (c i • μ i) := (μ i).smul_finite (hc i)
  apply Measure.pi_eq
  intro s hs
  simp [Measure.smul_apply, Measure.pi_pi, Finset.prod_mul_distrib]

/-- Simultaneous exponential memorylessness on a finite product space. -/
theorem exponential_pi_tail_translate {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (a : ℝ) (ha : 0 ≤ a) :
    Measure.map (fun x : Fin n → ℝ ↦ fun i ↦ x i - a)
      ((Measure.pi fun i ↦ expMeasure (r i)).restrict (univ.pi fun _ ↦ Ioi a)) =
      (∏ i, ENNReal.ofReal (Real.exp (-(r i * a)))) • Measure.pi (fun i ↦ expMeasure (r i)) := by
  let _ (i : Fin n) : IsProbabilityMeasure (expMeasure (r i)) :=
    isProbabilityMeasure_expMeasure (hr i)
  rw [Measure.restrict_pi_pi]
  rw [Measure.pi_map_pi (fun i ↦
    (show Measurable (fun x : ℝ ↦ x - a) by fun_prop).aemeasurable)]
  simp_rw [expMeasure_tail_translate (hr _) ha]
  exact pi_smul_finite (fun i ↦ expMeasure (r i)) _ (fun _ ↦ ENNReal.ofReal_ne_top)

/-- The strict-order cone of a finite real tuple is measurable. -/
theorem measurableSet_strictMono {n : ℕ} :
    MeasurableSet {x : Fin n → ℝ | StrictMono x} := by
  simp only [StrictMono, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i < j
  · simpa [hij] using measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)
  · simp [hij]

/-- Restricting every exponential clock above a common threshold only multiplies
its strict-order cone probability by the joint tail probability. -/
theorem exponential_order_above {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (a : ℝ) (ha : 0 ≤ a) :
    (Measure.pi fun i ↦ expMeasure (r i))
      {x | (∀ i, a < x i) ∧ StrictMono x} =
      (∏ i, ENNReal.ofReal (Real.exp (-(r i * a)))) *
        (Measure.pi fun i ↦ expMeasure (r i)) {x | StrictMono x} := by
  let _ (i : Fin n) : IsProbabilityMeasure (expMeasure (r i)) :=
    isProbabilityMeasure_expMeasure (hr i)
  have hmap := exponential_pi_tail_translate r hr a ha
  have hm : Measurable (fun x : Fin n → ℝ ↦ fun i ↦ x i - a) := by fun_prop
  have h := congrArg (fun μ : Measure (Fin n → ℝ) ↦ μ {x | StrictMono x}) hmap
  rw [Measure.map_apply hm measurableSet_strictMono,
    Measure.restrict_apply (measurableSet_strictMono.preimage hm), Measure.smul_apply] at h
  have heq : (fun x : Fin n → ℝ ↦ fun i ↦ x i - a) ⁻¹' {x | StrictMono x} ∩
      univ.pi (fun _ ↦ Ioi a) = {x | (∀ i, a < x i) ∧ StrictMono x} := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_univ_pi, mem_Ioi]
    constructor
    · intro h
      exact ⟨h.2, fun i j hij ↦ by have ht := h.1 hij; linarith⟩
    · intro h
      exact ⟨fun i j hij ↦ by have ht := h.2 hij; linarith, h.1⟩
  simpa only [heq, smul_eq_mul] using h

/-- A positive-rate exponential clock is nonnegative almost surely. -/
theorem ae_nonneg_expMeasure {r : ℝ} (hr : 0 < r) : ∀ᵐ x ∂expMeasure r, 0 ≤ x := by
  rw [ae_iff]
  simp only [not_le]
  change expMeasure r (Iio 0) = 0
  apply measure_mono_null Iio_subset_Iic_self
  simp [expMeasure_Iic hr]

/-- The probability of an ordered tuple factors by its first clock and the ordered tail. -/
theorem exponential_order_succ {n : ℕ} (r : Fin (n + 1) → ℝ) (hr : ∀ i, 0 < r i) :
    (Measure.pi fun i ↦ expMeasure (r i)) {x | StrictMono x} =
      ENNReal.ofReal (r 0 / ∑ i, r i) *
        (Measure.pi fun i : Fin n ↦ expMeasure (r i.succ)) {x | StrictMono x} := by
  let _ (i : Fin (n + 1)) : IsProbabilityMeasure (expMeasure (r i)) :=
    isProbabilityMeasure_expMeasure (hr i)
  let _ (i : Fin n) : IsProbabilityMeasure (expMeasure (r i.succ)) :=
    isProbabilityMeasure_expMeasure (hr i.succ)
  have hsplit := (measurePreserving_piFinSuccAbove (fun i ↦ expMeasure (r i)) 0).symm
  simp only [Fin.zero_succAbove] at hsplit
  rw [← hsplit.map_eq, Measure.map_apply hsplit.measurable measurableSet_strictMono]
  have heq : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm ⁻¹'
      {x | StrictMono x} = {z : ℝ × (Fin n → ℝ) | StrictMono (Fin.cons z.1 z.2)} := by
    ext z
    simp only [mem_preimage, mem_ofPred_eq, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_zero, cast_eq]
  have hmeas : MeasurableSet {z : ℝ × (Fin n → ℝ) | StrictMono (Fin.cons z.1 z.2)} := by
    rw [← heq]
    exact measurableSet_strictMono.preimage
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm.measurable
  rw [heq, Measure.prod_apply hmeas]
  have heq' (a : ℝ) (ha : 0 ≤ a) :
      (Measure.pi fun i : Fin n ↦ expMeasure (r i.succ))
        (Prod.mk a ⁻¹' {z : ℝ × (Fin n → ℝ) | StrictMono (Fin.cons z.1 z.2)}) =
      ENNReal.ofReal (Real.exp (-((∑ i : Fin n, r i.succ) * a))) *
        (Measure.pi fun i : Fin n ↦ expMeasure (r i.succ)) {x | StrictMono x} := by
    have hset : Prod.mk a ⁻¹' {z : ℝ × (Fin n → ℝ) | StrictMono (Fin.cons z.1 z.2)} =
        {x | (∀ i, a < x i) ∧ StrictMono x} := by
      ext x
      simp only [mem_preimage, mem_ofPred_eq, Fin.strictMono_cons]
    rw [hset, exponential_order_above (fun i ↦ r i.succ) (fun i ↦ hr i.succ) a ha]
    congr 1
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ (Real.exp_pos _).le),
      ← Real.exp_sum]
    congr 1
    rw [Finset.sum_neg_distrib, Finset.sum_mul]
  rw [lintegral_congr_ae ((ae_nonneg_expMeasure (hr 0)).mono fun a ha ↦ heq' a ha)]
  rw [lintegral_mul_const _ (by fun_prop), expMeasure_laplace (hr 0)
    (Finset.sum_nonneg fun i _ ↦ (hr i.succ).le)]
  rw [Fin.sum_univ_succ]

/-- The PR likelihood of the identity order splits into the first draw and the remaining order. -/
theorem likelihood_refl_succ {n : ℕ} (w : Fin (n + 1) → ℝ≥0) :
    RandomRanking.likelihood w (Equiv.refl _) =
      (w 0 / ∑ i, w i) * RandomRanking.likelihood (fun i : Fin n ↦ w i.succ) (Equiv.refl _) := by
  simp only [RandomRanking.likelihood, Equiv.refl_symm, Equiv.refl_apply]
  rw [Fin.prod_univ_succ]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro k _
    congr 1
    change (∑ x : Fin (n + 1) with k.succ ≤ x, w x) =
      ∑ x : Fin n with k ≤ x, w x.succ
    rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_succ]
    simp

/-- Independent exponential clocks produce the exact PR likelihood for the identity order. -/
theorem exponential_order_identity {n : ℕ} (w : Fin n → ℝ≥0) (hw : ∀ i, 0 < w i) :
    (Measure.pi fun i ↦ expMeasure (w i : ℝ)) {x | StrictMono x} =
      (RandomRanking.likelihood w (Equiv.refl _) : ℝ≥0∞) := by
  induction n with
  | zero =>
    have hs : {x : Fin 0 → ℝ | StrictMono x} = univ := by
      ext x
      simp [StrictMono]
    simp [hs, RandomRanking.likelihood]
  | succ n ih =>
    rw [exponential_order_succ (fun i ↦ (w i : ℝ)) (fun i ↦ by exact_mod_cast hw i),
      ih (fun i ↦ w i.succ) (fun i ↦ hw i.succ), likelihood_refl_succ]
    rw [ENNReal.coe_mul]
    congr 1
    simp only [← NNReal.coe_sum, ← NNReal.coe_div, ENNReal.ofReal_coe_nnreal]

/-- Reindexing the identity-order likelihood gives the PR candidate-to-rank likelihood. -/
theorem likelihood_reindex_identity {n : ℕ} (w : Fin n → ℝ≥0)
    (r : Equiv.Perm (Fin n)) :
    RandomRanking.likelihood (fun k ↦ w (r.symm k)) (Equiv.refl _) =
      RandomRanking.likelihood w r := by
  simp only [RandomRanking.likelihood, Equiv.refl_symm, Equiv.refl_apply]
  apply Finset.prod_congr rfl
  intro k _
  congr 1
  change (∑ h : Fin n with k ≤ h, w (r.symm h)) = ∑ x : Fin n with k ≤ r x, w x
  simp only [Finset.sum_filter]
  simpa using r.symm.sum_comp (fun x ↦ if k ≤ r x then w x else 0)

/-- Independent exponential clocks give the exact PR mass for every strict ordering cone. -/
theorem exponential_order_cone {n : ℕ} (w : Fin n → ℝ≥0) (hw : ∀ i, 0 < w i)
    (r : Equiv.Perm (Fin n)) :
    (Measure.pi fun i ↦ expMeasure (w i : ℝ)) {x | StrictMono (x ∘ r.symm)} =
      (RandomRanking.likelihood w r : ℝ≥0∞) := by
  let _ (i : Fin n) : IsProbabilityMeasure (expMeasure (w i : ℝ)) :=
    isProbabilityMeasure_expMeasure (by exact_mod_cast hw i)
  have hmp := (measurePreserving_piCongrLeft (fun i ↦ expMeasure (w i : ℝ)) r.symm).symm
  have h := congrArg (fun μ : Measure (Fin n → ℝ) ↦ μ {x | StrictMono x}) hmp.map_eq
  rw [Measure.map_apply hmp.measurable measurableSet_strictMono] at h
  have heq : (MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) r.symm).symm ⁻¹'
      {x | StrictMono x} = {x | StrictMono (x ∘ r.symm)} := by
    ext x
    rfl
  rw [heq] at h
  rw [h, exponential_order_identity (fun i ↦ w (r.symm i)) (fun i ↦ hw (r.symm i)),
    likelihood_reindex_identity]

/-- Independent exponential clocks have no atoms. -/
theorem nullSingletonClass_expMeasure (r : ℝ) : NullSingletonClass (expMeasure r) := by
  unfold expMeasure gammaMeasure
  infer_instance

/-- Injectivity of a finite real tuple is a measurable property. -/
theorem measurableSet_injective_tuple {n : ℕ} :
    MeasurableSet {x : Fin n → ℝ | Function.Injective x} := by
  have heq : {x : Fin n → ℝ | Function.Injective x} =
      ⋂ i : Fin n, ⋂ j : Fin n, {x : Fin n → ℝ | i = j ∨ x i ≠ x j} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro hx i j
      exact (eq_or_ne i j).elim Or.inl (fun h ↦ Or.inr (hx.ne h))
    · intro hx i j hval
      exact (hx i j).elim id (fun h ↦ False.elim (h hval))
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i = j
  · simp only [hij, true_or, ofPred_true]
    exact MeasurableSet.univ
  · simp only [hij, false_or]
    exact (measurableSet_eq_fun (show Measurable (fun x : Fin n → ℝ ↦ x i) by fun_prop)
      (show Measurable (fun x : Fin n → ℝ ↦ x j) by fun_prop)).compl

/-- A finite family of independent exponential clocks has no ties almost surely. -/
theorem ae_injective_exponentials {n : ℕ} (w : Fin n → ℝ≥0) (hw : ∀ i, 0 < w i) :
    ∀ᵐ x ∂(Measure.pi fun i ↦ expMeasure (w i : ℝ)), Function.Injective x := by
  induction n with
  | zero => exact Eventually.of_forall fun x i ↦ Fin.elim0 i
  | succ n ih =>
    let _ (i : Fin (n + 1)) : IsProbabilityMeasure (expMeasure (w i : ℝ)) :=
      isProbabilityMeasure_expMeasure (by exact_mod_cast hw i)
    let _ (i : Fin n) : IsProbabilityMeasure (expMeasure (w i.succ : ℝ)) :=
      isProbabilityMeasure_expMeasure (by exact_mod_cast hw i.succ)
    let _ (i : Fin n) : NullSingletonClass (expMeasure (w i.succ : ℝ)) :=
      nullSingletonClass_expMeasure _
    have hsplit := (measurePreserving_piFinSuccAbove (fun i ↦ expMeasure (w i : ℝ)) 0).symm
    simp only [Fin.zero_succAbove] at hsplit
    rw [← hsplit.map_eq, ae_map_iff hsplit.measurable.aemeasurable measurableSet_injective_tuple]
    have heq : {z : ℝ × (Fin n → ℝ) |
        Function.Injective ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) ↦ ℝ) 0).symm z)} =
        {z | Function.Injective (Fin.cons z.1 z.2)} := by
      ext z
      simp only [mem_ofPred_eq, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_zero, cast_eq]
    have hm : MeasurableSet {z : ℝ × (Fin n → ℝ) | Function.Injective (Fin.cons z.1 z.2)} := by
      rw [← heq]
      exact measurableSet_injective_tuple.preimage hsplit.measurable
    change ∀ᵐ z ∂(expMeasure (w 0 : ℝ)).prod
      (Measure.pi fun i : Fin n ↦ expMeasure (w i.succ : ℝ)), z ∈
      {z | Function.Injective ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) ↦ ℝ) 0).symm z)}
    rw [heq, Measure.ae_prod_mem_iff_ae_ae_mem hm]
    apply Eventually.of_forall
    intro a
    have hne : ∀ᵐ x ∂(Measure.pi fun i : Fin n ↦ expMeasure (w i.succ : ℝ)),
        ∀ i, x i ≠ a := eventually_all.mpr fun i ↦
      Measure.ae_eval_ne (fun i : Fin n ↦ expMeasure (w i.succ : ℝ)) i a
    filter_upwards [ih (fun i ↦ w i.succ) (fun i ↦ hw i.succ), hne] with x hx hne
    apply Fin.cons_injective_of_injective _ hx
    rintro ⟨i, hi⟩
    exact hne i hi

/-- The candidate-to-rank permutation obtained by sorting exponential clock values. -/
noncomputable def exponentialRank {n : ℕ} (x : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  (Tuple.sort x).symm

/-- A strict ordering identifies the sorted rank permutation when there are no ties. -/
theorem exponentialRank_eq_iff_of_injective {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (r : Equiv.Perm (Fin n)) :
    exponentialRank x = r ↔ StrictMono (x ∘ r.symm) := by
  constructor
  · intro h
    have hs : r.symm = Tuple.sort x := by
      exact (congrArg Equiv.symm h).symm
    rw [hs]
    exact (Tuple.monotone_sort x).strictMono_of_injective (hx.comp (Tuple.sort x).injective)
  · intro h
    have hs : r.symm = Tuple.sort x := Tuple.eq_sort_iff.mpr
      ⟨h.monotone, fun i j hij heq ↦ False.elim ((h hij).ne heq)⟩
    exact congrArg Equiv.symm hs.symm

/-- The exact fiber of the sorted rank is specified by weak order and the index tie-break. -/
theorem exponentialRank_eq_iff {n : ℕ} (x : Fin n → ℝ) (r : Equiv.Perm (Fin n)) :
    exponentialRank x = r ↔ Monotone (x ∘ r.symm) ∧
      ∀ i j, i < j → x (r.symm i) = x (r.symm j) → r.symm i < r.symm j := by
  have h : exponentialRank x = r ↔ r.symm = Tuple.sort x := by
    constructor
    · intro h
      exact (congrArg Equiv.symm h).symm
    · intro h
      exact congrArg Equiv.symm h.symm
  rw [h]
  exact Tuple.eq_sort_iff

/-- Every singleton fiber of the exponential rank map is measurable, including tied tuples. -/
theorem measurableSet_exponentialRank_fiber {n : ℕ} (r : Equiv.Perm (Fin n)) :
    MeasurableSet {x : Fin n → ℝ | exponentialRank x = r} := by
  have heq : {x : Fin n → ℝ | exponentialRank x = r} =
      (⋂ i : Fin n, ⋂ j : Fin n, {x : Fin n → ℝ |
        i ≤ j → x (r.symm i) ≤ x (r.symm j)}) ∩
      (⋂ i : Fin n, ⋂ j : Fin n, {x : Fin n → ℝ |
        i < j → x (r.symm i) ≠ x (r.symm j) ∨ r.symm i < r.symm j}) := by
    ext x
    simp only [mem_ofPred_eq, exponentialRank_eq_iff, mem_inter_iff, mem_iInter,
      Monotone, Function.comp_apply, imp_iff_not_or]
  rw [heq]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    by_cases hij : i ≤ j
    · simp only [hij, true_implies]
      exact measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _)
    · simp only [hij, false_implies, ofPred_true]
      exact MeasurableSet.univ
  · apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    by_cases hij : i < j
    · simp only [hij, true_implies]
      by_cases hrij : r.symm i < r.symm j
      · simp only [hrij, or_true, ofPred_true]
        exact MeasurableSet.univ
      · simp only [hrij, or_false]
        exact (measurableSet_eq_fun
          (show Measurable (fun x : Fin n → ℝ ↦ x (r.symm i)) by fun_prop)
          (show Measurable (fun x : Fin n → ℝ ↦ x (r.symm j)) by fun_prop)).compl
    · simp only [hij, false_implies, ofPred_true]
      exact MeasurableSet.univ

/-- The sorted candidate-to-rank map is measurable into the discrete permutation space. -/
theorem measurable_exponentialRank {n : ℕ} :
    @Measurable (Fin n → ℝ) (Equiv.Perm (Fin n)) inferInstance ⊤ exponentialRank := by
  let _ : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  change Measurable (exponentialRank (n := n))
  apply measurable_to_countable
  intro x
  exact measurableSet_exponentialRank_fiber (exponentialRank x)

/-- Sorting independent exponential priorities gives the PR's exact row likelihood. -/
theorem exponentialRank_singleton {n : ℕ} (w : Fin n → ℝ≥0) (hw : ∀ i, 0 < w i)
    (r : Equiv.Perm (Fin n)) :
    (Measure.pi fun i ↦ expMeasure (w i : ℝ)) {x | exponentialRank x = r} =
      (RandomRanking.likelihood w r : ℝ≥0∞) := by
  have heq : {x : Fin n → ℝ | exponentialRank x = r} =ᵐ[
      Measure.pi fun i ↦ expMeasure (w i : ℝ)] {x | StrictMono (x ∘ r.symm)} := by
    filter_upwards [ae_injective_exponentials w hw] with x hx
    exact propext (exponentialRank_eq_iff_of_injective x hx r)
  rw [measure_congr heq, exponential_order_cone w hw r]

/-- On a tuple without ties, the PR's rank comparison is exactly raw priority comparison. -/
theorem exponentialRank_lt_iff {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x)
    (m old : Fin n) : exponentialRank x m < exponentialRank x old ↔ x m < x old := by
  have hstrict : StrictMono (x ∘ Tuple.sort x) :=
    (Tuple.monotone_sort x).strictMono_of_injective (hx.comp (Tuple.sort x).injective)
  simpa only [exponentialRank, Function.comp_apply, Equiv.apply_symm_apply] using
    (hstrict.lt_iff_lt (a := (Tuple.sort x).symm m) (b := (Tuple.sort x).symm old)).symm

end TieredMatching
