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

public import TieredMatching.RankingPrefix

/-! # The first fresh value of an IID categorical stream

The canonical product measure is used throughout. These are one-step rejection-sampling laws;
no adaptive deferred-acceptance process is assumed to have an IID destination stream.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace TieredMatching.FirstFresh

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The canonical IID stream with categorical one-coordinate law `p`. -/
noncomputable def iidStream (p : PMF α) : Measure (ℕ → α) :=
  Measure.infinitePi fun _ : ℕ ↦ p.toMeasure

/-- All earlier draws are excluded, while the next draw lies in a designated target set. -/
def hitAt (S A : Set α) (k : ℕ) : Set (ℕ → α) :=
  {x | (∀ t < k, x t ∈ S) ∧ x k ∈ A}

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The finite first-hit cylinder as a finite-coordinate product set. -/
theorem hitAt_eq_pi (S A : Set α) (k : ℕ) :
    hitAt S A k = Set.pi (Finset.range (k + 1)) (fun t ↦ if t = k then A else S) := by
  ext x
  simp only [hitAt, Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_range]
  constructor
  · rintro ⟨hearlier, hlast⟩ t ht
    by_cases htk : t = k
    · simpa [htk] using hlast
    · simpa [htk] using hearlier t (by omega)
  · intro h
    constructor
    · intro t ht
      have htk : t ≠ k := ne_of_lt ht
      simpa [htk] using h t (by omega)
    · simpa using h k (by omega)

/-- Each first-hit cylinder is measurable. -/
theorem measurableSet_hitAt (S A : Set α) (k : ℕ) : MeasurableSet (hitAt S A k) := by
  rw [hitAt_eq_pi]
  exact MeasurableSet.pi (Finset.countable_toSet _)
    (fun _ _ ↦ (Set.toFinite _).measurableSet)

/-- The exact finite-cylinder mass preceding the first fresh draw. -/
theorem hitAt_measure (p : PMF α) (S A : Set α) (k : ℕ) :
    iidStream p (hitAt S A k) = (p.toMeasure S) ^ k * p.toMeasure A := by
  classical
  rw [hitAt_eq_pi, iidStream]
  rw [Measure.infinitePi_pi (fun _ : ℕ ↦ p.toMeasure)
    (fun t _ ↦ (Set.toFinite _).measurableSet), Finset.prod_range_succ]
  have hprod : (∏ t ∈ Finset.range k,
      p.toMeasure (if t = k then A else S)) = (p.toMeasure S) ^ k := by
    calc
      _ = ∏ _t ∈ Finset.range k, p.toMeasure S := by
        apply Finset.prod_congr rfl
        intro t ht
        rw [ite_eq_right (ne_of_lt (Finset.mem_range.mp ht))]
      _ = _ := by simp
  simp only [hprod, ite_true]

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- First-hit cylinders at distinct times are disjoint whenever targets are fresh. -/
theorem pairwiseDisjoint_hitAt (S A : Set α) (hSA : Disjoint S A) :
    Pairwise (fun k l ↦ Disjoint (hitAt S A k) (hitAt S A l)) := by
  intro k l hkl
  rw [Set.disjoint_left]
  intro x hxk hxl
  rcases lt_or_gt_of_ne hkl with h | h
  · exact Set.disjoint_left.mp hSA (hxl.1 k h) hxk.2
  · exact Set.disjoint_left.mp hSA (hxk.1 l h) hxl.2

/-- Summing the disjoint cylinders gives the exact geometric rejection-sampling law. -/
theorem firstHit_measure (p : PMF α) (S A : Set α) (hSA : Disjoint S A) :
    iidStream p (⋃ k, hitAt S A k) = p.toMeasure A / (1 - p.toMeasure S) := by
  rw [measure_iUnion (pairwiseDisjoint_hitAt S A hSA) (measurableSet_hitAt S A)]
  simp_rw [hitAt_measure]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, div_eq_mul_inv, mul_comm]

instance isProbabilityMeasure_iidStream (p : PMF α) : IsProbabilityMeasure (iidStream p) := by
  unfold iidStream
  infer_instance

/-- The exact first-value event; excluded values give the empty event. -/
def firstValue (S : Set α) (q : α) : Set (ℕ → α) :=
  ⋃ k, hitAt S ({q} \ S) k

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The event states explicitly that the chosen value occurs after only excluded draws. -/
theorem mem_firstValue_iff (S : Set α) (q : α) (x : ℕ → α) :
    x ∈ firstValue S q ↔ ∃ k, (∀ t < k, x t ∈ S) ∧ x k = q ∧ q ∉ S := by
  simp only [firstValue, Set.mem_iUnion, hitAt, Set.mem_ofPred_eq,
    Set.mem_sdiff, Set.mem_singleton_iff]
  aesop

open scoped Classical in
/-- The first fresh value has the categorical law renormalized over the complement. -/
theorem firstValue_measure (p : PMF α) (S : Set α) (q : α) :
    iidStream p (firstValue S q) =
      if q ∈ S then 0 else p q / (1 - p.toMeasure S) := by
  classical
  rw [firstValue, firstHit_measure p S ({q} \ S) Set.disjoint_sdiff_right]
  by_cases hq : q ∈ S
  · have hA : ({q} \ S : Set α) = ∅ := by aesop
    simp [hq, hA]
  · have hA : ({q} \ S : Set α) = {q} := by aesop
    rw [ite_eq_right hq, hA, PMF.toMeasure_apply_singleton p q (measurableSet_singleton q)]

/-- A first fresh draw occurs with probability one whenever the excluded mass is below one. -/
theorem firstFresh_measure_one (p : PMF α) (S : Set α) (hS : p.toMeasure S < 1) :
    iidStream p (⋃ k, hitAt S Sᶜ k) = 1 := by
  rw [firstHit_measure p S Sᶜ disjoint_compl_right,
    measure_compl (Set.toFinite S).measurableSet (measure_ne_top _ _), measure_univ]
  exact ENNReal.div_self (ne_of_gt (tsub_pos_iff_lt.mpr hS))
    (ENNReal.sub_ne_top ENNReal.one_ne_top)

/-- Almost every IID stream has a finite first draw outside the excluded set. -/
theorem ae_firstFresh (p : PMF α) (S : Set α) (hS : p.toMeasure S < 1) :
    ∀ᵐ x ∂iidStream p, ∃ k, (∀ t < k, x t ∈ S) ∧ x k ∉ S := by
  rw [ae_iff]
  have heq : {x : ℕ → α | ¬∃ k, (∀ t < k, x t ∈ S) ∧ x k ∉ S} =
      (⋃ k, hitAt S Sᶜ k)ᶜ := by
    ext x
    simp [hitAt]
  rw [heq, measure_compl (MeasurableSet.iUnion (measurableSet_hitAt S Sᶜ))
    (measure_ne_top _ _), firstFresh_measure_one p S hS, measure_univ, tsub_self]

/-- The measure of a finite categorical set is its normalized total weight. -/
theorem ofWeights_measure_finset [Nonempty α] (weight : α → ℝ≥0)
    (htotal : ∑ x, weight x ≠ 0) (S : Finset α) :
    (RandomRanking.ofWeights weight).toMeasure (S : Set α) =
      ((∑ x ∈ S, weight x) / (∑ x, weight x) : ℝ≥0) := by
  classical
  rw [PMF.toMeasure_apply_finset, Finset.sum_div, ENNReal.ofNNReal_finsetSum]
  apply Finset.sum_congr rfl
  intro q _
  rw [RandomRanking.ofWeights_apply weight htotal, ENNReal.coe_div htotal]

open scoped Classical in
/-- First-fresh IID rejection has exactly the same residual weighted kernel as PR rankings. -/
theorem firstValue_ofWeights [Nonempty α] (weight : α → ℝ≥0) (hw : ∀ x, 0 < weight x)
    (S : Finset α) (q : α) (hq : q ∉ S) :
    iidStream (RandomRanking.ofWeights weight) (firstValue (S : Set α) q) =
      (weight q / (∑ x with x ∉ S, weight x) : ℝ≥0) := by
  classical
  have htotal : (∑ x, weight x) ≠ 0 := ne_of_gt
    (Finset.sum_pos (fun x _ ↦ hw x) Finset.univ_nonempty)
  have hrest : (∑ x with x ∉ S, weight x) ≠ 0 := by
    apply ne_of_gt
    exact Finset.sum_pos' (fun _ _ ↦ zero_le) ⟨q, by simp [hq], hw q⟩
  have hcomp : 1 - (RandomRanking.ofWeights weight).toMeasure (S : Set α) =
      (RandomRanking.ofWeights weight).toMeasure ((S : Set α)ᶜ) := by
    rw [measure_compl S.measurableSet (measure_ne_top _ _), measure_univ]
  rw [firstValue_measure]
  simp only [Finset.mem_coe, ite_eq_right hq]
  rw [hcomp, RandomRanking.ofWeights_apply weight htotal]
  have hset : ((S : Set α)ᶜ) = (↑(Finset.univ.filter (fun x ↦ x ∉ S)) : Set α) := by
    ext x
    simp
  rw [hset, ofWeights_measure_finset weight htotal, ← ENNReal.coe_div htotal,
    ← ENNReal.coe_div (div_ne_zero hrest htotal), div_div_div_cancel_right₀ htotal]

/-- The unused stream strictly after coordinate `k`. -/
def tailAfter (k : ℕ) (x : ℕ → α) (t : ℕ) : α := x (k + 1 + t)

omit [Fintype α] [MeasurableSingletonClass α] in
/-- Discarding a finite head is measurable. -/
@[fun_prop]
theorem measurable_tailAfter (k : ℕ) :
    Measurable (tailAfter k : (ℕ → α) → ℕ → α) := by
  unfold tailAfter
  fun_prop

omit [Fintype α] [MeasurableSingletonClass α] in
/-- Disjoint coordinate blocks make the finite head independent of the full remaining stream. -/
theorem indepFun_head_tail (p : PMF α) (k : ℕ) :
    ProbabilityTheory.IndepFun (fun x : ℕ → α ↦ fun i : Fin (k + 1) ↦ x i)
      (tailAfter k) (iidStream p) := by
  let m : ℕ → MeasurableSpace (ℕ → α) :=
    fun i ↦ MeasurableSpace.comap (fun x ↦ x i) inferInstance
  have hind : ProbabilityTheory.iIndep m (iidStream p) :=
    (ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : ℕ ↦ p.toMeasure)
      (X := fun _ a ↦ a) (by fun_prop)).iIndep
  have hblocks := ProbabilityTheory.indep_iSup_of_disjoint
    (m := m) (fun i ↦ (measurable_pi_apply i).comap_le) hind
    (S := Set.Iio (k + 1)) (T := Set.Ici (k + 1)) (by
      rw [Set.disjoint_left]
      intro i hi hj
      simp only [Set.mem_Iio, Set.mem_Ici] at hi hj
      omega)
  rw [ProbabilityTheory.IndepFun_iff_Indep]
  apply ProbabilityTheory.indep_of_indep_of_le hblocks
  · rw [MeasurableSpace.comap_process_pi]
    exact iSup_le fun i ↦ le_iSup_of_le i.val (le_iSup_of_le i.isLt le_rfl)
  · change MeasurableSpace.comap (fun x : ℕ → α ↦ fun t ↦ x (k + 1 + t)) _ ≤ _
    rw [MeasurableSpace.comap_process_pi]
    exact iSup_le fun t ↦ le_iSup_of_le (k + 1 + t)
      (le_iSup_of_le (by simp only [Set.mem_Ici]; omega) le_rfl)

omit [Fintype α] [MeasurableSingletonClass α] in
/-- Discarding a deterministic finite head preserves the complete IID stream law. -/
theorem map_tailAfter (p : PMF α) (k : ℕ) :
    (iidStream p).map (tailAfter k) = iidStream p := by
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ ↦ p.toMeasure) (f := fun t ↦ k + 1 + t)
    (fun a b h ↦ Nat.add_left_cancel h)

/-- A finite first-hit cylinder is independent of any measurable future-stream event. -/
theorem hitAt_tail_measure (p : PMF α) (S A : Set α) (k : ℕ)
    (E : Set (ℕ → α)) (hE : MeasurableSet E) :
    iidStream p (hitAt S A k ∩ (tailAfter k) ⁻¹' E) =
      (p.toMeasure S) ^ k * p.toMeasure A * iidStream p E := by
  let C : Set (Fin (k + 1) → α) :=
    {y | (∀ i : Fin (k + 1), i.val < k → y i ∈ S) ∧ y ⟨k, by omega⟩ ∈ A}
  have hC : MeasurableSet C := (Set.toFinite C).measurableSet
  have hpre : (fun x : ℕ → α ↦ fun i : Fin (k + 1) ↦ x i) ⁻¹' C = hitAt S A k := by
    ext x
    constructor
    · rintro ⟨hall, hlast⟩
      exact ⟨fun t ht ↦ hall ⟨t, by omega⟩ ht, hlast⟩
    · rintro ⟨hall, hlast⟩
      exact ⟨fun i hi ↦ hall i hi, hlast⟩
  have h := (indepFun_head_tail p k).measure_inter_preimage_eq_mul C E hC hE
  rw [hpre, ← Measure.map_apply (by fun_prop) hE, map_tailAfter p k,
    hitAt_measure] at h
  exact h

/-- First-fresh rejection also leaves an independent IID future stream after its hit time. -/
theorem firstHit_tail_measure (p : PMF α) (S A : Set α) (hSA : Disjoint S A)
    (E : Set (ℕ → α)) (hE : MeasurableSet E) :
    iidStream p (⋃ k, hitAt S A k ∩ (tailAfter k) ⁻¹' E) =
      p.toMeasure A / (1 - p.toMeasure S) * iidStream p E := by
  have hd : Pairwise (fun k l ↦ Disjoint (hitAt S A k ∩ (tailAfter k) ⁻¹' E)
      (hitAt S A l ∩ (tailAfter l) ⁻¹' E)) := by
    intro k l hkl
    exact ((pairwiseDisjoint_hitAt S A hSA) hkl).mono Set.inter_subset_left
      Set.inter_subset_left
  rw [measure_iUnion hd (fun k ↦ (measurableSet_hitAt S A k).inter
    (hE.preimage (by fun_prop)))]
  simp_rw [hitAt_tail_measure p S A _ E hE]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
    div_eq_mul_inv]
  ac_rfl

/-- Joint law of the first fresh value and the entire IID stream strictly following it. -/
theorem firstValue_tail_measure (p : PMF α) (S : Set α) (q : α) (hq : q ∉ S)
    (E : Set (ℕ → α)) (hE : MeasurableSet E) :
    iidStream p (⋃ k, hitAt S {q} k ∩ (tailAfter k) ⁻¹' E) =
      p q / (1 - p.toMeasure S) * iidStream p E := by
  rw [firstHit_tail_measure p S {q} (Set.disjoint_singleton_right.mpr hq) E hE,
    PMF.toMeasure_apply_singleton p q (measurableSet_singleton q)]

/-- After the first fresh draw, the complete unused stream still has its original IID law. -/
theorem firstFresh_tail_measure (p : PMF α) (S : Set α) (hS : p.toMeasure S < 1)
    (E : Set (ℕ → α)) (hE : MeasurableSet E) :
    iidStream p (⋃ k, hitAt S Sᶜ k ∩ (tailAfter k) ⁻¹' E) = iidStream p E := by
  rw [firstHit_tail_measure p S Sᶜ disjoint_compl_right E hE,
    measure_compl (Set.toFinite S).measurableSet (measure_ne_top _ _), measure_univ,
    ENNReal.div_self (ne_of_gt (tsub_pos_iff_lt.mpr hS))
      (ENNReal.sub_ne_top ENNReal.one_ne_top), one_mul]

end TieredMatching.FirstFresh
