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

public import Ashlagi.OrdinalExposure
public import Ashlagi.ArrivalPrefixes
public import Ashlagi.Transfer

/-! # Exponential reference races on deterministic finite source prefixes -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Ashlagi.ReferenceRace

local instance {n : ℕ} : MeasurableSpace (Option (Fin n)) := ⊤

/-- Select the first minimum in the increasing list of a deterministic source set. -/
noncomputable def winner {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) : Option (Fin n) :=
  List.argmin x (S.sort (· ≤ ·))

/-- A list minimum is measurable even on the null set of ties. -/
theorem measurable_list_argmin {n : ℕ} (L : List (Fin n)) :
    Measurable (fun x : Fin n → ℝ ↦ List.argmin x L) := by
  induction L with
  | nil => exact measurable_const
  | cons a L ih =>
    have hbranch : Measurable (fun z : Option (Fin n) × (Fin n → ℝ) ↦
        z.1.elim (some a) (fun c ↦ if z.2 c < z.2 a then some c else some a)) := by
      apply measurable_from_prod_countable_right
      intro o
      cases o with
      | none => exact measurable_const
      | some c =>
        exact measurable_const.ite
          (measurableSet_lt (measurable_pi_apply c) (measurable_pi_apply a)) measurable_const
    convert hbranch.comp (ih.prodMk measurable_id) using 1
    funext x
    rw [List.argmin_cons]
    dsimp only [Function.comp_def, id_eq]
    cases List.argmin x L <;> rfl

/-- A deterministic finite reference winner is a measurable categorical variable. -/
theorem measurable_winner {n : ℕ} (S : Finset (Fin n)) : Measurable (winner S) :=
  measurable_list_argmin _

/-- A selected reference winner belongs to the source set. -/
theorem winner_mem {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) (m : Fin n)
    (hm : winner S x = some m) : m ∈ S := by
  simpa only [Finset.mem_sort] using List.argmin_mem hm

/-- Its score is minimal among the supplied source set. -/
theorem winner_min {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) (m : Fin n)
    (hm : winner S x = some m) : IsMinOn x (S : Set (Fin n)) m := by
  intro k hk
  change k ∈ S at hk
  exact List.le_of_mem_argmin (by simpa only [Finset.mem_sort] using hk) hm

/-- On distinct scores, the measurable reference winner is exactly the strict race winner. -/
theorem winner_eq_some_iff_strict {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ)
    (hx : Set.InjOn x S) (m : Fin n) :
    winner S x = some m ↔ m ∈ S ∧ ∀ k ∈ S, k ≠ m → x m < x k := by
  constructor
  · intro hm
    refine ⟨winner_mem S x m hm, fun k hk hkm ↦ ?_⟩
    exact lt_of_le_of_ne (winner_min S x m hm hk)
      (fun he ↦ hkm (hx hk (winner_mem S x m hm) he.symm))
  · rintro ⟨hm, hmin⟩
    apply List.argmin_eq_some_iff.mpr
    refine ⟨by simpa only [Finset.mem_sort] using hm, ?_, ?_⟩
    · intro k hk
      have hkS : k ∈ S := by simpa only [Finset.mem_sort] using hk
      by_cases hkm : k = m
      · simp [hkm]
      · exact (hmin k hkS hkm).le
    · intro k hk hkm
      have hkS : k ∈ S := by simpa only [Finset.mem_sort] using hk
      by_cases he : k = m
      · simp [he]
      · exact False.elim ((not_le_of_gt (hmin k hkS he)) hkm)

/-- The strict race probability on an arbitrary deterministic finite subset. -/
theorem strict_race_measure {n : ℕ} (r : Fin n → ℝ) (hr : ∀ m, 0 < r m)
    (S : Finset (Fin n)) (m : Fin n) (hm : m ∈ S) :
    (Measure.pi fun k ↦ expMeasure (r k))
      {x | ∀ k ∈ S, k ≠ m → x m < x k} =
      ENNReal.ofReal (r m / ∑ k ∈ S, r k) := by
  classical
  have (k : Fin n) : IsProbabilityMeasure (expMeasure (r k)) :=
    isProbabilityMeasure_expMeasure (hr k)
  have hh := exponential_fresh_wins_on_ordinal_event r hr
    (fun k ↦ k ∈ S.erase m) m (by simp) Set.univ MeasurableSet.univ (by
      intro x c
      simp)
  have heq : {x : Fin n → ℝ |
      (∀ k : {k // k ∈ S.erase m}, x m < x k) ∧
        (fun k : {k // k ∈ S.erase m} ↦ x k) ∈ Set.univ} =
      {x | ∀ k ∈ S, k ≠ m → x m < x k} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_univ, and_true, Subtype.forall,
      Finset.mem_erase]
    aesop
  rw [heq, measure_univ, mul_one] at hh
  rw [← Finset.sum_subtype (S.erase m) (fun _ ↦ Iff.rfl) r] at hh
  rw [add_comm (r m), Finset.sum_erase_add _ _ hm] at hh
  exact hh

/-- The measurable reference winner has exactly its exponential race mass. -/
theorem winner_measure {n : ℕ} (r : Fin n → ℝ) (hr : ∀ m, 0 < r m)
    (S : Finset (Fin n)) (m : Fin n) (hm : m ∈ S) :
    (Measure.pi fun k ↦ expMeasure (r k)) {x | winner S x = some m} =
      ENNReal.ofReal (r m / ∑ k ∈ S, r k) := by
  have hw (k : Fin n) : 0 < (⟨r k, (hr k).le⟩ : ℝ≥0) := hr k
  have hi := ae_injective_exponentials (fun k ↦ (⟨r k, (hr k).le⟩ : ℝ≥0)) hw
  have he : {x : Fin n → ℝ | winner S x = some m} =ᵐ[
      Measure.pi fun k ↦ expMeasure (r k)] {x | ∀ k ∈ S, k ≠ m → x m < x k} := by
    filter_upwards [hi] with x hx
    exact propext (by simpa only [hm, true_and] using
      winner_eq_some_iff_strict S x hx.injOn m)
  exact (measure_congr he).trans (strict_race_measure r hr S m hm)

/-- A subcollection wins with probability equal to its fraction of the total rate. -/
theorem winner_in_measure {n : ℕ} (r : Fin n → ℝ) (hr : ∀ m, 0 < r m)
    (S T : Finset (Fin n)) (hTS : T ⊆ S) :
    (Measure.pi fun k ↦ expMeasure (r k)) {x | ∃ m ∈ T, winner S x = some m} =
      ENNReal.ofReal ((∑ k ∈ T, r k) / ∑ k ∈ S, r k) := by
  classical
  have heq : {x : Fin n → ℝ | ∃ m ∈ T, winner S x = some m} =
      ⋃ m ∈ T, {x | winner S x = some m} := by ext x; simp
  have hd : (T : Set (Fin n)).PairwiseDisjoint
      (fun m ↦ {x : Fin n → ℝ | winner S x = some m}) := by
    intro a _ b _ hab
    exact Set.disjoint_left.mpr fun x ha hb ↦ hab (Option.some.inj (ha.symm.trans hb))
  have hm (m : Fin n) : MeasurableSet {x : Fin n → ℝ | winner S x = some m} :=
    (measurableSet_singleton _).preimage (measurable_winner S)
  rw [heq, measure_biUnion_finset hd (fun m _ ↦ hm m)]
  have hv : (∑ m ∈ T, (Measure.pi fun k ↦ expMeasure (r k))
      {x | winner S x = some m}) = ∑ m ∈ T, ENNReal.ofReal (r m / ∑ k ∈ S, r k) :=
    Finset.sum_congr rfl fun m hm ↦ winner_measure r hr S m (hTS hm)
  rw [hv]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ ↦
    div_nonneg (hr m).le (Finset.sum_nonneg fun k _ ↦ (hr k).le)), Finset.sum_div]

/-- The shell outside a smaller prefix has its exact complementary race probability. -/
theorem winner_outside_measure {n : ℕ} (r : Fin n → ℝ) (hr : ∀ m, 0 < r m)
    (S T : Finset (Fin n)) (hTS : T ⊆ S) :
    (Measure.pi fun k ↦ expMeasure (r k)) {x | ¬ ∃ m ∈ T, winner S x = some m} =
      1 - ENNReal.ofReal ((∑ k ∈ T, r k) / ∑ k ∈ S, r k) := by
  have (k : Fin n) : IsProbabilityMeasure (expMeasure (r k)) :=
    isProbabilityMeasure_expMeasure (hr k)
  have hE : MeasurableSet {x : Fin n → ℝ | ∃ m ∈ T, winner S x = some m} := by
    have heq : {x : Fin n → ℝ | ∃ m ∈ T, winner S x = some m} =
        ⋃ m ∈ T, {x | winner S x = some m} := by ext x; simp
    rw [heq]
    exact Finset.measurableSet_biUnion _ fun m _ ↦
      (measurableSet_singleton _).preimage (measurable_winner S)
  change (Measure.pi fun k ↦ expMeasure (r k))
    ({x : Fin n → ℝ | ∃ m ∈ T, winner S x = some m}ᶜ) = _
  rw [measure_compl hE (measure_ne_top _ _), measure_univ, winner_in_measure r hr S T hTS]

/-- Reference categories are deterministic relabelings of the selected source. -/
noncomputable def category {n : ℕ} {κ : Type*} (S : Finset (Fin n)) (label : Fin n → κ)
    (x : Fin n → ℝ) : Option κ := (winner S x).map label

/-- Any deterministic labeling of a reference winner is measurable. -/
theorem measurable_category {n : ℕ} {κ : Type*} [MeasurableSpace (Option κ)]
    (S : Finset (Fin n)) (label : Fin n → κ) : Measurable (category S label) :=
  (measurable_of_countable (fun o : Option (Fin n) ↦ o.map label)).comp (measurable_winner S)

/-- Category probability is the total rate carried by that category inside the prefix. -/
theorem category_measure {n : ℕ} {κ : Type*} [DecidableEq κ]
    (r : Fin n → ℝ) (hr : ∀ m, 0 < r m) (S : Finset (Fin n))
    (label : Fin n → κ) (j : κ) :
    (Measure.pi fun k ↦ expMeasure (r k)) {x | category S label x = some j} =
      ENNReal.ofReal ((∑ k ∈ S with label k = j, r k) / ∑ k ∈ S, r k) := by
  have heq : {x : Fin n → ℝ | category S label x = some j} =
      {x | ∃ m ∈ S.filter (fun k ↦ label k = j), winner S x = some m} := by
    ext x
    change (winner S x).map label = some j ↔
      ∃ m ∈ S.filter (fun k ↦ label k = j), winner S x = some m
    cases hw : winner S x with
    | none => simp
    | some m =>
      simp only [Option.map_some, Option.some.injEq, Finset.mem_filter]
      constructor
      · intro hm
        exact ⟨m, ⟨winner_mem S x m hw, hm⟩, rfl⟩
      · rintro ⟨k, ⟨_, hk⟩, hkm⟩
        simpa only [← hkm] using hk
  rw [heq]
  exact winner_in_measure r hr S _ (Finset.filter_subset _ _)

/-- The real category probability is the literal ratio of the competing finite rate sums. -/
theorem category_real {n : ℕ} {κ : Type*} [DecidableEq κ]
    (r : Fin n → ℝ) (hr : ∀ m, 0 < r m) (S : Finset (Fin n))
    (label : Fin n → κ) (j : κ) :
    (Measure.pi fun k ↦ expMeasure (r k)).real {x | category S label x = some j} =
      (∑ k ∈ S with label k = j, r k) / ∑ k ∈ S, r k := by
  rw [measureReal_def, category_measure r hr S label j, ENNReal.toReal_ofReal]
  exact div_nonneg (Finset.sum_nonneg fun k _ ↦ (hr k).le)
    (Finset.sum_nonneg fun k _ ↦ (hr k).le)

end Ashlagi.ReferenceRace
