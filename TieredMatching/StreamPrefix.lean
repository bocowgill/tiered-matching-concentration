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

public import TieredMatching.FirstFresh

/-! # Ordered finite-prefix and unused-tail laws for the canonical iid stream

The stream is `FirstFresh.iidStream p`, the infinite product of the exact categorical PMF p.
Every finite ordered cylinder has the product of its coordinate masses, including impossible
prefixes and the empty prefix. Conditioning events expose no unused stream coordinates.
-/

@[expose] public section

namespace TieredMatching.StreamPrefix

open MeasureTheory
open scoped ENNReal NNReal

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- A finite ordered iid cylinder, using the first k coordinates without repetitions of indices. -/
def tupleEvent {k : ℕ} (y : Fin k → α) : Set (ℕ → α) :=
  {x | ∀ i : Fin k, x i = y i}

/-- An ordered finite list prefix of the raw iid stream. Repeated values are permitted. -/
def prefixEvent (L : List α) : Set (ℕ → α) :=
  {x | ∀ i : Fin L.length, x i = L.get i}

omit [Fintype α] in
/-- Finite ordered cylinder events are measurable. -/
theorem measurableSet_tupleEvent {k : ℕ} (y : Fin k → α) : MeasurableSet (tupleEvent y) := by
  have he : tupleEvent y = ⋂ i : Fin k, {x : ℕ → α | x i = y i} := by
    ext x
    simp [tupleEvent]
  rw [he]
  exact MeasurableSet.iInter fun i ↦ (measurableSet_singleton (y i)).preimage
    (measurable_pi_apply i.val)

omit [Fintype α] in
/-- Every finite list prefix event is measurable. -/
theorem measurableSet_prefixEvent (L : List α) : MeasurableSet (prefixEvent L) :=
  measurableSet_tupleEvent L.get

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- An ordered tuple cylinder is a finite-coordinate product cylinder. -/
theorem tupleEvent_eq_pi {k : ℕ} (y : Fin k → α) :
    tupleEvent y = Set.pi (Finset.range k)
      (fun t ↦ if ht : t < k then {y ⟨t, ht⟩} else Set.univ) := by
  ext x
  simp only [tupleEvent, Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_range]
  constructor
  · intro h t ht
    simpa only [dite_eq_left ht, Set.mem_singleton_iff] using h ⟨t, ht⟩
  · intro h i
    simpa only [dite_eq_left i.isLt, Set.mem_singleton_iff] using h i i.isLt

/-- The exact ordered cylinder mass is the literal product of categorical point masses. -/
theorem tupleEvent_measure (p : PMF α) {k : ℕ} (y : Fin k → α) :
    FirstFresh.iidStream p (tupleEvent y) = ∏ i, p (y i) := by
  classical
  rw [tupleEvent_eq_pi, FirstFresh.iidStream,
    Measure.infinitePi_pi (fun _ : ℕ ↦ p.toMeasure)
      (fun t _ ↦ (Set.toFinite _).measurableSet), Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro t ht
  have htk := Finset.mem_range.mp ht
  simp only [dite_eq_left htk, PMF.toMeasure_apply_singleton p _ (measurableSet_singleton _)]

/-- The exact iid finite-prefix mass permits zero-probability entries and the empty list. -/
theorem prefixEvent_measure (p : PMF α) (L : List α) :
    FirstFresh.iidStream p (prefixEvent L) = (L.map fun q ↦ p q).prod := by
  change FirstFresh.iidStream p (tupleEvent L.get) = _
  rw [tupleEvent_measure, ← List.prod_ofFn]
  have hlist : List.ofFn (fun i : Fin L.length ↦ p (L.get i)) = L.map (fun q ↦ p q) := by
    change List.ofFn ((fun q ↦ p q) ∘ L.get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  rw [hlist]

/-- Revealing one additional stream value multiplies prefix mass by exactly its PMF mass. -/
theorem prefixEvent_append_measure (p : PMF α) (L : List α) (q : α) :
    FirstFresh.iidStream p (prefixEvent (L ++ [q])) =
      p q * FirstFresh.iidStream p (prefixEvent L) := by
  rw [prefixEvent_measure, prefixEvent_measure]
  simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]
  exact mul_comm _ _

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Extending an ordered prefix fixes exactly the next unused coordinate. -/
theorem prefixEvent_append (L : List α) (q : α) :
    prefixEvent (L ++ [q]) = prefixEvent L ∩ {x : ℕ → α | x L.length = q} := by
  ext x
  change (∀ i : Fin (L ++ [q]).length, x i = (L ++ [q]).get i) ↔
    (∀ i : Fin L.length, x i = L.get i) ∧ x L.length = q
  constructor
  · intro h
    constructor
    · intro i
      have hi : i.val < (L ++ [q]).length := by simp
      have hh := h ⟨i.val, hi⟩
      simpa only [List.get_eq_getElem, List.getElem_append_left i.isLt] using hh
    · have hi : L.length < (L ++ [q]).length := by simp
      have hh := h ⟨L.length, hi⟩
      simpa using hh
  · rintro ⟨h, hq⟩ i
    have hi := i.isLt
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hleft : i.val < L.length
    · have hh := h ⟨i.val, hleft⟩
      simpa only [List.get_eq_getElem, List.getElem_append_left hleft] using hh
    · have heq : i.val = L.length := by omega
      rw [List.get_eq_getElem, List.getElem_append_right
        (as := L) (bs := [q]) (i := i.val) (Nat.le_of_not_gt hleft)]
      simpa only [heq, Nat.sub_self, List.getElem_cons_zero] using hq

/-- The next singleton coordinate keeps its exact original law after any finite past prefix. -/
theorem prefixEvent_next_measure (p : PMF α) (L : List α) (q : α) :
    FirstFresh.iidStream p (prefixEvent L ∩ {x : ℕ → α | x L.length = q}) =
      p q * FirstFresh.iidStream p (prefixEvent L) := by
  rw [← prefixEvent_append, prefixEvent_append_measure]

/-- The unused infinite stream starting exactly at coordinate k. -/
def tailFrom (k : ℕ) (x : ℕ → α) (t : ℕ) : α := x (k + t)

omit [Fintype α] [MeasurableSingletonClass α] in
/-- Taking the unused tail is measurable, including at the empty prefix. -/
@[fun_prop]
theorem measurable_tailFrom (k : ℕ) : Measurable (tailFrom k : (ℕ → α) → ℕ → α) := by
  unfold tailFrom
  fun_prop

omit [Fintype α] [MeasurableSingletonClass α] in
/-- The full unused tail has exactly the original iid stream law. -/
theorem map_tailFrom (p : PMF α) (k : ℕ) :
    (FirstFresh.iidStream p).map (tailFrom k) = FirstFresh.iidStream p := by
  cases k with
  | zero =>
    have he : (tailFrom 0 : (ℕ → α) → ℕ → α) = id := by
      funext x t
      simp [tailFrom]
    rw [he, Measure.map_id]
  | succ k => exact FirstFresh.map_tailAfter p k

omit [Fintype α] [MeasurableSingletonClass α] in
/-- Every deterministic finite tuple is independent of the complete unused tail. -/
theorem indepFun_tuple_tail (p : PMF α) (k : ℕ) :
    ProbabilityTheory.IndepFun (fun x : ℕ → α ↦ fun i : Fin k ↦ x i)
      (tailFrom k) (FirstFresh.iidStream p) := by
  cases k with
  | zero =>
    have he : (fun x : ℕ → α ↦ fun i : Fin 0 ↦ x i) =
        (fun _ : ℕ → α ↦ fun i : Fin 0 ↦ Fin.elim0 i) := by
      funext x i
      exact Fin.elim0 i
    rw [he]
    exact ProbabilityTheory.indepFun_const_left _ _
  | succ k => exact FirstFresh.indepFun_head_tail p k

omit [Fintype α] in
/-- An ordered finite cylinder is independent of every measurable unused-tail event. -/
theorem tupleEvent_tail_measure (p : PMF α) {k : ℕ} (y : Fin k → α)
    (E : Set (ℕ → α)) (hE : MeasurableSet E) :
    FirstFresh.iidStream p (tupleEvent y ∩ (tailFrom k) ⁻¹' E) =
      FirstFresh.iidStream p (tupleEvent y) * FirstFresh.iidStream p E := by
  let C : Set (Fin k → α) := {y}
  have hpre : (fun x : ℕ → α ↦ fun i : Fin k ↦ x i) ⁻¹' C = tupleEvent y := by
    ext x
    simp only [C, Set.mem_preimage, Set.mem_singleton_iff, tupleEvent, Set.mem_ofPred_eq]
    exact funext_iff
  have h := (indepFun_tuple_tail p k).measure_inter_preimage_eq_mul C E
    (measurableSet_singleton y) hE
  rw [hpre, ← Measure.map_apply (measurable_tailFrom k) hE, map_tailFrom] at h
  exact h

omit [Fintype α] in
/-- After any exact finite past list, the entire unused stream is independent and iid. -/
theorem prefixEvent_tail_measure (p : PMF α) (L : List α)
    (E : Set (ℕ → α)) (hE : MeasurableSet E) :
    FirstFresh.iidStream p (prefixEvent L ∩ (tailFrom L.length) ⁻¹' E) =
      FirstFresh.iidStream p (prefixEvent L) * FirstFresh.iidStream p E :=
  tupleEvent_tail_measure p L.get E hE

/-- Revealing one additional value also leaves every measurable future-tail event independent. -/
theorem prefixEvent_next_tail_measure (p : PMF α) (L : List α) (q : α)
    (E : Set (ℕ → α)) (hE : MeasurableSet E) :
    FirstFresh.iidStream p
      (prefixEvent L ∩ {x : ℕ → α | x L.length = q} ∩ (tailFrom (L.length + 1)) ⁻¹' E) =
      p q * FirstFresh.iidStream p (prefixEvent L) * FirstFresh.iidStream p E := by
  rw [← prefixEvent_append]
  have hlen : L.length + 1 = (L ++ [q]).length := by simp
  rw [hlen, prefixEvent_tail_measure p (L ++ [q]) E hE, prefixEvent_append_measure]

end TieredMatching.StreamPrefix
