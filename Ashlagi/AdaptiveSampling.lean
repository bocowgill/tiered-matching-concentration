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

public import Ashlagi.Nonanticipating
public import Ashlagi.StreamPrefix

/-! # Fresh adaptive reads from an IID array

A fixed observed value word determines a unique policy-consistent coordinate history. Its exact
fiber is a finite cylinder; structural freshness makes its queried indices distinct.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace Ashlagi.AdaptiveSampling

variable {ι α : Type*}

/-- A newest-first history follows the querying rule on every predecessor history. -/
def Coherent (next : List (ι × α) → ι) : List (ι × α) → Prop
  | [] => True
  | (i, _) :: h => Coherent next h ∧ i = next h

/-- The policy never rereads a coordinate on any policy-consistent revealed history. -/
def Fresh (next : List (ι × α) → ι) : Prop :=
  ∀ h, Coherent next h → next h ∉ h.map Prod.fst

/-- A value word, newest first, determines its entire coordinate history without an input array. -/
def script (next : List (ι × α) → ι) : List α → List (ι × α)
  | [] => []
  | a :: L => (next (script next L), a) :: script next L

/-- The scripted coordinate history has exactly the supplied values. -/
theorem script_values (next : List (ι × α) → ι) (L : List α) :
    (script next L).map Prod.snd = L := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [script, List.map_cons, ih]

/-- Scripted histories are structurally legal for every value word, even a zero-mass one. -/
theorem coherent_script (next : List (ι × α) → ι) (L : List α) :
    Coherent next (script next L) := by
  induction L with
  | nil => trivial
  | cons a L ih => exact ⟨ih, rfl⟩

/-- A scripted word consumes one coordinate per observed value. -/
theorem script_length (next : List (ι × α) → ι) (L : List α) :
    (script next L).length = L.length := by
  have h := congrArg List.length (script_values next L)
  simpa only [List.length_map] using h

/-- Actual query histories have one record per adaptive read. -/
theorem queryHistory_length (next : List (ι × α) → ι) (x : ι → α) (t : ℕ) :
    (queryHistory next x t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [queryHistory, List.length_cons] using congrArg Nat.succ ih

/-- Every generated history is coherent with the querying rule. -/
theorem coherent_queryHistory (next : List (ι × α) → ι) (x : ι → α) (t : ℕ) :
    Coherent next (queryHistory next x t) := by
  induction t with
  | zero => trivial
  | succ t ih => exact ⟨ih, rfl⟩

/-- Coherent histories are determined by their value words alone. -/
theorem script_eq_of_coherent (next : List (ι × α) → ι) (h : List (ι × α))
    (hc : Coherent next h) : script next (h.map Prod.snd) = h := by
  induction h with
  | nil => rfl
  | cons entry h ih =>
    rcases entry with ⟨i, a⟩
    simp only [List.map_cons, script, ih hc.1, hc.2]

/-- Coordinate constraints imposed by a finite history, with no restriction on other entries. -/
def coordinateEvent (h : List (ι × α)) : Set (ι → α) :=
  {x | ∀ e ∈ h, x e.1 = e.2}

/-- Exact history fibers are their policy consistency and finite queried-coordinate constraints. -/
theorem queryHistory_eq_iff (next : List (ι × α) → ι) (x : ι → α)
    (h : List (ι × α)) :
    queryHistory next x h.length = h ↔ Coherent next h ∧ x ∈ coordinateEvent h := by
  induction h with
  | nil => simp [queryHistory, Coherent, coordinateEvent]
  | cons entry h ih =>
    rcases entry with ⟨i, a⟩
    constructor
    · intro heq
      have ht := (List.cons.inj heq).2
      have hh := (List.cons.inj heq).1
      obtain ⟨hc, hx⟩ := ih.mp ht
      rw [ht] at hh
      obtain ⟨hi, ha⟩ := Prod.mk.inj hh
      refine ⟨⟨hc, hi.symm⟩, ?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · simpa only [hi] using ha
      · exact hx e he
    · rintro ⟨⟨hc, hi⟩, hx⟩
      have hprev : x ∈ coordinateEvent h := fun e he ↦ hx e (List.mem_cons_of_mem _ he)
      have ht := ih.mpr ⟨hc, hprev⟩
      have ha : x i = a := hx (i, a) List.mem_cons_self
      simp only [List.length_cons, queryHistory, ht]
      rw [← hi, ha]

/-- Structural freshness gives distinct queried coordinates in every scripted history. -/
theorem script_nodup_coordinates (next : List (ι × α) → ι) (hf : Fresh next) (L : List α) :
    ((script next L).map Prod.fst).Nodup := by
  induction L with
  | nil => simp [script]
  | cons a L ih =>
    simpa only [script, List.map_cons, List.nodup_cons] using
      And.intro (hf _ (coherent_script next L)) ih

/-- A finite-history coordinate event is measurable, irrespective of freshness or consistency. -/
theorem measurableSet_coordinateEvent [MeasurableSpace α] [MeasurableSingletonClass α]
    (h : List (ι × α)) : MeasurableSet (coordinateEvent h) := by
  classical
  have heq : coordinateEvent h = ⋂ e ∈ h.toFinset, {x : ι → α | x e.1 = e.2} := by
    ext x
    simp [coordinateEvent]
  rw [heq]
  exact Finset.measurableSet_biInter _ (fun e _ ↦
    (measurableSet_singleton e.2).preimage (measurable_pi_apply e.1))

/-- Distinct fixed queried coordinates have exactly the product of their categorical masses. -/
theorem coordinateEvent_measure [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (h : List (ι × α)) (hnodup : (h.map Prod.fst).Nodup) :
    (Measure.infinitePi fun _ : ι ↦ p.toMeasure) (coordinateEvent h) =
      (h.map fun e ↦ p e.2).prod := by
  classical
  let coords : Fin h.length → ι := fun i ↦ (h.get i).1
  let vals : Fin h.length → α := fun i ↦ (h.get i).2
  have hcoords : List.ofFn coords = h.map Prod.fst := by
    change List.ofFn (fun i ↦ Prod.fst (h.get i)) = _
    rw [List.ofFn_comp', List.ofFn_get]
  have hinj : Function.Injective coords := List.nodup_ofFn.mp (hcoords ▸ hnodup)
  have hmap := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ι ↦ p.toMeasure) (f := coords) hinj
  have hm : MeasurableSet (Set.univ.pi fun i : Fin h.length ↦ {vals i}) :=
    MeasurableSet.univ_pi fun _ ↦ measurableSet_singleton _
  have heq : (fun x : ι → α ↦ fun i ↦ x (coords i)) ⁻¹'
      (Set.univ.pi fun i : Fin h.length ↦ {vals i}) = coordinateEvent h := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_singleton_iff, coordinateEvent,
      Set.mem_ofPred_eq]
    constructor
    · intro hx e he
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp he
      simpa only [coords, vals, hi] using hx i
    · intro hx i
      exact hx (h.get i) (List.get_mem _ _)
  have hh := congrArg (fun μ ↦ μ (Set.univ.pi fun i : Fin h.length ↦ {vals i})) hmap
  rw [Measure.map_apply (by fun_prop) hm, heq] at hh
  have hbox : (Measure.infinitePi fun _ : Fin h.length ↦ p.toMeasure)
      (Set.univ.pi fun i ↦ {vals i}) = ∏ i, p (vals i) := by
    simpa only [Finset.coe_univ, PMF.toMeasure_apply_singleton _ _
      (measurableSet_singleton _)] using Measure.infinitePi_pi
        (fun _ : Fin h.length ↦ p.toMeasure) (s := Finset.univ)
        (t := fun i ↦ {vals i}) (fun _ _ ↦ measurableSet_singleton _)
  rw [hbox] at hh
  rw [hh, ← List.prod_ofFn]
  congr 1
  change List.ofFn (fun i ↦ p (h.get i).2) = _
  rw [List.ofFn_comp' h.get (fun e ↦ p e.2), List.ofFn_get]

/-- A prescribed value word has one exact coherent history fiber, a finite coordinate cylinder. -/
theorem script_event_eq (next : List (ι × α) → ι) (L : List α) :
    {x : ι → α | queryHistory next x L.length = script next L} =
      coordinateEvent (script next L) := by
  ext x
  change (queryHistory next x L.length = script next L) ↔ x ∈ coordinateEvent (script next L)
  simpa only [script_length, coherent_script, true_and] using
    queryHistory_eq_iff next x (script next L)

/-- A fixed value word has the exact IID product probability under fresh adaptive reads. -/
theorem scripted_history_measure [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (next : List (ι × α) → ι) (hf : Fresh next) (p : PMF α) (L : List α) :
    (Measure.infinitePi fun _ : ι ↦ p.toMeasure)
      {x | queryHistory next x L.length = script next L} = (L.map fun a ↦ p a).prod := by
  rw [script_event_eq, coordinateEvent_measure p _ (script_nodup_coordinates next hf L)]
  have hm : (script next L).map (fun e ↦ p e.2) = L.map (fun a ↦ p a) := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (fun K : List α ↦ K.map (fun a ↦ p a)) (script_values next L)
  rw [hm]

/-- The observed values in chronological order, including every adaptive read. -/
def valueWord (next : List (ι × α) → ι) (x : ι → α) (t : ℕ) : List α :=
  ((queryHistory next x t).map Prod.snd).reverse

/-- The observed word has one categorical value per read. -/
theorem valueWord_length (next : List (ι × α) → ι) (x : ι → α) (t : ℕ) :
    (valueWord next x t).length = t := by
  simp only [valueWord, List.length_reverse, List.length_map, queryHistory_length]

/-- Exact chronological value fibers are the corresponding uniquely scripted history fibers. -/
theorem valueWord_eq_iff (next : List (ι × α) → ι) (x : ι → α) (t : ℕ) (L : List α) :
    valueWord next x t = L ↔ queryHistory next x t = script next L.reverse := by
  constructor
  · intro hword
    have hvalues := congrArg List.reverse hword
    simp only [valueWord, List.reverse_reverse] at hvalues
    rw [← script_eq_of_coherent next (queryHistory next x t) (coherent_queryHistory next x t),
      hvalues]
  · intro hhist
    simp only [valueWord, hhist, script_values, List.reverse_reverse]

/-- Chronological words have the exact product law, including repeated values and zero masses. -/
theorem valueWord_measure [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (next : List (ι × α) → ι) (hf : Fresh next) (p : PMF α) (L : List α) :
    (Measure.infinitePi fun _ : ι ↦ p.toMeasure) {x | valueWord next x L.length = L} =
      (L.map fun a ↦ p a).prod := by
  have heq : {x : ι → α | valueWord next x L.length = L} =
      {x | queryHistory next x L.reverse.length = script next L.reverse} := by
    ext x
    change (valueWord next x L.length = L) ↔
      queryHistory next x L.reverse.length = script next L.reverse
    simpa only [List.length_reverse] using valueWord_eq_iff next x L.length L
  rw [heq, scripted_history_measure next hf p L.reverse, List.map_reverse, List.prod_reverse]

/-- Exact joint IID masses for every prescribed chronological vector of adaptive values. -/
theorem chronological_vector_measure [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (next : List (ι × α) → ι) (hf : Fresh next)
    (p : PMF α) (t : ℕ) (v : Fin t → α) :
    (Measure.infinitePi fun _ : ι ↦ p.toMeasure) {x | valueWord next x t = List.ofFn v} =
      ∏ k, p (v k) := by
  have hh := valueWord_measure next hf p (List.ofFn v)
  simpa only [List.length_ofFn, List.map_ofFn, List.prod_ofFn, Function.comp_apply] using hh

/-- The finite value word is measurable without any measurability assumption on next. -/
theorem measurable_valueWord [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (next : List (ι × α) → ι) (t : ℕ) :
    @Measurable (ι → α) (List α) inferInstance ⊤ (fun x ↦ valueWord next x t) := by
  let : MeasurableSpace (List α) := ⊤
  apply measurable_to_countable'
  intro L
  change MeasurableSet {x : ι → α | valueWord next x t = L}
  by_cases hlen : L.length = t
  · have heq : {x : ι → α | valueWord next x t = L} =
        coordinateEvent (script next L.reverse) := by
      ext x
      change (valueWord next x t = L) ↔ x ∈ coordinateEvent (script next L.reverse)
      rw [valueWord_eq_iff]
      have hh := queryHistory_eq_iff next x (script next L.reverse)
      simpa only [script_length, List.length_reverse, hlen, coherent_script, true_and] using hh
    rw [heq]
    exact measurableSet_coordinateEvent _
  · have heq : {x : ι → α | valueWord next x t = L} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hlen (by rw [← hx, valueWord_length])
    rw [heq]
    exact MeasurableSet.empty

/-- Number of raw coordinates already consumed from a specified man's stream. -/
def slotCount {M : Type*} [DecidableEq M] (h : List ((M × ℕ) × α)) (m : M) : ℕ :=
  (h.filter fun e ↦ e.1.1 = m).length

/-- Any visible man-selection rule reads his next unused per-man counter slot. -/
def slotPolicy {M : Type*} [DecidableEq M] (choose : List ((M × ℕ) × α) → M)
    (h : List ((M × ℕ) × α)) : M × ℕ := (choose h, slotCount h (choose h))

/-- Appending a raw record increments precisely its man's slot count. -/
theorem slotCount_cons {M : Type*} [DecidableEq M] (h : List ((M × ℕ) × α))
    (q : M × ℕ) (a : α) (m : M) :
    slotCount ((q, a) :: h) m = slotCount h m + if q.1 = m then 1 else 0 := by
  by_cases hm : q.1 = m <;> simp [slotCount, hm]

/-- In every coherent count-slot history, each used slot is strictly below the current counter. -/
theorem coherent_slot_bound {M : Type*} [DecidableEq M]
    (choose : List ((M × ℕ) × α) → M) (h : List ((M × ℕ) × α))
    (hc : Coherent (slotPolicy choose) h) :
    ∀ e ∈ h, e.1.2 < slotCount h e.1.1 := by
  induction h with
  | nil => simp
  | cons entry h ih =>
    rcases entry with ⟨q, a⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · change q.2 < slotCount ((q, a) :: h) q.1
      rw [hc.2, slotCount_cons]
      simp [slotPolicy]
    · have hh := ih hc.1 e he
      rw [slotCount_cons]
      omega

/-- Count-slot policies are fresh for arbitrary visible choices, including dummy continuation. -/
theorem fresh_slotPolicy {M : Type*} [DecidableEq M]
    (choose : List ((M × ℕ) × α) → M) : Fresh (slotPolicy choose) := by
  intro h hc hmem
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
  have hb := coherent_slot_bound choose h hc e he
  rw [heq] at hb
  exact Nat.lt_irrefl _ hb

/-- Per-man next-counter reads produce IID global destination words for every visible rule. -/
theorem slotPolicy_vector_measure {M : Type*} [DecidableEq M] [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (choose : List ((M × ℕ) × α) → M) (p : PMF α) (t : ℕ) (v : Fin t → α) :
    (Measure.infinitePi fun _ : M × ℕ ↦ p.toMeasure)
      {x | valueWord (slotPolicy choose) x t = List.ofFn v} = ∏ k, p (v k) :=
  chronological_vector_measure (slotPolicy choose) (fresh_slotPolicy choose) p t v

/-- Static finite contexts can change the nonanticipating policy without harming measurability. -/
theorem measurable_context_valueWord {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (next : K → List (ι × α) → ι) (t : ℕ) :
    @Measurable (K × (ι → α)) (List α) inferInstance ⊤
      (fun z ↦ valueWord (next z.1) z.2 t) := by
  let : MeasurableSpace (List α) := ⊤
  exact measurable_from_prod_countable_right (fun c ↦ measurable_valueWord (next c) t)

/-- Adaptive IID words are independent of a static finite context that selects the policy. -/
theorem context_vector_measure {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : PMF K) (next : K → List (ι × α) → ι) (hf : ∀ c, Fresh (next c))
    (p : PMF α) (C : Set K) (t : ℕ) (v : Fin t → α) :
    (ν.toMeasure.prod (Measure.infinitePi fun _ : ι ↦ p.toMeasure))
      {z | z.1 ∈ C ∧ valueWord (next z.1) z.2 t = List.ofFn v} =
      ν.toMeasure C * ∏ k, p (v k) := by
  classical
  let : MeasurableSpace (List α) := ⊤
  have hmeas : MeasurableSet {z : K × (ι → α) |
      z.1 ∈ C ∧ valueWord (next z.1) z.2 t = List.ofFn v} :=
    ((Set.toFinite C).measurableSet.preimage measurable_fst).inter
      ((measurableSet_singleton (List.ofFn v)).preimage (measurable_context_valueWord next t))
  rw [Measure.prod_apply hmeas]
  have hsection (c : K) : (Measure.infinitePi fun _ : ι ↦ p.toMeasure)
      (Prod.mk c ⁻¹' {z : K × (ι → α) |
        z.1 ∈ C ∧ valueWord (next z.1) z.2 t = List.ofFn v}) =
      C.indicator (fun _ ↦ ∏ k, p (v k)) c := by
    by_cases hc : c ∈ C
    · rw [Set.indicator_of_mem hc]
      have heq : Prod.mk c ⁻¹' {z : K × (ι → α) |
          z.1 ∈ C ∧ valueWord (next z.1) z.2 t = List.ofFn v} =
          {x | valueWord (next c) x t = List.ofFn v} := by ext x; simp [hc]
      rw [heq]
      exact chronological_vector_measure (next c) (hf c) p t v
    · rw [Set.indicator_of_notMem hc]
      have heq : Prod.mk c ⁻¹' {z : K × (ι → α) |
          z.1 ∈ C ∧ valueWord (next z.1) z.2 t = List.ofFn v} = ∅ := by ext x; simp [hc]
      rw [heq, measure_empty]
  simp_rw [hsection]
  rw [lintegral_indicator_const (Set.toFinite C).measurableSet]
  exact mul_comm _ _

/-- The complete chronological observation stream of the nonanticipating array reads. -/
def observationStream (next : List (ι × α) → ι) (x : ι → α) (k : ℕ) : α :=
  x (next (queryHistory next x k))

/-- One more adaptive read appends its actual observed value to the chronological word. -/
theorem valueWord_succ (next : List (ι × α) → ι) (x : ι → α) (t : ℕ) :
    valueWord next x (t + 1) = valueWord next x t ++ [observationStream next x t] := by
  simp only [valueWord, queryHistory, List.map_cons, List.reverse_cons, observationStream]

/-- The existing finite word is precisely the initial vector of the complete observation stream. -/
theorem ofFn_observationStream (next : List (ι × α) → ι) (x : ι → α) (t : ℕ) :
    List.ofFn (fun i : Fin t ↦ observationStream next x i) = valueWord next x t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [List.ofFn_succ', valueWord_succ]
    simp only [List.concat_eq_append, Fin.val_castSucc, Fin.val_last, ih]

/-- The complete observation stream is measurable. -/
@[fun_prop]
theorem measurable_observationStream [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [Nonempty α] (next : List (ι × α) → ι) :
    Measurable (observationStream next) := by
  classical
  let : MeasurableSpace (List α) := ⊤
  let a : α := Classical.choice inferInstance
  apply Measurable.of_eval
  intro k
  let getValue : List α → α := fun L ↦ L[k]?.getD a
  have heq : (fun x : ι → α ↦ observationStream next x k) =
      getValue ∘ (fun x ↦ valueWord next x (k + 1)) := by
    funext x
    change observationStream next x k = getValue (valueWord next x (k + 1))
    rw [← ofFn_observationStream]
    simp only [getValue, List.getElem?_ofFn, dite_eq_left (Nat.lt_succ_self k), Option.getD_some]
  rw [heq]
  exact (measurable_of_countable getValue).comp (measurable_valueWord next (k + 1))

/-- Every finite initial vector of the complete observation stream has the exact product law. -/
theorem observationPrefix_law [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (next : List (ι × α) → ι) (hf : Fresh next) (p : PMF α) (H : ℕ) :
    Measure.map (fun x : ι → α ↦ fun i : Fin H ↦ observationStream next x i)
      (Measure.infinitePi fun _ : ι ↦ p.toMeasure) =
      Measure.pi (fun _ : Fin H ↦ p.toMeasure) := by
  obtain ⟨a, _⟩ := p.support_nonempty
  let : Nonempty α := ⟨a⟩
  have hm : Measurable (fun x : ι → α ↦ fun i : Fin H ↦ observationStream next x i) := by
    fun_prop
  apply Measure.ext_of_singleton
  intro v
  rw [Measure.map_apply hm (measurableSet_singleton v)]
  have heq : (fun x : ι → α ↦ fun i : Fin H ↦ observationStream next x i) ⁻¹' {v} =
      {x | valueWord next x H = List.ofFn v} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    rw [← ofFn_observationStream next x H]
    exact List.ofFn_injective.eq_iff.symm
  rw [heq, chronological_vector_measure next hf p H v]
  rw [← Set.univ_pi_singleton, Measure.pi_pi]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

/-- Every finite coordinate cylinder of the adaptive observation stream has its IID product mass. -/
theorem observation_finite_cylinder_measure [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (next : List (ι × α) → ι) (hf : Fresh next)
    (p : PMF α) (s : Finset ℕ) (T : ℕ → Set α) (hT : ∀ i, MeasurableSet (T i)) :
    (Measure.infinitePi fun _ : ι ↦ p.toMeasure)
      (observationStream next ⁻¹' Set.pi (s : Set ℕ) T) =
      ∏ i ∈ s, p.toMeasure (T i) := by
  classical
  obtain ⟨a, _⟩ := p.support_nonempty
  let : Nonempty α := ⟨a⟩
  let H := s.sup id + 1
  have hH (i : ℕ) (hi : i ∈ s) : i < H :=
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  let I : Finset (Fin H) := Finset.univ.filter (fun j ↦ j.val ∈ s)
  let B : Set (Fin H → α) := Set.pi (I : Set (Fin H)) (fun j ↦ T j.val)
  have hB : MeasurableSet B := MeasurableSet.pi (Finset.countable_toSet I)
    (fun j _ ↦ hT j.val)
  have hpre : (fun x : ι → α ↦ fun j : Fin H ↦ observationStream next x j) ⁻¹' B =
      observationStream next ⁻¹' Set.pi (s : Set ℕ) T := by
    ext x
    simp only [B, I, Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro hx i hi
      exact hx ⟨i, hH i hi⟩ hi
    · intro hx j hj
      exact hx j.val hj
  have hh := congrArg (fun ν ↦ ν B) (observationPrefix_law next hf p H)
  rw [Measure.map_apply (by fun_prop) hB, hpre] at hh
  change _ = (Measure.pi (fun _ : Fin H ↦ p.toMeasure))
    (Set.pi (I : Set (Fin H)) (fun j ↦ T j.val)) at hh
  rw [Measure.pi_pi_finset] at hh
  apply hh.trans
  apply Finset.prod_bij (fun j _ ↦ j.val)
  · intro j hj
    exact (Finset.mem_filter.mp hj).2
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro i hi
    exact ⟨⟨i, hH i hi⟩, by simp [I, hi], rfl⟩
  · intro _ _
    rfl

/-- Fresh nonanticipating reads preserve the complete infinite IID observation-stream law. -/
theorem observationStream_law [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (next : List (ι × α) → ι) (hf : Fresh next) (p : PMF α) :
    Measure.map (observationStream next) (Measure.infinitePi fun _ : ι ↦ p.toMeasure) =
      FirstFresh.iidStream p := by
  obtain ⟨a, _⟩ := p.support_nonempty
  let : Nonempty α := ⟨a⟩
  apply Measure.eq_infinitePi (fun _ : ℕ ↦ p.toMeasure)
  intro s T hT
  rw [Measure.map_apply (measurable_observationStream next)
    (MeasurableSet.pi (Finset.countable_toSet s) (fun i _ ↦ hT i))]
  exact observation_finite_cylinder_measure next hf p s T hT

/-- A static finite context can select the full observation policy measurably. -/
@[fun_prop]
theorem measurable_context_observationStream {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [Nonempty α] (next : K → List (ι × α) → ι) :
    Measurable (fun z : K × (ι → α) ↦ observationStream (next z.1) z.2) :=
  measurable_from_prod_countable_right (fun c ↦ measurable_observationStream (next c))

/-- The complete adaptive stream is independent of the static context that selects its policy. -/
theorem context_stream_measure {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : PMF K) (next : K → List (ι × α) → ι) (hf : ∀ c, Fresh (next c))
    (p : PMF α) (C : Set K) (E : Set (ℕ → α)) (hE : MeasurableSet E) :
    (ν.toMeasure.prod (Measure.infinitePi fun _ : ι ↦ p.toMeasure))
      {z | z.1 ∈ C ∧ observationStream (next z.1) z.2 ∈ E} =
      ν.toMeasure C * FirstFresh.iidStream p E := by
  classical
  obtain ⟨a, _⟩ := p.support_nonempty
  let : Nonempty α := ⟨a⟩
  have hmeas : MeasurableSet {z : K × (ι → α) |
      z.1 ∈ C ∧ observationStream (next z.1) z.2 ∈ E} :=
    ((Set.toFinite C).measurableSet.preimage measurable_fst).inter
      (hE.preimage (measurable_context_observationStream next))
  rw [Measure.prod_apply hmeas]
  have hsection (c : K) : (Measure.infinitePi fun _ : ι ↦ p.toMeasure)
      (Prod.mk c ⁻¹' {z : K × (ι → α) |
        z.1 ∈ C ∧ observationStream (next z.1) z.2 ∈ E}) =
      C.indicator (fun _ ↦ FirstFresh.iidStream p E) c := by
    by_cases hc : c ∈ C
    · rw [Set.indicator_of_mem hc]
      have heq : Prod.mk c ⁻¹' {z : K × (ι → α) |
          z.1 ∈ C ∧ observationStream (next z.1) z.2 ∈ E} =
          observationStream (next c) ⁻¹' E := by ext x; simp [hc]
      rw [heq, ← Measure.map_apply (measurable_observationStream (next c)) hE,
        observationStream_law (next c) (hf c) p]
    · rw [Set.indicator_of_notMem hc]
      have heq : Prod.mk c ⁻¹' {z : K × (ι → α) |
          z.1 ∈ C ∧ observationStream (next z.1) z.2 ∈ E} = ∅ := by ext x; simp [hc]
      rw [heq, measure_empty]
  simp_rw [hsection]
  rw [lintegral_indicator_const (Set.toFinite C).measurableSet]
  exact mul_comm _ _

/-- Joint pushforward retains the static context and an independent complete IID stream. -/
theorem context_observationStream_law {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : PMF K) (next : K → List (ι × α) → ι) (hf : ∀ c, Fresh (next c)) (p : PMF α) :
    Measure.map (fun z : K × (ι → α) ↦ (z.1, observationStream (next z.1) z.2))
      (ν.toMeasure.prod (Measure.infinitePi fun _ : ι ↦ p.toMeasure)) =
      ν.toMeasure.prod (FirstFresh.iidStream p) := by
  obtain ⟨a, _⟩ := p.support_nonempty
  let : Nonempty α := ⟨a⟩
  symm
  apply Measure.prod_eq
  intro C E hC hE
  rw [Measure.map_apply (measurable_fst.prodMk (measurable_context_observationStream next))
    (hC.prod hE)]
  have heq : (fun z : K × (ι → α) ↦ (z.1, observationStream (next z.1) z.2)) ⁻¹'
      (C ×ˢ E) =
      {z | z.1 ∈ C ∧ observationStream (next z.1) z.2 ∈ E} := by ext z; rfl
  rw [heq]
  exact context_stream_measure ν next hf p C E hE

/-- Arbitrary visible count-slot selection preserves the entire infinite global IID stream. -/
theorem slotPolicy_stream_law {M : Type*} [DecidableEq M] [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (choose : List ((M × ℕ) × α) → M) (p : PMF α) :
    Measure.map (observationStream (slotPolicy choose))
      (Measure.infinitePi fun _ : M × ℕ ↦ p.toMeasure) = FirstFresh.iidStream p :=
  observationStream_law (slotPolicy choose) (fresh_slotPolicy choose) p

end Ashlagi.AdaptiveSampling
