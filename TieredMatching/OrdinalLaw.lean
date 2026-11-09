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

public import TieredMatching.OrdinalHistory

/-! # Exact probability identities for revealed ordinal DA transcripts -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TieredMatching.Ordinal

/-- Restricting a finite independent array to a subset preserves its product marginal. -/
theorem measurePreserving_restrict_subtype {ι α : Type*} [Fintype ι]
    [MeasurableSpace α] (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p] :
    MeasurePreserving (fun x : ι → α ↦ fun i : {i // p i} ↦ x i)
      (Measure.pi μ) (Measure.pi fun i : {i // p i} ↦ μ i) := by
  exact measurePreserving_fst.comp (measurePreserving_piEquivPiSubtypeProd μ p)

/-- A one-coordinate conditional probability identity multiplies through independent rows. -/
theorem measure_pi_row_factor {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace α] (μ : ι → Measure α) [∀ i, SigmaFinite (μ i)]
    (E : ι → Set α) (A : Set α) (w : ι) (q : ℝ≥0∞)
    (hA : μ w (A ∩ E w) = q * μ w (E w)) :
    (Measure.pi μ) {x | (∀ v, x v ∈ E v) ∧ x w ∈ A} =
      q * (Measure.pi μ) (univ.pi E) := by
  have heq : {x | (∀ v, x v ∈ E v) ∧ x w ∈ A} =
      univ.pi (Function.update E w (A ∩ E w)) := by
    ext x
    simp only [mem_ofPred_eq, mem_univ_pi]
    constructor
    · rintro ⟨hrows, hnew⟩ v
      by_cases hv : v = w
      · subst v
        simpa only [Function.update_self, mem_inter_iff] using And.intro hnew (hrows w)
      · simpa only [Function.update_of_ne hv] using hrows v
    · intro hrows
      have hw : x w ∈ A ∩ E w := by simpa only [Function.update_self] using hrows w
      refine ⟨fun v ↦ ?_, hw.1⟩
      by_cases hv : v = w
      · simpa only [hv] using hw.2
      · simpa only [Function.update_of_ne hv] using hrows v
  rw [heq, Measure.pi_pi, Measure.pi_pi]
  have hfun : (fun v ↦ μ v (Function.update E w (A ∩ E w) v)) =
      Function.update (fun v ↦ μ v (E v)) w (μ w (A ∩ E w)) := by
    funext v
    by_cases hv : v = w <;> simp [hv]
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ w), hA]
  rw [Finset.sdiff_singleton_eq_erase,
    ← Finset.mul_prod_erase Finset.univ (fun v ↦ μ v (E v)) (Finset.mem_univ w)]
  exact mul_assoc _ _ _

/-- A full row's exact history event has the product probability of its seen-coordinate event. -/
theorem exponential_rowFiber_measure {n : ℕ} (r : Fin n → ℝ) (hr : ∀ m, 0 < r m)
    (h : List (Entry n)) (w : Fin n) :
    (Measure.pi fun m ↦ expMeasure (r m)) {row | RowFiber h w row} =
      (Measure.pi fun m : SeenMen h w ↦ expMeasure (r m)) (seenRowEvent h w) := by
  have (m : Fin n) : IsProbabilityMeasure (expMeasure (r m)) :=
    isProbabilityMeasure_expMeasure (hr m)
  have hmp := measurePreserving_restrict_subtype (fun m ↦ expMeasure (r m))
    (fun m ↦ (w, m) ∈ seenEdges h)
  rw [← hmp.map_eq, Measure.map_apply hmp.measurable (measurableSet_seenRowEvent h w)]
  congr 1
  ext row
  exact rowFiber_iff_seenRowEvent h w row

/-- Acceptance on a single exact ordinal row event has the rate ratio obtained from precisely
its already seen proposers. The new edge's freshness is a structural transcript condition. -/
theorem exponential_row_acceptance_measure {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ m, 0 < r m) (h : List (Entry n)) (w m : Fin n)
    (hfresh : (w, m) ∉ seenEdges h) :
    (Measure.pi fun k ↦ expMeasure (r k))
      {row | (∀ k : SeenMen h w, row m < row k.val) ∧ RowFiber h w row} =
      ENNReal.ofReal (r m / (r m + ∑ k : SeenMen h w, r k.val)) *
        (Measure.pi fun k ↦ expMeasure (r k)) {row | RowFiber h w row} := by
  have h := exponential_fresh_wins_on_ordinal_event r hr
    (fun k ↦ (w, k) ∈ seenEdges h) m hfresh (seenRowEvent h w)
    (measurableSet_seenRowEvent h w) (translationInvariant_seenRowEvent h w)
  rw [← exponential_rowFiber_measure r hr _ w] at h
  convert h using 1
  congr 1
  ext row
  exact and_congr_right fun _ ↦ rowFiber_iff_seenRowEvent _ w row

/-- The exact finite ordinal DA transcript gives the published acceptance probability.
This is a joint-event identity, so it is valid even for a zero-probability transcript. -/
theorem exponential_transcript_acceptance_measure {n : ℕ}
    (P : Fin n → Equiv.Perm (Fin n)) (r : Fin n → ℝ) (hr : ∀ m, 0 < r m)
    (t : ℕ) (h : List (Entry n)) (hlen : h.length = t) (hvalid : Valid P h)
    (w m : Fin n) (hnext : Arrival.nextEdge P (recordState h) = some (w, m)) :
    (Measure.pi fun _ : Fin n ↦ Measure.pi fun k ↦ expMeasure (r k))
      {x | transcript P (Function.uncurry x) t = h ∧
        accept (Function.uncurry x) (recordState h) (w, m) = true} =
      ENNReal.ofReal (r m / (r m + ∑ k : SeenMen h w, r k.val)) *
        (Measure.pi fun _ : Fin n ↦ Measure.pi fun k ↦ expMeasure (r k))
          {x | transcript P (Function.uncurry x) t = h} := by
  have (m : Fin n) : IsProbabilityMeasure (expMeasure (r m)) :=
    isProbabilityMeasure_expMeasure (hr m)
  let E (v : Fin n) : Set (Fin n → ℝ) := {row | RowFiber h v row}
  let A : Set (Fin n → ℝ) := {row | ∀ k : SeenMen h w, row m < row k.val}
  let q := ENNReal.ofReal (r m / (r m + ∑ k : SeenMen h w, r k.val))
  have hfresh := nextEdge_fresh_of_valid P h hvalid (w, m) hnext
  have hA : (Measure.pi fun k ↦ expMeasure (r k)) (A ∩ E w) =
      q * (Measure.pi fun k ↦ expMeasure (r k)) (E w) :=
    exponential_row_acceptance_measure r hr h w m hfresh
  have hfactor := measure_pi_row_factor (fun _ : Fin n ↦
    Measure.pi fun k ↦ expMeasure (r k)) E A w q hA
  have heq : {x : Fin n → Fin n → ℝ | transcript P (Function.uncurry x) t = h} =
      univ.pi E := by
    ext x
    simp only [mem_ofPred_eq, mem_univ_pi]
    constructor
    · intro hx
      exact ((transcript_eq_iff P (Function.uncurry x) t h).mp hx).2.2
    · intro hx
      exact (transcript_eq_iff P (Function.uncurry x) t h).mpr ⟨hlen, hvalid, hx⟩
  have heqA : {x : Fin n → Fin n → ℝ |
      transcript P (Function.uncurry x) t = h ∧
        accept (Function.uncurry x) (recordState h) (w, m) = true} =
      {x | (∀ v, x v ∈ E v) ∧ x w ∈ A} := by
    ext x
    constructor
    · rintro ⟨hx, hacc⟩
      have hrows := ((transcript_eq_iff P (Function.uncurry x) t h).mp hx).2.2
      exact ⟨hrows, (accept_true_iff_all_seen h w m (Function.uncurry x) (hrows w)).mp hacc⟩
    · rintro ⟨hrows, hacc⟩
      exact ⟨(transcript_eq_iff P (Function.uncurry x) t h).mpr ⟨hlen, hvalid, hrows⟩,
        (accept_true_iff_all_seen h w m (Function.uncurry x) (hrows w)).mpr hacc⟩
  rw [heqA, heq]
  exact hfactor

/-- A finite selector on the first input can select any measurable event on the second. -/
theorem measurableSet_selected_row_event {R Ω : Type*} [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] [MeasurableSpace Ω]
    (E : R → Set Ω) (hE : ∀ r, MeasurableSet (E r)) :
    MeasurableSet {z : R × Ω | z.2 ∈ E z.1} := by
  have heq : {z : R × Ω | z.2 ∈ E z.1} = ⋃ r, ({r} ×ˢ E r) := by
    ext z
    simp
  rw [heq]
  exact MeasurableSet.iUnion fun r ↦ (measurableSet_singleton r).prod (hE r)

/-- Conditional event identities for every finite first input remain valid after that input
is hidden. This uses product integration, without disclosing any of the unused second input. -/
theorem measure_prod_selected_event_factor {R Ω : Type*} [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] [MeasurableSpace Ω]
    (ν : Measure R) (μ : Measure Ω) [SFinite ν] [SFinite μ]
    (E : R → Set Ω) (hE : ∀ r, MeasurableSet (E r)) (A : Set Ω)
    (hA : MeasurableSet A) (q : ℝ≥0∞)
    (hfactor : ∀ r, μ (E r ∩ A) = q * μ (E r)) :
    (ν.prod μ) {z | z.2 ∈ E z.1 ∧ z.2 ∈ A} =
      q * (ν.prod μ) {z | z.2 ∈ E z.1} := by
  have hm := measurableSet_selected_row_event E hE
  have hmA : MeasurableSet {z : R × Ω | z.2 ∈ E z.1 ∧ z.2 ∈ A} :=
    hm.inter (hA.preimage measurable_snd)
  rw [Measure.prod_apply hmA, Measure.prod_apply hm]
  simp only [preimage_ofPred_eq]
  simp_rw [show ∀ r, {a | a ∈ E r ∧ a ∈ A} = E r ∩ A by intro r; rfl, hfactor]
  exact lintegral_const_mul _ (measurable_of_countable _)

local instance {n : ℕ} : MeasurableSpace (Fin n → Equiv.Perm (Fin n)) := ⊤

/-- The next proposal's acceptance law remains exact when the independent men's ranking tuple
is hidden. Only the prior ordinal transcript and the identity of the next edge are retained. -/
theorem exponential_hidden_rank_acceptance_measure {n : ℕ}
    (ν : Measure (Fin n → Equiv.Perm (Fin n))) [SFinite ν]
    (r : Fin n → ℝ) (hr : ∀ m, 0 < r m) (t : ℕ) (h : List (Entry n))
    (hlen : h.length = t) (w m : Fin n) :
    (ν.prod (Measure.pi fun _ : Fin n ↦ Measure.pi fun k ↦ expMeasure (r k)))
      {z | transcript z.1 (Function.uncurry z.2) t = h ∧
        Arrival.nextEdge z.1 (recordState h) = some (w, m) ∧
        accept (Function.uncurry z.2) (recordState h) (w, m) = true} =
      ENNReal.ofReal (r m / (r m + ∑ k : SeenMen h w, r k.val)) *
        (ν.prod (Measure.pi fun _ : Fin n ↦ Measure.pi fun k ↦ expMeasure (r k)))
          {z | transcript z.1 (Function.uncurry z.2) t = h ∧
            Arrival.nextEdge z.1 (recordState h) = some (w, m)} := by
  classical
  have (m : Fin n) : IsProbabilityMeasure (expMeasure (r m)) :=
    isProbabilityMeasure_expMeasure (hr m)
  let E (P : Fin n → Equiv.Perm (Fin n)) : Set (Fin n → Fin n → ℝ) :=
    {x | transcript P (Function.uncurry x) t = h ∧
      Arrival.nextEdge P (recordState h) = some (w, m)}
  let A : Set (Fin n → Fin n → ℝ) :=
    {x | accept (Function.uncurry x) (recordState h) (w, m) = true}
  let μ := Measure.pi fun _ : Fin n ↦ Measure.pi fun k ↦ expMeasure (r k)
  let q := ENNReal.ofReal (r m / (r m + ∑ k : SeenMen h w, r k.val))
  have hE (P : Fin n → Equiv.Perm (Fin n)) : MeasurableSet (E P) := by
    have hm := (measurableSet_transcript_fiber P t h).preimage
      (show Measurable (Function.uncurry : (Fin n → Fin n → ℝ) → Arrival.Edge n → ℝ) by fun_prop)
    by_cases hn : Arrival.nextEdge P (recordState h) = some (w, m)
    · simpa [E, hn] using hm
    · simp only [E, hn, and_false, ofPred_false, MeasurableSet.empty]
  have hA : MeasurableSet A := by
    cases hh : (recordState h).held w with
    | none => simp only [A, accept, hh, ofPred_true, MeasurableSet.univ]
    | some old =>
      have heq : A = {x : Fin n → Fin n → ℝ | x w m < x w old} := by
        ext x
        by_cases hc : x w m < x w old <;> simp [A, accept, hh, Function.uncurry, hc]
      rw [heq]
      exact measurableSet_lt
        (show Measurable (fun x : Fin n → Fin n → ℝ ↦ x w m) by fun_prop)
        (show Measurable (fun x : Fin n → Fin n → ℝ ↦ x w old) by fun_prop)
  have hfactor (P : Fin n → Equiv.Perm (Fin n)) : μ (E P ∩ A) = q * μ (E P) := by
    by_cases hn : Arrival.nextEdge P (recordState h) = some (w, m)
    · by_cases hv : Valid P h
      · simpa [μ, q, E, A, hn, ofPred_and] using
          exponential_transcript_acceptance_measure P r hr t h hlen hv w m hn
      · have he : E P = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro x hx
          exact hv ((transcript_eq_iff P (Function.uncurry x) t h).mp hx.1).2.1
        simp only [he, empty_inter, measure_empty, mul_zero]
    · have he : E P = ∅ := by simp only [E, hn, and_false, ofPred_false]
      simp only [he, empty_inter, measure_empty, mul_zero]
  have hout := measure_prod_selected_event_factor ν μ E hE A hA q hfactor
  simpa only [E, A, mem_ofPred_eq, and_assoc] using hout

end TieredMatching.Ordinal
