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

public import Ashlagi.RawHistory
public import Ashlagi.RawMarketLaw

/-! # Exact coarse transition kernels for raw iid proposal attempts

The conditioning event is the actual revealed raw transcript, including repeated destinations
and ordinal acceptance bits. Its fixed fiber is a product of consumed stream prefixes and
women's ordinal row events. No future ranking or raw priority value is revealed.
-/

@[expose] public section

namespace Ashlagi.Raw

open MeasureTheory StableMarriage
open Arrival
open scoped ENNReal NNReal

/-- Independent men's iid streams and women's nested priority rows, in rawInputLaw orientation. -/
abbrev Sources (n : ℕ) := (Fin n → ℕ → Fin n) × (Fin n → Fin n → ℝ)

/-- The actual raw transcript on the nested source space used by rawInputLaw. -/
noncomputable def inputTranscript {n : ℕ} (C : Protocol n) (t : ℕ) (z : Sources n) :
    List (Entry n) := transcript C z.1 (Function.uncurry z.2) t

/-- The exact event that the revealed actual raw history is h. -/
def historyEvent {n : ℕ} (C : Protocol n) (h : List (Entry n)) : Set (Sources n) :=
  {z | inputTranscript C h.length z = h}

/-- The fixed ordered prefix event in every man's iid stream. -/
def streamFiber {n : ℕ} (h : List (Entry n)) : Set (Fin n → ℕ → Fin n) :=
  Set.univ.pi fun m ↦ StreamPrefix.prefixEvent (drawOrder h m)

/-- The ordinal row event imposed on every woman's priorities by a raw history. -/
def womenFiber {n : ℕ} (h : List (Entry n)) : Set (Fin n → Fin n → ℝ) :=
  Set.univ.pi fun w ↦ {row | Ordinal.RowFiber (ordinary h) w row}

/-- Every independent male prefix fiber is measurable. -/
theorem measurableSet_streamFiber {n : ℕ} (h : List (Entry n)) :
    MeasurableSet (streamFiber h) :=
  MeasurableSet.univ_pi fun m ↦ StreamPrefix.measurableSet_prefixEvent (drawOrder h m)

/-- Every independent female ordinal fiber is measurable. -/
theorem measurableSet_womenFiber {n : ℕ} (h : List (Entry n)) :
    MeasurableSet (womenFiber h) :=
  MeasurableSet.univ_pi fun w ↦ Ordinal.measurableSet_rowFiber (ordinary h) w

/-- The exact actual raw transcript fiber is a product of consumed prefixes and ordinal rows. -/
theorem historyEvent_eq_product {n : ℕ} (C : Protocol n) (h : List (Entry n))
    (hv : Valid C h) : historyEvent C h = streamFiber h ×ˢ womenFiber h := by
  ext z
  simp only [historyEvent, inputTranscript, Set.mem_ofPred_eq, transcript_eq_iff,
    hv, true_and, streamFiber, womenFiber, Set.mem_prod, Set.mem_univ_pi,
    Function.uncurry]

/-- An invalid raw record list has an empty actual-history fiber. -/
theorem historyEvent_eq_empty {n : ℕ} (C : Protocol n) (h : List (Entry n))
    (hv : ¬ Valid C h) : historyEvent C h = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact hv ((transcript_eq_iff C z.1 (Function.uncurry z.2) h.length h).mp hz).2.1

/-- Exact revealed-history events are measurable on the concrete independent source space. -/
theorem measurableSet_historyEvent {n : ℕ} (C : Protocol n) (h : List (Entry n)) :
    MeasurableSet (historyEvent C h) := by
  classical
  by_cases hv : Valid C h
  · rw [historyEvent_eq_product C h hv]
    exact (measurableSet_streamFiber h).prod (measurableSet_womenFiber h)
  · rw [historyEvent_eq_empty C h hv]
    exact MeasurableSet.empty

/-- A first unconsumed coordinate keeps its original iid law after all men's consumed prefixes. -/
theorem streamFiber_next_coordinate_measure {n : ℕ} [NeZero n]
    (P : Fin n → Fin n → ℝ≥0) (h : List (Entry n)) (w m : Fin n) :
    (Measure.pi fun k ↦ FirstFresh.iidStream (RandomRanking.ofWeights (P k)))
      (streamFiber h ∩ {streams | streams m (rawCounter h m) = w}) =
      (RandomRanking.ofWeights (P m) w) *
        (Measure.pi fun k ↦ FirstFresh.iidStream (RandomRanking.ofWeights (P k)))
          (streamFiber h) := by
  let E (k : Fin n) := StreamPrefix.prefixEvent (drawOrder h k)
  let A : Set (ℕ → Fin n) := {x | x (rawCounter h m) = w}
  have hA : FirstFresh.iidStream (RandomRanking.ofWeights (P m)) (A ∩ E m) =
      RandomRanking.ofWeights (P m) w *
        FirstFresh.iidStream (RandomRanking.ofWeights (P m)) (E m) := by
    rw [Set.inter_comm]
    exact StreamPrefix.prefixEvent_next_measure (RandomRanking.ofWeights (P m))
      (drawOrder h m) w
  have hf := Ordinal.measure_pi_row_factor
    (fun k ↦ FirstFresh.iidStream (RandomRanking.ofWeights (P k))) E A m
    (RandomRanking.ofWeights (P m) w) hA
  have he : streamFiber h ∩ {streams | streams m (rawCounter h m) = w} =
      {streams | (∀ k, streams k ∈ E k) ∧ streams m ∈ A} := by
    ext streams
    simp only [streamFiber, E, A, Set.mem_inter_iff, Set.mem_univ_pi, Set.mem_ofPred_eq]
  rw [he]
  exact hf

/-- Given only the actual raw history, every man's first unconsumed coordinate retains its
categorical marginal, even if that man is not selected next. No positivity of P is needed. -/
theorem history_next_coordinate_measure {n : ℕ} [NeZero n]
    (P Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    (C : Protocol n) (h : List (Entry n)) (w m : Fin n) :
    rawInputLaw P Q {z | z ∈ historyEvent C h ∧ z.1 m (rawCounter h m) = w} =
      RandomRanking.ofWeights (P m) w * rawInputLaw P Q (historyEvent C h) := by
  classical
  have (m w : Fin n) : IsProbabilityMeasure
      (ProbabilityTheory.expMeasure (Q m w : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by exact_mod_cast hQ m w)
  by_cases hv : Valid C h
  · have he : {z : Sources n | z ∈ historyEvent C h ∧ z.1 m (rawCounter h m) = w} =
        (streamFiber h ∩ {streams | streams m (rawCounter h m) = w}) ×ˢ womenFiber h := by
      ext z
      simp only [historyEvent_eq_product C h hv, Set.mem_ofPred_eq, Set.mem_prod,
        Set.mem_inter_iff]
      tauto
    rw [he, historyEvent_eq_product C h hv, rawInputLaw, Measure.prod_prod,
      Measure.prod_prod, streamFiber_next_coordinate_measure, mul_assoc]
  · have he : {z : Sources n | z ∈ historyEvent C h ∧ z.1 m (rawCounter h m) = w} = ∅ := by
      simp only [historyEvent_eq_empty C h hv, Set.mem_empty_iff_false,
        false_and, Set.ofPred_false]
    rw [he, historyEvent_eq_empty C h hv, measure_empty, mul_zero]

/-- An actual selected next edge has the exact original categorical destination law after
only the revealed raw transcript, for arbitrary partial or suspended protocols. -/
theorem next_destination_measure {n : ℕ} [NeZero n]
    (P Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    (C : Protocol n) (h : List (Entry n)) (w m : Fin n)
    (hs : selected C h = some m) :
    rawInputLaw P Q {z | z ∈ historyEvent C h ∧ nextEdge C z.1 h = some (w, m)} =
      RandomRanking.ofWeights (P m) w * rawInputLaw P Q (historyEvent C h) := by
  have he : {z : Sources n | z ∈ historyEvent C h ∧ nextEdge C z.1 h = some (w, m)} =
      {z | z ∈ historyEvent C h ∧ z.1 m (rawCounter h m) = w} := by
    ext z
    simp only [nextEdge, hs, Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
  rw [he]
  exact history_next_coordinate_measure P Q hQ C h w m

/-- A woman's exact raw-history ordinal event has the published fresh acceptance factor.
All other women's events are independent product factors and no raw value is conditioned on. -/
theorem womenFiber_acceptance_measure {n : ℕ} (Q : Fin n → Fin n → ℝ≥0)
    (hQ : ∀ m w, 0 < Q m w) (h : List (Entry n)) (w m : Fin n)
    (hfresh : (w, m) ∉ seenEdges h) :
    (Measure.pi fun v ↦ Measure.pi fun k ↦ ProbabilityTheory.expMeasure (Q k v : ℝ))
      {x | x ∈ womenFiber h ∧
        Ordinal.accept (Function.uncurry x) (state h) (w, m) = true} =
      ENNReal.ofReal ((Q m w : ℝ) / ((Q m w : ℝ) +
        ∑ k : Ordinal.SeenMen (ordinary h) w, (Q k.val w : ℝ))) *
        (Measure.pi fun v ↦ Measure.pi fun k ↦ ProbabilityTheory.expMeasure (Q k v : ℝ))
          (womenFiber h) := by
  have (m w : Fin n) : IsProbabilityMeasure
      (ProbabilityTheory.expMeasure (Q m w : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by exact_mod_cast hQ m w)
  let E (v : Fin n) : Set (Fin n → ℝ) := {row | Ordinal.RowFiber (ordinary h) v row}
  let A : Set (Fin n → ℝ) :=
    {row | ∀ k : Ordinal.SeenMen (ordinary h) w, row m < row k.val}
  let q := ENNReal.ofReal ((Q m w : ℝ) / ((Q m w : ℝ) +
    ∑ k : Ordinal.SeenMen (ordinary h) w, (Q k.val w : ℝ)))
  have hA : (Measure.pi fun k ↦ ProbabilityTheory.expMeasure (Q k w : ℝ)) (A ∩ E w) =
      q * (Measure.pi fun k ↦ ProbabilityTheory.expMeasure (Q k w : ℝ)) (E w) :=
    Ordinal.exponential_row_acceptance_measure (fun k ↦ (Q k w : ℝ))
      (fun k ↦ by exact_mod_cast hQ k w) (ordinary h) w m hfresh
  have hf := Ordinal.measure_pi_row_factor
    (fun v ↦ Measure.pi fun k ↦ ProbabilityTheory.expMeasure (Q k v : ℝ)) E A w q hA
  have he : {x : Fin n → Fin n → ℝ | x ∈ womenFiber h ∧
        Ordinal.accept (Function.uncurry x) (state h) (w, m) = true} =
      {x | (∀ v, x v ∈ E v) ∧ x w ∈ A} := by
    ext x
    have ha (hx : x ∈ womenFiber h) :
        Ordinal.accept (Function.uncurry x) (state h) (w, m) = true ↔ x w ∈ A := by
      have hr : Ordinal.RowFiber (ordinary h) w (x w) := by
        have hh : ∀ v, Ordinal.RowFiber (ordinary h) v (x v) := by
          simpa only [womenFiber, Set.mem_univ_pi, Set.mem_ofPred_eq] using hx
        exact hh w
      exact Ordinal.accept_true_iff_all_seen (ordinary h) w m (Function.uncurry x) hr
    constructor
    · rintro ⟨hx, haccept⟩
      refine ⟨?_, (ha hx).mp haccept⟩
      simpa only [womenFiber, E, Set.mem_univ_pi] using hx
    · rintro ⟨hx, hwin⟩
      have hh : x ∈ womenFiber h := by
        simpa only [womenFiber, E, Set.mem_univ_pi] using hx
      exact ⟨hh, (ha hh).mpr hwin⟩
  rw [he]
  exact hf

/-- The exact raw next-edge event factors all stream information from every female row. -/
theorem history_next_eq_product {n : ℕ} (C : Protocol n) (h : List (Entry n))
    (q : Edge n) (hv : Valid C h) :
    {z : Sources n | z ∈ historyEvent C h ∧ nextEdge C z.1 h = some q} =
      (streamFiber h ∩ {streams | nextEdge C streams h = some q}) ×ˢ womenFiber h := by
  ext z
  simp only [historyEvent_eq_product C h hv, Set.mem_ofPred_eq, Set.mem_prod,
    Set.mem_inter_iff]
  tauto

/-- Fresh acceptance after only the actual raw transcript and next edge has the exact rate
ratio. This holds for any partial/suspended protocol, even for impossible history fibers. -/
theorem next_acceptance_measure {n : ℕ} [NeZero n]
    (P Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    (C : Protocol n) (h : List (Entry n)) (w m : Fin n)
    (hfresh : (w, m) ∉ seenEdges h) :
    rawInputLaw P Q {z | z ∈ historyEvent C h ∧ nextEdge C z.1 h = some (w, m) ∧
      Ordinal.accept (Function.uncurry z.2) (state h) (w, m) = true} =
      ENNReal.ofReal ((Q m w : ℝ) / ((Q m w : ℝ) +
        ∑ k : Ordinal.SeenMen (ordinary h) w, (Q k.val w : ℝ))) *
        rawInputLaw P Q {z | z ∈ historyEvent C h ∧ nextEdge C z.1 h = some (w, m)} := by
  classical
  have (m w : Fin n) : IsProbabilityMeasure
      (ProbabilityTheory.expMeasure (Q m w : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by exact_mod_cast hQ m w)
  by_cases hv : Valid C h
  · have heA : {z : Sources n | z ∈ historyEvent C h ∧ nextEdge C z.1 h = some (w, m) ∧
        Ordinal.accept (Function.uncurry z.2) (state h) (w, m) = true} =
        (streamFiber h ∩ {streams | nextEdge C streams h = some (w, m)}) ×ˢ
          {x | x ∈ womenFiber h ∧
            Ordinal.accept (Function.uncurry x) (state h) (w, m) = true} := by
      ext z
      simp only [historyEvent_eq_product C h hv, Set.mem_ofPred_eq, Set.mem_prod,
        Set.mem_inter_iff]
      tauto
    rw [heA, history_next_eq_product C h (w, m) hv, rawInputLaw, Measure.prod_prod,
      Measure.prod_prod, womenFiber_acceptance_measure Q hQ h w m hfresh]
    ac_rfl
  · simp only [historyEvent_eq_empty C h hv, Set.mem_empty_iff_false, false_and,
      Set.ofPred_false, measure_empty, mul_zero]

/-- One actual raw transcript extension fixes just its old history and next observation. -/
theorem inputTranscript_cons_iff {n : ℕ} (C : Protocol n) (z : Sources n)
    (h : List (Entry n)) (entry : Entry n) :
    inputTranscript C (h.length + 1) z = entry :: h ↔
      z ∈ historyEvent C h ∧ observation C z.1 (Function.uncurry z.2) h = entry := by
  change observation C z.1 (Function.uncurry z.2) (inputTranscript C h.length z) ::
      inputTranscript C h.length z = entry :: h ↔ _
  rw [List.cons.injEq]
  constructor
  · rintro ⟨hentry, htail⟩
    exact ⟨htail, by simpa only [htail] using hentry⟩
  · rintro ⟨htail, hentry⟩
    change inputTranscript C h.length z = h at htail
    exact ⟨by simpa only [htail] using hentry, htail⟩

/-- A fresh raw observation records exactly its edge and actual ordinal acceptance bit. -/
theorem observation_fresh_iff {n : ℕ} (C : Protocol n)
    (streams : Fin n → ℕ → Fin n) (female : Edge n → ℝ)
    (h : List (Entry n)) (q : Edge n) (a : Bool) (hfresh : q ∉ seenEdges h) :
    observation C streams female h = some (q, some a) ↔
      nextEdge C streams h = some q ∧ Ordinal.accept female (state h) q = a := by
  rw [observation_eq_iff]
  change (nextEdge C streams h = some q ∧ q ∉ seenEdges h ∧
      ∀ w, Ordinal.RowConstraint (state h) (some (q, a)) w (fun m ↦ female (w, m))) ↔ _
  simp only [hfresh, not_false_eq_true, true_and]
  rw [← Ordinal.accept_eq_iff_rows]

/-- A repeated raw edge is ignored deterministically and reveals no new female comparison. -/
theorem observation_repeat_iff {n : ℕ} (C : Protocol n)
    (streams : Fin n → ℕ → Fin n) (female : Edge n → ℝ)
    (h : List (Entry n)) (q : Edge n) (hseen : q ∈ seenEdges h) :
    observation C streams female h = some (q, none) ↔ nextEdge C streams h = some q := by
  rw [observation_eq_iff]
  change (nextEdge C streams h = some q ∧ q ∈ seenEdges h ∧
      ∀ w, Ordinal.RowConstraint (state h) none w (fun m ↦ female (w, m))) ↔ _
  simp only [hseen, Ordinal.RowConstraint, implies_true, and_true]

/-- The actual extended raw-history mass for a fresh accepted edge is the categorical
sample mass times its exact ordinal rate ratio times the previous history mass. -/
theorem extend_fresh_true_measure {n : ℕ} [NeZero n]
    (P Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    (C : Protocol n) (h : List (Entry n)) (w m : Fin n)
    (hs : selected C h = some m) (hfresh : (w, m) ∉ seenEdges h) :
    rawInputLaw P Q {z | inputTranscript C (h.length + 1) z = some ((w, m), some true) :: h} =
      ENNReal.ofReal ((Q m w : ℝ) / ((Q m w : ℝ) +
        ∑ k : Ordinal.SeenMen (ordinary h) w, (Q k.val w : ℝ))) *
      RandomRanking.ofWeights (P m) w * rawInputLaw P Q (historyEvent C h) := by
  have he : {z : Sources n |
      inputTranscript C (h.length + 1) z = some ((w, m), some true) :: h} =
      {z | z ∈ historyEvent C h ∧ nextEdge C z.1 h = some (w, m) ∧
        Ordinal.accept (Function.uncurry z.2) (state h) (w, m) = true} := by
    ext z
    exact (inputTranscript_cons_iff C z h _).trans
      (and_congr_right fun _ ↦ observation_fresh_iff C z.1 (Function.uncurry z.2) h _ _ hfresh)
  rw [he, next_acceptance_measure P Q hQ C h w m hfresh,
    next_destination_measure P Q hQ C h w m hs, mul_assoc]

/-- The actual extended raw-history mass for a repeated destination is just its categorical
sample mass times the past history mass; the repeat has the ignored `none` tag. -/
theorem extend_repeat_measure {n : ℕ} [NeZero n]
    (P Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    (C : Protocol n) (h : List (Entry n)) (w m : Fin n)
    (hs : selected C h = some m) (hseen : (w, m) ∈ seenEdges h) :
    rawInputLaw P Q {z | inputTranscript C (h.length + 1) z = some ((w, m), none) :: h} =
      RandomRanking.ofWeights (P m) w * rawInputLaw P Q (historyEvent C h) := by
  have he : {z : Sources n |
      inputTranscript C (h.length + 1) z = some ((w, m), none) :: h} =
      {z | z ∈ historyEvent C h ∧ nextEdge C z.1 h = some (w, m)} := by
    ext z
    exact (inputTranscript_cons_iff C z h _).trans
      (and_congr_right fun _ ↦ observation_repeat_iff C z.1 (Function.uncurry z.2) h _ hseen)
  rw [he]
  exact next_destination_measure P Q hQ C h w m hs

/-- The concrete independent raw input law is a probability measure for positive female rates. -/
theorem isProbabilityMeasure_rawInputLaw {n : ℕ} [NeZero n]
    (P Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) :
    IsProbabilityMeasure (rawInputLaw P Q) := by
  have (m w : Fin n) : IsProbabilityMeasure
      (ProbabilityTheory.expMeasure (Q m w : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by exact_mod_cast hQ m w)
  unfold rawInputLaw
  infer_instance

/-- Either fresh acceptance bit extends exactly the prior history and the next edge event. -/
theorem extend_fresh_event {n : ℕ} (C : Protocol n) (h : List (Entry n))
    (q : Edge n) (a : Bool) (hfresh : q ∉ seenEdges h) :
    {z : Sources n | inputTranscript C (h.length + 1) z = some (q, some a) :: h} =
      {z | z ∈ historyEvent C h ∧ nextEdge C z.1 h = some q ∧
        Ordinal.accept (Function.uncurry z.2) (state h) q = a} := by
  ext z
  exact (inputTranscript_cons_iff C z h _).trans
    (and_congr_right fun _ ↦ observation_fresh_iff C z.1 (Function.uncurry z.2) h q a hfresh)

/-- The exact complementary fresh rejection law on the actual raw-history filtration. -/
theorem extend_fresh_false_measure {n : ℕ} [NeZero n]
    (P Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    (C : Protocol n) (h : List (Entry n)) (w m : Fin n)
    (hs : selected C h = some m) (hfresh : (w, m) ∉ seenEdges h) :
    rawInputLaw P Q {z | inputTranscript C (h.length + 1) z = some ((w, m), some false) :: h} =
      (1 - ENNReal.ofReal ((Q m w : ℝ) / ((Q m w : ℝ) +
        ∑ k : Ordinal.SeenMen (ordinary h) w, (Q k.val w : ℝ)))) *
      RandomRanking.ofWeights (P m) w * rawInputLaw P Q (historyEvent C h) := by
  have : IsProbabilityMeasure (rawInputLaw P Q) := isProbabilityMeasure_rawInputLaw P Q hQ
  let B : Set (Sources n) := {z | z ∈ historyEvent C h ∧ nextEdge C z.1 h = some (w, m)}
  let T : Set (Sources n) := {z | z ∈ historyEvent C h ∧ nextEdge C z.1 h = some (w, m) ∧
    Ordinal.accept (Function.uncurry z.2) (state h) (w, m) = true}
  have hT : MeasurableSet T := by
    rw [show T = {z : Sources n | inputTranscript C (h.length + 1) z =
      some ((w, m), some true) :: h} from (extend_fresh_event C h (w, m) true hfresh).symm]
    exact measurableSet_historyEvent C (some ((w, m), some true) :: h)
  have hsub : T ⊆ B := fun _ hz ↦ ⟨hz.1, hz.2.1⟩
  have he : {z : Sources n |
      inputTranscript C (h.length + 1) z = some ((w, m), some false) :: h} = B \ T := by
    rw [extend_fresh_event C h (w, m) false hfresh]
    ext z
    simp only [B, T, Set.mem_ofPred_eq, Set.mem_sdiff]
    cases ha : Ordinal.accept (Function.uncurry z.2) (state h) (w, m) <;> simp
  rw [he, measure_sdiff hsub hT.nullMeasurableSet (measure_ne_top _ _)]
  dsimp only [B, T]
  rw [next_acceptance_measure P Q hQ C h w m hfresh]
  let q := ENNReal.ofReal ((Q m w : ℝ) / ((Q m w : ℝ) +
    ∑ k : Ordinal.SeenMen (ordinary h) w, (Q k.val w : ℝ)))
  change rawInputLaw P Q B - q * rawInputLaw P Q B =
    (1 - q) * RandomRanking.ofWeights (P m) w * rawInputLaw P Q (historyEvent C h)
  have hm : rawInputLaw P Q B - q * rawInputLaw P Q B = (1 - q) * rawInputLaw P Q B := by
    simpa only [one_mul] using (ENNReal.sub_mul (a := 1) (b := q)
      (c := rawInputLaw P Q B) (fun _ _ ↦ measure_ne_top _ _)).symm
  rw [hm]
  dsimp only [B]
  rw [next_destination_measure P Q hQ C h w m hs, mul_assoc]

/-- A protocol suspension records padding and leaves the actual raw history state unchanged. -/
theorem extend_pause_measure {n : ℕ} [NeZero n] (P Q : Fin n → Fin n → ℝ≥0)
    (C : Protocol n) (h : List (Entry n)) (hs : selected C h = none) :
    rawInputLaw P Q {z | inputTranscript C (h.length + 1) z = none :: h} =
      rawInputLaw P Q (historyEvent C h) := by
  congr 1
  ext z
  change inputTranscript C (h.length + 1) z = none :: h ↔ z ∈ historyEvent C h
  rw [inputTranscript_cons_iff]
  simp only [observation, nextEdge, hs, Option.map_none, and_true]

/-- Positive raw destination scores give their literal normalized-weight categorical law. -/
theorem next_destination_weight_measure {n : ℕ} [NeZero n]
    (P Q : Fin n → Fin n → ℝ≥0) (hP : ∀ m w, 0 < P m w) (hQ : ∀ m w, 0 < Q m w)
    (C : Protocol n) (h : List (Entry n)) (w m : Fin n) (hs : selected C h = some m) :
    rawInputLaw P Q {z | z ∈ historyEvent C h ∧ nextEdge C z.1 h = some (w, m)} =
      (P m w / (∑ v, P m v) : ℝ≥0) * rawInputLaw P Q (historyEvent C h) := by
  have ht : (∑ v, P m v) ≠ 0 := ne_of_gt
    (Finset.sum_pos (fun v _ ↦ hP m v) Finset.univ_nonempty)
  rw [next_destination_measure P Q hQ C h w m hs,
    RandomRanking.ofWeights_apply (P m) ht, ← ENNReal.coe_div ht]

/-- For the PR's tiered scores, each actual raw destination has the common α-weighted law,
regardless of the selected eligible man, with only the raw ordinal history revealed. -/
theorem tiered_next_destination_measure {n I J : ℕ} [NeZero n]
    (womanTier : Fin n → Fin I) (manTier : Fin n → Fin J)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (C : Protocol n) (h : List (Entry n)) (w m : Fin n) (hs : selected C h = some m) :
    rawInputLaw (fun _ v ↦ α (womanTier v)) (fun k _ ↦ β (manTier k))
      {z | z ∈ historyEvent C h ∧ nextEdge C z.1 h = some (w, m)} =
      (α (womanTier w) / (∑ v, α (womanTier v)) : ℝ≥0) *
        rawInputLaw (fun _ v ↦ α (womanTier v)) (fun k _ ↦ β (manTier k)) (historyEvent C h) :=
  next_destination_weight_measure _ _ (fun _ v ↦ hα (womanTier v))
    (fun k _ ↦ hβ (manTier k)) C h w m hs

/-- The PR tiered raw-source process has the exact fresh accepted-transition kernel. -/
theorem tiered_extend_fresh_true_measure {n I J : ℕ} [NeZero n]
    (womanTier : Fin n → Fin I) (manTier : Fin n → Fin J)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (C : Protocol n) (h : List (Entry n)) (w m : Fin n)
    (hs : selected C h = some m) (hfresh : (w, m) ∉ seenEdges h) :
    rawInputLaw (fun _ v ↦ α (womanTier v)) (fun k _ ↦ β (manTier k))
      {z | inputTranscript C (h.length + 1) z = some ((w, m), some true) :: h} =
      ENNReal.ofReal ((β (manTier m) : ℝ) / ((β (manTier m) : ℝ) +
        ∑ k : Ordinal.SeenMen (ordinary h) w, (β (manTier k.val) : ℝ))) *
      (α (womanTier w) / (∑ v, α (womanTier v)) : ℝ≥0) *
        rawInputLaw (fun _ v ↦ α (womanTier v)) (fun k _ ↦ β (manTier k)) (historyEvent C h) := by
  have ht : (∑ v, α (womanTier v)) ≠ 0 := ne_of_gt
    (Finset.sum_pos (fun v _ ↦ hα (womanTier v)) Finset.univ_nonempty)
  rw [extend_fresh_true_measure _ _ (fun k _ ↦ hβ (manTier k)) C h w m hs hfresh,
    RandomRanking.ofWeights_apply _ ht, ← ENNReal.coe_div ht]

end Ashlagi.Raw
