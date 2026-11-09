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

public import TieredMatching.TranscriptKernel
public import TieredMatching.StreamPrefix

/-! # Actual raw proposal transcripts with repeated IID destinations

Each raw attempt reads only the selected man's next unused IID coordinate. Repeated edges
leave the ordinal state unchanged, while fresh edges expose the woman's actual comparison.
-/

@[expose] public section

namespace TieredMatching.Raw

open StableMarriage MeasureTheory
open Arrival

/-- Padding, an ignored repeated edge, or a fresh edge with its ordinal acceptance bit. -/
abbrev Entry (n : ℕ) := Option (Edge n × Option Bool)

/-- Erase repeats and pauses to ordinal padding while preserving the raw time index. -/
def ordinaryEntry {n : ℕ} (entry : Entry n) : Ordinal.Entry n :=
  entry.bind fun e ↦ e.2.map fun accepted ↦ (e.1, accepted)

/-- The ordinary fresh-proposal replay, with one ordinal entry per raw time step. -/
def ordinary {n : ℕ} (h : List (Entry n)) : List (Ordinal.Entry n) := h.map ordinaryEntry

/-- The visible discrete state after ignoring repeated raw proposals. -/
def state {n : ℕ} (h : List (Entry n)) : ProposalState n := Ordinal.recordState (ordinary h)

/-- Edges already exposed by genuine fresh proposals. -/
def seenEdges {n : ℕ} (h : List (Entry n)) : Finset (Edge n) := Ordinal.seenEdges (ordinary h)

/-- Every destination drawn by one man, including repeats, in chronological order. -/
def drawOrder {n : ℕ} : List (Entry n) → Fin n → List (Fin n)
  | [], _ => []
  | none :: h, m => drawOrder h m
  | some (q, _) :: h, m => if q.2 = m then drawOrder h m ++ [q.1] else drawOrder h m

/-- The number of IID coordinates already consumed from the selected man's raw stream. -/
def rawCounter {n : ℕ} (h : List (Entry n)) (m : Fin n) : ℕ := (drawOrder h m).length

/-- A raw protocol can inspect only the finite revealed history and can suspend the run. -/
abbrev Protocol (n : ℕ) := List (Entry n) → Option (Fin n)

/-- Sanitize a protocol's selection using only visible freedom and fresh-list exhaustion. -/
def selected {n : ℕ} (C : Protocol n) (h : List (Entry n)) : Option (Fin n) :=
  (C h).filter fun m ↦ (state h).next m < n ∧ ∀ w, (state h).held w ≠ some m

/-- An actual selection is a free man who still has an untried distinct destination. -/
theorem selected_some_spec {n : ℕ} (C : Protocol n) (h : List (Entry n)) (m : Fin n)
    (hm : selected C h = some m) :
    (state h).next m < n ∧ ∀ w, (state h).held w ≠ some m := by
  simpa using (Option.filter_eq_some_iff.mp hm).2

/-- The raw edge reads the next unused stream coordinate without inspecting any future rank. -/
def nextEdge {n : ℕ} (C : Protocol n) (streams : Fin n → ℕ → Fin n)
    (h : List (Entry n)) : Option (Edge n) :=
  (selected C h).map fun m ↦ (streams m (rawCounter h m), m)

/-- Classify the actual draw as an ignored repeat or a fresh ordinal comparison. -/
noncomputable def observation {n : ℕ} (C : Protocol n) (streams : Fin n → ℕ → Fin n)
    (female : Edge n → ℝ) (h : List (Entry n)) : Entry n :=
  (nextEdge C streams h).map fun q ↦ (q,
    if q ∈ seenEdges h then none else some (Ordinal.accept female (state h) q))

/-- The recursively generated actual raw transcript, newest record first. -/
noncomputable def transcript {n : ℕ} (C : Protocol n) (streams : Fin n → ℕ → Fin n)
    (female : Edge n → ℝ) : ℕ → List (Entry n)
  | 0 => []
  | t + 1 => let h := transcript C streams female t; observation C streams female h :: h

/-- A record's tag agrees with whether its edge was already seen; it reveals no raw value. -/
def TagValid {n : ℕ} (h : List (Entry n)) : Entry n → Prop
  | none => True
  | some (q, none) => q ∈ seenEdges h
  | some (q, some _) => q ∉ seenEdges h

/-- Preference-independent raw scheduling and repeat/fresh-tag legality. -/
def Valid {n : ℕ} (C : Protocol n) : List (Entry n) → Prop
  | [] => True
  | entry :: h => Valid C h ∧ selected C h = entry.map (fun e ↦ e.1.2) ∧ TagValid h entry

/-- The one raw stream value revealed by a record. Pauses reveal no coordinate. -/
def DrawConstraint {n : ℕ} (h : List (Entry n)) (entry : Entry n)
    (streams : Fin n → ℕ → Fin n) : Prop :=
  match entry with
  | none => True
  | some (q, _) => streams q.2 (rawCounter h q.2) = q.1

/-- Every raw observation agrees with the exact fixed history's stream coordinates. -/
def Draws {n : ℕ} (streams : Fin n → ℕ → Fin n) : List (Entry n) → Prop
  | [] => True
  | entry :: h => Draws streams h ∧ DrawConstraint h entry streams

/-- All recorded raw observations actually occur in their replayed predecessor states. -/
def Observes {n : ℕ} (C : Protocol n) (streams : Fin n → ℕ → Fin n)
    (female : Edge n → ℝ) : List (Entry n) → Prop
  | [] => True
  | entry :: h => Observes C streams female h ∧ observation C streams female h = entry

/-- The selected-man projection of an actual raw draw is exactly the sanitized protocol choice. -/
theorem nextEdge_map_man {n : ℕ} (C : Protocol n) (streams : Fin n → ℕ → Fin n)
    (h : List (Entry n)) : (nextEdge C streams h).map Prod.snd = selected C h := by
  cases hm : selected C h <;> simp [nextEdge, hm]

/-- A fixed raw edge reveals only the selected man's next unused categorical draw. -/
theorem nextEdge_eq_iff {n : ℕ} (C : Protocol n) (streams : Fin n → ℕ → Fin n)
    (h : List (Entry n)) (entry : Entry n) :
    nextEdge C streams h = entry.map Prod.fst ↔
      selected C h = entry.map (fun e ↦ e.1.2) ∧ DrawConstraint h entry streams := by
  cases entry with
  | none => simp [nextEdge, DrawConstraint]
  | some entry =>
    rcases entry with ⟨⟨w, m⟩, tag⟩
    simp only [nextEdge, Option.map_some, Option.map_eq_some_iff, Prod.mk.injEq,
      DrawConstraint]
    aesop

/-- An observation exposes one raw draw and, only if fresh, one ordinal comparison. -/
theorem observation_eq_iff {n : ℕ} (C : Protocol n) (streams : Fin n → ℕ → Fin n)
    (female : Edge n → ℝ) (h : List (Entry n)) (entry : Entry n) :
    observation C streams female h = entry ↔
      nextEdge C streams h = entry.map Prod.fst ∧ TagValid h entry ∧
      ∀ w, Ordinal.RowConstraint (state h) (ordinaryEntry entry) w (fun m ↦ female (w, m)) := by
  cases entry with
  | none => simp [observation, TagValid, ordinaryEntry, Ordinal.RowConstraint]
  | some entry =>
    rcases entry with ⟨q, tag⟩
    have hm : observation C streams female h = some (q, tag) ↔
        nextEdge C streams h = some q ∧
          (if q ∈ seenEdges h then none else some (Ordinal.accept female (state h) q)) = tag := by
      simp only [observation, Option.map_eq_some_iff, Prod.mk.injEq]
      aesop
    rw [hm]
    by_cases hseen : q ∈ seenEdges h
    · cases tag <;> simp [hseen, TagValid, ordinaryEntry, Ordinal.RowConstraint]
    · cases tag with
      | none => simp [hseen, TagValid]
      | some accepted =>
        simp only [hseen, ↓reduceIte, Option.some.injEq, Option.map_some, TagValid,
          not_false_eq_true, true_and, ordinaryEntry, Option.bind_some]
        rw [Ordinal.accept_eq_iff_rows]

/-- Exact raw observation fibers factor into visible legality, consumed draws, and ordinal rows. -/
theorem observes_iff_valid_draws_rows {n : ℕ} (C : Protocol n)
    (streams : Fin n → ℕ → Fin n) (female : Edge n → ℝ) (h : List (Entry n)) :
    Observes C streams female h ↔ Valid C h ∧ Draws streams h ∧
      ∀ w, Ordinal.RowFiber (ordinary h) w (fun m ↦ female (w, m)) := by
  induction h with
  | nil => simp [Observes, Valid, Draws, ordinary, Ordinal.RowFiber]
  | cons entry h ih =>
    simp only [Observes, Valid, Draws, ih, observation_eq_iff, nextEdge_eq_iff,
      ordinary, List.map_cons, Ordinal.RowFiber, forall_and, state]
    tauto

/-- There is exactly one raw record, including ignored repeats and pauses, per time step. -/
theorem transcript_length {n : ℕ} (C : Protocol n) (streams : Fin n → ℕ → Fin n)
    (female : Edge n → ℝ) (t : ℕ) : (transcript C streams female t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [transcript, List.length_cons] using congrArg Nat.succ ih

/-- Recorded observations characterize the actual generated raw transcript. -/
theorem observes_iff_transcript {n : ℕ} (C : Protocol n) (streams : Fin n → ℕ → Fin n)
    (female : Edge n → ℝ) (h : List (Entry n)) :
    Observes C streams female h ↔ transcript C streams female h.length = h := by
  induction h with
  | nil => simp [Observes, transcript]
  | cons entry h ih =>
    change (Observes C streams female h ∧ observation C streams female h = entry) ↔
      observation C streams female (transcript C streams female h.length) ::
        transcript C streams female h.length = entry :: h
    constructor
    · rintro ⟨hprev, hentry⟩
      rw [ih.mp hprev, hentry]
    · intro heq
      have htail := (List.cons.inj heq).2
      have hentry := (List.cons.inj heq).1
      rw [htail] at hentry
      exact ⟨ih.mpr htail, hentry⟩

/-- Every fixed-time raw transcript has exactly the stated stream-coordinate and ordinal fibers. -/
theorem transcript_eq_iff_constraints {n : ℕ} (C : Protocol n)
    (streams : Fin n → ℕ → Fin n) (female : Edge n → ℝ) (t : ℕ) (h : List (Entry n)) :
    transcript C streams female t = h ↔ h.length = t ∧ Valid C h ∧ Draws streams h ∧
      ∀ w, Ordinal.RowFiber (ordinary h) w (fun m ↦ female (w, m)) := by
  constructor
  · intro heq
    have hlen : h.length = t := heq ▸ transcript_length C streams female t
    refine ⟨hlen, ?_⟩
    exact (observes_iff_valid_draws_rows C streams female h).mp
      ((observes_iff_transcript C streams female h).mpr (by simpa only [hlen] using heq))
  · rintro ⟨hlen, hvalid, hdraws, hrows⟩
    have heq := (observes_iff_transcript C streams female h).mp
      ((observes_iff_valid_draws_rows C streams female h).mpr ⟨hvalid, hdraws, hrows⟩)
    simpa only [hlen] using heq

/-- The ordinary replay preserves the raw clock by replacing repeats with ordinal padding. -/
theorem ordinary_length {n : ℕ} (h : List (Entry n)) : (ordinary h).length = h.length := by
  simp [ordinary]

/-- The next source coordinate is exactly the first index beyond the consumed raw prefix. -/
theorem nextEdge_some_spec {n : ℕ} (C : Protocol n) (streams : Fin n → ℕ → Fin n)
    (h : List (Entry n)) (q : Edge n) (hq : nextEdge C streams h = some q) :
    selected C h = some q.2 ∧ streams q.2 (drawOrder h q.2).length = q.1 := by
  exact (nextEdge_eq_iff C streams h (some (q, none))).mp hq

/-- Each raw draw consumes one new stream index even when its destination repeats. -/
theorem rawCounter_record {n : ℕ} (h : List (Entry n)) (q : Edge n) (tag : Option Bool)
    (m : Fin n) :
    rawCounter (some (q, tag) :: h) m = rawCounter h m + if q.2 = m then 1 else 0 := by
  by_cases hm : q.2 = m <;> simp [rawCounter, drawOrder, hm]

/-- An ignored repeat leaves the ordinary proposal state unchanged. -/
theorem state_repeat {n : ℕ} (h : List (Entry n)) (q : Edge n) :
    state (some (q, none) :: h) = state h := rfl

/-- Recording any raw draw fixes the next stream value and extends exactly one man's prefix. -/
theorem prefixes_record_iff {n : ℕ} (streams : Fin n → ℕ → Fin n)
    (h : List (Entry n)) (q : Edge n) (tag : Option Bool) :
    (∀ m, streams m ∈ StreamPrefix.prefixEvent (drawOrder (some (q, tag) :: h) m)) ↔
      (∀ m, streams m ∈ StreamPrefix.prefixEvent (drawOrder h m)) ∧
        streams q.2 (rawCounter h q.2) = q.1 := by
  constructor
  · intro hp
    have hq := hp q.2
    simp only [drawOrder, ite_true, StreamPrefix.prefixEvent_append,
      Set.mem_inter_iff, Set.mem_ofPred_eq] at hq
    refine ⟨?_, hq.2⟩
    intro m
    by_cases hm : q.2 = m
    · subst m
      exact hq.1
    · simpa only [drawOrder, ite_eq_right hm] using hp m
  · rintro ⟨hp, hq⟩ m
    by_cases hm : q.2 = m
    · subst m
      simpa only [drawOrder, ite_true, StreamPrefix.prefixEvent_append,
        Set.mem_inter_iff, Set.mem_ofPred_eq, rawCounter] using And.intro (hp q.2) hq
    · simpa only [drawOrder, ite_eq_right hm] using hp m

/-- All consumed raw coordinates are exactly the fixed ordered prefix of each man's IID stream. -/
theorem draws_iff_prefixes {n : ℕ} (streams : Fin n → ℕ → Fin n) (h : List (Entry n)) :
    Draws streams h ↔ ∀ m, streams m ∈ StreamPrefix.prefixEvent (drawOrder h m) := by
  induction h with
  | nil => simp [Draws, drawOrder, StreamPrefix.prefixEvent]
  | cons entry h ih =>
    cases entry with
    | none => simpa only [Draws, DrawConstraint, and_true, drawOrder] using ih
    | some entry =>
      rcases entry with ⟨q, tag⟩
      rw [Draws, ih, prefixes_record_iff]
      rfl

/-- Exact actual raw transcript fibers separate visible legality, IID stream prefixes, and
woman-specific ordinal row events. No complete preference ranking is conditioned on.
-/
theorem transcript_eq_iff {n : ℕ} (C : Protocol n)
    (streams : Fin n → ℕ → Fin n) (female : Edge n → ℝ) (t : ℕ) (h : List (Entry n)) :
    transcript C streams female t = h ↔ h.length = t ∧ Valid C h ∧
      (∀ m, streams m ∈ StreamPrefix.prefixEvent (drawOrder h m)) ∧
      ∀ w, Ordinal.RowFiber (ordinary h) w (fun m ↦ female (w, m)) := by
  rw [transcript_eq_iff_constraints, draws_iff_prefixes]

/-- Every fixed actual raw transcript fiber is measurable in the full independent source array. -/
theorem measurableSet_transcript_fiber {n : ℕ} (C : Protocol n) (t : ℕ)
    (h : List (Entry n)) :
    MeasurableSet {z : (Fin n → ℕ → Fin n) × (Edge n → ℝ) |
      transcript C z.1 z.2 t = h} := by
  have heq : {z : (Fin n → ℕ → Fin n) × (Edge n → ℝ) | transcript C z.1 z.2 t = h} =
      {z | (h.length = t ∧ Valid C h) ∧
        (∀ m, z.1 m ∈ StreamPrefix.prefixEvent (drawOrder h m)) ∧
        ∀ w, Ordinal.RowFiber (ordinary h) w (fun m ↦ z.2 (w, m))} := by
    ext z
    change (transcript C z.1 z.2 t = h) ↔
      ((h.length = t ∧ Valid C h) ∧
        (∀ m, z.1 m ∈ StreamPrefix.prefixEvent (drawOrder h m)) ∧
        ∀ w, Ordinal.RowFiber (ordinary h) w (fun m ↦ z.2 (w, m)))
    simpa only [and_assoc] using transcript_eq_iff C z.1 z.2 t h
  rw [heq]
  by_cases hgood : h.length = t ∧ Valid C h
  · simp only [hgood, true_and]
    apply MeasurableSet.inter
    · change MeasurableSet {z : (Fin n → ℕ → Fin n) × (Edge n → ℝ) |
        ∀ m, z.1 m ∈ StreamPrefix.prefixEvent (drawOrder h m)}
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter fun m ↦ (StreamPrefix.measurableSet_prefixEvent
        (drawOrder h m)).preimage ((measurable_pi_apply m).comp measurable_fst)
    · change MeasurableSet {z : (Fin n → ℕ → Fin n) × (Edge n → ℝ) |
        ∀ w, Ordinal.RowFiber (ordinary h) w (fun m ↦ z.2 (w, m))}
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter fun w ↦ (Ordinal.measurableSet_rowFiber (ordinary h) w).preimage
        (Measurable.of_eval (fun m ↦ (measurable_pi_apply (w, m)).comp measurable_snd))
  · simp [hgood]

/-- Every edge named by any raw draw, including repeats. -/
def allEdges {n : ℕ} : List (Entry n) → Finset (Edge n)
  | [] => ∅
  | none :: h => allEdges h
  | some (q, _) :: h => insert q (allEdges h)

/-- Valid repeat tags make raw and ordinary seen-edge sets exactly equal. -/
theorem seenEdges_eq_allEdges {n : ℕ} (C : Protocol n) (h : List (Entry n))
    (hv : Valid C h) : seenEdges h = allEdges h := by
  induction h with
  | nil => rfl
  | cons entry h ih =>
    have hprev := ih hv.1
    cases entry with
    | none => exact hprev
    | some entry =>
      rcases entry with ⟨q, tag⟩
      cases tag with
      | none =>
        have hmem : q ∈ seenEdges h := hv.2.2
        change seenEdges h = insert q (allEdges h)
        rw [← hprev, Finset.insert_eq_of_mem hmem]
      | some accepted =>
        change insert q (seenEdges h) = insert q (allEdges h)
        rw [hprev]

/-- Membership in one man's raw destination list is exactly membership in the raw edge set. -/
theorem mem_drawOrder_iff_allEdges {n : ℕ} (h : List (Entry n)) (w m : Fin n) :
    w ∈ drawOrder h m ↔ (w, m) ∈ allEdges h := by
  induction h with
  | nil => simp [drawOrder, allEdges]
  | cons entry h ih =>
    cases entry with
    | none => exact ih
    | some entry =>
      rcases entry with ⟨⟨v, k⟩, tag⟩
      by_cases hk : k = m
      · subst k
        simp [drawOrder, allEdges, ih, or_comm]
      · simp [drawOrder, allEdges, hk, Ne.symm hk, ih]

/-- Deduplicating raw destinations gives exactly the ordinary fresh proposal set for each man. -/
theorem drawOrder_toFinset_eq_ordinary {n : ℕ} (C : Protocol n) (h : List (Entry n))
    (hv : Valid C h) (m : Fin n) :
    (drawOrder h m).toFinset = (Ordinal.manOrder (ordinary h) m).toFinset := by
  ext w
  simp only [List.mem_toFinset, mem_drawOrder_iff_allEdges,
    Ordinal.mem_manOrder_iff_seenEdges]
  rw [← seenEdges_eq_allEdges C h hv]
  rfl

/-- Every fresh ordinary proposal appears only once in a valid raw history. -/
theorem nodup_ordinary_manOrder {n : ℕ} (C : Protocol n) (h : List (Entry n))
    (hv : Valid C h) (m : Fin n) : (Ordinal.manOrder (ordinary h) m).Nodup := by
  induction h with
  | nil => simp [ordinary, Ordinal.manOrder]
  | cons entry h ih =>
    have hp := ih hv.1
    cases entry with
    | none => exact hp
    | some entry =>
      rcases entry with ⟨q, tag⟩
      cases tag with
      | none => exact hp
      | some accepted =>
        have hfresh : q ∉ seenEdges h := hv.2.2
        change (if q.2 = m then Ordinal.manOrder (ordinary h) m ++ [q.1]
          else Ordinal.manOrder (ordinary h) m).Nodup
        by_cases hm : q.2 = m
        · rw [ite_eq_left hm]
          have hnot : q.1 ∉ Ordinal.manOrder (ordinary h) m := by
            intro hmem
            have he := (Ordinal.mem_manOrder_iff_seenEdges (ordinary h) q.1 m).mp hmem
            apply hfresh
            simpa only [seenEdges, ← hm, Prod.mk.eta] using he
          apply List.nodup_append_comm.mpr
          simpa only [List.singleton_append] using List.nodup_cons.mpr ⟨hnot, hp⟩
        · simpa only [ite_eq_right hm] using hp

/-- The visible ordinary proposal counter is exactly the number of distinct raw destinations. -/
theorem ordinary_count_eq_distinct_raw {n : ℕ} (C : Protocol n) (h : List (Entry n))
    (hv : Valid C h) (m : Fin n) :
    (state h).next m = (drawOrder h m).toFinset.card := by
  calc
    (state h).next m = (Ordinal.manOrder (ordinary h) m).length :=
      (Ordinal.length_manOrder (ordinary h) m).symm
    _ = (Ordinal.manOrder (ordinary h) m).toFinset.card :=
      (List.toFinset_card_of_nodup (nodup_ordinary_manOrder C h hv m)).symm
    _ = (drawOrder h m).toFinset.card :=
      congrArg Finset.card (drawOrder_toFinset_eq_ordinary C h hv m).symm

/-- Every generated raw transcript satisfies its exact visible scheduling and tag legality. -/
theorem valid_transcript {n : ℕ} (C : Protocol n) (streams : Fin n → ℕ → Fin n)
    (female : Edge n → ℝ) (t : ℕ) : Valid C (transcript C streams female t) := by
  exact ((transcript_eq_iff_constraints C streams female t _).mp rfl).2.1

/-- The distinct-raw-destination counter identity holds along the actual generated process. -/
theorem transcript_count_eq_distinct_raw {n : ℕ} (C : Protocol n)
    (streams : Fin n → ℕ → Fin n) (female : Edge n → ℝ) (t : ℕ) (m : Fin n) :
    (state (transcript C streams female t)).next m =
      (drawOrder (transcript C streams female t) m).toFinset.card :=
  ordinary_count_eq_distinct_raw C _ (valid_transcript C streams female t) m

/-- The whole fixed-time actual transcript is measurable into the discrete history space. -/
theorem measurable_transcript {n : ℕ} (C : Protocol n) (t : ℕ) :
    @Measurable ((Fin n → ℕ → Fin n) × (Edge n → ℝ)) (List (Entry n)) inferInstance ⊤
      (fun z ↦ transcript C z.1 z.2 t) := by
  let : MeasurableSpace (List (Entry n)) := ⊤
  apply measurable_to_countable
  intro z
  exact measurableSet_transcript_fiber C t (transcript C z.1 z.2 t)

/-- Raw transcript fibers use only consumed male prefixes and seen female coordinates. -/
theorem transcript_eq_iff_seenRows {n : ℕ} (C : Protocol n)
    (streams : Fin n → ℕ → Fin n) (female : Edge n → ℝ) (t : ℕ) (h : List (Entry n)) :
    transcript C streams female t = h ↔ h.length = t ∧ Valid C h ∧
      (∀ m, streams m ∈ StreamPrefix.prefixEvent (drawOrder h m)) ∧
      ∀ w, (fun m : Ordinal.SeenMen (ordinary h) w ↦ female (w, m.val)) ∈
        Ordinal.seenRowEvent (ordinary h) w := by
  rw [transcript_eq_iff]
  constructor
  · rintro ⟨hlen, hv, hp, hf⟩
    exact ⟨hlen, hv, hp, fun w ↦
      (Ordinal.rowFiber_iff_seenRowEvent (ordinary h) w _).mp (hf w)⟩
  · rintro ⟨hlen, hv, hp, hf⟩
    exact ⟨hlen, hv, hp, fun w ↦
      (Ordinal.rowFiber_iff_seenRowEvent (ordinary h) w _).mpr (hf w)⟩

end TieredMatching.Raw
