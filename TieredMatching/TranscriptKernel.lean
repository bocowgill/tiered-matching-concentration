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

public import TieredMatching.OrdinalLaw
public import TieredMatching.RankingPrefix
public import TieredMatching.SourcePremise

/-! # The exact destination law given an ordinal DA transcript

Transcript validity factors into a preference-independent schedule condition and a prefix
condition on each man's strict preference list. The still hidden preference suffixes therefore
retain the PR's weighted sampling-without-replacement law.
-/

@[expose] public section

namespace TieredMatching.Ordinal

open StableMarriage MeasureTheory
open Arrival
open scoped NNReal ENNReal

/-- The PR scheduler's selected man depends only on the replayed discrete state. -/
def scheduledMan {n : ℕ} (s : ProposalState n) : Option (Fin n) :=
  (List.finRange n).find? (fun m ↦ s.next m < n ∧ ∀ w, s.held w ≠ some m)

/-- Scheduling legality of a recorded transcript, without inspecting a preference ranking. -/
def ScheduleValid {n : ℕ} : List (Entry n) → Prop
  | [] => True
  | entry :: h => ScheduleValid h ∧
      scheduledMan (recordState h) = entry.map (fun e ↦ e.1.2)

/-- One man's observed destinations in chronological order, hiding every future destination. -/
def manOrder {n : ℕ} : List (Entry n) → Fin n → List (Fin n)
  | [], _ => []
  | none :: h, m => manOrder h m
  | some (q, _) :: h, m =>
      if q.2 = m then manOrder h m ++ [q.1] else manOrder h m

/-- The number of recorded destinations is exactly the PR counter, even for malformed records. -/
theorem length_manOrder {n : ℕ} (h : List (Entry n)) (m : Fin n) :
    (manOrder h m).length = (recordState h).next m := by
  induction h with
  | nil => rfl
  | cons entry h ih =>
    cases entry with
    | none => exact ih
    | some e =>
      rcases e with ⟨q, a⟩
      by_cases hm : q.2 = m
      · subst m
        cases a <;> simp [manOrder, recordState, recordStep, ih]
      · cases a <;> simp [manOrder, recordState, recordStep, hm, Ne.symm hm, ih]

/-- The selected proposer's remaining list is nonempty, and he is free. -/
theorem scheduledMan_some_spec {n : ℕ} (s : ProposalState n) (m : Fin n)
    (hs : scheduledMan s = some m) : s.next m < n ∧ ∀ w, s.held w ≠ some m := by
  simpa using List.find?_some hs

/-- The edge rule's projection onto the proposer is exactly the preference-independent scheduler. -/
theorem nextEdge_map_man {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (s : ProposalState n) : (nextEdge P s).map Prod.snd = scheduledMan s := by
  cases hs : scheduledMan s with
  | none =>
    have hf : (List.finRange n).find?
        (fun m ↦ s.next m < n ∧ ∀ w, s.held w ≠ some m) = none := hs
    simp only [nextEdge, hf, Option.map_none]
  | some m =>
    have hm := scheduledMan_some_spec s m hs
    have hf : (List.finRange n).find?
        (fun m ↦ s.next m < n ∧ ∀ w, s.held w ≠ some m) = some m := hs
    simp only [nextEdge, hf, dite_eq_left hm.1, Option.map_some]

/-- Appending a candidate to a prefix fixes exactly the next list entry. -/
theorem prefix_append_singleton_iff {α : Type*} (L R : List α) (q : α) :
    (L ++ [q]).IsPrefix R ↔ L.IsPrefix R ∧ R[L.length]? = some q := by
  induction L generalizing R with
  | nil => cases R <;> simp [eq_comm]
  | cons a L ih =>
    cases R with
    | nil => simp
    | cons b R =>
      simp only [List.cons_append, List.cons_prefix_cons, ih, List.length_cons,
        List.getElem?_cons_succ]
      tauto

/-- A legal next destination extends exactly one man's exposed list prefix. -/
theorem prefixes_record_iff {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (h : List (Entry n)) (w m : Fin n) (a : Bool)
    (hs : scheduledMan (recordState h) = some m) :
    (∀ k, (manOrder (some ((w, m), a) :: h) k).IsPrefix (List.ofFn (P k).symm)) ↔
      (∀ k, (manOrder h k).IsPrefix (List.ofFn (P k).symm)) ∧
        nextEdge P (recordState h) = some (w, m) := by
  classical
  have hn := (scheduledMan_some_spec (recordState h) m hs).1
  have hval : (List.ofFn (P m).symm)[(manOrder h m).length]? =
      some ((P m).symm ⟨(recordState h).next m, hn⟩) := by
    simp [length_manOrder, hn]
  have hedge : nextEdge P (recordState h) = some (w, m) ↔
      (P m).symm ⟨(recordState h).next m, hn⟩ = w := by
    have hf : (List.finRange n).find?
        (fun m ↦ (recordState h).next m < n ∧ ∀ w, (recordState h).held w ≠ some m) =
          some m := hs
    simp only [nextEdge, hf, dite_eq_left hn, Option.some.injEq, Prod.mk.injEq, and_true]
  rw [hedge]
  constructor
  · intro hall
    have hm := hall m
    simp only [manOrder, ite_true, prefix_append_singleton_iff, hval,
      Option.some.injEq] at hm
    refine ⟨fun k ↦ ?_, hm.2⟩
    by_cases hk : k = m
    · simpa only [hk] using hm.1
    · simpa only [manOrder, ite_eq_right (Ne.symm hk)] using hall k
  · rintro ⟨hall, hnext⟩ k
    by_cases hk : k = m
    · subst k
      simp only [manOrder, ite_true, prefix_append_singleton_iff, hval,
        Option.some.injEq]
      exact ⟨hall m, hnext⟩
    · simpa only [manOrder, ite_eq_right (Ne.symm hk)] using hall k

/-- Exact deterministic factorization: the PR transcript constrains only scheduler legality
and the chronological exposed prefix of each man's ranking. It never reveals hidden suffixes. -/
theorem valid_iff_schedule_prefixes {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (h : List (Entry n)) :
    Valid P h ↔ ScheduleValid h ∧
      ∀ m, (manOrder h m).IsPrefix (List.ofFn (P m).symm) := by
  induction h with
  | nil => simp [Valid, ScheduleValid, manOrder]
  | cons entry h ih =>
    cases entry with
    | none =>
      have hedge : nextEdge P (recordState h) = none ↔
          scheduledMan (recordState h) = none := by
        constructor
        · intro hn
          simpa only [hn, Option.map_none] using (nextEdge_map_man P (recordState h)).symm
        · intro hn
          have hf : (List.finRange n).find?
              (fun m ↦ (recordState h).next m < n ∧
                ∀ w, (recordState h).held w ≠ some m) = none := hn
          simp only [nextEdge, hf]
      simp only [Valid, ScheduleValid, manOrder, Option.map_none, ih, hedge]
      tauto
    | some e =>
      rcases e with ⟨⟨w, m⟩, a⟩
      constructor
      · rintro ⟨hprev, hnext⟩
        have hs : scheduledMan (recordState h) = some m := by
          have hh := nextEdge_map_man P (recordState h)
          simpa only [hnext, Option.map_some] using hh.symm
        have hp := ih.mp hprev
        exact ⟨⟨hp.1, hs⟩, (prefixes_record_iff P h w m a hs).mpr ⟨hp.2, hnext⟩⟩
      · rintro ⟨⟨hschedule, hs⟩, hp⟩
        have hh := (prefixes_record_iff P h w m a hs).mp hp
        exact ⟨ih.mpr ⟨hschedule, hh.1⟩, hh.2⟩

/-- Literal likelihood of independent men's rows satisfying their separately exposed prefixes. -/
theorem sum_prefix_likelihoods {n : ℕ} (W : Fin n → Fin n → ℝ≥0)
    (L : Fin n → List (Fin n)) :
    (∑ P : Fin n → Equiv.Perm (Fin n),
      if ∀ m, (L m).IsPrefix (List.ofFn (P m).symm) then
        ∏ m, RandomRanking.likelihood (W m) (P m) else 0) =
      ∏ m, prefixLikelihood (W m) (L m) := by
  classical
  simp only [prefixLikelihood]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro P _
  by_cases hp : ∀ m, (L m).IsPrefix (List.ofFn (P m).symm) <;>
    simp [Fintype.prod_ite_zero, hp]

open scoped Classical in
/-- The exact PR likelihood factors exposed men's prefixes from any event on women's rankings. -/
theorem profile_prefix_likelihood {n : ℕ} (W V : Fin n → Fin n → ℝ≥0)
    (L : Fin n → List (Fin n)) (E : (Fin n → Equiv.Perm (Fin n)) → Prop) :
    (∑ p : Profile n,
      if (∀ m, (L m).IsPrefix (List.ofFn (p.manRank m).symm)) ∧ E p.womanRank then
        (∏ m, RandomRanking.likelihood (W m) (p.manRank m)) *
          ∏ w, RandomRanking.likelihood (fun m ↦ V m w) (p.womanRank w) else 0) =
      (∏ m, prefixLikelihood (W m) (L m)) *
        ∑ Q : Fin n → Equiv.Perm (Fin n),
          if E Q then ∏ w, RandomRanking.likelihood (fun m ↦ V m w) (Q w) else 0 := by
  classical
  rw [← (profileCoordinates n).symm.sum_comp]
  simp only [profileCoordinates, Equiv.coe_fn_symm_mk]
  rw [Fintype.sum_prod_type]
  have hind (P Q : Fin n → Equiv.Perm (Fin n)) :
      (if (∀ m, (L m).IsPrefix (List.ofFn (P m).symm)) ∧ E Q then
        (∏ m, RandomRanking.likelihood (W m) (P m)) *
          ∏ w, RandomRanking.likelihood (fun m ↦ V m w) (Q w) else 0) =
      (if ∀ m, (L m).IsPrefix (List.ofFn (P m).symm) then
        ∏ m, RandomRanking.likelihood (W m) (P m) else 0) *
      (if E Q then ∏ w, RandomRanking.likelihood (fun m ↦ V m w) (Q w) else 0) := by
    by_cases hp : ∀ m, (L m).IsPrefix (List.ofFn (P m).symm) <;>
      by_cases hq : E Q <;> simp [hp, hq]
  simp_rw [hind, ← Finset.mul_sum]
  rw [← Finset.sum_mul, sum_prefix_likelihoods]

open scoped Classical in
/-- Exposed row prefixes factor under the original globally normalized PR profile measure.
The checked normalizer-one theorem supplies the literal independent row likelihoods. -/
theorem profile_prefix_measure {n : ℕ} (W V : Fin n → Fin n → ℝ≥0)
    (hW : ∀ m w, 0 < W m w) (hV : ∀ m w, 0 < V m w)
    (L : Fin n → List (Fin n)) (E : (Fin n → Equiv.Perm (Fin n)) → Prop) :
    (RandomRanking.profile W V).toMeasure
      {p | (∀ m, (L m).IsPrefix (List.ofFn (p.manRank m).symm)) ∧ E p.womanRank} =
      (((∏ m, prefixLikelihood (W m) (L m)) *
        ∑ Q : Fin n → Equiv.Perm (Fin n),
          if E Q then ∏ w, RandomRanking.likelihood (fun m ↦ V m w) (Q w) else 0 : ℝ≥0) :
        ℝ≥0∞) := by
  classical
  rw [← profile_prefix_likelihood W V L E, ENNReal.ofNNReal_finsetSum,
    PMF.toMeasure_apply _ (by trivial), tsum_fintype]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : (∀ m, (L m).IsPrefix (List.ofFn (p.manRank m).symm)) ∧ E p.womanRank
  · simpa [Set.indicator, hp] using
      profile_apply_eq_product W V hW hV p
  · simp [Set.indicator, hp]

/-- Priorities given by the exact women's candidate-to-rank permutation. Their comparisons
are precisely the original PR's ordinal comparisons. -/
def profilePriorities {n : ℕ} (p : Profile n) : Edge n → ℝ :=
  fun q ↦ (p.womanRank q.1 q.2).val

/-- The observable transcript obtained directly from the original preference profile. -/
noncomputable def profileTranscript {n : ℕ} (p : Profile n) (t : ℕ) : List (Entry n) :=
  transcript p.manRank (profilePriorities p) t

/-- A woman's ordinal transcript constraints expressed directly on her strict ranking row. -/
def rankRowsEvent {n : ℕ} (h : List (Entry n))
    (Q : Fin n → Equiv.Perm (Fin n)) : Prop :=
  ∀ w, RowFiber h w (fun m ↦ ((Q w m).val : ℝ))

/-- Exact finite-profile transcript factorization, now including the hidden men's row prefixes. -/
theorem profileTranscript_iff {n : ℕ} (p : Profile n) (h : List (Entry n)) :
    profileTranscript p h.length = h ↔ ScheduleValid h ∧
      (∀ m, (manOrder h m).IsPrefix (List.ofFn (p.manRank m).symm)) ∧
        rankRowsEvent h p.womanRank := by
  simp only [profileTranscript, transcript_eq_iff, true_and,
    valid_iff_schedule_prefixes, profilePriorities, rankRowsEvent]
  tauto

/-- Recording the next destination appends to precisely the selected man's list. -/
theorem manOrder_record_eq_update {n : ℕ} (h : List (Entry n)) (w m : Fin n) (a : Bool) :
    manOrder (some ((w, m), a) :: h) =
      Function.update (manOrder h) m (manOrder h m ++ [w]) := by
  classical
  funext k
  by_cases hk : k = m
  · subst k
    simp [manOrder]
  · simp [manOrder, hk, Ne.symm hk]

/-- The fixed-transcript next-destination event exposes just one more men's ranking entry. -/
theorem profileTranscript_next_iff {n : ℕ} (p : Profile n) (h : List (Entry n))
    (w m : Fin n) (hs : scheduledMan (recordState h) = some m) :
    (profileTranscript p h.length = h ∧ nextEdge p.manRank (recordState h) = some (w, m)) ↔
      ScheduleValid h ∧
        (∀ k, (Function.update (manOrder h) m (manOrder h m ++ [w]) k).IsPrefix
          (List.ofFn (p.manRank k).symm)) ∧ rankRowsEvent h p.womanRank := by
  rw [profileTranscript_iff]
  have hp := prefixes_record_iff p.manRank h w m true hs
  rw [manOrder_record_eq_update] at hp
  tauto

/-- Updating one exposed list multiplies its independent-row prefix likelihood by exactly
its residual weighted-choice ratio. -/
theorem prod_prefixLikelihood_update {n : ℕ} (W : Fin n → Fin n → ℝ≥0)
    (hW : ∀ m w, 0 < W m w) (L : Fin n → List (Fin n)) (m w : Fin n)
    (hL : (L m).Nodup) (hlen : (L m).length < n) (hw : w ∉ L m) :
    (∏ k, prefixLikelihood (W k) (Function.update L m (L m ++ [w]) k)) =
      (W m w / (∑ v with v ∉ L m, W m v)) * ∏ k, prefixLikelihood (W k) (L k) := by
  classical
  have hf : (fun k ↦ prefixLikelihood (W k) (Function.update L m (L m ++ [w]) k)) =
      Function.update (fun k ↦ prefixLikelihood (W k) (L k)) m
        (prefixLikelihood (W m) (L m ++ [w])) := by
    funext k
    by_cases hk : k = m <;> simp [hk]
  rw [hf, Finset.prod_update_of_mem (Finset.mem_univ m),
    prefixLikelihood_append (W m) (hW m) (L m) hL hlen w hw,
    Finset.sdiff_singleton_eq_erase, mul_assoc,
    Finset.mul_prod_erase Finset.univ (fun k ↦ prefixLikelihood (W k) (L k))
      (Finset.mem_univ m)]

/-- The exact PR next-destination identity conditioned only on the ordinal transcript.
All men's unobserved ranking suffixes remain hidden. Zero-mass and impossible histories are
included because this is a joint-event identity rather than division by an assumed positive mass. -/
theorem profile_next_destination_measure {n : ℕ} (W V : Fin n → Fin n → ℝ≥0)
    (hW : ∀ m w, 0 < W m w) (hV : ∀ m w, 0 < V m w)
    (h : List (Entry n)) (w m : Fin n)
    (hs : scheduledMan (recordState h) = some m) (hw : w ∉ manOrder h m) :
    (RandomRanking.profile W V).toMeasure
      {p | profileTranscript p h.length = h ∧
        nextEdge p.manRank (recordState h) = some (w, m)} =
      (W m w / (∑ v with v ∉ manOrder h m, W m v) : ℝ≥0) *
        (RandomRanking.profile W V).toMeasure {p | profileTranscript p h.length = h} := by
  classical
  by_cases hex : ∃ P, Valid P h
  · obtain ⟨P, hP⟩ := hex
    have hvalid := (valid_iff_schedule_prefixes P h).mp hP
    have hL : (manOrder h m).Nodup :=
      (hvalid.2 m).sublist.nodup (List.nodup_ofFn.mpr (P m).symm.injective)
    have hlen : (manOrder h m).length < n := by
      rw [length_manOrder]
      exact (scheduledMan_some_spec (recordState h) m hs).1
    have he : {p : Profile n | profileTranscript p h.length = h} =
        {p | (∀ k, (manOrder h k).IsPrefix (List.ofFn (p.manRank k).symm)) ∧
          rankRowsEvent h p.womanRank} := by
      ext p
      simp only [Set.mem_ofPred_eq, profileTranscript_iff, hvalid.1, true_and]
    have heN : {p : Profile n | profileTranscript p h.length = h ∧
        nextEdge p.manRank (recordState h) = some (w, m)} =
        {p | (∀ k, (Function.update (manOrder h) m (manOrder h m ++ [w]) k).IsPrefix
          (List.ofFn (p.manRank k).symm)) ∧ rankRowsEvent h p.womanRank} := by
      ext p
      simp only [Set.mem_ofPred_eq, profileTranscript_next_iff p h w m hs,
        hvalid.1, true_and]
    rw [heN, he, profile_prefix_measure W V hW hV,
      profile_prefix_measure W V hW hV,
      prod_prefixLikelihood_update W hW (manOrder h) m w hL hlen hw]
    simp only [ENNReal.coe_mul, mul_assoc]
  · have he : {p : Profile n | profileTranscript p h.length = h} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hex ⟨p.manRank,
        ((transcript_eq_iff p.manRank (profilePriorities p) h.length h).mp hp).2.1⟩
    have heN : {p : Profile n | profileTranscript p h.length = h ∧
        nextEdge p.manRank (recordState h) = some (w, m)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact Set.notMem_empty p (he ▸ hp.1)
    rw [heN, he, measure_empty, mul_zero]

/-- The next unseen destination under the unchanged original PR market has weight α divided
by the total α-weight of this man's unseen women, given only the revealed ordinal transcript. -/
theorem market_next_destination_measure {n I J : ℕ}
    (womanTier : Fin n → Fin I) (manTier : Fin n → Fin J)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (h : List (Entry n)) (w m : Fin n)
    (hs : scheduledMan (recordState h) = some m) (hw : w ∉ manOrder h m) :
    (Arxiv.«2009.05124».market womanTier manTier α β).toMeasure
      {p | profileTranscript p h.length = h ∧
        nextEdge p.manRank (recordState h) = some (w, m)} =
      (α (womanTier w) / (∑ v with v ∉ manOrder h m, α (womanTier v)) : ℝ≥0) *
        (Arxiv.«2009.05124».market womanTier manTier α β).toMeasure
          {p | profileTranscript p h.length = h} :=
  profile_next_destination_measure (fun _ w ↦ α (womanTier w))
    (fun m _ ↦ β (manTier m)) (fun _ w ↦ hα (womanTier w))
    (fun m _ ↦ hβ (manTier m)) h w m hs hw

/-- Replaying the directly observed profile transcript is exactly the original PR run. -/
theorem recordState_profileTranscript_eq_run {n : ℕ} (p : Profile n) (t : ℕ) :
    recordState (profileTranscript p t) = run p t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change recordStep (recordState (profileTranscript p t))
      (observation p.manRank (profilePriorities p) (recordState (profileTranscript p t))) = _
    have hc : ∀ w m old, p.womanRank w m < p.womanRank w old ↔
        profilePriorities p (w, m) < profilePriorities p (w, old) := by
      intro w m old
      simp only [profilePriorities, Fin.lt_def, Nat.cast_lt]
    rw [recordStep_observation_eq_step p (profilePriorities p) hc, ih]
    exact (Function.iterate_succ_apply' (proposalStep p) t _).symm

/-- A destination is in a man's revealed list exactly when its actual edge has been seen. -/
theorem mem_manOrder_iff_seenEdges {n : ℕ} (h : List (Entry n)) (w m : Fin n) :
    w ∈ manOrder h m ↔ (w, m) ∈ seenEdges h := by
  induction h with
  | nil => simp [manOrder, seenEdges]
  | cons entry h ih =>
    cases entry with
    | none => exact ih
    | some e =>
      rcases e with ⟨⟨v, k⟩, a⟩
      by_cases hk : k = m
      · subst k
        simp [manOrder, seenEdges, ih, or_comm]
      · simp [manOrder, seenEdges, hk, Ne.symm hk, ih]

/-- A previously proposed destination has zero next-destination mass under the exact PR law. -/
theorem profile_next_seen_destination_measure {n : ℕ} (W V : Fin n → Fin n → ℝ≥0)
    (h : List (Entry n)) (w m : Fin n) (hw : w ∈ manOrder h m) :
    (RandomRanking.profile W V).toMeasure
      {p | profileTranscript p h.length = h ∧
        nextEdge p.manRank (recordState h) = some (w, m)} = 0 := by
  have he : {p : Profile n | profileTranscript p h.length = h ∧
      nextEdge p.manRank (recordState h) = some (w, m)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hv : Valid p.manRank h :=
      ((transcript_eq_iff p.manRank (profilePriorities p) h.length h).mp hp.1).2.1
    exact nextEdge_fresh_of_valid p.manRank h hv (w, m) hp.2
      ((mem_manOrder_iff_seenEdges h w m).mp hw)
  rw [he, measure_empty]

/-- The full next-destination kernel has no support on already proposed women. -/
theorem profile_next_destination_kernel {n : ℕ} (W V : Fin n → Fin n → ℝ≥0)
    (hW : ∀ m w, 0 < W m w) (hV : ∀ m w, 0 < V m w)
    (h : List (Entry n)) (w m : Fin n)
    (hs : scheduledMan (recordState h) = some m) :
    (RandomRanking.profile W V).toMeasure
      {p | profileTranscript p h.length = h ∧
        nextEdge p.manRank (recordState h) = some (w, m)} =
      (if w ∈ manOrder h m then 0 else
        ((W m w / (∑ v with v ∉ manOrder h m, W m v) : ℝ≥0) : ℝ≥0∞)) *
        (RandomRanking.profile W V).toMeasure {p | profileTranscript p h.length = h} := by
  classical
  by_cases hw : w ∈ manOrder h m
  · rw [ite_eq_left hw, zero_mul]
    exact profile_next_seen_destination_measure W V h w m hw
  · rw [ite_eq_right hw]
    exact profile_next_destination_measure W V hW hV h w m hs hw

/-- Row transcript constraints depend only on pairwise ordinal comparisons. -/
theorem rowFiber_congr_lt {n : ℕ} (h : List (Entry n)) (w : Fin n)
    (x y : Fin n → ℝ) (hc : ∀ a b, x a < x b ↔ y a < y b) :
    RowFiber h w x ↔ RowFiber h w y := by
  induction h with
  | nil => rfl
  | cons entry h ih =>
    apply and_congr ih
    cases entry with
    | none => rfl
    | some e =>
      rcases e with ⟨q, a⟩
      by_cases hq : q.1 = w
      · simp only [RowConstraint, hq, true_implies]
        cases hh : (recordState h).held w with
        | none => rfl
        | some old => cases a <;> simp only [Bool.false_eq_true, ite_false,
            ite_true, ← not_lt, hc]
      · simp [RowConstraint, hq]

/-- The real priorities supplied by a strict candidate-to-rank row. -/
def rankValues {n : ℕ} (r : Equiv.Perm (Fin n)) : Fin n → ℝ := fun m ↦ (r m).val

/-- Sorting a tie-free priority row preserves every ordinal comparison. -/
theorem rankValues_exponentialRank_lt {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (a b : Fin n) :
    rankValues (exponentialRank x) a < rankValues (exponentialRank x) b ↔ x a < x b := by
  simpa only [rankValues, Nat.cast_lt, ← Fin.lt_def] using exponentialRank_lt_iff x hx a b

local instance {n : ℕ} : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- The sorted-row map pushes independent exponentials to the exact PR row PMF. -/
theorem exponential_row_rank_law {n : ℕ} (r : Fin n → ℝ≥0) (hr : ∀ m, 0 < r m) :
    Measure.map exponentialRank
      (Measure.pi fun m ↦ ProbabilityTheory.expMeasure (r m : ℝ)) =
      (RandomRanking.ofWeights (RandomRanking.likelihood r)).toMeasure := by
  apply Measure.ext_of_singleton
  intro rank
  rw [Measure.map_apply measurable_exponentialRank (by trivial),
    PMF.toMeasure_apply_singleton _ rank (by trivial), row_ofWeights_apply r hr]
  exact exponentialRank_singleton r hr rank

/-- The exact finite-row probability that a fresh proposer beats all seen men, together with
an ordinal transcript row event, is the exponential rate ratio times that row event's mass. -/
theorem rank_row_acceptance_measure {n : ℕ} (r : Fin n → ℝ≥0)
    (hr : ∀ m, 0 < r m) (h : List (Entry n)) (w m : Fin n)
    (hfresh : (w, m) ∉ seenEdges h) :
    (RandomRanking.ofWeights (RandomRanking.likelihood r)).toMeasure
      {rank | (∀ k : SeenMen h w, rankValues rank m < rankValues rank k.val) ∧
        RowFiber h w (rankValues rank)} =
      ENNReal.ofReal ((r m : ℝ) / ((r m : ℝ) + ∑ k : SeenMen h w, (r k.val : ℝ))) *
        (RandomRanking.ofWeights (RandomRanking.likelihood r)).toMeasure
          {rank | RowFiber h w (rankValues rank)} := by
  rw [← exponential_row_rank_law r hr,
    Measure.map_apply measurable_exponentialRank (by trivial),
    Measure.map_apply measurable_exponentialRank (by trivial)]
  simp only [Set.preimage_ofPred_eq]
  have he (x : Fin n → ℝ) (hx : Function.Injective x) :
      RowFiber h w (rankValues (exponentialRank x)) ↔ RowFiber h w x :=
    rowFiber_congr_lt h w _ _ (rankValues_exponentialRank_lt x hx)
  have hE : {x : Fin n → ℝ | RowFiber h w (rankValues (exponentialRank x))} =ᵐ[
      Measure.pi fun k ↦ ProbabilityTheory.expMeasure (r k : ℝ)]
        {x | RowFiber h w x} := by
    filter_upwards [ae_injective_exponentials r hr] with x hx
    exact propext (he x hx)
  have hA : {x : Fin n → ℝ |
      (∀ k : SeenMen h w, rankValues (exponentialRank x) m <
        rankValues (exponentialRank x) k.val) ∧ RowFiber h w (rankValues (exponentialRank x))}
      =ᵐ[Measure.pi fun k ↦ ProbabilityTheory.expMeasure (r k : ℝ)]
        {x | (∀ k : SeenMen h w, x m < x k.val) ∧ RowFiber h w x} := by
    filter_upwards [ae_injective_exponentials r hr] with x hx
    apply propext
    exact and_congr (forall_congr' fun k ↦ rankValues_exponentialRank_lt x hx m k.val) (he x hx)
  rw [measure_congr hE, measure_congr hA]
  exact exponential_row_acceptance_measure (fun k ↦ (r k : ℝ))
    (fun k ↦ by exact_mod_cast hr k) h w m hfresh

/-- The literal likelihood mass of an arbitrary event on a single strict ranking row. -/
noncomputable def rowEventLikelihood {n : ℕ} (r : Fin n → ℝ≥0)
    (E : Equiv.Perm (Fin n) → Prop) : ℝ≥0 := by
  classical
  exact ∑ rank, if E rank then RandomRanking.likelihood r rank else 0

/-- Row event likelihoods are exactly the finite PR row probabilities. -/
theorem rowEventLikelihood_measure {n : ℕ} (r : Fin n → ℝ≥0) (hr : ∀ m, 0 < r m)
    (E : Equiv.Perm (Fin n) → Prop) :
    (RandomRanking.ofWeights (RandomRanking.likelihood r)).toMeasure {rank | E rank} =
      (rowEventLikelihood r E : ℝ≥0∞) := by
  classical
  rw [PMF.toMeasure_apply _ (by trivial), tsum_fintype, rowEventLikelihood,
    ENNReal.ofNNReal_finsetSum]
  apply Finset.sum_congr rfl
  intro rank _
  by_cases he : E rank
  · simp only [Set.indicator, Set.mem_ofPred_eq, he, ite_true, row_ofWeights_apply r hr]
  · simp [Set.indicator, he]


open scoped Classical in
/-- Arbitrary independent women's ranking-row events factor into literal PR row masses. -/
theorem sum_rowEventLikelihood {n : ℕ} (V : Fin n → Fin n → ℝ≥0)
    (E : Fin n → Equiv.Perm (Fin n) → Prop) :
    (∑ Q : Fin n → Equiv.Perm (Fin n),
      if ∀ w, E w (Q w) then ∏ w, RandomRanking.likelihood (fun m ↦ V m w) (Q w) else 0) =
      ∏ w, rowEventLikelihood (fun m ↦ V m w) (E w) := by
  classical
  simp only [rowEventLikelihood]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro Q _
  by_cases hp : ∀ w, E w (Q w) <;> simp [Fintype.prod_ite_zero, hp]

/-- Under the exact finite PR law, exposed men's prefixes and women's row events factor. -/
theorem profile_prefix_rows_measure {n : ℕ} (W V : Fin n → Fin n → ℝ≥0)
    (hW : ∀ m w, 0 < W m w) (hV : ∀ m w, 0 < V m w)
    (L : Fin n → List (Fin n)) (E : Fin n → Equiv.Perm (Fin n) → Prop) :
    (RandomRanking.profile W V).toMeasure
      {p | (∀ m, (L m).IsPrefix (List.ofFn (p.manRank m).symm)) ∧
        ∀ w, E w (p.womanRank w)} =
      (∏ m, (prefixLikelihood (W m) (L m) : ℝ≥0∞)) *
        ∏ w, (RandomRanking.ofWeights (RandomRanking.likelihood (fun m ↦ V m w))).toMeasure
          {rank | E w rank} := by
  classical
  rw [profile_prefix_measure W V hW hV L (fun Q ↦ ∀ w, E w (Q w))]
  simp_rw [rowEventLikelihood_measure _ (fun m ↦ hV m _)]
  simp only [← ENNReal.ofNNReal_finsetProd, ← ENNReal.coe_mul]
  congr 1
  congr 1
  simp only [rowEventLikelihood]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro Q _
  by_cases hp : ∀ w, E w (Q w) <;> simp [Fintype.prod_ite_zero, hp]

/-- The next proposal's acceptance ratio under the original PR profile law, with all unused
rankings hidden. Only the ordinal transcript and the new edge are retained in the base event. -/
theorem profile_next_acceptance_measure {n : ℕ} (W V : Fin n → Fin n → ℝ≥0)
    (hW : ∀ m w, 0 < W m w) (hV : ∀ m w, 0 < V m w)
    (h : List (Entry n)) (w m : Fin n) :
    (RandomRanking.profile W V).toMeasure
      {p | profileTranscript p h.length = h ∧
        nextEdge p.manRank (recordState h) = some (w, m) ∧
        accept (profilePriorities p) (recordState h) (w, m) = true} =
      ENNReal.ofReal ((V m w : ℝ) / ((V m w : ℝ) +
        ∑ k : SeenMen h w, (V k.val w : ℝ))) *
        (RandomRanking.profile W V).toMeasure
          {p | profileTranscript p h.length = h ∧
            nextEdge p.manRank (recordState h) = some (w, m)} := by
  classical
  by_cases hex : ∃ P, Valid P h ∧ nextEdge P (recordState h) = some (w, m)
  · obtain ⟨P, hP, hnext⟩ := hex
    have hvalid := (valid_iff_schedule_prefixes P h).mp hP
    have hs : scheduledMan (recordState h) = some m := by
      have hh := nextEdge_map_man P (recordState h)
      simpa only [hnext, Option.map_some] using hh.symm
    have hfresh := nextEdge_fresh_of_valid P h hP (w, m) hnext
    let L := Function.update (manOrder h) m (manOrder h m ++ [w])
    let E (v : Fin n) (rank : Equiv.Perm (Fin n)) := RowFiber h v (rankValues rank)
    let A (rank : Equiv.Perm (Fin n)) :=
      ∀ k : SeenMen h w, rankValues rank m < rankValues rank k.val
    let E' := Function.update E w (fun rank ↦ A rank ∧ E w rank)
    have hrows (Q : Fin n → Equiv.Perm (Fin n)) :
        (∀ v, E' v (Q v)) ↔ (∀ v, E v (Q v)) ∧ A (Q w) := by
      constructor
      · intro hall
        have hw : A (Q w) ∧ E w (Q w) := by simpa only [E', Function.update_self] using hall w
        refine ⟨fun v ↦ ?_, hw.1⟩
        by_cases hv : v = w
        · simpa only [hv] using hw.2
        · simpa only [E', Function.update_of_ne hv] using hall v
      · rintro ⟨hall, ha⟩ v
        by_cases hv : v = w
        · subst v
          simpa only [E', Function.update_self] using And.intro ha (hall w)
        · simpa only [E', Function.update_of_ne hv] using hall v
    have he : {p : Profile n | profileTranscript p h.length = h ∧
        nextEdge p.manRank (recordState h) = some (w, m)} =
        {p | (∀ k, (L k).IsPrefix (List.ofFn (p.manRank k).symm)) ∧
          ∀ v, E v (p.womanRank v)} := by
      ext p
      change (_ ∧ _) ↔ _
      rw [profileTranscript_next_iff p h w m hs]
      simp only [hvalid.1, true_and]
      rfl
    have heA : {p : Profile n | profileTranscript p h.length = h ∧
        nextEdge p.manRank (recordState h) = some (w, m) ∧
        accept (profilePriorities p) (recordState h) (w, m) = true} =
        {p | (∀ k, (L k).IsPrefix (List.ofFn (p.manRank k).symm)) ∧
          ∀ v, E' v (p.womanRank v)} := by
      ext p
      change (_ ∧ _ ∧ _) ↔ _
      constructor
      · rintro ⟨hp, hn, ha⟩
        have hbase : (∀ k, (L k).IsPrefix (List.ofFn (p.manRank k).symm)) ∧
            ∀ v, E v (p.womanRank v) := (Set.ext_iff.mp he p).mp (And.intro hp hn)
        have haccept : accept (profilePriorities p) (recordState h) (w, m) = true ↔
            A (p.womanRank w) := accept_true_iff_all_seen h w m (profilePriorities p) (hbase.2 w)
        exact ⟨hbase.1, (hrows p.womanRank).mpr ⟨hbase.2, haccept.mp ha⟩⟩
      · rintro ⟨hpref, hr⟩
        have hr' := (hrows p.womanRank).mp hr
        have hbase : profileTranscript p h.length = h ∧
            nextEdge p.manRank (recordState h) = some (w, m) :=
          (Set.ext_iff.mp he p).mpr (And.intro hpref hr'.1)
        have haccept : accept (profilePriorities p) (recordState h) (w, m) = true ↔
            A (p.womanRank w) := accept_true_iff_all_seen h w m (profilePriorities p) (hr'.1 w)
        exact ⟨hbase.1, hbase.2, haccept.mpr hr'.2⟩
    let f (v : Fin n) :=
      (RandomRanking.ofWeights (RandomRanking.likelihood (fun k ↦ V k v))).toMeasure
        {rank | E v rank}
    have hf : (fun v ↦
        (RandomRanking.ofWeights (RandomRanking.likelihood (fun k ↦ V k v))).toMeasure
          {rank | E' v rank}) = Function.update f w
          ((RandomRanking.ofWeights (RandomRanking.likelihood (fun k ↦ V k w))).toMeasure
            {rank | A rank ∧ E w rank}) := by
      funext v
      by_cases hv : v = w
      · subst v
        simp only [E', f, Function.update_self]
      · simp only [E', f, Function.update_of_ne hv]
    have hprod : (∏ v,
        (RandomRanking.ofWeights (RandomRanking.likelihood (fun k ↦ V k v))).toMeasure
          {rank | E' v rank}) =
        ENNReal.ofReal ((V m w : ℝ) / ((V m w : ℝ) +
          ∑ k : SeenMen h w, (V k.val w : ℝ))) * ∏ v, f v := by
      rw [hf, Finset.prod_update_of_mem (Finset.mem_univ w),
        rank_row_acceptance_measure (fun k ↦ V k w) (fun k ↦ hV k w) h w m hfresh,
        Finset.sdiff_singleton_eq_erase, mul_assoc,
        Finset.mul_prod_erase Finset.univ f (Finset.mem_univ w)]
    rw [heA, he, profile_prefix_rows_measure W V hW hV,
      profile_prefix_rows_measure W V hW hV, hprod]
    dsimp only [f]
    ac_rfl
  · have he : {p : Profile n | profileTranscript p h.length = h ∧
        nextEdge p.manRank (recordState h) = some (w, m)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hex ⟨p.manRank,
        ((transcript_eq_iff p.manRank (profilePriorities p) h.length h).mp hp.1).2.1, hp.2⟩
    have heA : {p : Profile n | profileTranscript p h.length = h ∧
        nextEdge p.manRank (recordState h) = some (w, m) ∧
        accept (profilePriorities p) (recordState h) (w, m) = true} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact Set.notMem_empty p (he ▸ And.intro hp.1 hp.2.1)
    rw [heA, he, measure_empty, mul_zero]

/-- The original tiered PR market has the exact published acceptance probability β_m over
β_m plus the β-weights of previously seen proposers, given only its ordinal history and new edge. -/
theorem market_next_acceptance_measure {n I J : ℕ}
    (womanTier : Fin n → Fin I) (manTier : Fin n → Fin J)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (h : List (Entry n)) (w m : Fin n) :
    (Arxiv.«2009.05124».market womanTier manTier α β).toMeasure
      {p | profileTranscript p h.length = h ∧
        nextEdge p.manRank (recordState h) = some (w, m) ∧
        accept (profilePriorities p) (recordState h) (w, m) = true} =
      ENNReal.ofReal ((β (manTier m) : ℝ) / ((β (manTier m) : ℝ) +
        ∑ k : SeenMen h w, (β (manTier k.val) : ℝ))) *
        (Arxiv.«2009.05124».market womanTier manTier α β).toMeasure
          {p | profileTranscript p h.length = h ∧
            nextEdge p.manRank (recordState h) = some (w, m)} :=
  profile_next_acceptance_measure (fun _ w ↦ α (womanTier w))
    (fun m _ ↦ β (manTier m)) (fun _ w ↦ hα (womanTier w))
    (fun m _ ↦ hβ (manTier m)) h w m

/-- One next observation splits exactly into its destination and acceptance bit. -/
theorem observation_eq_some_iff {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (x : Edge n → ℝ) (s : ProposalState n) (q : Edge n) (a : Bool) :
    observation P x s = some (q, a) ↔ nextEdge P s = some q ∧ accept x s q = a := by
  rw [observation_eq_iff]
  simpa only [Option.map_some] using
    (and_congr_right (fun _ ↦ (accept_eq_iff_rows x s q a).symm))

/-- An extended observable profile transcript fixes precisely its previous transcript and
its next observation. No hidden ranking coordinates are included in the conditioning event. -/
theorem profileTranscript_cons_iff {n : ℕ} (p : Profile n) (h : List (Entry n))
    (entry : Entry n) :
    profileTranscript p (h.length + 1) = entry :: h ↔
      profileTranscript p h.length = h ∧
        observation p.manRank (profilePriorities p) (recordState h) = entry := by
  change observation p.manRank (profilePriorities p) (recordState (profileTranscript p h.length))
      :: profileTranscript p h.length = entry :: h ↔ _
  rw [List.cons.injEq]
  constructor
  · rintro ⟨hentry, htail⟩
    exact ⟨htail, by simpa only [htail] using hentry⟩
  · rintro ⟨htail, hentry⟩
    exact ⟨by simpa only [htail] using hentry, htail⟩

/-- The exact original-PR coarse transition kernel for an accepted new destination. -/
theorem market_transcript_extend_true_measure {n I J : ℕ}
    (womanTier : Fin n → Fin I) (manTier : Fin n → Fin J)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (h : List (Entry n)) (w m : Fin n)
    (hs : scheduledMan (recordState h) = some m) (hw : w ∉ manOrder h m) :
    (Arxiv.«2009.05124».market womanTier manTier α β).toMeasure
      {p | profileTranscript p (h.length + 1) = some ((w, m), true) :: h} =
      ENNReal.ofReal ((β (manTier m) : ℝ) / ((β (manTier m) : ℝ) +
        ∑ k : SeenMen h w, (β (manTier k.val) : ℝ))) *
      (α (womanTier w) / (∑ v with v ∉ manOrder h m, α (womanTier v)) : ℝ≥0) *
        (Arxiv.«2009.05124».market womanTier manTier α β).toMeasure
          {p | profileTranscript p h.length = h} := by
  have he : {p : Profile n | profileTranscript p (h.length + 1) = some ((w, m), true) :: h} =
      {p | profileTranscript p h.length = h ∧
        nextEdge p.manRank (recordState h) = some (w, m) ∧
        accept (profilePriorities p) (recordState h) (w, m) = true} := by
    ext p
    exact (profileTranscript_cons_iff p h _).trans
      (and_congr_right fun _ ↦ observation_eq_some_iff _ _ _ _ _)
  rw [he, market_next_acceptance_measure womanTier manTier α β hα hβ,
    market_next_destination_measure womanTier manTier α β hα hβ h w m hs hw, mul_assoc]

end TieredMatching.Ordinal
