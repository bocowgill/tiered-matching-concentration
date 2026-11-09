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

public import TieredMatching.Protocols

/-! # Exact original-PR transition kernels for ordinal proposer protocols

Only the protocol's revealed ordinal transcript is conditioned on. Men's unseen preference
suffixes and women's unobserved priorities remain hidden. The direct finite PR profile law
supplies destination and acceptance kernels for partial or suspended proposer schedules.
-/

@[expose] public section

namespace TieredMatching.Protocols

open StableMarriage MeasureTheory TieredMatching.Ordinal Arrival
open scoped ENNReal NNReal

/-- The actual protocol transcript generated directly from the original PR preference profile. -/
noncomputable def profileTranscript {n : ℕ} (C : Protocol n) (p : Profile n) (t : ℕ) :
    List (Entry n) := transcript C p.manRank (profilePriorities p) t

/-- Exact fixed-profile fibers separate visible protocol legality, men's exposed prefixes,
and independent women's ordinal row constraints. -/
theorem profileTranscript_iff {n : ℕ} (C : Protocol n) (p : Profile n) (h : List (Entry n)) :
    profileTranscript C p h.length = h ↔ ScheduleValid C h ∧
      (∀ m, (manOrder h m).IsPrefix (List.ofFn (p.manRank m).symm)) ∧
        rankRowsEvent h p.womanRank := by
  simp only [profileTranscript, transcript_eq_iff, true_and,
    valid_iff_schedule_prefixes, profilePriorities, rankRowsEvent]
  tauto

/-- The actual next protocol edge exposes exactly one further candidate in one man's list. -/
theorem profileTranscript_next_iff {n : ℕ} (C : Protocol n) (p : Profile n)
    (h : List (Entry n)) (w m : Fin n) (hs : selected C h = some m) :
    (profileTranscript C p h.length = h ∧ nextEdge C p.manRank h = some (w, m)) ↔
      ScheduleValid C h ∧
        (∀ k, (Function.update (manOrder h) m (manOrder h m ++ [w]) k).IsPrefix
          (List.ofFn (p.manRank k).symm)) ∧ rankRowsEvent h p.womanRank := by
  rw [profileTranscript_iff]
  have hp := prefixes_record_iff C p.manRank h w m true hs
  rw [manOrder_record_eq_update] at hp
  tauto

/-- The exact PR next-destination identity conditioned only on the ordinal transcript.
All men's unobserved ranking suffixes remain hidden. Zero-mass and impossible histories are
included because this is a joint-event identity rather than division by an assumed positive mass. -/
theorem profile_next_destination_measure {n : ℕ} (W V : Fin n → Fin n → ℝ≥0)
    (hW : ∀ m w, 0 < W m w) (hV : ∀ m w, 0 < V m w)
    (C : Protocol n) (h : List (Entry n)) (w m : Fin n)
    (hs : selected C h = some m) (hw : w ∉ manOrder h m) :
    (RandomRanking.profile W V).toMeasure
      {p | profileTranscript C p h.length = h ∧
        nextEdge C p.manRank h = some (w, m)} =
      (W m w / (∑ v with v ∉ manOrder h m, W m v) : ℝ≥0) *
        (RandomRanking.profile W V).toMeasure {p | profileTranscript C p h.length = h} := by
  classical
  by_cases hex : ∃ P, ValidProtocol C P h
  · obtain ⟨P, hP⟩ := hex
    have hvalid := (valid_iff_schedule_prefixes C P h).mp hP
    have hL : (manOrder h m).Nodup :=
      (hvalid.2 m).sublist.nodup (List.nodup_ofFn.mpr (P m).symm.injective)
    have hlen : (manOrder h m).length < n := by
      rw [length_manOrder]
      exact (selected_some_spec C h m hs).1
    have he : {p : Profile n | profileTranscript C p h.length = h} =
        {p | (∀ k, (manOrder h k).IsPrefix (List.ofFn (p.manRank k).symm)) ∧
          rankRowsEvent h p.womanRank} := by
      ext p
      simp only [Set.mem_ofPred_eq, profileTranscript_iff, hvalid.1, true_and]
    have heN : {p : Profile n | profileTranscript C p h.length = h ∧
        nextEdge C p.manRank h = some (w, m)} =
        {p | (∀ k, (Function.update (manOrder h) m (manOrder h m ++ [w]) k).IsPrefix
          (List.ofFn (p.manRank k).symm)) ∧ rankRowsEvent h p.womanRank} := by
      ext p
      simp only [Set.mem_ofPred_eq, profileTranscript_next_iff C p h w m hs,
        hvalid.1, true_and]
    rw [heN, he, profile_prefix_measure W V hW hV,
      profile_prefix_measure W V hW hV,
      prod_prefixLikelihood_update W hW (manOrder h) m w hL hlen hw]
    simp only [ENNReal.coe_mul, mul_assoc]
  · have he : {p : Profile n | profileTranscript C p h.length = h} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hex ⟨p.manRank,
        ((transcript_eq_iff C p.manRank (profilePriorities p) h.length h).mp hp).2.1⟩
    have heN : {p : Profile n | profileTranscript C p h.length = h ∧
        nextEdge C p.manRank h = some (w, m)} = ∅ := by
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
    (C : Protocol n) (h : List (Entry n)) (w m : Fin n)
    (hs : selected C h = some m) (hw : w ∉ manOrder h m) :
    (Arxiv.«2009.05124».market womanTier manTier α β).toMeasure
      {p | profileTranscript C p h.length = h ∧
        nextEdge C p.manRank h = some (w, m)} =
      (α (womanTier w) / (∑ v with v ∉ manOrder h m, α (womanTier v)) : ℝ≥0) *
        (Arxiv.«2009.05124».market womanTier manTier α β).toMeasure
          {p | profileTranscript C p h.length = h} :=
  profile_next_destination_measure (fun _ w ↦ α (womanTier w))
    (fun m _ ↦ β (manTier m)) (fun _ w ↦ hα (womanTier w))
    (fun m _ ↦ hβ (manTier m)) C h w m hs hw

/-- A previously proposed destination has zero next-destination mass under the exact PR law. -/
theorem profile_next_seen_destination_measure {n : ℕ} (W V : Fin n → Fin n → ℝ≥0)
    (C : Protocol n) (h : List (Entry n)) (w m : Fin n) (hw : w ∈ manOrder h m) :
    (RandomRanking.profile W V).toMeasure
      {p | profileTranscript C p h.length = h ∧
        nextEdge C p.manRank h = some (w, m)} = 0 := by
  have he : {p : Profile n | profileTranscript C p h.length = h ∧
      nextEdge C p.manRank h = some (w, m)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hv : ValidProtocol C p.manRank h :=
      ((transcript_eq_iff C p.manRank (profilePriorities p) h.length h).mp hp.1).2.1
    exact nextEdge_fresh_of_valid C p.manRank h hv (w, m) hp.2
      ((mem_manOrder_iff_seenEdges h w m).mp hw)
  rw [he, measure_empty]

/-- The full next-destination kernel has no support on already proposed women. -/
theorem profile_next_destination_kernel {n : ℕ} (W V : Fin n → Fin n → ℝ≥0)
    (hW : ∀ m w, 0 < W m w) (hV : ∀ m w, 0 < V m w)
    (C : Protocol n) (h : List (Entry n)) (w m : Fin n)
    (hs : selected C h = some m) :
    (RandomRanking.profile W V).toMeasure
      {p | profileTranscript C p h.length = h ∧
        nextEdge C p.manRank h = some (w, m)} =
      (if w ∈ manOrder h m then 0 else
        ((W m w / (∑ v with v ∉ manOrder h m, W m v) : ℝ≥0) : ℝ≥0∞)) *
        (RandomRanking.profile W V).toMeasure {p | profileTranscript C p h.length = h} := by
  classical
  by_cases hw : w ∈ manOrder h m
  · rw [ite_eq_left hw, zero_mul]
    exact profile_next_seen_destination_measure W V C h w m hw
  · rw [ite_eq_right hw]
    exact profile_next_destination_measure W V hW hV C h w m hs hw

local instance {n : ℕ} : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- The next proposal's acceptance ratio under the original PR profile law, with all unused
rankings hidden. Only the ordinal transcript and the new edge are retained in the base event. -/
theorem profile_next_acceptance_measure {n : ℕ} (W V : Fin n → Fin n → ℝ≥0)
    (hW : ∀ m w, 0 < W m w) (hV : ∀ m w, 0 < V m w)
    (C : Protocol n) (h : List (Entry n)) (w m : Fin n) :
    (RandomRanking.profile W V).toMeasure
      {p | profileTranscript C p h.length = h ∧
        nextEdge C p.manRank h = some (w, m) ∧
        accept (profilePriorities p) (recordState h) (w, m) = true} =
      ENNReal.ofReal ((V m w : ℝ) / ((V m w : ℝ) +
        ∑ k : SeenMen h w, (V k.val w : ℝ))) *
        (RandomRanking.profile W V).toMeasure
          {p | profileTranscript C p h.length = h ∧
            nextEdge C p.manRank h = some (w, m)} := by
  classical
  by_cases hex : ∃ P, ValidProtocol C P h ∧ nextEdge C P h = some (w, m)
  · obtain ⟨P, hP, hnext⟩ := hex
    have hvalid := (valid_iff_schedule_prefixes C P h).mp hP
    have hs : selected C h = some m := by
      have hh := nextEdge_map_man C P h
      simpa only [hnext, Option.map_some] using hh.symm
    have hfresh := nextEdge_fresh_of_valid C P h hP (w, m) hnext
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
    have he : {p : Profile n | profileTranscript C p h.length = h ∧
        nextEdge C p.manRank h = some (w, m)} =
        {p | (∀ k, (L k).IsPrefix (List.ofFn (p.manRank k).symm)) ∧
          ∀ v, E v (p.womanRank v)} := by
      ext p
      change (_ ∧ _) ↔ _
      rw [profileTranscript_next_iff C p h w m hs]
      simp only [hvalid.1, true_and]
      rfl
    have heA : {p : Profile n | profileTranscript C p h.length = h ∧
        nextEdge C p.manRank h = some (w, m) ∧
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
        have hbase : profileTranscript C p h.length = h ∧
            nextEdge C p.manRank h = some (w, m) :=
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
  · have he : {p : Profile n | profileTranscript C p h.length = h ∧
        nextEdge C p.manRank h = some (w, m)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hex ⟨p.manRank,
        ((transcript_eq_iff C p.manRank (profilePriorities p) h.length h).mp hp.1).2.1, hp.2⟩
    have heA : {p : Profile n | profileTranscript C p h.length = h ∧
        nextEdge C p.manRank h = some (w, m) ∧
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
    (C : Protocol n) (h : List (Entry n)) (w m : Fin n) :
    (Arxiv.«2009.05124».market womanTier manTier α β).toMeasure
      {p | profileTranscript C p h.length = h ∧
        nextEdge C p.manRank h = some (w, m) ∧
        accept (profilePriorities p) (recordState h) (w, m) = true} =
      ENNReal.ofReal ((β (manTier m) : ℝ) / ((β (manTier m) : ℝ) +
        ∑ k : SeenMen h w, (β (manTier k.val) : ℝ))) *
        (Arxiv.«2009.05124».market womanTier manTier α β).toMeasure
          {p | profileTranscript C p h.length = h ∧
            nextEdge C p.manRank h = some (w, m)} :=
  profile_next_acceptance_measure (fun _ w ↦ α (womanTier w))
    (fun m _ ↦ β (manTier m)) (fun _ w ↦ hα (womanTier w))
    (fun m _ ↦ hβ (manTier m)) C h w m

/-- A protocol observation fixes exactly its selected edge and actual ordinal acceptance bit. -/
theorem observation_eq_some_iff {n : ℕ} (C : Protocol n)
    (P : Fin n → Equiv.Perm (Fin n)) (x : Edge n → ℝ) (h : List (Entry n))
    (q : Edge n) (a : Bool) :
    observation C P x h = some (q, a) ↔
      nextEdge C P h = some q ∧ Ordinal.accept x (recordState h) q = a := by
  rw [observation_eq_iff]
  simpa only [Option.map_some] using
    (and_congr_right (fun _ ↦ (accept_eq_iff_rows x (recordState h) q a).symm))

/-- An actual protocol-history extension specifies its old history and next observation. -/
theorem profileTranscript_cons_iff {n : ℕ} (C : Protocol n) (p : Profile n)
    (h : List (Entry n)) (entry : Entry n) :
    profileTranscript C p (h.length + 1) = entry :: h ↔
      profileTranscript C p h.length = h ∧ observation C p.manRank (profilePriorities p) h =
        entry := by
  change observation C p.manRank (profilePriorities p) (profileTranscript C p h.length) ::
      profileTranscript C p h.length = entry :: h ↔ _
  rw [List.cons.injEq]
  constructor
  · rintro ⟨hentry, htail⟩
    exact ⟨htail, by simpa only [htail] using hentry⟩
  · rintro ⟨htail, hentry⟩
    exact ⟨by simpa only [htail] using hentry, htail⟩

/-- Either observed acceptance bit is exactly the next protocol edge and ordinal comparison. -/
theorem profile_extend_event {n : ℕ} (C : Protocol n) (h : List (Entry n))
    (q : Edge n) (a : Bool) :
    {p : Profile n | profileTranscript C p (h.length + 1) = some (q, a) :: h} =
      {p | profileTranscript C p h.length = h ∧ nextEdge C p.manRank h = some q ∧
        Ordinal.accept (profilePriorities p) (recordState h) q = a} := by
  ext p
  exact (profileTranscript_cons_iff C p h _).trans
    (and_congr_right fun _ ↦ observation_eq_some_iff C _ _ h q a)

/-- The exact finite-PR next accepted-history mass for any ordinal proposer protocol. -/
theorem profile_transcript_extend_true_measure {n : ℕ} (W V : Fin n → Fin n → ℝ≥0)
    (hW : ∀ m w, 0 < W m w) (hV : ∀ m w, 0 < V m w)
    (C : Protocol n) (h : List (Entry n)) (w m : Fin n)
    (hs : selected C h = some m) (hw : w ∉ manOrder h m) :
    (RandomRanking.profile W V).toMeasure
      {p | profileTranscript C p (h.length + 1) = some ((w, m), true) :: h} =
      ENNReal.ofReal ((V m w : ℝ) / ((V m w : ℝ) +
        ∑ k : SeenMen h w, (V k.val w : ℝ))) *
      (W m w / (∑ v with v ∉ manOrder h m, W m v) : ℝ≥0) *
        (RandomRanking.profile W V).toMeasure {p | profileTranscript C p h.length = h} := by
  rw [profile_extend_event, profile_next_acceptance_measure W V hW hV C h w m,
    profile_next_destination_measure W V hW hV C h w m hs hw, mul_assoc]

/-- The exact finite-PR complementary rejection-history mass for the same visible protocol. -/
theorem profile_transcript_extend_false_measure {n : ℕ} (W V : Fin n → Fin n → ℝ≥0)
    (hW : ∀ m w, 0 < W m w) (hV : ∀ m w, 0 < V m w)
    (C : Protocol n) (h : List (Entry n)) (w m : Fin n)
    (hs : selected C h = some m) (hw : w ∉ manOrder h m) :
    (RandomRanking.profile W V).toMeasure
      {p | profileTranscript C p (h.length + 1) = some ((w, m), false) :: h} =
      (1 - ENNReal.ofReal ((V m w : ℝ) / ((V m w : ℝ) +
        ∑ k : SeenMen h w, (V k.val w : ℝ)))) *
      (W m w / (∑ v with v ∉ manOrder h m, W m v) : ℝ≥0) *
        (RandomRanking.profile W V).toMeasure {p | profileTranscript C p h.length = h} := by
  let μ := (RandomRanking.profile W V).toMeasure
  let B : Set (Profile n) :=
    {p | profileTranscript C p h.length = h ∧ nextEdge C p.manRank h = some (w, m)}
  let T : Set (Profile n) := {p | profileTranscript C p h.length = h ∧
    nextEdge C p.manRank h = some (w, m) ∧
    Ordinal.accept (profilePriorities p) (recordState h) (w, m) = true}
  have hT : MeasurableSet T := by trivial
  have hsub : T ⊆ B := fun _ hp ↦ ⟨hp.1, hp.2.1⟩
  have he : {p : Profile n |
      profileTranscript C p (h.length + 1) = some ((w, m), false) :: h} = B \ T := by
    rw [profile_extend_event]
    ext p
    simp only [B, T, Set.mem_ofPred_eq, Set.mem_sdiff]
    cases ha : Ordinal.accept (profilePriorities p) (recordState h) (w, m) <;> simp
  rw [he, measure_sdiff hsub hT.nullMeasurableSet (measure_ne_top _ _)]
  dsimp only [B, T]
  rw [profile_next_acceptance_measure W V hW hV C h w m]
  let q := ENNReal.ofReal ((V m w : ℝ) / ((V m w : ℝ) +
    ∑ k : SeenMen h w, (V k.val w : ℝ)))
  change μ B - q * μ B = (1 - q) * (W m w / (∑ v with v ∉ manOrder h m, W m v) : ℝ≥0) *
    μ {p | profileTranscript C p h.length = h}
  have hm : μ B - q * μ B = (1 - q) * μ B := by
    simpa only [one_mul] using (ENNReal.sub_mul (a := 1) (b := q) (c := μ B)
      (fun _ _ ↦ measure_ne_top _ _)).symm
  rw [hm]
  dsimp only [μ, B]
  rw [profile_next_destination_measure W V hW hV C h w m hs hw, mul_assoc]

/-- A suspended protocol adds only a padding record, even if other men remain eligible. -/
theorem profile_transcript_extend_pause_measure {n : ℕ} (W V : Fin n → Fin n → ℝ≥0)
    (C : Protocol n) (h : List (Entry n)) (hs : selected C h = none) :
    (RandomRanking.profile W V).toMeasure
      {p | profileTranscript C p (h.length + 1) = none :: h} =
      (RandomRanking.profile W V).toMeasure {p | profileTranscript C p h.length = h} := by
  congr 1
  ext p
  change profileTranscript C p (h.length + 1) = none :: h ↔ _
  rw [profileTranscript_cons_iff]
  simp only [observation, nextEdge, hs, Option.map_none, and_true, Set.mem_ofPred_eq]

/-- The exact original tiered PR transition law for an accepted edge under any partial or
suspended ordinal protocol. Only its revealed history is retained. -/
theorem market_transcript_extend_true_measure {n I J : ℕ}
    (womanTier : Fin n → Fin I) (manTier : Fin n → Fin J)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (C : Protocol n) (h : List (Entry n)) (w m : Fin n)
    (hs : selected C h = some m) (hw : w ∉ manOrder h m) :
    (Arxiv.«2009.05124».market womanTier manTier α β).toMeasure
      {p | profileTranscript C p (h.length + 1) = some ((w, m), true) :: h} =
      ENNReal.ofReal ((β (manTier m) : ℝ) / ((β (manTier m) : ℝ) +
        ∑ k : SeenMen h w, (β (manTier k.val) : ℝ))) *
      (α (womanTier w) / (∑ v with v ∉ manOrder h m, α (womanTier v)) : ℝ≥0) *
        (Arxiv.«2009.05124».market womanTier manTier α β).toMeasure
          {p | profileTranscript C p h.length = h} :=
  profile_transcript_extend_true_measure (fun _ w ↦ α (womanTier w))
    (fun m _ ↦ β (manTier m)) (fun _ w ↦ hα (womanTier w))
    (fun m _ ↦ hβ (manTier m)) C h w m hs hw

/-- Every directly observed profile transcript replays to an admissible partial-entrant DA state. -/
theorem profileTranscript_reachable {n : ℕ} (C : Protocol n) (p : Profile n)
    (A : Finset (Fin n)) (t : ℕ) (hu : Uses A C (profileTranscript C p t)) :
    Schedules.Reachable p A (recordState (profileTranscript C p t)) := by
  have hc : ∀ w m old, profilePriorities p (w, m) < profilePriorities p (w, old) ↔
      p.womanRank w m < p.womanRank w old := by
    intro w m old
    simp only [profilePriorities, Nat.cast_lt, Fin.lt_def]
  apply recordState_reachable C p (profilePriorities p) hc A _ _ hu
  apply (observes_iff_transcript C p.manRank (profilePriorities p) _).mpr
  have hlen : (profileTranscript C p t).length = t :=
    transcript_length C p.manRank (profilePriorities p) t
  rw [hlen]
  rfl

/-- Each protocol state has at most n genuine proposals per man, independently of pauses. -/
theorem profileTranscript_next_le {n : ℕ} (C : Protocol n) (p : Profile n) (t : ℕ)
    (m : Fin n) : (recordState (profileTranscript C p t)).next m ≤ n :=
  (Schedules.reachable_valid p Finset.univ
    (profileTranscript_reachable C p Finset.univ t (uses_univ C _))).next_le m

/-- A terminal active-subset protocol agrees with the uniquely proved partial DA state. -/
theorem profileTranscript_terminal_eq_active {n : ℕ} (C : Protocol n) (p : Profile n)
    (A : Finset (Fin n)) (t : ℕ) (hu : Uses A C (profileTranscript C p t))
    (ht : Schedules.Terminal A (recordState (profileTranscript C p t))) :
    recordState (profileTranscript C p t) = Schedules.activeDeferredAcceptance p A :=
  Schedules.terminal_state_eq_active p A (profileTranscript_reachable C p A t hu) ht

/-- A terminal all-entrant protocol has exactly the original PR terminal state. -/
theorem profileTranscript_terminal_eq_pr {n : ℕ} (C : Protocol n) (p : Profile n) (t : ℕ)
    (ht : Schedules.Terminal Finset.univ (recordState (profileTranscript C p t))) :
    recordState (profileTranscript C p t) = deferredAcceptance p :=
  Schedules.terminal_state_eq_pr p
    (profileTranscript_reachable C p Finset.univ t (uses_univ C _)) ht

end TieredMatching.Protocols
