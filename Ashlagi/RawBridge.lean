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
public import Ashlagi.RawSemantics
public import Ashlagi.RawMarketLaw

/-! # Actual IID-driven raw proposals realize the exact PR deferred acceptance

The finite-prefix first-discovery compatibility is proved from the stream itself before it is
used to justify any actual raw transition. Terminal statements make no finite hitting-time claim.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace Ashlagi.RawBridge

open StableMarriage Arrival

variable {α : Type*} [DecidableEq α]

/-- First distinct labels in a chronological finite word, omitting excluded labels. -/
def distinctPrefix (S : Finset α) : List α → List α
  | [] => []
  | q :: L => if q ∈ S then distinctPrefix S L else q :: distinctPrefix (insert q S) L

/-- Dropping one excluded draw preserves the exact full discovery-order event. -/
theorem discoveryEvent_shift_excluded (S : Finset α) (R : List α) (x : ℕ → α)
    (hx : x ∈ IIDRanking.discoveryEvent S R) (hzero : x 0 ∈ S) :
    FirstFresh.tailAfter 0 x ∈ IIDRanking.discoveryEvent S R := by
  cases R with
  | nil => trivial
  | cons q R =>
    obtain ⟨hq, k, hk, hxq, htail⟩ := (IIDRanking.mem_discoveryEvent_cons _ _ _ _).mp hx
    cases k with
    | zero => exact False.elim (hq (hxq ▸ hzero))
    | succ k =>
      apply (IIDRanking.mem_discoveryEvent_cons _ _ _ _).mpr
      refine ⟨hq, k, ?_, ?_, ?_⟩
      · intro t ht
        simpa [FirstFresh.tailAfter, Nat.add_comm] using hk (t + 1) (by omega)
      · simpa [FirstFresh.tailAfter, Nat.add_comm] using hxq
      · have heq : FirstFresh.tailAfter k (FirstFresh.tailAfter 0 x) =
            FirstFresh.tailAfter (k + 1) x := by
          funext t
          simp [FirstFresh.tailAfter, Nat.add_comm, Nat.add_left_comm]
        rw [heq]
        exact htail

/-- A fresh zeroth draw is the first discovery, with the residual event on its actual tail. -/
theorem discoveryEvent_fresh_head (S : Finset α) (q : α) (R : List α) (x : ℕ → α)
    (hx : x ∈ IIDRanking.discoveryEvent S (q :: R)) (hzero : x 0 ∉ S) :
    q = x 0 ∧ FirstFresh.tailAfter 0 x ∈ IIDRanking.discoveryEvent (insert (x 0) S) R := by
  obtain ⟨_, k, hk, hxq, htail⟩ := (IIDRanking.mem_discoveryEvent_cons _ _ _ _).mp hx
  have hk0 : k = 0 := by
    by_contra hne
    exact hzero (hk 0 (by omega))
  subst k
  exact ⟨hxq.symm, by simpa only [hxq] using htail⟩

omit [DecidableEq α] in
/-- Removing the first word entry also removes the zeroth coordinate of its actual stream prefix. -/
theorem streamPrefix_cons (x : ℕ → α) (q : α) (L : List α)
    (hp : x ∈ StreamPrefix.prefixEvent (q :: L)) :
    x 0 = q ∧ FirstFresh.tailAfter 0 x ∈ StreamPrefix.prefixEvent L := by
  have hhead := hp ⟨0, by simp⟩
  refine ⟨hhead, ?_⟩
  intro i
  have hi := hp ⟨i.val + 1, by simp⟩
  simpa [FirstFresh.tailAfter, List.get_eq_getElem, Nat.add_comm] using hi

/-- First distinct labels in every finite consumed word follow its actual discovery order. -/
theorem distinctPrefix_isPrefix (S : Finset α) (R L : List α) (x : ℕ → α)
    (hx : x ∈ IIDRanking.discoveryEvent S R) (hcover : ∀ q, q ∈ S ∨ q ∈ R)
    (hp : x ∈ StreamPrefix.prefixEvent L) : (distinctPrefix S L).IsPrefix R := by
  induction L generalizing S R x with
  | nil => simp [distinctPrefix]
  | cons q L ih =>
    obtain ⟨hxq, hp'⟩ := streamPrefix_cons x q L hp
    by_cases hq : q ∈ S
    · rw [distinctPrefix, ite_eq_left hq]
      exact ih S R (FirstFresh.tailAfter 0 x)
        (discoveryEvent_shift_excluded S R x hx (hxq ▸ hq)) hcover hp'
    · cases R with
      | nil => have hh := (hcover q).resolve_left hq; simp at hh
      | cons a R =>
        have hfirst := discoveryEvent_fresh_head S a R x hx (hxq ▸ hq)
        have haq : a = q := hfirst.1.trans hxq
        rw [distinctPrefix, ite_eq_right hq, List.cons_prefix_cons]
        refine ⟨haq.symm, ?_⟩
        apply ih (insert q S) R (FirstFresh.tailAfter 0 x)
        · simpa only [hxq] using hfirst.2
        · intro b
          rcases hcover b with hb | hb
          · exact Or.inl (Finset.mem_insert_of_mem hb)
          · rcases List.mem_cons.mp hb with heq | hb
            · exact Or.inl (Finset.mem_insert.mpr (Or.inl (heq.trans haq)))
            · exact Or.inr hb
        · exact hp'

/-- Deduplicated finite prefixes contain exactly the original labels outside the excluded set. -/
theorem distinctPrefix_toFinset (S : Finset α) (L : List α) :
    (distinctPrefix S L).toFinset = L.toFinset \ S := by
  induction L generalizing S with
  | nil => simp [distinctPrefix]
  | cons q L ih =>
    by_cases hq : q ∈ S
    · rw [distinctPrefix, ite_eq_left hq, ih]
      ext a
      by_cases haq : a = q <;> simp [haq, hq]
    · rw [distinctPrefix, ite_eq_right hq, List.toFinset_cons, ih]
      ext a
      by_cases haq : a = q <;> simp [haq, hq]

/-- The chronological first-distinct scan has no repeated output label. -/
theorem distinctPrefix_nodup (S : Finset α) (L : List α) : (distinctPrefix S L).Nodup := by
  induction L generalizing S with
  | nil => simp [distinctPrefix]
  | cons q L ih =>
    by_cases hq : q ∈ S
    · simpa only [distinctPrefix, ite_eq_left hq] using ih S
    · rw [distinctPrefix, ite_eq_right hq, List.nodup_cons]
      refine ⟨?_, ih _⟩
      intro hmem
      have hm : q ∈ (distinctPrefix (insert q S) L).toFinset := List.mem_toFinset.mpr hmem
      rw [distinctPrefix_toFinset] at hm
      simp at hm

/-- The length of the first-distinct scan is the exact number of distinct original labels. -/
theorem length_distinctPrefix_empty (L : List α) :
    (distinctPrefix ∅ L).length = L.toFinset.card := by
  rw [← List.toFinset_card_of_nodup (distinctPrefix_nodup ∅ L), distinctPrefix_toFinset]
  simp

/-- The first-distinct scan concatenates using exactly the labels excluded by the first word. -/
theorem distinctPrefix_append (S : Finset α) (L M : List α) :
    distinctPrefix S (L ++ M) =
      distinctPrefix S L ++ distinctPrefix (S ∪ L.toFinset) M := by
  induction L generalizing S with
  | nil => simp [distinctPrefix]
  | cons q L ih =>
    by_cases hq : q ∈ S
    · simp only [List.cons_append, distinctPrefix, hq, ↓reduceIte, ih, List.toFinset_cons]
      congr 1
      congr 1
      ext a
      simp
      aesop
    · simp only [List.cons_append, distinctPrefix, hq, ↓reduceIte, ih, List.toFinset_cons]
      congr 2
      ext a
      simp

/-- Appending a genuinely unseen label appends exactly one first-distinct discovery. -/
theorem distinctPrefix_append_fresh (L : List α) (q : α) (hq : q ∉ L) :
    distinctPrefix ∅ (L ++ [q]) = distinctPrefix ∅ L ++ [q] := by
  rw [distinctPrefix_append]
  simp [distinctPrefix, hq]

/-- A fresh stream draw has rank equal to the previous number of distinct destinations. -/
theorem fresh_rank_eq_card {n : ℕ} (x : ℕ → Fin n) (r : Equiv.Perm (Fin n))
    (hx : x ∈ IIDRanking.rankEvent r) (L : List (Fin n))
    (hp : x ∈ StreamPrefix.prefixEvent L) (q : Fin n) (hq : q ∉ L)
    (hnext : x L.length = q) : (r q).val = L.toFinset.card := by
  have hext : x ∈ StreamPrefix.prefixEvent (L ++ [q]) := by
    rw [StreamPrefix.prefixEvent_append]
    exact ⟨hp, hnext⟩
  have hcover : ∀ a : Fin n, a ∈ (∅ : Finset (Fin n)) ∨ a ∈ List.ofFn r.symm := by
    intro a
    exact Or.inr (List.mem_ofFn.mpr ⟨r a, r.symm_apply_apply a⟩)
  have hd := distinctPrefix_isPrefix ∅ (List.ofFn r.symm) (L ++ [q]) x hx hcover hext
  rw [distinctPrefix_append_fresh L q hq] at hd
  have hlen := hd.length_le
  simp only [List.length_append, List.length_singleton, List.length_ofFn] at hlen
  have hn : (distinctPrefix ∅ L).length < n := by omega
  have hget := (Ordinal.prefix_append_singleton_iff _ _ q).mp hd |>.2
  have hdest : r.symm ⟨(distinctPrefix ∅ L).length, hn⟩ = q := by
    simpa only [List.getElem?_ofFn, dite_eq_left hn, Option.some.injEq] using hget
  have hr := congrArg (fun a ↦ (r a).val) hdest
  simpa only [Equiv.apply_symm_apply, length_distinctPrefix_empty] using hr.symm

/-- Remove suspended slots while retaining every repeated and fresh actual raw edge. -/
def trace {n : ℕ} : List (Raw.Entry n) → List (RawSemantics.Edge n)
  | [] => []
  | none :: h => trace h
  | some (q, _) :: h => q :: trace h

/-- The trace contains exactly the original raw records, with suspension erased. -/
theorem trace_toFinset {n : ℕ} (h : List (Raw.Entry n)) :
    (trace h).toFinset = Raw.allEdges h := by
  induction h with
  | nil => rfl
  | cons entry h ih => cases entry with
    | none => exact ih
    | some entry =>
      rcases entry with ⟨q, tag⟩
      simp only [trace, List.toFinset_cons, Raw.allEdges, ih]

/-- An active-set restriction concerns only the history-dependent protocol selection. -/
def Supports {n : ℕ} (C : Raw.Protocol n) (A : Finset (Fin n)) : Prop :=
  ∀ h m, Raw.selected C h = some m → m ∈ A

/-- Every raw protocol supports the full active market. -/
theorem supports_univ {n : ℕ} (C : Raw.Protocol n) : Supports C Finset.univ := by
  intro _ m _
  exact Finset.mem_univ m

/-- A fresh recorded comparison is exactly the PR chosen-man transition on its next-ranked edge. -/
theorem recordStep_eq_propose {n : ℕ} (p : Profile n) (female : Arrival.Edge n → ℝ)
    (s : ProposalState n) (q : Arrival.Edge n) (accepted : Bool) (hn : s.next q.2 < n)
    (hrank : (p.manRank q.2 q.1).val = s.next q.2)
    (hcompare : ∀ w m old, p.womanRank w m < p.womanRank w old ↔
      female (w, m) < female (w, old))
    (haccept : Ordinal.accept female s q = accepted) :
    Ordinal.recordStep s (some (q, accepted)) = Schedules.propose p s q.2 hn := by
  have hdest : (p.manRank q.2).symm ⟨s.next q.2, hn⟩ = q.1 := by
    apply (p.manRank q.2).injective
    simp only [Equiv.apply_symm_apply]
    exact Fin.ext hrank.symm
  rw [← haccept]
  unfold Schedules.propose
  rw [hdest]
  cases hh : s.held q.1 <;> simp [Ordinal.recordStep, Ordinal.accept, hh, hcompare]

/-- Exact actual observations induce an admissible raw DA trace and the identical replay state.
The pointwise discovery-order premise is later proved almost surely under the original source law.
-/
theorem observes_admissible_replay {n : ℕ} (C : Raw.Protocol n)
    (streams : Fin n → ℕ → Fin n) (female : Arrival.Edge n → ℝ) (p : Profile n)
    (A : Finset (Fin n)) (hactive : Supports C A)
    (horders : ∀ m, streams m ∈ IIDRanking.rankEvent (p.manRank m))
    (hcompare : ∀ w m old, p.womanRank w m < p.womanRank w old ↔
      female (w, m) < female (w, old))
    (h : List (Raw.Entry n)) (hobs : Raw.Observes C streams female h) :
    RawSemantics.RawAdmissible p A (trace h) ∧
      Raw.state h = RawSemantics.replay p (trace h) := by
  induction h with
  | nil => exact ⟨trivial, rfl⟩
  | cons entry h ih =>
    obtain ⟨hprev, hentry⟩ := hobs
    obtain ⟨hadm, hstate⟩ := ih hprev
    have hfixed := (Raw.observes_iff_valid_draws_rows C streams female h).mp hprev
    have hv : Raw.Valid C h := hfixed.1
    have hprefix := (Raw.draws_iff_prefixes streams h).mp hfixed.2.1
    cases entry with
    | none => exact ⟨hadm, hstate⟩
    | some entry =>
      rcases entry with ⟨q, tag⟩
      have hob := (Raw.observation_eq_iff C streams female h (some (q, tag))).mp hentry
      have hnext : Raw.nextEdge C streams h = some q := hob.1
      have hraw := Raw.nextEdge_some_spec C streams h q hnext
      have hsel := Raw.selected_some_spec C h q.2 hraw.1
      have hel : Schedules.Eligible A (RawSemantics.replay p (trace h)) q.2 := by
        rw [← hstate]
        exact ⟨hactive h q.2 hraw.1, hsel⟩
      have hseen : q ∈ trace h ↔ q ∈ Raw.seenEdges h := by
        rw [← List.mem_toFinset, trace_toFinset, ← Raw.seenEdges_eq_allEdges C h hv]
      cases tag with
      | none =>
        have hmem : q ∈ Raw.seenEdges h := hob.2.1
        have htrace : q ∈ trace h := hseen.mpr hmem
        have hp := (RawSemantics.mem_trace_iff_hasProposed p A hadm q.1 q.2).mp htrace
        refine ⟨⟨hadm, hel, Or.inl hp⟩, ?_⟩
        change Raw.state h = RawSemantics.replay p (q :: trace h)
        rw [RawSemantics.replay_cons_of_mem p A hadm htrace]
        exact hstate
      | some accepted =>
        have hnot : q ∉ Raw.seenEdges h := hob.2.1
        have hq : q.1 ∉ Raw.drawOrder h q.2 := by
          intro hm
          have he := (Raw.mem_drawOrder_iff_allEdges h q.1 q.2).mp hm
          exact hnot ((Raw.seenEdges_eq_allEdges C h hv).symm ▸ he)
        have hrank : (p.manRank q.2 q.1).val = (Raw.state h).next q.2 :=
          (fresh_rank_eq_card (streams q.2) (p.manRank q.2) (horders q.2)
            (Raw.drawOrder h q.2) (hprefix q.2) q.1 hq hraw.2).trans
            (Raw.ordinary_count_eq_distinct_raw C h hv q.2).symm
        have hpnot : ¬ HasProposed p (RawSemantics.replay p (trace h)) q.2 q.1 := by
          intro hp
          exact hnot (hseen.mp
            ((RawSemantics.mem_trace_iff_hasProposed p A hadm q.1 q.2).mpr hp))
        have haccept : Ordinal.accept female (Raw.state h) q = accepted := by
          apply (Ordinal.accept_eq_iff_rows female (Raw.state h) q accepted).mpr
          simpa only [Raw.ordinaryEntry, Option.bind_some, Option.map_some] using hob.2.2
        have hstep := recordStep_eq_propose p female (Raw.state h) q accepted hsel.1
          hrank hcompare haccept
        have hstep' : Raw.state (some (q, some accepted) :: h) =
            Schedules.propose p (RawSemantics.replay p (trace h)) q.2 hel.2.1 := by
          change Ordinal.recordStep (Raw.state h) (some (q, accepted)) = _
          simpa only [hstate] using hstep
        refine ⟨⟨hadm, hel, Or.inr (by simpa only [hstate] using hrank)⟩, ?_⟩
        simpa only [trace, RawSemantics.replay, RawSemantics.rawStep, ite_eq_right hpnot,
          dite_eq_left hel.2.1] using hstep'

/-- The actual raw protocol has admissible repeat-erasure semantics at every finite time. -/
theorem transcript_admissible_replay {n : ℕ} (C : Raw.Protocol n)
    (streams : Fin n → ℕ → Fin n) (female : Arrival.Edge n → ℝ) (p : Profile n)
    (A : Finset (Fin n)) (hactive : Supports C A)
    (horders : ∀ m, streams m ∈ IIDRanking.rankEvent (p.manRank m))
    (hcompare : ∀ w m old, p.womanRank w m < p.womanRank w old ↔
      female (w, m) < female (w, old)) (t : ℕ) :
    RawSemantics.RawAdmissible p A (trace (Raw.transcript C streams female t)) ∧
      Raw.state (Raw.transcript C streams female t) =
        RawSemantics.replay p (trace (Raw.transcript C streams female t)) :=
  observes_admissible_replay C streams female p A hactive horders hcompare _
    ((Raw.observes_iff_transcript C streams female _).mpr (by rw [Raw.transcript_length]))

/-- The exact PR-law preference profile extracted from the original raw source arrays. -/
noncomputable def sourceProfile {n : ℕ}
    (z : (Fin n → ℕ → Fin n) × (Fin n → Fin n → ℝ)) : Profile n :=
  mixedRankProfile IIDRanking.iidRank exponentialRank z

/-- The original women's priorities in the edge convention used by raw observations. -/
def sourceFemale {n : ℕ} (z : (Fin n → ℕ → Fin n) × (Fin n → Fin n → ℝ)) :
    Arrival.Edge n → ℝ := fun q ↦ z.2 q.1 q.2

/-- The actual raw history evaluated on the original mixed IID/exponential source. -/
noncomputable def history {n : ℕ} (C : Raw.Protocol n)
    (z : (Fin n → ℕ → Fin n) × (Fin n → Fin n → ℝ)) (t : ℕ) : List (Raw.Entry n) :=
  Raw.transcript C z.1 (sourceFemale z) t

/-- Every original male stream agrees with its complete extracted discovery rank almost surely. -/
theorem ae_source_orders {n : ℕ} [NeZero n] (P Q : Fin n → Fin n → ℝ≥0)
    (hP : ∀ m w, 0 < P m w) :
    ∀ᵐ z ∂rawInputLaw P Q, ∀ m,
      z.1 m ∈ IIDRanking.rankEvent ((sourceProfile z).manRank m) := by
  have hrow (m : Fin n) :
      ∀ᵐ x ∂(Measure.pi fun m ↦ FirstFresh.iidStream (RandomRanking.ofWeights (P m))),
        x m ∈ IIDRanking.rankEvent (IIDRanking.iidRank (x m)) :=
    (Measure.tendsto_eval_ae_ae (μ := fun m ↦
      FirstFresh.iidStream (RandomRanking.ofWeights (P m))) (i := m)).eventually
        (IIDRanking.ae_rankEvent_iidRank (P m) (hP m))
  exact Measure.quasiMeasurePreserving_fst.ae (Filter.eventually_all.mpr hrow)

/-- All original exponential woman rows are injective almost surely under the actual raw source. -/
theorem ae_source_female_injective {n : ℕ} [NeZero n] (P Q : Fin n → Fin n → ℝ≥0)
    (hQ : ∀ m w, 0 < Q m w) :
    ∀ᵐ z ∂rawInputLaw P Q, ∀ w, Function.Injective (z.2 w) := by
  have (m w : Fin n) : IsProbabilityMeasure (ProbabilityTheory.expMeasure (Q m w : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by exact_mod_cast hQ m w)
  have hrow (w : Fin n) :
      ∀ᵐ x ∂(Measure.pi fun w ↦ Measure.pi fun m ↦
        ProbabilityTheory.expMeasure (Q m w : ℝ)), Function.Injective (x w) :=
    (Measure.tendsto_eval_ae_ae (μ := fun w ↦ Measure.pi fun m ↦
      ProbabilityTheory.expMeasure (Q m w : ℝ)) (i := w)).eventually
        (ae_injective_exponentials (fun m ↦ Q m w) (fun m ↦ hQ m w))
  exact Measure.quasiMeasurePreserving_snd.ae (Filter.eventually_all.mpr hrow)

/-- Under the actual raw input law, all finite raw histories have exact PR repeat-erasure semantics.
Neither admissibility nor a finite-prefix ranking agreement is assumed in this conclusion.
-/
theorem ae_transcript_bridge {n : ℕ} [NeZero n] (P Q : Fin n → Fin n → ℝ≥0)
    (hP : ∀ m w, 0 < P m w) (hQ : ∀ m w, 0 < Q m w)
    (C : Raw.Protocol n) (A : Finset (Fin n)) (hactive : Supports C A) :
    ∀ᵐ z ∂rawInputLaw P Q, ∀ t,
      RawSemantics.RawAdmissible (sourceProfile z) A (trace (history C z t)) ∧
      Raw.state (history C z t) =
        RawSemantics.replay (sourceProfile z) (trace (history C z t)) := by
  filter_upwards [ae_source_orders P Q hP, ae_source_female_injective P Q hQ] with z hz hzi
  intro t
  apply transcript_admissible_replay C z.1 (sourceFemale z) (sourceProfile z) A hactive hz
  intro w m old
  exact exponentialRank_lt_iff (z.2 w) (hzi w) m old

/-- Actual raw states are ordinary DA states for the chosen active entrants, almost surely. -/
theorem ae_reachable {n : ℕ} [NeZero n] (P Q : Fin n → Fin n → ℝ≥0)
    (hP : ∀ m w, 0 < P m w) (hQ : ∀ m w, 0 < Q m w)
    (C : Raw.Protocol n) (A : Finset (Fin n)) (hactive : Supports C A) :
    ∀ᵐ z ∂rawInputLaw P Q, ∀ t, Schedules.Reachable (sourceProfile z) A
      (Raw.state (history C z t)) := by
  filter_upwards [ae_transcript_bridge P Q hP hQ C A hactive] with z hz
  intro t
  rw [(hz t).2]
  exact RawSemantics.replay_reachable (sourceProfile z) A (hz t).1

/-- Any terminal partial-entrant raw state is the canonical active-set DA state almost surely. -/
theorem ae_terminal_eq_active {n : ℕ} [NeZero n] (P Q : Fin n → Fin n → ℝ≥0)
    (hP : ∀ m w, 0 < P m w) (hQ : ∀ m w, 0 < Q m w)
    (C : Raw.Protocol n) (A : Finset (Fin n)) (hactive : Supports C A) :
    ∀ᵐ z ∂rawInputLaw P Q, ∀ t, Schedules.Terminal A (Raw.state (history C z t)) →
      Raw.state (history C z t) = Schedules.activeDeferredAcceptance (sourceProfile z) A := by
  filter_upwards [ae_transcript_bridge P Q hP hQ C A hactive] with z hz
  intro t hterm
  rw [(hz t).2] at hterm ⊢
  exact RawSemantics.replay_eq_active_of_terminal (sourceProfile z) A (hz t).1 hterm

/-- Actual full-market coupon completion is precisely terminal DA and realizes the exact PR state.
This is a finite-time equivalence; it asserts no random hitting-time bound.
-/
theorem ae_coupon_terminal_pr {n : ℕ} [NeZero n] (P Q : Fin n → Fin n → ℝ≥0)
    (hP : ∀ m w, 0 < P m w) (hQ : ∀ m w, 0 < Q m w) (C : Raw.Protocol n) :
    ∀ᵐ z ∂rawInputLaw P Q, ∀ t,
      (Schedules.Terminal Finset.univ (Raw.state (history C z t)) ↔
        ∀ w, ∃ m, (w, m) ∈ trace (history C z t)) ∧
      ((∀ w, ∃ m, (w, m) ∈ trace (history C z t)) →
        Raw.state (history C z t) = deferredAcceptance (sourceProfile z)) := by
  filter_upwards [ae_transcript_bridge P Q hP hQ C Finset.univ (supports_univ C)] with z hz
  intro t
  constructor
  · rw [(hz t).2]
    exact RawSemantics.terminal_univ_iff_all_hit (sourceProfile z) (hz t).1
  · intro hall
    exact (hz t).2.trans (RawSemantics.replay_eq_pr_of_all_hit (sourceProfile z) (hz t).1 hall)

/-- Raw attempts equal exact PR proposals plus discarded repeats at actual coupon completion. -/
theorem ae_coupon_proposal_counts {n : ℕ} [NeZero n] (P Q : Fin n → Fin n → ℝ≥0)
    (hP : ∀ m w, 0 < P m w) (hQ : ∀ m w, 0 < Q m w) (C : Raw.Protocol n) :
    ∀ᵐ z ∂rawInputLaw P Q, ∀ t,
      (∀ w, ∃ m, (w, m) ∈ trace (history C z t)) →
      RawSemantics.distinctCount (trace (history C z t)) = numProposals (sourceProfile z) ∧
      (trace (history C z t)).length = numProposals (sourceProfile z) +
        RawSemantics.repeatCount (trace (history C z t)) := by
  filter_upwards [ae_transcript_bridge P Q hP hQ C Finset.univ (supports_univ C)] with z hz
  intro t hall
  exact ⟨RawSemantics.distinctCount_eq_pr_numProposals_of_all_hit (sourceProfile z) (hz t).1 hall,
    RawSemantics.length_eq_pr_numProposals_add_repeats_of_all_hit (sourceProfile z) (hz t).1 hall⟩

end Ashlagi.RawBridge
