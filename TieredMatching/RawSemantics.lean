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

public import TieredMatching.Schedules
public import Mathlib.Data.List.Dedup

/-!
# Deterministic repeat-erasure semantics

Traces are newest first and record `(woman, man)` edges. Every record is made by an eligible
active man. A repeated destination leaves the state unchanged; a new destination must be the
next entry in that man's strict list. No trace may continue after its state is terminal.
This module proves no random-destination law or finite stopping-time estimate.
-/

@[expose] public section

namespace TieredMatching.RawSemantics

open StableMarriage Schedules

/-- A raw proposal records its destination woman followed by its proposing man. -/
abbrev Edge (n : ℕ) := Fin n × Fin n

/-- A repeated proposal is ignored; every fresh record uses the exact chosen-man transition. -/
def rawStep {n : ℕ} (p : Profile n) (s : ProposalState n) (e : Edge n) : ProposalState n :=
  if HasProposed p s e.2 e.1 then s
  else if hn : s.next e.2 < n then propose p s e.2 hn else s

/-- Replay a newest-first finite raw trace from the empty state. -/
def replay {n : ℕ} (p : Profile n) : List (Edge n) → ProposalState n
  | [] => ⟨fun _ ↦ 0, fun _ ↦ none⟩
  | e :: t => rawStep p (replay p t) e

/-- Every raw record has an eligible active proposer. Its destination either repeats a
previous query or has the exact next rank in the proposer's strict list. -/
def RawAdmissible {n : ℕ} (p : Profile n) (A : Finset (Fin n)) : List (Edge n) → Prop
  | [] => True
  | e :: t => RawAdmissible p A t ∧ Eligible A (replay p t) e.2 ∧
      (HasProposed p (replay p t) e.2 e.1 ∨
        (p.manRank e.2 e.1).val = (replay p t).next e.2)

/-- Ignoring repeats leaves a reachable ordinary DA state after every admissible raw prefix. -/
theorem replay_reachable {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {t : List (Edge n)} (ht : RawAdmissible p A t) : Reachable p A (replay p t) := by
  induction t with
  | nil => exact Reachable.initial
  | cons e t ih =>
    rcases ht with ⟨ht, hm, _⟩
    have hr := ih ht
    by_cases hp : HasProposed p (replay p t) e.2 e.1
    · simpa only [replay, rawStep, ite_eq_left hp] using hr
    · simpa only [replay, rawStep, ite_eq_right hp, dite_eq_left hm.2.1] using
        Reachable.step hr e.2 hm

/-- The exact queried relation after a chosen-man transition adds precisely its next edge. -/
theorem hasProposed_propose_iff {n : ℕ} (p : Profile n) (s : ProposalState n)
    (m : Fin n) (hn : s.next m < n) (k v : Fin n) :
    HasProposed p (propose p s m hn) k v ↔ HasProposed p s k v ∨
      k = m ∧ v = (p.manRank m).symm ⟨s.next m, hn⟩ :=
  hasProposed_update_iff p s m hn (propose p s m hn).held k v

/-- A raw edge is seen exactly when the man's PR counter includes that destination. -/
theorem mem_trace_iff_hasProposed {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {t : List (Edge n)} (ht : RawAdmissible p A t) (w m : Fin n) :
    (w, m) ∈ t ↔ HasProposed p (replay p t) m w := by
  induction t generalizing w m with
  | nil => simp [replay, HasProposed]
  | cons e t ih =>
    rcases ht with ⟨ht, hm, hd⟩
    rcases e with ⟨v, k⟩
    change Eligible A (replay p t) k at hm
    change HasProposed p (replay p t) k v ∨
      (p.manRank k v).val = (replay p t).next k at hd
    by_cases hp : HasProposed p (replay p t) k v
    · have hmem : (v, k) ∈ t := (ih ht v k).mpr hp
      simp only [List.mem_cons, replay, rawStep, ite_eq_left hp]
      rw [← ih ht w m]
      constructor
      · rintro (heq | h)
        · exact heq ▸ hmem
        · exact h
      · exact Or.inr
    · have hrank := hd.resolve_left hp
      have hv : v = (p.manRank k).symm ⟨(replay p t).next k, hm.2.1⟩ := by
        apply (p.manRank k).injective
        simp only [Equiv.apply_symm_apply]
        exact Fin.ext hrank
      simp only [List.mem_cons, replay, rawStep, ite_eq_right hp, dite_eq_left hm.2.1]
      rw [hasProposed_propose_iff, ← ih ht w m]
      simp only [Prod.mk.injEq]
      constructor
      · rintro (⟨hw, hmk⟩ | hold)
        · exact Or.inr ⟨hmk, hw.trans hv⟩
        · exact Or.inl hold
      · rintro (hold | ⟨hmk, hw⟩)
        · exact Or.inr hold
        · exact Or.inl ⟨hw.trans hv.symm, hmk⟩

/-- Erasing repeated records preserves the exact replay state. Since traces are newest first,
`List.dedup` retains the first chronological occurrence of each edge. -/
theorem replay_dedup_eq {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {t : List (Edge n)} (ht : RawAdmissible p A t) : replay p t.dedup = replay p t := by
  induction t with
  | nil => rfl
  | cons e t ih =>
    rcases ht with ⟨ht, hm, hd⟩
    by_cases he : e ∈ t
    · have hp := (mem_trace_iff_hasProposed p A ht e.1 e.2).mp he
      rw [List.dedup_cons_of_mem he, ih ht]
      simp only [replay, rawStep, ite_eq_left hp]
    · rw [List.dedup_cons_of_notMem he]
      simp only [replay, ih ht]

/-- The repeat-erased trace is an admissible ordinary execution for the same active men. -/
theorem dedup_admissible {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {t : List (Edge n)} (ht : RawAdmissible p A t) : RawAdmissible p A t.dedup := by
  induction t with
  | nil => trivial
  | cons e t ih =>
    rcases ht with ⟨ht, hm, hd⟩
    by_cases he : e ∈ t
    · rw [List.dedup_cons_of_mem he]
      exact ih ht
    · rw [List.dedup_cons_of_notMem he]
      change RawAdmissible p A t.dedup ∧ Eligible A (replay p t.dedup) e.2 ∧ _
      rw [replay_dedup_eq p A ht]
      exact ⟨ih ht, hm, hd⟩

/-- Every genuine proposal increments the sum of the exact PR counters by one. -/
theorem propose_potential_succ {n : ℕ} (p : Profile n) (s : ProposalState n)
    (m : Fin n) (hn : s.next m < n) : potential (propose p s m hn) = potential s + 1 := by
  classical
  have hold : (∑ k : Fin n, s.next k) = s.next m +
      ∑ k ∈ Finset.univ \ {m}, s.next k := by
    simpa only [Function.update_eq_self] using
      Finset.sum_update_of_mem (Finset.mem_univ m) s.next (s.next m)
  change (∑ k : Fin n, Function.update s.next m (s.next m + 1) k) = (∑ k, s.next k) + 1
  rw [Finset.sum_update_of_mem (Finset.mem_univ m), hold]
  omega

/-- Number of distinct raw edges, irrespective of chronological repetitions. -/
def distinctCount {n : ℕ} (t : List (Edge n)) : ℕ := t.toFinset.card

/-- Number of raw attempts discarded by repeat erasure. -/
def repeatCount {n : ℕ} (t : List (Edge n)) : ℕ := t.length - distinctCount t

/-- Exact distinct-edge counting agrees with the sum of ordinary proposal counters. -/
theorem distinctCount_eq_potential {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {t : List (Edge n)} (ht : RawAdmissible p A t) :
    distinctCount t = potential (replay p t) := by
  induction t with
  | nil => simp [distinctCount, replay, potential]
  | cons e t ih =>
    rcases ht with ⟨ht, hm, hd⟩
    by_cases he : e ∈ t
    · have hp := (mem_trace_iff_hasProposed p A ht e.1 e.2).mp he
      have hmem : e ∈ t.toFinset := by simpa using he
      simpa only [distinctCount, List.toFinset_cons, Finset.insert_eq_of_mem hmem,
        replay, rawStep, ite_eq_left hp] using ih ht
    · have hp : ¬ HasProposed p (replay p t) e.2 e.1 :=
        fun h ↦ he ((mem_trace_iff_hasProposed p A ht e.1 e.2).mpr h)
      have hmem : e ∉ t.toFinset := by simpa using he
      simp only [distinctCount, List.toFinset_cons, Finset.card_insert_of_notMem hmem,
        replay, rawStep, ite_eq_right hp, dite_eq_left hm.2.1, propose_potential_succ]
      exact congrArg (fun k ↦ k + 1) (ih ht)

/-- Raw length is exactly ordinary distinct proposals plus discarded repeated attempts. -/
theorem length_eq_potential_add_repeats {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {t : List (Edge n)} (ht : RawAdmissible p A t) :
    t.length = potential (replay p t) + repeatCount t := by
  have hcard := t.toFinset_card_le
  rw [← distinctCount_eq_potential p A ht]
  unfold repeatCount distinctCount
  omega

/-- The repeat-erased execution has exactly one record per genuine proposal. -/
theorem dedup_length_eq_potential {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {t : List (Edge n)} (ht : RawAdmissible p A t) :
    t.dedup.length = potential (replay p t) := by
  rw [← distinctCount_eq_potential p A ht]
  exact t.card_toFinset.symm

/-- An admissible raw trace cannot be extended after its replay is terminal. -/
theorem not_admissible_cons_of_terminal {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    (t : List (Edge n)) (e : Edge n) (hterm : Terminal A (replay p t)) :
    ¬ RawAdmissible p A (e :: t) := by
  intro ht
  exact hterm e.2 ht.2.1

/-- Women who have received at least one raw attempt. -/
noncomputable def hitWomen {n : ℕ} (t : List (Edge n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun w ↦ ∃ m, (w, m) ∈ t

/-- Women currently holding a man. -/
noncomputable def occupied {n : ℕ} (s : ProposalState n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun w ↦ ∃ m, s.held w = some m

/-- Men currently held by some woman. -/
noncomputable def heldMen {n : ℕ} (s : ProposalState n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun m ↦ ∃ w, s.held w = some m

/-- A raw hit is equivalent to a nonempty current holding; rejections cannot empty a woman. -/
theorem hit_iff_held {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {t : List (Edge n)} (ht : RawAdmissible p A t) (w : Fin n) :
    (∃ m, (w, m) ∈ t) ↔ ∃ m, (replay p t).held w = some m := by
  have hb := (reachable_valid p A (replay_reachable p A ht)).best
  constructor
  · rintro ⟨m, hm⟩
    have hp := (mem_trace_iff_hasProposed p A ht w m).mp hm
    obtain ⟨k, hk, _⟩ := (hb w).2 m hp
    exact ⟨k, hk⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, (mem_trace_iff_hasProposed p A ht w m).mpr ((hb w).1 m hm)⟩

/-- The raw set of hit women is exactly the currently occupied set. -/
theorem hitWomen_eq_occupied {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {t : List (Edge n)} (ht : RawAdmissible p A t) : hitWomen t = occupied (replay p t) := by
  classical
  ext w
  simpa only [hitWomen, occupied, Finset.mem_filter, Finset.mem_univ, true_and] using
    hit_iff_held p A ht w

/-- Only active entrants can be held in an admissible ordinary state. -/
theorem heldMen_subset_active {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {s : ProposalState n} (hs : Reachable p A s) : heldMen s ⊆ A := by
  classical
  intro m hm
  obtain ⟨w, hw⟩ := by simpa only [heldMen, Finset.mem_filter,
    Finset.mem_univ, true_and] using hm
  exact held_active p A hs hw

/-- Unique holdings give equal numbers of occupied women and held men. -/
theorem occupied_card_eq_heldMen_card {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {s : ProposalState n} (hs : Reachable p A s) : (occupied s).card = (heldMen s).card := by
  classical
  have hv := reachable_valid p A hs
  have hex (w : Fin n) (hw : w ∈ occupied s) : ∃ m, s.held w = some m := by
    simpa only [occupied, Finset.mem_filter, Finset.mem_univ, true_and] using hw
  let f : (w : Fin n) → w ∈ occupied s → Fin n := fun w hw ↦ Classical.choose (hex w hw)
  have hf (w : Fin n) (hw : w ∈ occupied s) : s.held w = some (f w hw) :=
    Classical.choose_spec (hex w hw)
  apply Finset.card_bij f
  · intro w hw
    simp only [heldMen, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hf w hw⟩
  · intro w hw v hv' heq
    exact hv.held_injective w v (f w hw) (hf w hw) (by rw [heq]; exact hf v hv')
  · intro m hm
    obtain ⟨w, hw⟩ := by simpa only [heldMen, Finset.mem_filter,
      Finset.mem_univ, true_and] using hm
    have hw' : w ∈ occupied s := by
      simp only [occupied, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨m, hw⟩
    exact ⟨w, hw', Option.some.inj ((hf w hw').symm.trans hw)⟩

/-- Termination is equivalent to holding every active entrant. -/
theorem terminal_iff_heldMen_eq_active {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {s : ProposalState n} (hs : Reachable p A s) : Terminal A s ↔ heldMen s = A := by
  classical
  constructor
  · intro hterm
    ext m
    simpa only [heldMen, Finset.mem_filter, Finset.mem_univ, true_and] using
      terminal_held_iff_active p A hs hterm m
  · intro heq m hm
    have hh : m ∈ heldMen s := heq.symm ▸ hm.1
    obtain ⟨w, hw⟩ := by simpa only [heldMen, Finset.mem_filter,
      Finset.mem_univ, true_and] using hh
    exact hm.2.2 w hw

/-- A partial-entrant ordinary state is terminal exactly when its occupied count equals
the number of active men. This includes the empty active set. -/
theorem terminal_iff_occupied_card {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {s : ProposalState n} (hs : Reachable p A s) :
    Terminal A s ↔ (occupied s).card = A.card := by
  constructor
  · intro ht
    rw [occupied_card_eq_heldMen_card p A hs, (terminal_iff_heldMen_eq_active p A hs).mp ht]
  · intro hc
    have hsub := heldMen_subset_active p A hs
    have hcard : A.card ≤ (heldMen s).card := by
      rw [← occupied_card_eq_heldMen_card p A hs]
      exact hc.ge
    exact (terminal_iff_heldMen_eq_active p A hs).mpr (Finset.eq_of_subset_of_card_le hsub hcard)

/-- The exact raw completion test for partial active sets counts the women ever hit. -/
theorem terminal_iff_hitWomen_card {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {t : List (Edge n)} (ht : RawAdmissible p A t) :
    Terminal A (replay p t) ↔ (hitWomen t).card = A.card := by
  rw [hitWomen_eq_occupied p A ht]
  exact terminal_iff_occupied_card p A (replay_reachable p A ht)

/-- With all men active, raw DA terminates exactly when every woman has been hit.
This is a deterministic coupon-completion equivalence, not a random stopping-time claim. -/
theorem terminal_univ_iff_all_hit {n : ℕ} (p : Profile n)
    {t : List (Edge n)} (ht : RawAdmissible p Finset.univ t) :
    Terminal Finset.univ (replay p t) ↔ ∀ w, ∃ m, (w, m) ∈ t := by
  classical
  rw [terminal_iff_hitWomen_card p Finset.univ ht]
  constructor
  · intro hc
    have heq : hitWomen t = Finset.univ := (hitWomen t).eq_univ_of_card (by simpa using hc)
    intro w
    have hw : w ∈ hitWomen t := by rw [heq]; exact Finset.mem_univ _
    simpa only [hitWomen, Finset.mem_filter, Finset.mem_univ, true_and] using hw
  · intro hall
    have heq : hitWomen t = Finset.univ := by
      ext w
      simp only [hitWomen, Finset.mem_filter, Finset.mem_univ, true_and]
      exact iff_true_intro (hall w)
    rw [heq]

/-- Any explicitly terminal raw trace realizes the canonical partial-entrant DA state. -/
theorem replay_eq_active_of_terminal {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {t : List (Edge n)} (ht : RawAdmissible p A t) (hterm : Terminal A (replay p t)) :
    replay p t = activeDeferredAcceptance p A :=
  terminal_state_eq_active p A (replay_reachable p A ht) hterm

/-- Full raw coupon completion realizes the exact PR's terminal state and proposal counters. -/
theorem replay_eq_pr_of_all_hit {n : ℕ} (p : Profile n)
    {t : List (Edge n)} (ht : RawAdmissible p Finset.univ t)
    (hall : ∀ w, ∃ m, (w, m) ∈ t) : replay p t = deferredAcceptance p :=
  terminal_state_eq_pr p (replay_reachable p Finset.univ ht)
    ((terminal_univ_iff_all_hit p ht).mpr hall)

/-- An admissible full raw trace stops at completion; no repeated attempt is permitted afterward. -/
theorem not_admissible_cons_of_all_hit {n : ℕ} (p : Profile n)
    {t : List (Edge n)} (ht : RawAdmissible p Finset.univ t)
    (hall : ∀ w, ∃ m, (w, m) ∈ t) (e : Edge n) :
    ¬ RawAdmissible p Finset.univ (e :: t) :=
  not_admissible_cons_of_terminal p Finset.univ t e ((terminal_univ_iff_all_hit p ht).mpr hall)

/-- The raw seen-edge finite set equals the exact bounded-prefix queried relation. -/
theorem toFinset_eq_proposedPairs {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {t : List (Edge n)} (ht : RawAdmissible p A t) :
    t.toFinset = Finset.univ.filter (fun e : Edge n ↦
      HasProposed p (replay p t) e.2 e.1) := by
  ext e
  simpa only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and] using
    mem_trace_iff_hasProposed p A ht e.1 e.2

/-- A repeated edge is an exact identity step on an admissible raw prefix. -/
theorem replay_cons_of_mem {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {t : List (Edge n)} (ht : RawAdmissible p A t) {e : Edge n} (he : e ∈ t) :
    replay p (e :: t) = replay p t := by
  have hp := (mem_trace_iff_hasProposed p A ht e.1 e.2).mp he
  simp only [replay, rawStep, ite_eq_left hp]

/-- Every fresh admissible record makes exactly one ordinary chosen-man update. -/
theorem replay_cons_of_notMem {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {t : List (Edge n)} {e : Edge n} (ht : RawAdmissible p A (e :: t)) (he : e ∉ t) :
    replay p (e :: t) = propose p (replay p t) e.2 ht.2.1.2.1 := by
  have hp : ¬ HasProposed p (replay p t) e.2 e.1 :=
    fun h ↦ he ((mem_trace_iff_hasProposed p A ht.1 e.1 e.2).mpr h)
  simp only [replay, rawStep, ite_eq_right hp, dite_eq_left ht.2.1.2.1]

/-- A completed full raw trace has the exact PR's total distinct-proposal count. -/
theorem distinctCount_eq_pr_numProposals_of_all_hit {n : ℕ} (p : Profile n)
    {t : List (Edge n)} (ht : RawAdmissible p Finset.univ t)
    (hall : ∀ w, ∃ m, (w, m) ∈ t) : distinctCount t = numProposals p := by
  rw [distinctCount_eq_potential p Finset.univ ht, replay_eq_pr_of_all_hit p ht hall]
  rfl

/-- At coupon completion, raw total attempts equal exact ordinary PR proposals plus repeats. -/
theorem length_eq_pr_numProposals_add_repeats_of_all_hit {n : ℕ} (p : Profile n)
    {t : List (Edge n)} (ht : RawAdmissible p Finset.univ t)
    (hall : ∀ w, ∃ m, (w, m) ∈ t) : t.length = numProposals p + repeatCount t := by
  have hh := length_eq_potential_add_repeats p Finset.univ ht
  rw [replay_eq_pr_of_all_hit p ht hall] at hh
  exact hh

end TieredMatching.RawSemantics
