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

public import Ashlagi.DA
public import Ashlagi.AdaptiveAllocation
public import Ashlagi.ExponentialOrder

/-! # The concrete nonanticipating DA arrival-slot policy -/

@[expose] public section

namespace Ashlagi.Arrival

open StableMarriage

/-- Coordinates are oriented as woman then man. The same finite type indexes source slots. -/
abbrev Edge (n : ℕ) := Fin n × Fin n

/-- The PR state together with the raw priority of each currently held man. Values at women
without holders are immaterial. -/
structure RawState (n : ℕ) where
  state : ProposalState n
  score : Fin n → ℝ

/-- The empty initial state. -/
def initial (n : ℕ) : RawState n := ⟨⟨fun _ ↦ 0, fun _ ↦ none⟩, fun _ ↦ 0⟩

/-- The exact first-free-man choice and next candidate used by the PR. -/
def nextEdge {n : ℕ} (P : Fin n → Equiv.Perm (Fin n)) (s : ProposalState n) :
    Option (Edge n) :=
  match (List.finRange n).find? (fun m ↦ s.next m < n ∧ ∀ w, s.held w ≠ some m) with
  | none => none
  | some m => if h : s.next m < n then some ((P m).symm ⟨s.next m, h⟩, m) else none

/-- Process the next proposal using its newly exposed raw priority. -/
noncomputable def advance {n : ℕ} (P : Fin n → Equiv.Perm (Fin n)) (s : RawState n)
    (value : ℝ) :
    RawState n :=
  match nextEdge P s.state with
  | none => s
  | some (w, m) =>
    let accept := match s.state.held w with
      | none => true
      | some _ => decide (value < s.score w)
    ⟨⟨Function.update s.state.next m (s.state.next m + 1),
      if accept then Function.update s.state.held w (some m) else s.state.held⟩,
      if accept then Function.update s.score w value else s.score⟩

/-- The first still unused source coordinate in the target woman's target men's tier.
The inverse allocation of the target is a total fallback, used only on malformed histories. -/
def sourceSlot {n J : ℕ} (manTier : Fin n → Fin J) (q : Edge n)
    (reindex : Equiv.Perm (Edge n)) (seen : List (Edge n)) : Edge n :=
  match (List.finRange n).find?
      (fun m ↦ manTier m = manTier q.2 ∧ (q.1, m) ∉ seen) with
  | some m => (q.1, m)
  | none => reindex q

/-- A source swap for the next actual edge, or an identity swap after termination. -/
def pairForState {n J : ℕ} [NeZero n] (P : Fin n → Equiv.Perm (Fin n))
    (manTier : Fin n → Fin J) (s : RawState n)
    (reindex : Equiv.Perm (Edge n)) (seen : List (Edge n)) : Edge n × Edge n :=
  match nextEdge P s.state with
  | none => (default, default)
  | some q => (sourceSlot manTier q reindex seen, reindex q)

/-- Replay a revealed source history, maintaining the raw DA state and the complete map from
output edge labels to source slots. The recorded keys matter only through the seen set. -/
noncomputable def replay {n J : ℕ} [NeZero n] (P : Fin n → Equiv.Perm (Fin n))
    (manTier : Fin n → Fin J) : List (Edge n × ℝ) → RawState n × Equiv.Perm (Edge n)
  | [] => (initial n, Equiv.refl _)
  | (_, value) :: h =>
    let old := replay P manTier h
    let pair := pairForState P manTier old.1 old.2 (h.map Prod.fst)
    (advance P old.1 value, old.2.trans (Equiv.swap pair.1 pair.2))

/-- The concrete policy is a function of the revealed source history alone. -/
noncomputable def pick {n J : ℕ} [NeZero n] (P : Fin n → Equiv.Perm (Fin n))
    (manTier : Fin n → Fin J) (h : List (Edge n × ℝ)) : Edge n × Edge n :=
  let old := replay P manTier h
  pairForState P manTier old.1 old.2 (h.map Prod.fst)

/-- The replayed labeling map is the exact map used by the generic allocation theorem. -/
theorem replay_reindex {n J : ℕ} [NeZero n] (P : Fin n → Equiv.Perm (Fin n))
    (manTier : Fin n → Fin J) (h : List (Edge n × ℝ)) :
    (replay P manTier h).2 = allocationReindex (pick P manTier) h := by
  induction h with
  | nil => rfl
  | cons entry h ih =>
    change (replay P manTier h).2.trans
      (Equiv.swap (pick P manTier h).1 (pick P manTier h).2) =
        (allocationReindex (pick P manTier) h).trans
          (Equiv.swap (pick P manTier h).1 (pick P manTier h).2)
    rw [ih]

/-- Once no edge remains, further raw observations have no effect on the DA state. -/
theorem advance_of_nextEdge_none {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (s : RawState n) (h : nextEdge P s.state = none) (value : ℝ) :
    advance P s value = s := by
  simp only [advance, h]

/-- A selected edge is the next strict-list entry of a currently free man. -/
theorem nextEdge_some_spec {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (s : ProposalState n) (q : Edge n) (hq : nextEdge P s = some q) :
    ∃ m, ∃ hn : s.next m < n, q = ((P m).symm ⟨s.next m, hn⟩, m) ∧
      ∀ w, s.held w ≠ some m := by
  unfold nextEdge at hq
  split at hq
  · contradiction
  · rename_i m hfind
    split at hq
    · rename_i hn
      have hbool := List.find?_some hfind
      have hm : s.next m < n ∧ ∀ w, s.held w ≠ some m := by simpa using hbool
      exact ⟨m, hn, (Option.some.inj hq).symm, hm.2⟩
    · contradiction

/-- The queried labels are precisely the edges below their men's strict-list counters. -/
def Queried {n : ℕ} (P : Fin n → Equiv.Perm (Fin n)) (s : RawState n) (q : Edge n) : Prop :=
  (P q.2 q.1).val < s.state.next q.2

/-- The next actual edge has not yet been queried. -/
theorem nextEdge_not_queried {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (s : RawState n) (q : Edge n) (hq : nextEdge P s.state = some q) : ¬ Queried P s q := by
  obtain ⟨m, hn, rfl, _⟩ := nextEdge_some_spec P s.state q hq
  simp [Queried]

/-- A raw advance adds exactly its selected edge to the queried-label set. -/
theorem queried_advance_iff {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (s : RawState n) (value : ℝ) (q q' : Edge n) (hq : nextEdge P s.state = some q) :
    Queried P (advance P s value) q' ↔ Queried P s q' ∨ q' = q := by
  obtain ⟨m, hn, rfl, _⟩ := nextEdge_some_spec P s.state q hq
  simp only [advance, hq]
  change HasProposed ⟨P, fun _ ↦ Equiv.refl _⟩
      ⟨Function.update s.state.next m (s.state.next m + 1), _⟩ q'.2 q'.1 ↔
    HasProposed ⟨P, fun _ ↦ Equiv.refl _⟩ s.state q'.2 q'.1 ∨
      q' = ((P m).symm ⟨s.state.next m, hn⟩, m)
  rw [hasProposed_update_iff _ _ _ hn]
  simp only [Prod.ext_iff, and_comm]

/-- A source block consists of one woman and one men's tier. -/
def block {n J : ℕ} (manTier : Fin n → Fin J) (q : Edge n) : Fin n × Fin J :=
  (q.1, manTier q.2)

/-- A valid reindexing sends every output label to a source slot in its block. -/
def PreservesBlocks {n J : ℕ} (manTier : Fin n → Fin J)
    (reindex : Equiv.Perm (Edge n)) : Prop :=
  ∀ q, block manTier (reindex q) = block manTier q

/-- The canonical source slot has the same block as the target label. -/
theorem sourceSlot_block {n J : ℕ} (manTier : Fin n → Fin J) (q : Edge n)
    (reindex : Equiv.Perm (Edge n)) (seen : List (Edge n))
    (hπ : PreservesBlocks manTier reindex) :
    block manTier (sourceSlot manTier q reindex seen) = block manTier q := by
  unfold sourceSlot
  split
  · rename_i m hfind
    have hbool := List.find?_some hfind
    have hm : manTier m = manTier q.2 ∧ (q.1, m) ∉ seen := by simpa using hbool
    exact Prod.ext rfl hm.1
  · exact hπ q

/-- If the target's present source slot is unseen, so is the selected canonical source slot. -/
theorem sourceSlot_fresh {n J : ℕ} (manTier : Fin n → Fin J) (q : Edge n)
    (reindex : Equiv.Perm (Edge n)) (seen : List (Edge n)) (hb : reindex q ∉ seen) :
    sourceSlot manTier q reindex seen ∉ seen := by
  unfold sourceSlot
  split
  · rename_i m hfind
    have hbool := List.find?_some hfind
    have hm : manTier m = manTier q.2 ∧ (q.1, m) ∉ seen := by simpa using hbool
    exact hm.2
  · exact hb

/-- Every chosen swap stays within one woman/tier block, including identity padding. -/
theorem pairForState_block {n J : ℕ} [NeZero n] (P : Fin n → Equiv.Perm (Fin n))
    (manTier : Fin n → Fin J) (s : RawState n)
    (reindex : Equiv.Perm (Edge n)) (seen : List (Edge n))
    (hπ : PreservesBlocks manTier reindex) :
    block manTier (pairForState P manTier s reindex seen).1 =
      block manTier (pairForState P manTier s reindex seen).2 := by
  unfold pairForState
  split
  · rfl
  · rename_i q hq
    exact (sourceSlot_block manTier q reindex seen hπ).trans (hπ q).symm

/-- A swap of two coordinates from the same block preserves every coordinate's block. -/
theorem block_swap {n J : ℕ} (manTier : Fin n → Fin J) (a b q : Edge n)
    (hab : block manTier a = block manTier b) :
    block manTier (Equiv.swap a b q) = block manTier q := by
  by_cases ha : q = a
  · subst q
    simpa only [Equiv.swap_apply_left] using hab.symm
  · by_cases hb : q = b
    · subst q
      simpa only [Equiv.swap_apply_right] using hab
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

/-- The complete labeling permutation preserves blocks for every history, not merely for
histories generated by the algorithm. -/
theorem replay_preservesBlocks {n J : ℕ} [NeZero n] (P : Fin n → Equiv.Perm (Fin n))
    (manTier : Fin n → Fin J) (h : List (Edge n × ℝ)) :
    PreservesBlocks manTier (replay P manTier h).2 := by
  induction h with
  | nil => exact fun _ ↦ rfl
  | cons entry h ih =>
    intro q
    change block manTier (Equiv.swap (pick P manTier h).1 (pick P manTier h).2
      ((replay P manTier h).2 q)) = block manTier q
    have hp : block manTier (pick P manTier h).1 = block manTier (pick P manTier h).2 :=
      pairForState_block P manTier (replay P manTier h).1 (replay P manTier h).2
        (h.map Prod.fst) ih
    rw [block_swap manTier _ _ _ hp]
    exact ih q

/-- The concrete policy's endpoints have equal exponential rates whenever rates depend only
on the man tier. This is a purely deterministic statement about all possible histories. -/
theorem pick_block {n J : ℕ} [NeZero n] (P : Fin n → Equiv.Perm (Fin n))
    (manTier : Fin n → Fin J) (h : List (Edge n × ℝ)) :
    block manTier (pick P manTier h).1 = block manTier (pick P manTier h).2 :=
  pairForState_block P manTier _ _ _ (replay_preservesBlocks P manTier h)

/-- Swapping two fresh source coordinates and then recording the first one adds precisely
the pre-swap second coordinate to the observed preimage. -/
theorem swap_mem_cons_iff {ι : Type*} [DecidableEq ι] (a b u : ι) (seen : List ι)
    (ha : a ∉ seen) (hb : b ∉ seen) :
    Equiv.swap a b u ∈ a :: seen ↔ u ∈ seen ∨ u = b := by
  by_cases hua : u = a
  · subst u
    simp [ha, hb, eq_comm]
  · by_cases hub : u = b
    · subst u
      simp
    · simp [Equiv.swap_apply_of_ne_of_ne hua hub, hua, hub]

/-- Before termination, source observations are exactly the inverse images of labels whose
strict-list counters have been traversed. Identity padding after termination is harmless. -/
theorem history_seen_queried_or_stopped {n J : ℕ} [NeZero n]
    (P : Fin n → Equiv.Perm (Fin n)) (manTier : Fin n → Fin J)
    (x : Edge n → ℝ) (t : ℕ) :
    let h := allocationHistory (pick P manTier) x t
    let old := replay P manTier h
    nextEdge P old.1.state = none ∨
      ∀ q, old.2 q ∈ h.map Prod.fst ↔ Queried P old.1 q := by
  induction t with
  | zero =>
    right
    intro q
    simp [allocationHistory, queryHistory, replay, initial, Queried]
  | succ t ih =>
    let h := allocationHistory (pick P manTier) x t
    have hhist : allocationHistory (pick P manTier) x (t + 1) =
        ((pick P manTier h).1, x (pick P manTier h).1) :: h := rfl
    rw [hhist]
    rcases ih with hstop | hseen
    · left
      change nextEdge P (advance P (replay P manTier h).1 _).state = none
      rw [advance_of_nextEdge_none P _ hstop]
      exact hstop
    · cases hnext : nextEdge P (replay P manTier h).1.state with
      | none =>
        left
        change nextEdge P (advance P (replay P manTier h).1 _).state = none
        rw [advance_of_nextEdge_none P _ hnext]
        exact hnext
      | some q =>
        have hb : (replay P manTier h).2 q ∉ h.map Prod.fst := by
          intro hq
          exact nextEdge_not_queried P _ q hnext ((hseen q).mp hq)
        have ha := sourceSlot_fresh manTier q (replay P manTier h).2
          (h.map Prod.fst) hb
        have hpick : pick P manTier h =
            (sourceSlot manTier q (replay P manTier h).2 (h.map Prod.fst),
              (replay P manTier h).2 q) := by
          simp only [pick, pairForState, hnext]
        right
        intro q'
        change Equiv.swap (pick P manTier h).1 (pick P manTier h).2
            ((replay P manTier h).2 q') ∈
              (pick P manTier h).1 :: h.map Prod.fst ↔
          Queried P (advance P (replay P manTier h).1 _) q'
        rw [hpick, queried_advance_iff P _ _ q q' hnext]
        exact (swap_mem_cons_iff _ _ _ _ ha hb).trans
          (or_congr (hseen q') (replay P manTier h).2.injective.eq_iff)

/-- Every concrete selected swap either is the identity or has two unseen source endpoints. -/
theorem pick_fresh {n J : ℕ} [NeZero n] (P : Fin n → Equiv.Perm (Fin n))
    (manTier : Fin n → Fin J) (x : Edge n → ℝ) (t : ℕ) :
    let h := allocationHistory (pick P manTier) x t
    (pick P manTier h).1 = (pick P manTier h).2 ∨
      ((pick P manTier h).1 ∉ h.map Prod.fst ∧ (pick P manTier h).2 ∉ h.map Prod.fst) := by
  let h := allocationHistory (pick P manTier) x t
  change (pick P manTier h).1 = (pick P manTier h).2 ∨
    ((pick P manTier h).1 ∉ h.map Prod.fst ∧ (pick P manTier h).2 ∉ h.map Prod.fst)
  rcases history_seen_queried_or_stopped P manTier x t with hstop | hseen
  · left
    change nextEdge P (replay P manTier h).1.state = none at hstop
    simp only [pick, pairForState, hstop]
  · cases hnext : nextEdge P (replay P manTier h).1.state with
    | none =>
      left
      simp only [pick, pairForState, hnext]
    | some q =>
      have hb : (replay P manTier h).2 q ∉ h.map Prod.fst := by
        intro hq
        exact nextEdge_not_queried P _ q hnext ((hseen q).mp hq)
      right
      simpa only [pick, pairForState, hnext] using
        And.intro (sourceSlot_fresh manTier q _ _ hb) hb

/-- Selected swaps fix the source slot of every previously queried label. -/
theorem picked_swap_fixes_queried {n J : ℕ} [NeZero n]
    (P : Fin n → Equiv.Perm (Fin n)) (manTier : Fin n → Fin J)
    (x : Edge n → ℝ) (t : ℕ) (q : Edge n) :
    let h := allocationHistory (pick P manTier) x t
    Queried P (replay P manTier h).1 q →
      Equiv.swap (pick P manTier h).1 (pick P manTier h).2
        ((replay P manTier h).2 q) = (replay P manTier h).2 q := by
  let h := allocationHistory (pick P manTier) x t
  change Queried P (replay P manTier h).1 q →
    Equiv.swap (pick P manTier h).1 (pick P manTier h).2
      ((replay P manTier h).2 q) = (replay P manTier h).2 q
  intro hq
  rcases history_seen_queried_or_stopped P manTier x t with hstop | hseen
  · change nextEdge P (replay P manTier h).1.state = none at hstop
    simp only [pick, pairForState, hstop, Equiv.swap_self, Equiv.coe_refl, id_eq]
  · rcases pick_fresh P manTier x t with heq | ⟨ha, hb⟩
    · change (pick P manTier h).1 = (pick P manTier h).2 at heq
      simp only [heq, Equiv.swap_self, Equiv.coe_refl, id_eq]
    · have hmem : (replay P manTier h).2 q ∈ h.map Prod.fst := (hseen q).mpr hq
      have hqa : (replay P manTier h).2 q ≠ (pick P manTier h).1 :=
        fun heq ↦ ha (heq ▸ hmem)
      have hqb : (replay P manTier h).2 q ≠ (pick P manTier h).2 :=
        fun heq ↦ hb (heq ▸ hmem)
      exact Equiv.swap_apply_of_ne_of_ne hqa hqb

/-- Once a strict-list edge is queried, advancing cannot remove it. -/
theorem queried_advance_mono {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (s : RawState n) (value : ℝ) (q : Edge n) :
    Queried P s q → Queried P (advance P s value) q := by
  cases hnext : nextEdge P s.state with
  | none => simpa only [advance_of_nextEdge_none P s hnext value] using id
  | some edge => exact fun hq ↦ (queried_advance_iff P s value edge q hnext).mpr (Or.inl hq)

/-- A complete labeled array realizes an observed history if its actual proposal edges have
exactly the raw values recorded during that history. Padding values impose no condition. -/
def Realizes {n J : ℕ} [NeZero n] (P : Fin n → Equiv.Perm (Fin n))
    (manTier : Fin n → Fin J) (y : Edge n → ℝ) : List (Edge n × ℝ) → Prop
  | [] => True
  | (_, value) :: h => Realizes P manTier y h ∧
      match nextEdge P (replay P manTier h).1.state with
      | none => True
      | some q => y q = value

/-- Realization depends only on values at labels already traversed by the replay counters. -/
theorem realizes_congr {n J : ℕ} [NeZero n] (P : Fin n → Equiv.Perm (Fin n))
    (manTier : Fin n → Fin J) (y z : Edge n → ℝ) (h : List (Edge n × ℝ))
    (hy : Realizes P manTier y h)
    (heq : ∀ q, Queried P (replay P manTier h).1 q → z q = y q) :
    Realizes P manTier z h := by
  induction h with
  | nil => trivial
  | cons entry h ih =>
    rcases hy with ⟨hprev, hvalue⟩
    refine ⟨ih hprev (fun q hq ↦ heq q (queried_advance_mono P _ entry.2 q hq)), ?_⟩
    cases hnext : nextEdge P (replay P manTier h).1.state with
    | none => trivial
    | some q =>
      have hq : Queried P (replay P manTier (entry :: h)).1 q :=
        (queried_advance_iff P _ entry.2 q q hnext).mpr (Or.inr rfl)
      exact (heq q hq).trans (by simpa only [hnext] using hvalue)

/-- The completed allocation realizes every value actually observed by the concrete DA
arrival policy. This proves the labeled-array/history bridge without a law hypothesis. -/
theorem history_realizes {n J : ℕ} [NeZero n] (P : Fin n → Equiv.Perm (Fin n))
    (manTier : Fin n → Fin J) (x : Edge n → ℝ) (t : ℕ) :
    let h := allocationHistory (pick P manTier) x t
    Realizes P manTier (x ∘ (replay P manTier h).2) h := by
  induction t with
  | zero => trivial
  | succ t ih =>
    let h := allocationHistory (pick P manTier) x t
    have hhist : allocationHistory (pick P manTier) x (t + 1) =
        ((pick P manTier h).1, x (pick P manTier h).1) :: h := rfl
    rw [hhist]
    constructor
    · apply realizes_congr P manTier _ _ h ih
      intro q hq
      change x (Equiv.swap (pick P manTier h).1 (pick P manTier h).2
        ((replay P manTier h).2 q)) = x ((replay P manTier h).2 q)
      rw [picked_swap_fixes_queried P manTier x t q hq]
    · cases hnext : nextEdge P (replay P manTier h).1.state with
      | none => trivial
      | some q =>
        change x (Equiv.swap (pick P manTier h).1 (pick P manTier h).2
          ((replay P manTier h).2 q)) = x (pick P manTier h).1
        have hsnd : (pick P manTier h).2 = (replay P manTier h).2 q := by
          simp only [pick, pairForState, hnext]
        rw [← hsnd, Equiv.swap_apply_right]

/-- Generic-API form of the completed-array realization theorem. -/
theorem adaptiveAllocation_realizes {n J : ℕ} [NeZero n]
    (P : Fin n → Equiv.Perm (Fin n)) (manTier : Fin n → Fin J)
    (x : Edge n → ℝ) (t : ℕ) :
    Realizes P manTier (adaptiveAllocation (pick P manTier) x t)
      (allocationHistory (pick P manTier) x t) := by
  simpa only [replay_reindex, adaptiveAllocation] using history_realizes P manTier x t

/-- The priority stored with each current holder agrees with its complete labeled array. -/
def Aligned {n : ℕ} (s : RawState n) (y : Edge n → ℝ) : Prop :=
  ∀ w m, s.state.held w = some m → s.score w = y (w, m)

/-- Realizing all observed values aligns every currently held priority with the complete
array, even if that array is selected after the entire history is observed. -/
theorem realizes_aligned {n J : ℕ} [NeZero n] (P : Fin n → Equiv.Perm (Fin n))
    (manTier : Fin n → Fin J) (y : Edge n → ℝ) (h : List (Edge n × ℝ))
    (hy : Realizes P manTier y h) : Aligned (replay P manTier h).1 y := by
  induction h with
  | nil => simp [Aligned, replay, initial]
  | cons entry h ih =>
    rcases hy with ⟨hprev, hvalue⟩
    change Aligned (advance P (replay P manTier h).1 entry.2) y
    cases hnext : nextEdge P (replay P manTier h).1.state with
    | none => simpa only [advance_of_nextEdge_none P _ hnext entry.2] using ih hprev
    | some q =>
      rcases q with ⟨w, m⟩
      have hval : y (w, m) = entry.2 := by simpa only [hnext] using hvalue
      simp only [advance, hnext]
      split_ifs
      · intro v k hheld
        by_cases hv : v = w
        · subst v
          have hmk : m = k := by simpa using hheld
          subst k
          simpa using hval.symm
        · have hold : (replay P manTier h).1.state.held v = some k := by
            simpa [Function.update_apply, hv] using hheld
          simpa [Function.update_apply, hv] using ih hprev v k hold
      · exact ih hprev

/-- Complete women's rankings from raw priorities, with men's rankings held fixed. -/
noncomputable def profile {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (y : Edge n → ℝ) : Profile n :=
  ⟨P, fun w ↦ exponentialRank (fun m ↦ y (w, m))⟩

/-- A raw step is exactly the PR transition whenever rank comparisons agree with the
complete priorities. This comparison interface is discharged by injective exponential sorting. -/
theorem advance_state_eq_proposalStep {n : ℕ} (p : Profile n) (y : Edge n → ℝ)
    (hcompare : ∀ w m old, p.womanRank w m < p.womanRank w old ↔ y (w, m) < y (w, old))
    (s : RawState n) (hs : Aligned s y) (value : ℝ)
    (hvalue : ∀ q, nextEdge p.manRank s.state = some q → value = y q) :
    (advance p.manRank s value).state = proposalStep p s.state := by
  cases hfind : (List.finRange n).find?
      (fun m ↦ s.state.next m < n ∧ ∀ w, s.state.held w ≠ some m) with
  | none => simp only [advance, nextEdge, proposalStep, hfind]
  | some m =>
    have hbool := List.find?_some hfind
    have hm : s.state.next m < n ∧ ∀ w, s.state.held w ≠ some m := by simpa using hbool
    have hval := hvalue ((p.manRank m).symm ⟨s.state.next m, hm.1⟩, m)
      (by simp only [nextEdge, hfind, hm.1, ↓reduceDIte])
    simp only [advance, nextEdge, proposalStep, hfind, hm.1, ↓reduceDIte]
    cases hheld : s.state.held ((p.manRank m).symm ⟨s.state.next m, hm.1⟩) with
    | none => rfl
    | some old =>
      have hscore := hs _ old hheld
      simp only [hval, hscore, hcompare]

/-- In particular, injective exponential-rank rows discharge the exact step comparison. -/
theorem advance_profile_state {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (y : Edge n → ℝ) (hy : ∀ w, Function.Injective (fun m ↦ y (w, m)))
    (s : RawState n) (hs : Aligned s y) (value : ℝ)
    (hvalue : ∀ q, nextEdge P s.state = some q → value = y q) :
    (advance P s value).state = proposalStep (profile P y) s.state := by
  exact advance_state_eq_proposalStep (profile P y) y
    (fun w m old ↦ exponentialRank_lt_iff _ (hy w) m old) s hs value hvalue

/-- Every realization of a history reproduces the exact PR run under its completed rankings. -/
theorem realizes_state_eq_run {n J : ℕ} [NeZero n] (P : Fin n → Equiv.Perm (Fin n))
    (manTier : Fin n → Fin J) (y : Edge n → ℝ)
    (hy : ∀ w, Function.Injective (fun m ↦ y (w, m)))
    (h : List (Edge n × ℝ)) (hreal : Realizes P manTier y h) :
    (replay P manTier h).1.state = run (profile P y) h.length := by
  induction h with
  | nil => rfl
  | cons entry h ih =>
    rcases hreal with ⟨hprev, hvalue⟩
    change (advance P (replay P manTier h).1 entry.2).state =
      run (profile P y) (h.length + 1)
    have hnew : ∀ q, nextEdge P (replay P manTier h).1.state = some q →
        entry.2 = y q := by
      intro q hq
      exact (show y q = entry.2 by simpa only [hq] using hvalue).symm
    rw [advance_profile_state P y hy _ (realizes_aligned P manTier y h hprev) entry.2 hnew,
      ih hprev]
    simp only [run, Function.iterate_succ_apply']

/-- Within-woman injectivity is preserved by every block-respecting labeling permutation. -/
theorem row_injective_reindex {n J : ℕ} (manTier : Fin n → Fin J)
    (reindex : Equiv.Perm (Edge n)) (hπ : PreservesBlocks manTier reindex)
    (x : Edge n → ℝ) (hx : ∀ w, Function.Injective (fun m ↦ x (w, m))) :
    ∀ w, Function.Injective (fun m ↦ (x ∘ reindex) (w, m)) := by
  intro w m k heq
  change x (reindex (w, m)) = x (reindex (w, k)) at heq
  have hm : (reindex (w, m)).1 = w := congrArg Prod.fst (hπ (w, m))
  have hk : (reindex (w, k)).1 = w := congrArg Prod.fst (hπ (w, k))
  have hpm : reindex (w, m) = (w, (reindex (w, m)).2) := Prod.ext hm rfl
  have hpk : reindex (w, k) = (w, (reindex (w, k)).2) := Prod.ext hk rfl
  rw [hpm, hpk] at heq
  have hsecond := hx w heq
  have hpair : (w, (reindex (w, m)).2) = (w, (reindex (w, k)).2) := Prod.ext rfl hsecond
  have hind : reindex (w, m) = reindex (w, k) := hpm.trans (hpair.trans hpk.symm)
  exact congrArg Prod.snd (reindex.injective hind)

/-- Exactly one source observation, possibly identity padding, is recorded at each step. -/
theorem history_length {n J : ℕ} [NeZero n] (P : Fin n → Equiv.Perm (Fin n))
    (manTier : Fin n → Fin J) (x : Edge n → ℝ) (t : ℕ) :
    (allocationHistory (pick P manTier) x t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (allocationHistory (pick P manTier) x t).length + 1 = t + 1
    rw [ih]

/-- The raw DA state reconstructed by the arrival policy is the exact PR run for its
completed allocation. The sole pointwise hypothesis excludes ties, which exponentials do a.e. -/
theorem allocation_state_eq_run {n J : ℕ} [NeZero n]
    (P : Fin n → Equiv.Perm (Fin n)) (manTier : Fin n → Fin J)
    (x : Edge n → ℝ) (hx : ∀ w, Function.Injective (fun m ↦ x (w, m))) (t : ℕ) :
    (replay P manTier (allocationHistory (pick P manTier) x t)).1.state =
      run (profile P (adaptiveAllocation (pick P manTier) x t)) t := by
  let h := allocationHistory (pick P manTier) x t
  have hrow : ∀ w, Function.Injective
      (fun m ↦ adaptiveAllocation (pick P manTier) x t (w, m)) := by
    simpa only [adaptiveAllocation, ← replay_reindex] using
      row_injective_reindex manTier (replay P manTier h).2
        (replay_preservesBlocks P manTier h) x hx
  have heq := realizes_state_eq_run P manTier _ hrow h
    (adaptiveAllocation_realizes P manTier x t)
  simpa only [h, history_length] using heq

/-- After `n²` observations, the completed allocation and raw replay have exactly the PR's
terminal holding relation and proposal counters. -/
theorem allocation_terminal_state {n J : ℕ} [NeZero n]
    (P : Fin n → Equiv.Perm (Fin n)) (manTier : Fin n → Fin J)
    (x : Edge n → ℝ) (hx : ∀ w, Function.Injective (fun m ↦ x (w, m))) :
    (replay P manTier (allocationHistory (pick P manTier) x (n * n))).1.state =
      deferredAcceptance (profile P (adaptiveAllocation (pick P manTier) x (n * n))) :=
  allocation_state_eq_run P manTier x hx (n * n)

/-- Source slots attached to genuine proposals; identity-padding observations are excluded. -/
noncomputable def usedSources {n J : ℕ} [NeZero n]
    (P : Fin n → Equiv.Perm (Fin n)) (manTier : Fin n → Fin J) :
    List (Edge n × ℝ) → Finset (Edge n)
  | [] => ∅
  | (source, _) :: h =>
    if nextEdge P (replay P manTier h).1.state = none then usedSources P manTier h
    else insert source (usedSources P manTier h)

/-- Every genuinely used source key occurs in the recorded observation history. -/
theorem usedSources_subset_keys {n J : ℕ} [NeZero n]
    (P : Fin n → Equiv.Perm (Fin n)) (manTier : Fin n → Fin J)
    (h : List (Edge n × ℝ)) (source : Edge n) :
    source ∈ usedSources P manTier h → source ∈ h.map Prod.fst := by
  induction h with
  | nil => simp [usedSources]
  | cons entry h ih =>
    simp only [usedSources, List.map_cons, List.mem_cons]
    split_ifs
    · exact fun hs ↦ Or.inr (ih hs)
    · intro hs
      rcases Finset.mem_insert.mp hs with heq | hmem
      · exact Or.inl heq
      · exact Or.inr (ih hmem)

/-- Finite-set form of fresh-swap observation bookkeeping. -/
theorem swap_mem_insert_iff {ι : Type*} [DecidableEq ι] (a b u : ι) (used : Finset ι)
    (ha : a ∉ used) (hb : b ∉ used) :
    Equiv.swap a b u ∈ insert a used ↔ u ∈ used ∨ u = b := by
  by_cases hua : u = a
  · subst u
    simp [ha, hb, eq_comm]
  · by_cases hub : u = b
    · subst u
      simp
    · simp [Equiv.swap_apply_of_ne_of_ne hua hub, hua, hub]

/-- The concrete used-source set is exactly the reindexing of actual queried edge labels,
including after an arbitrary number of terminal identity-padding observations. -/
theorem history_used_queried {n J : ℕ} [NeZero n]
    (P : Fin n → Equiv.Perm (Fin n)) (manTier : Fin n → Fin J)
    (x : Edge n → ℝ) (t : ℕ) :
    let h := allocationHistory (pick P manTier) x t
    ∀ q, (replay P manTier h).2 q ∈ usedSources P manTier h ↔
      Queried P (replay P manTier h).1 q := by
  dsimp only
  induction t with
  | zero =>
    intro q
    simp [allocationHistory, queryHistory, replay, initial, usedSources, Queried]
  | succ t ih =>
    let h := allocationHistory (pick P manTier) x t
    have hhist : allocationHistory (pick P manTier) x (t + 1) =
        ((pick P manTier h).1, x (pick P manTier h).1) :: h := rfl
    rw [hhist]
    intro q'
    change Equiv.swap (pick P manTier h).1 (pick P manTier h).2
          ((replay P manTier h).2 q') ∈
        (if nextEdge P (replay P manTier h).1.state = none then usedSources P manTier h
         else insert (pick P manTier h).1 (usedSources P manTier h)) ↔
      Queried P (advance P (replay P manTier h).1 _) q'
    cases hnext : nextEdge P (replay P manTier h).1.state with
    | none =>
      simp only [pick, pairForState, hnext, Equiv.swap_self, Equiv.coe_refl, id_eq,
        ↓reduceIte, advance_of_nextEdge_none P _ hnext]
      exact ih q'
    | some q =>
      rcases history_seen_queried_or_stopped P manTier x t with hstop | hseen
      · change nextEdge P (replay P manTier h).1.state = none at hstop
        simp [hstop] at hnext
      · have hb : (replay P manTier h).2 q ∉ h.map Prod.fst := by
          intro hq
          exact nextEdge_not_queried P _ q hnext ((hseen q).mp hq)
        have ha := sourceSlot_fresh manTier q (replay P manTier h).2 (h.map Prod.fst) hb
        have hbused : (replay P manTier h).2 q ∉ usedSources P manTier h :=
          fun hmem ↦ hb (usedSources_subset_keys P manTier h _ hmem)
        have haused : sourceSlot manTier q (replay P manTier h).2 (h.map Prod.fst) ∉
            usedSources P manTier h :=
          fun hmem ↦ ha (usedSources_subset_keys P manTier h _ hmem)
        have hpick : pick P manTier h =
            (sourceSlot manTier q (replay P manTier h).2 (h.map Prod.fst),
              (replay P manTier h).2 q) := by
          simp only [pick, pairForState, hnext]
        rw [ite_eq_right (by simp only [reduceCtorEq, not_false_eq_true]), hpick,
          queried_advance_iff P _ _ q q' hnext]
        exact (swap_mem_insert_iff _ _ _ _ haused hbused).trans
          (or_congr (ih q') (replay P manTier h).2.injective.eq_iff)

/-- Every earlier man in the selected source tier has already appeared in the source history.
The unseen source currently assigned to the target guarantees that the fallback is not used. -/
theorem sourceSlot_minimal {n J : ℕ} (manTier : Fin n → Fin J) (q : Edge n)
    (reindex : Equiv.Perm (Edge n)) (seen : List (Edge n))
    (hπ : PreservesBlocks manTier reindex) (hb : reindex q ∉ seen) :
    ∀ m, manTier m = manTier q.2 → m < (sourceSlot manTier q reindex seen).2 →
      (q.1, m) ∈ seen := by
  unfold sourceSlot
  split
  · rename_i k hfind
    have hfirst := (List.find?_ofFn_eq_some_of_injective
      (f := fun m : Fin n ↦ m) Function.injective_id).mp hfind
    intro m hm hmk
    by_contra hmem
    exact hfirst.2 m hmk (decide_eq_true (And.intro hm hmem))
  · rename_i hfind
    have hw : (reindex q).1 = q.1 :=
      congrArg (fun b : Fin n × Fin J ↦ b.1) (hπ q)
    have ht : manTier (reindex q).2 = manTier q.2 := congrArg Prod.snd (hπ q)
    have hnot := List.find?_eq_none.mp hfind (reindex q).2 (by simp)
    have hnotseen : (q.1, (reindex q).2) ∉ seen := by
      simpa only [← hw, Prod.mk.eta] using hb
    exact False.elim (hnot (decide_eq_true (And.intro ht hnotseen)))

/-- Before termination, no padding has occurred, so every recorded source key is genuinely
used. This identity is only asserted while there is a next actual edge. -/
theorem active_seen_iff_used {n J : ℕ} [NeZero n]
    (P : Fin n → Equiv.Perm (Fin n)) (manTier : Fin n → Fin J)
    (x : Edge n → ℝ) (t : ℕ) (hne :
      nextEdge P (replay P manTier (allocationHistory (pick P manTier) x t)).1.state ≠ none)
    (r : Edge n) :
    r ∈ (allocationHistory (pick P manTier) x t).map Prod.fst ↔
      r ∈ usedSources P manTier (allocationHistory (pick P manTier) x t) := by
  let h := allocationHistory (pick P manTier) x t
  rcases history_seen_queried_or_stopped P manTier x t with hstop | hseen
  · exact False.elim (hne hstop)
  · have hseen' := hseen ((replay P manTier h).2.symm r)
    have hused := history_used_queried P manTier x t ((replay P manTier h).2.symm r)
    simpa only [h, Equiv.apply_symm_apply] using hseen'.trans hused.symm

/-- Genuine source slots form an initial segment in each woman/tier block, with the natural
order of source men. This includes terminal histories with identity padding. -/
theorem usedSources_downward {n J : ℕ} [NeZero n]
    (P : Fin n → Equiv.Perm (Fin n)) (manTier : Fin n → Fin J)
    (x : Edge n → ℝ) (t : ℕ) :
    let h := allocationHistory (pick P manTier) x t
    ∀ a ∈ usedSources P manTier h, ∀ r,
      block manTier r = block manTier a → r.2 < a.2 → r ∈ usedSources P manTier h := by
  dsimp only
  induction t with
  | zero => simp [allocationHistory, queryHistory, usedSources]
  | succ t ih =>
    let h := allocationHistory (pick P manTier) x t
    have hhist : allocationHistory (pick P manTier) x (t + 1) =
        ((pick P manTier h).1, x (pick P manTier h).1) :: h := rfl
    rw [hhist]
    cases hnext : nextEdge P (replay P manTier h).1.state with
    | none =>
      simp only [usedSources, hnext, ↓reduceIte]
      exact ih
    | some q =>
      have hne : nextEdge P (replay P manTier h).1.state ≠ none := by simp only [hnext, ne_eq,
        reduceCtorEq, not_false_eq_true]
      have hb : (replay P manTier h).2 q ∉ h.map Prod.fst := by
        intro hmem
        have hu := (active_seen_iff_used P manTier x t hne _).mp hmem
        exact nextEdge_not_queried P _ q hnext ((history_used_queried P manTier x t q).mp hu)
      have hpick : (pick P manTier h).1 =
          sourceSlot manTier q (replay P manTier h).2 (h.map Prod.fst) := by
        simp only [pick, pairForState, hnext]
      simp only [usedSources, hnext, reduceCtorEq, ↓reduceIte, hpick]
      intro a ha r hblock hlt
      rcases Finset.mem_insert.mp ha with rfl | hold
      · have hbr : block manTier r = block manTier q :=
          hblock.trans (sourceSlot_block manTier q _ _ (replay_preservesBlocks P manTier h))
        have hrw : r.1 = q.1 := congrArg (fun b : Fin n × Fin J ↦ b.1) hbr
        have hrt : manTier r.2 = manTier q.2 := congrArg Prod.snd hbr
        have hseen := sourceSlot_minimal manTier q (replay P manTier h).2
          (h.map Prod.fst) (replay_preservesBlocks P manTier h) hb r.2 hrt hlt
        have hused := (active_seen_iff_used P manTier x t hne _).mp hseen
        exact Finset.mem_insert_of_mem (by simpa only [← hrw, Prod.mk.eta] using hused)
      · exact Finset.mem_insert_of_mem (ih a hold r hblock hlt)

end Ashlagi.Arrival
