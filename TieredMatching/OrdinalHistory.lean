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

public import TieredMatching.ArrivalPolicy
public import TieredMatching.OrdinalExposure

/-! # Exact ordinal transcript fibers of deferred acceptance

A transcript records the actual edge and its acceptance bit. After termination a `none` entry
records padding. Fixed transcript fibers factor into ordinal constraints on the seen priorities
of each woman. No unqueried priority is constrained.
-/

@[expose] public section

namespace TieredMatching.Ordinal

open StableMarriage MeasureTheory
open Arrival

/-- An actual proposal and acceptance bit, or terminal padding. -/
abbrev Entry (n : ℕ) := Option (Edge n × Bool)

/-- Update the discrete PR state according to a recorded edge and acceptance bit. -/
def recordStep {n : ℕ} (s : ProposalState n) (entry : Entry n) : ProposalState n :=
  match entry with
  | none => s
  | some (q, accepted) =>
    ⟨Function.update s.next q.2 (s.next q.2 + 1),
      if accepted then Function.update s.held q.1 (some q.2) else s.held⟩

/-- The state replayed from newest-first records, independently of any raw priorities. -/
def recordState {n : ℕ} : List (Entry n) → ProposalState n
  | [] => ⟨fun _ ↦ 0, fun _ ↦ none⟩
  | entry :: h => recordStep (recordState h) entry

/-- The raw ordinal comparison made by a woman on the proposed edge. -/
noncomputable def accept {n : ℕ} (x : Edge n → ℝ) (s : ProposalState n) (q : Edge n) : Bool :=
  match s.held q.1 with
  | none => true
  | some old => decide (x q < x (q.1, old))

/-- One observable proposal record, selected using precisely the PR's next-edge rule. -/
noncomputable def observation {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (x : Edge n → ℝ) (s : ProposalState n) : Entry n :=
  (nextEdge P s).map fun q ↦ (q, accept x s q)

/-- The exact padded ordinal transcript after a fixed number of proposal attempts. -/
noncomputable def transcript {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (x : Edge n → ℝ) : ℕ → List (Entry n)
  | 0 => []
  | t + 1 =>
    let h := transcript P x t
    observation P x (recordState h) :: h

/-- A fixed record list uses exactly the edges selected from its discrete predecessor states. -/
def Valid {n : ℕ} (P : Fin n → Equiv.Perm (Fin n)) : List (Entry n) → Prop
  | [] => True
  | entry :: h => Valid P h ∧ nextEdge P (recordState h) = entry.map Prod.fst

/-- One record constrains only its woman's comparison with her current holder. -/
def RowConstraint {n : ℕ} (s : ProposalState n) (entry : Entry n)
    (w : Fin n) (row : Fin n → ℝ) : Prop :=
  match entry with
  | none => True
  | some (q, accepted) => q.1 = w →
    match s.held w with
    | none => accepted = true
    | some old => if accepted then row q.2 < row old else row old ≤ row q.2

/-- All ordinal constraints imposed on one woman's raw priorities by a fixed transcript. -/
def RowFiber {n : ℕ} : List (Entry n) → Fin n → (Fin n → ℝ) → Prop
  | [], _, _ => True
  | entry :: h, w, row => RowFiber h w row ∧ RowConstraint (recordState h) entry w row

/-- A complete array realizes each recorded observation from its fixed predecessor state. -/
def Observes {n : ℕ} (P : Fin n → Equiv.Perm (Fin n)) (x : Edge n → ℝ) :
    List (Entry n) → Prop
  | [] => True
  | entry :: h => Observes P x h ∧ observation P x (recordState h) = entry

/-- The acceptance bit is equivalent to the row-local constraints on all women. -/
theorem accept_eq_iff_rows {n : ℕ} (x : Edge n → ℝ) (s : ProposalState n)
    (q : Edge n) (accepted : Bool) :
    accept x s q = accepted ↔
      ∀ w, RowConstraint s (some (q, accepted)) w (fun m ↦ x (w, m)) := by
  have hrows : (∀ w, RowConstraint s (some (q, accepted)) w (fun m ↦ x (w, m))) ↔
      RowConstraint s (some (q, accepted)) q.1 (fun m ↦ x (q.1, m)) := by
    constructor
    · exact fun h ↦ h q.1
    · intro h w hw
      subst w
      exact h rfl
  rw [hrows]
  cases hheld : s.held q.1 <;> cases accepted <;>
    simp [accept, RowConstraint, hheld, not_lt]

/-- Each observation fiber is the conjunction of a discrete edge constraint and independent
row-local ordinal constraints. No probabilistic independence is assumed in this identity. -/
theorem observation_eq_iff {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (x : Edge n → ℝ) (s : ProposalState n) (entry : Entry n) :
    observation P x s = entry ↔
      nextEdge P s = entry.map Prod.fst ∧
        ∀ w, RowConstraint s entry w (fun m ↦ x (w, m)) := by
  cases entry with
  | none => simp [observation, RowConstraint]
  | some entry =>
    rcases entry with ⟨q, accepted⟩
    change observation P x s = some (q, accepted) ↔ nextEdge P s = some q ∧ _
    rw [← accept_eq_iff_rows]
    rcases q with ⟨w, m⟩
    simp [observation, Option.map_eq_some_iff, Prod.mk.injEq]

/-- Exact factorization of a complete fixed transcript into its discrete validity and each
woman's ordinal row event. The same statement covers impossible transcripts by an empty fiber. -/
theorem observes_iff_valid_rows {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (x : Edge n → ℝ) (h : List (Entry n)) :
    Observes P x h ↔ Valid P h ∧ ∀ w, RowFiber h w (fun m ↦ x (w, m)) := by
  induction h with
  | nil => simp [Observes, Valid, RowFiber]
  | cons entry h ih =>
    simp only [Observes, Valid, RowFiber, ih, observation_eq_iff, forall_and]
    tauto

/-- The recursively generated transcript has one entry per proposal attempt. -/
theorem transcript_length {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (x : Edge n → ℝ) (t : ℕ) : (transcript P x t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [transcript, List.length_cons] using congrArg Nat.succ ih

/-- Recorded observations characterize the exact generated transcript, rather than merely a
collection of necessary inequalities on priorities. -/
theorem observes_iff_transcript {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (x : Edge n → ℝ) (h : List (Entry n)) :
    Observes P x h ↔ transcript P x h.length = h := by
  induction h with
  | nil => simp [Observes, transcript]
  | cons entry h ih =>
    change (Observes P x h ∧ observation P x (recordState h) = entry) ↔
      observation P x (recordState (transcript P x h.length)) :: transcript P x h.length =
        entry :: h
    constructor
    · rintro ⟨hprev, hentry⟩
      rw [ih.mp hprev, hentry]
    · intro heq
      have htail := (List.cons.inj heq).2
      have hentry := (List.cons.inj heq).1
      rw [htail] at hentry
      exact ⟨ih.mpr htail, hentry⟩

/-- Every fixed-time transcript fiber is exactly a product of woman-specific ordinal events,
intersected with fixed discrete conditions. -/
theorem transcript_eq_iff {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (x : Edge n → ℝ) (t : ℕ) (h : List (Entry n)) :
    transcript P x t = h ↔ h.length = t ∧ Valid P h ∧
      ∀ w, RowFiber h w (fun m ↦ x (w, m)) := by
  constructor
  · intro heq
    have hlen : h.length = t := heq ▸ transcript_length P x t
    refine ⟨hlen, ?_⟩
    exact (observes_iff_valid_rows P x h).mp
      ((observes_iff_transcript P x h).mpr (by simpa only [hlen] using heq))
  · rintro ⟨hlen, hvalid, hrows⟩
    have heq := (observes_iff_transcript P x h).mp
      ((observes_iff_valid_rows P x h).mpr ⟨hvalid, hrows⟩)
    simpa only [hlen] using heq

/-- The ordinal observation and its recorded update are exactly the PR transition whenever
the profile's rank comparisons agree with the complete raw values. -/
theorem recordStep_observation_eq_step {n : ℕ} (p : Profile n) (x : Edge n → ℝ)
    (hcompare : ∀ w m old, p.womanRank w m < p.womanRank w old ↔ x (w, m) < x (w, old))
    (s : ProposalState n) :
    recordStep s (observation p.manRank x s) = proposalStep p s := by
  cases hfind : (List.finRange n).find?
      (fun m ↦ s.next m < n ∧ ∀ w, s.held w ≠ some m) with
  | none => simp only [recordStep, observation, nextEdge, proposalStep, hfind, Option.map_none]
  | some m =>
    have hbool := List.find?_some hfind
    have hm : s.next m < n ∧ ∀ w, s.held w ≠ some m := by simpa using hbool
    simp only [observation, nextEdge, proposalStep, hfind, hm.1, ↓reduceDIte,
      Option.map_some, recordStep, accept, hcompare]
    rfl

/-- On tie-free raw rows, the replayed discrete ordinal transcript is the exact PR run. -/
theorem recordState_transcript_eq_run {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (x : Edge n → ℝ) (hx : ∀ w, Function.Injective (fun m ↦ x (w, m))) (t : ℕ) :
    recordState (transcript P x t) = run (Arrival.profile P x) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change recordStep (recordState (transcript P x t))
        (observation P x (recordState (transcript P x t))) =
      run (Arrival.profile P x) (t + 1)
    have hstep := recordStep_observation_eq_step (Arrival.profile P x) x
      (fun w m old ↦ exponentialRank_lt_iff _ (hx w) m old)
      (recordState (transcript P x t))
    change recordStep (recordState (transcript P x t))
        (observation P x (recordState (transcript P x t))) = _ at hstep
    rw [hstep, ih]
    simp only [run, Function.iterate_succ_apply']

/-- Actual edge labels appearing in a fixed transcript, excluding terminal padding. -/
def seenEdges {n : ℕ} : List (Entry n) → Finset (Edge n)
  | [] => ∅
  | none :: h => seenEdges h
  | some (q, _) :: h => insert q (seenEdges h)

/-- Extending a record list never removes a seen edge. -/
theorem seenEdges_tail_subset {n : ℕ} (entry : Entry n) (h : List (Entry n)) :
    seenEdges h ⊆ seenEdges (entry :: h) := by
  cases entry with
  | none => exact Finset.Subset.refl _
  | some entry => exact Finset.subset_insert _ _

/-- Every holder in a discrete record replay was named by an earlier actual proposal.
This holds even for malformed transcripts, so later fiber identities need no validity premise. -/
theorem recordState_held_seen {n : ℕ} (h : List (Entry n)) (w m : Fin n)
    (hheld : (recordState h).held w = some m) : (w, m) ∈ seenEdges h := by
  induction h with
  | nil => simp [recordState] at hheld
  | cons entry h ih =>
    cases entry with
    | none => exact ih hheld
    | some entry =>
      rcases entry with ⟨q, accepted⟩
      simp only [recordState, recordStep] at hheld
      split_ifs at hheld
      · by_cases hw : w = q.1
        · subst w
          have hm : q.2 = m := by simpa using hheld
          subst m
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (ih (by simpa [Function.update_apply, hw] using hheld))
      · exact Finset.mem_insert_of_mem (ih hheld)

/-- A single row constraint is a measurable weak or strict comparison of two coordinates. -/
theorem measurableSet_rowConstraint {n : ℕ} (s : ProposalState n) (entry : Entry n)
    (w : Fin n) : MeasurableSet {row : Fin n → ℝ | RowConstraint s entry w row} := by
  cases entry with
  | none => simp [RowConstraint]
  | some entry =>
    rcases entry with ⟨q, accepted⟩
    by_cases hqw : q.1 = w
    · simp only [RowConstraint, hqw, true_implies]
      cases hheld : s.held w with
      | none => cases accepted <;> simp
      | some old =>
        cases accepted with
        | false => exact measurableSet_le (measurable_pi_apply old) (measurable_pi_apply q.2)
        | true => exact measurableSet_lt (measurable_pi_apply q.2) (measurable_pi_apply old)
    · simp [RowConstraint, hqw]

/-- Each fixed woman's transcript fiber is measurable in her full raw priority row. -/
theorem measurableSet_rowFiber {n : ℕ} (h : List (Entry n)) (w : Fin n) :
    MeasurableSet {row : Fin n → ℝ | RowFiber h w row} := by
  induction h with
  | nil => simp [RowFiber]
  | cons entry h ih =>
    exact ih.inter (measurableSet_rowConstraint (recordState h) entry w)

/-- A row's new constraint is unchanged by a common shift of its seen priorities. The current
holder's edge is seen by an unconditional replay invariant, not a probabilistic assumption. -/
theorem rowConstraint_shift_seen {n : ℕ} (h : List (Entry n)) (entry : Entry n)
    (w : Fin n) (x y : Fin n → ℝ) (c : ℝ)
    (hshift : ∀ m, (w, m) ∈ seenEdges (entry :: h) → y m = x m + c) :
    RowConstraint (recordState h) entry w y ↔ RowConstraint (recordState h) entry w x := by
  cases entry with
  | none => rfl
  | some entry =>
    rcases entry with ⟨q, accepted⟩
    by_cases hqw : q.1 = w
    · subst w
      cases hheld : (recordState h).held q.1 with
      | none => simp only [RowConstraint, hheld]
      | some old =>
        have hnew : y q.2 = x q.2 + c :=
          hshift q.2 (Finset.mem_insert_self _ _)
        have hold : y old = x old + c := hshift old
          (seenEdges_tail_subset _ _ (recordState_held_seen h _ old hheld))
        cases accepted <;> simp only [RowConstraint, hheld, true_implies, ↓reduceIte,
          hnew, hold, add_le_add_iff_right, add_lt_add_iff_right]
    · simp [RowConstraint, hqw]

/-- A fixed row fiber constrains only seen coordinates, and is invariant under their common
translation. Coordinates not seen in the transcript may be changed arbitrarily. -/
theorem rowFiber_shift_seen {n : ℕ} (h : List (Entry n)) (w : Fin n)
    (x y : Fin n → ℝ) (c : ℝ)
    (hshift : ∀ m, (w, m) ∈ seenEdges h → y m = x m + c) :
    RowFiber h w y ↔ RowFiber h w x := by
  induction h with
  | nil => rfl
  | cons entry h ih =>
    exact and_congr (ih (fun m hm ↦ hshift m (seenEdges_tail_subset entry h hm)))
      (rowConstraint_shift_seen h entry w x y c hshift)

/-- The finite index type of men whose edges to a fixed woman appear in a transcript. -/
abbrev SeenMen {n : ℕ} (h : List (Entry n)) (w : Fin n) :=
  {m : Fin n // (w, m) ∈ seenEdges h}

/-- Extend a seen-priority row arbitrarily by zero on the unqueried coordinates. -/
def extendSeen {n : ℕ} (h : List (Entry n)) (w : Fin n) (v : SeenMen h w → ℝ) :
    Fin n → ℝ :=
  fun m ↦ if hm : (w, m) ∈ seenEdges h then v ⟨m, hm⟩ else 0

/-- The row fiber as an event on precisely the finite set of already seen priority variables. -/
def seenRowEvent {n : ℕ} (h : List (Entry n)) (w : Fin n) : Set (SeenMen h w → ℝ) :=
  {v | RowFiber h w (extendSeen h w v)}

/-- The zero extension map is measurable, including when no coordinate has been observed. -/
theorem measurable_extendSeen {n : ℕ} (h : List (Entry n)) (w : Fin n) :
    Measurable (extendSeen h w) := by
  apply Measurable.of_eval
  intro m
  by_cases hm : (w, m) ∈ seenEdges h
  · simpa only [extendSeen, dite_eq_left hm] using measurable_pi_apply (⟨m, hm⟩ : SeenMen h w)
  · simpa only [extendSeen, dite_eq_right hm] using
      (measurable_const : Measurable (fun _ : SeenMen h w → ℝ ↦ (0 : ℝ)))

/-- The restricted seen-coordinate row event is measurable. -/
theorem measurableSet_seenRowEvent {n : ℕ} (h : List (Entry n)) (w : Fin n) :
    MeasurableSet (seenRowEvent h w) :=
  (measurableSet_rowFiber h w).preimage (measurable_extendSeen h w)

/-- Restricting a full row to seen coordinates preserves its exact transcript-fiber predicate. -/
theorem rowFiber_iff_seenRowEvent {n : ℕ} (h : List (Entry n)) (w : Fin n)
    (row : Fin n → ℝ) :
    RowFiber h w row ↔ (fun m : SeenMen h w ↦ row m.val) ∈ seenRowEvent h w := by
  exact (rowFiber_shift_seen h w row (extendSeen h w (fun m ↦ row m.val)) 0
    (fun m hm ↦ by simp only [extendSeen, dite_eq_left hm, add_zero])).symm

/-- Seen-coordinate transcript events satisfy the exact translation-invariance interface of
the unconditional exponential residual-race theorem. No unused priority variable is shifted. -/
theorem translationInvariant_seenRowEvent {n : ℕ} (h : List (Entry n)) (w : Fin n) :
    TranslationInvariant (seenRowEvent h w) := by
  intro v a
  exact rowFiber_shift_seen h w (extendSeen h w v)
    (extendSeen h w (fun m ↦ v m - a)) (-a)
    (fun m hm ↦ by simp only [extendSeen, dite_eq_left hm, sub_eq_add_neg])

/-- Exact transcript fibers on the product of restricted seen-row events. Unqueried values
do not occur on the right-hand side. -/
theorem transcript_eq_iff_seenRows {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (x : Edge n → ℝ) (t : ℕ) (h : List (Entry n)) :
    transcript P x t = h ↔ h.length = t ∧ Valid P h ∧
      ∀ w, (fun m : SeenMen h w ↦ x (w, m.val)) ∈ seenRowEvent h w := by
  rw [transcript_eq_iff]
  constructor
  · rintro ⟨hlen, hvalid, hrows⟩
    exact ⟨hlen, hvalid, fun w ↦
      (rowFiber_iff_seenRowEvent h w (fun m ↦ x (w, m))).mp (hrows w)⟩
  · rintro ⟨hlen, hvalid, hrows⟩
    exact ⟨hlen, hvalid, fun w ↦
      (rowFiber_iff_seenRowEvent h w (fun m ↦ x (w, m))).mpr (hrows w)⟩

/-- Every exact transcript fiber is measurable in the full independent edge array. -/
theorem measurableSet_transcript_fiber {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (t : ℕ) (h : List (Entry n)) :
    MeasurableSet {x : Edge n → ℝ | transcript P x t = h} := by
  have heq : {x : Edge n → ℝ | transcript P x t = h} =
      {x | (h.length = t ∧ Valid P h) ∧ ∀ w, RowFiber h w (fun m ↦ x (w, m))} := by
    ext x
    change (transcript P x t = h) ↔
      ((h.length = t ∧ Valid P h) ∧ ∀ w, RowFiber h w (fun m ↦ x (w, m)))
    simpa only [and_assoc] using transcript_eq_iff P x t h
  rw [heq]
  by_cases hgood : h.length = t ∧ Valid P h
  · simp only [hgood, true_and]
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro w
    have hm : Measurable (fun x : Edge n → ℝ ↦ fun m : Fin n ↦ x (w, m)) :=
      Measurable.of_eval (fun m ↦ measurable_pi_apply (w, m))
    exact (measurableSet_rowFiber h w).preimage hm
  · simp [hgood]

/-- A valid actual record adds precisely the next strict-list edge to the counter prefix,
regardless of its acceptance bit. -/
theorem recordStep_hasProposed_iff {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (s : ProposalState n) (q q' : Edge n) (accepted : Bool)
    (hnext : nextEdge P s = some q) :
    HasProposed ⟨P, fun _ ↦ Equiv.refl _⟩ (recordStep s (some (q, accepted))) q'.2 q'.1 ↔
      HasProposed ⟨P, fun _ ↦ Equiv.refl _⟩ s q'.2 q'.1 ∨ q' = q := by
  obtain ⟨m, hn, rfl, _⟩ := nextEdge_some_spec P s q hnext
  change HasProposed ⟨P, fun _ ↦ Equiv.refl _⟩
      ⟨Function.update s.next m (s.next m + 1), _⟩ q'.2 q'.1 ↔ _
  rw [hasProposed_update_iff _ _ _ hn]
  simp only [Prod.ext_iff, and_comm]

/-- On every valid fixed transcript, the seen labels are exactly the strict-list counter
prefixes. Thus the word "seen" has the exact proposal semantics used in Proposition G.2. -/
theorem seenEdges_iff_hasProposed {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (h : List (Entry n)) (hvalid : Valid P h) (q : Edge n) :
    q ∈ seenEdges h ↔ HasProposed ⟨P, fun _ ↦ Equiv.refl _⟩ (recordState h) q.2 q.1 := by
  induction h with
  | nil => simp [seenEdges, recordState, HasProposed]
  | cons entry h ih =>
    rcases hvalid with ⟨hprev, hnext⟩
    cases entry with
    | none => exact ih hprev
    | some entry =>
      rcases entry with ⟨edge, accepted⟩
      change q ∈ insert edge (seenEdges h) ↔
        HasProposed ⟨P, fun _ ↦ Equiv.refl _⟩
          (recordStep (recordState h) (some (edge, accepted))) q.2 q.1
      rw [recordStep_hasProposed_iff P _ edge q accepted hnext, Finset.mem_insert,
        ih hprev, or_comm]

/-- A next actual proposal is outside the seen-variable set of its exact fixed transcript. -/
theorem nextEdge_fresh_of_valid {n : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (h : List (Entry n)) (hvalid : Valid P h) (q : Edge n)
    (hnext : nextEdge P (recordState h) = some q) : q ∉ seenEdges h := by
  intro hseen
  exact nextEdge_not_queried P ⟨recordState h, fun _ ↦ 0⟩ q hnext
    ((seenEdges_iff_hasProposed P h hvalid q).mp hseen)

/-- Within its exact ordinal row event, a woman's current holder is no worse than every
seen man. This also proves existence of a holder whenever her seen set is nonempty. -/
theorem rowFiber_has_best {n : ℕ} (h : List (Entry n)) (w : Fin n) (row : Fin n → ℝ)
    (hrow : RowFiber h w row) :
    ∀ m, (w, m) ∈ seenEdges h →
      ∃ k, (recordState h).held w = some k ∧ row k ≤ row m := by
  induction h with
  | nil => simp [seenEdges]
  | cons entry h ih =>
    rcases hrow with ⟨hprev, hconstraint⟩
    cases entry with
    | none => exact ih hprev
    | some entry =>
      rcases entry with ⟨q, accepted⟩
      by_cases hqw : q.1 = w
      · subst w
        cases accepted with
        | false =>
          intro m hm
          rcases Finset.mem_insert.mp hm with hnew | hold
          · have hm' : m = q.2 := congrArg Prod.snd hnew
            subst m
            cases hk : (recordState h).held q.1 with
            | none => simp [RowConstraint, hk] at hconstraint
            | some k =>
              exact ⟨k, hk, by simpa [RowConstraint, hk] using hconstraint⟩
          · exact ih hprev m hold
        | true =>
          intro m hm
          refine ⟨q.2, by simp [recordState, recordStep], ?_⟩
          rcases Finset.mem_insert.mp hm with hnew | hold
          · have hm' : m = q.2 := congrArg Prod.snd hnew
            subst m
            exact le_rfl
          · obtain ⟨k, hk, hdom⟩ := ih hprev m hold
            have hlt : row q.2 < row k := by
              simpa [RowConstraint, hk] using hconstraint
            exact le_trans hlt.le hdom
      · intro m hm
        have hold : (w, m) ∈ seenEdges h := by
          rcases Finset.mem_insert.mp hm with hnew | hold
          · exact False.elim (hqw (congrArg Prod.fst hnew).symm)
          · exact hold
        have hheld : (recordState (some (q, accepted) :: h)).held w =
            (recordState h).held w := by
          cases accepted with
          | false => rfl
          | true =>
            change Function.update (recordState h).held q.1 (some q.2) w = _
            exact Function.update_of_ne (Ne.symm hqw) _ _
        obtain ⟨k, hk, hdom⟩ := ih hprev m hold
        exact ⟨k, hheld.trans hk, hdom⟩

/-- A specified current holder is a minimum of the seen raw priorities on its row fiber. -/
theorem rowFiber_held_isMinOn {n : ℕ} (h : List (Entry n)) (w k : Fin n)
    (row : Fin n → ℝ) (hrow : RowFiber h w row)
    (hheld : (recordState h).held w = some k) :
    IsMinOn row {m | (w, m) ∈ seenEdges h} k := by
  intro m hm
  obtain ⟨old, hold, hdom⟩ := rowFiber_has_best h w row hrow m hm
  have heq : k = old := Option.some.inj (hheld.symm.trans hold)
  change row k ≤ row m
  simpa only [heq] using hdom

/-- With no current holder, the exact row fiber forces the seen-coordinate type to be empty. -/
theorem rowFiber_no_holder_no_seen {n : ℕ} (h : List (Entry n)) (w : Fin n)
    (row : Fin n → ℝ) (hrow : RowFiber h w row)
    (hheld : (recordState h).held w = none) : ∀ m, (w, m) ∉ seenEdges h := by
  intro m hm
  obtain ⟨k, hk, _⟩ := rowFiber_has_best h w row hrow m hm
  simp only [hheld, reduceCtorEq] at hk

/-- On an actual fixed ordinal row fiber, accepting the next man is exactly the event that
his fresh priority beats all previously seen priorities. -/
theorem accept_true_iff_all_seen {n : ℕ} (h : List (Entry n)) (w m : Fin n)
    (x : Edge n → ℝ) (hrow : RowFiber h w (fun k ↦ x (w, k))) :
    accept x (recordState h) (w, m) = true ↔
      ∀ k : SeenMen h w, x (w, m) < x (w, k.val) := by
  cases hheld : (recordState h).held w with
  | none =>
    constructor
    · intro _ k
      exact False.elim (rowFiber_no_holder_no_seen h w _ hrow hheld k.val k.property)
    · intro _
      simp only [accept, hheld]
  | some old =>
    simp only [accept, hheld, decide_eq_true_eq]
    constructor
    · intro hlt k
      exact lt_of_lt_of_le hlt ((rowFiber_held_isMinOn h w old _ hrow hheld) k.property)
    · intro hall
      exact hall ⟨old, recordState_held_seen h w old hheld⟩

end TieredMatching.Ordinal
