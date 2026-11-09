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

public import Ashlagi.ProtocolKernel
public import Ashlagi.RawSemantics

/-! # Visible priority protocols for partial entrant markets

The partial-market setup and the two first-acceptance phases use only revealed ordinal
records. Their updates are genuine deferred acceptance proposals under the original profile.
-/

@[expose] public section

namespace Ashlagi.Protocols

open StableMarriage Ashlagi.Ordinal

/-- Choose the first active, free, unexhausted man in the specified visible priority list. -/
def chooseFrom {n : ℕ} (A : Finset (Fin n)) (L : List (Fin n)) (s : ProposalState n) :
    Option (Fin n) := L.find? fun m ↦ m ∈ A ∧ s.next m < n ∧ ∀ w, s.held w ≠ some m

/-- Every chosen man is both listed and eligible. -/
theorem chooseFrom_some {n : ℕ} (A : Finset (Fin n)) (L : List (Fin n))
    (s : ProposalState n) (m : Fin n) (hm : chooseFrom A L s = some m) :
    m ∈ L ∧ Schedules.Eligible A s m := by
  exact ⟨List.mem_of_find?_eq_some hm, by
    simpa [chooseFrom, Schedules.Eligible] using List.find?_some hm⟩

/-- A complete priority list returns no man exactly at an active-market terminal state. -/
theorem chooseFrom_finRange_none {n : ℕ} (A : Finset (Fin n)) (s : ProposalState n) :
    chooseFrom A (List.finRange n) s = none ↔ Schedules.Terminal A s := by
  simp [chooseFrom, List.find?_eq_none, Schedules.Terminal, Schedules.Eligible]

/-- Canonical visible first-eligible scheduling for a fixed entrant subset. -/
def activeProtocol {n : ℕ} (A : Finset (Fin n)) : Protocol n :=
  fun h ↦ chooseFrom A (List.finRange n) (recordState h)

/-- Sanitization never changes the active-subset chooser. -/
theorem selected_activeProtocol {n : ℕ} (A : Finset (Fin n)) (h : List (Entry n)) :
    selected (activeProtocol A) h = activeProtocol A h := by
  cases hm : activeProtocol A h with
  | none => simp only [selected, hm, Option.filter_none]
  | some m =>
    exact selected_eq_of_eligible _ _ m hm
      (chooseFrom_some A _ _ m hm).2.2

/-- No record selected by the active protocol uses an inactive man. -/
theorem activeProtocol_uses {n : ℕ} (A : Finset (Fin n)) (h : List (Entry n)) :
    Uses A (activeProtocol A) h := by
  induction h with
  | nil => trivial
  | cons entry h ih =>
    refine ⟨ih, fun m hm ↦ ?_⟩
    rw [selected_activeProtocol] at hm
    exact (chooseFrom_some A _ _ m hm).2.1

/-- The complete active chooser pauses exactly when every active entrant is held. -/
theorem activeProtocol_none_iff_terminal {n : ℕ} (A : Finset (Fin n))
    (h : List (Entry n)) :
    selected (activeProtocol A) h = none ↔ Schedules.Terminal A (recordState h) := by
  rw [selected_activeProtocol]
  exact chooseFrom_finRange_none A _

/-- Direct-profile record transitions agree with the exact chosen-man DA update. -/
theorem profile_recordStep_eq_propose {n : ℕ} (C : Protocol n) (p : Profile n)
    (h : List (Entry n)) (m : Fin n) (hm : selected C h = some m) :
    recordStep (recordState h) (observation C p.manRank (Ashlagi.Ordinal.profilePriorities p) h) =
      Schedules.propose p (recordState h) m (selected_some_spec C h m hm).1 := by
  apply recordStep_observation_eq_propose C p _ _ h m hm
  intro w k old
  simp only [Ashlagi.Ordinal.profilePriorities, Nat.cast_lt, Fin.lt_def]

/-- A paused observation leaves its replayed state unchanged. -/
theorem profile_state_succ_of_none {n : ℕ} (C : Protocol n) (p : Profile n) (t : ℕ)
    (hm : selected C (profileTranscript C p t) = none) :
    recordState (profileTranscript C p (t + 1)) = recordState (profileTranscript C p t) := by
  simp only [profileTranscript, transcript, recordState, observation, nextEdge] at *
  simp only [hm, Option.map_none, recordStep]

/-- A genuine selected record strictly increases the total number of proposals. -/
theorem profile_potential_succ_lt {n : ℕ} (C : Protocol n) (p : Profile n) (t : ℕ)
    (m : Fin n) (hm : selected C (profileTranscript C p t) = some m) :
    potential (recordState (profileTranscript C p t)) <
      potential (recordState (profileTranscript C p (t + 1))) := by
  change potential (recordState (profileTranscript C p t)) <
    potential (recordStep (recordState (profileTranscript C p t)) (observation C p.manRank
    (Ashlagi.Ordinal.profilePriorities p) (profileTranscript C p t)))
  rw [profile_recordStep_eq_propose C p _ m hm]
  exact Schedules.propose_potential_lt p _ m _

/-- A terminal active-market state remains unchanged at every further public setup step. -/
theorem activeProtocol_terminal_succ {n : ℕ} (A : Finset (Fin n)) (p : Profile n) (t : ℕ)
    (ht : Schedules.Terminal A (recordState (profileTranscript (activeProtocol A) p t))) :
    recordState (profileTranscript (activeProtocol A) p (t + 1)) =
      recordState (profileTranscript (activeProtocol A) p t) :=
  profile_state_succ_of_none _ p t ((activeProtocol_none_iff_terminal A _).mpr ht)

/-- Before termination the public setup has made at least one genuine proposal per step. -/
theorem activeProtocol_time_le_or_terminal {n : ℕ} (A : Finset (Fin n))
    (p : Profile n) (t : ℕ) :
    t ≤ potential (recordState (profileTranscript (activeProtocol A) p t)) ∨
      Schedules.Terminal A (recordState (profileTranscript (activeProtocol A) p t)) := by
  induction t with
  | zero => exact Or.inl (Nat.zero_le _)
  | succ t ih =>
    rcases ih with htime | hterm
    · cases hm : selected (activeProtocol A) (profileTranscript (activeProtocol A) p t) with
      | none =>
        have ht := (activeProtocol_none_iff_terminal A _).mp hm
        exact Or.inr ((activeProtocol_terminal_succ A p t ht).symm ▸ ht)
      | some m =>
        have hi := profile_potential_succ_lt (activeProtocol A) p t m hm
        exact Or.inl (by omega)
    · exact Or.inr ((activeProtocol_terminal_succ A p t hterm).symm ▸ hterm)

/-- Every partial-market setup has terminated by exactly n² public steps, with padding. -/
theorem activeProtocol_terminal {n : ℕ} (A : Finset (Fin n)) (p : Profile n) :
    Schedules.Terminal A (recordState (profileTranscript (activeProtocol A) p (n * n))) := by
  rcases activeProtocol_time_le_or_terminal A p (n * n) with htime | hterm
  · cases hm : selected (activeProtocol A)
        (profileTranscript (activeProtocol A) p (n * n)) with
    | none => exact (activeProtocol_none_iff_terminal A _).mp hm
    | some m =>
      have hi := profile_potential_succ_lt (activeProtocol A) p (n * n) m hm
      have hb := Schedules.reachable_potential_le p A
        (profileTranscript_reachable (activeProtocol A) p A (n * n + 1)
          (activeProtocol_uses A _))
      omega
  · exact hterm

/-- The concrete public setup realizes the unique schedule-independent partial DA state. -/
theorem activeProtocol_state {n : ℕ} (A : Finset (Fin n)) (p : Profile n) :
    recordState (profileTranscript (activeProtocol A) p (n * n)) =
      Schedules.activeDeferredAcceptance p A :=
  profileTranscript_terminal_eq_active _ p A _ (activeProtocol_uses A _)
    (activeProtocol_terminal A p)

/-- Setup proposals and holders are confined to the active entrant set. -/
theorem activeProtocol_support {n : ℕ} (A : Finset (Fin n)) (p : Profile n) (t : ℕ) :
    (∀ m, m ∉ A → (recordState (profileTranscript (activeProtocol A) p t)).next m = 0) ∧
      (∀ w m, (recordState (profileTranscript (activeProtocol A) p t)).held w = some m →
        m ∈ A) := by
  have hr := profileTranscript_reachable (activeProtocol A) p A t (activeProtocol_uses A _)
  exact ⟨(Schedules.reachable_valid p A hr).inactive,
    fun _ _ hh ↦ Schedules.held_active p A hr hh⟩

/-- Every proposal counter in a partial-market execution has active support. -/
theorem activeProtocol_proposed_active {n : ℕ} (A : Finset (Fin n)) (p : Profile n) (t : ℕ)
    (m w : Fin n)
    (hp : HasProposed p (recordState (profileTranscript (activeProtocol A) p t)) m w) :
    m ∈ A :=
  Schedules.proposed_active p A
    (profileTranscript_reachable _ p A t (activeProtocol_uses A _)) hp

/-- Every edge visible during setup was proposed by an active ordinary entrant. -/
theorem activeProtocol_seen_active {n : ℕ} (A : Finset (Fin n)) (p : Profile n) (t : ℕ)
    (w m : Fin n) (hq : (w, m) ∈ seenEdges (profileTranscript (activeProtocol A) p t)) :
    m ∈ A := by
  have hv := transcript_valid (activeProtocol A) p.manRank (profilePriorities p) t
  have hp := (seenEdges_iff_hasProposed (activeProtocol A) p.manRank _ hv (w, m)).mp hq
  exact activeProtocol_proposed_active A p t m w hp

/-- The initial ordinary entrants when the distinct men u and v arrive last. -/
def ordinaryEntrants {n : ℕ} (u v : Fin n) : Finset (Fin n) :=
  (Finset.univ.erase u).erase v

/-- Neither last entrant has made a proposal or is held at the setup boundary. -/
theorem ordinary_setup_inactive {n : ℕ} (p : Profile n) (u v : Fin n) :
    let s := recordState (profileTranscript (activeProtocol (ordinaryEntrants u v)) p (n * n))
    s.next u = 0 ∧ s.next v = 0 ∧ (∀ w, s.held w ≠ some u) ∧
      (∀ w, s.held w ≠ some v) := by
  have hs := activeProtocol_support (ordinaryEntrants u v) p (n * n)
  have hu : u ∉ ordinaryEntrants u v := by simp [ordinaryEntrants]
  have hv : v ∉ ordinaryEntrants u v := by simp [ordinaryEntrants]
  exact ⟨hs.1 u hu, hs.1 v hv, fun w hh ↦ hu (hs.2 w u hh),
    fun w hh ↦ hv (hs.2 w v hh)⟩

/-- Exactly n−2 ordinary men are held at the completed setup. -/
theorem ordinary_setup_held_card {n : ℕ} (p : Profile n) (u v : Fin n) (huv : u ≠ v) :
    (RawSemantics.heldMen
      (recordState (profileTranscript (activeProtocol (ordinaryEntrants u v)) p (n * n)))).card =
        n - 2 := by
  have hr := profileTranscript_reachable (activeProtocol (ordinaryEntrants u v)) p
    (ordinaryEntrants u v) (n * n) (activeProtocol_uses _ _)
  rw [(RawSemantics.terminal_iff_heldMen_eq_active p _ hr).mp
    (activeProtocol_terminal _ p)]
  simp only [ordinaryEntrants, Finset.card_erase_of_mem (Finset.mem_erase.mpr
    ⟨Ne.symm huv, Finset.mem_univ v⟩), Finset.card_erase_of_mem (Finset.mem_univ u),
    Finset.card_univ, Fintype.card_fin]
  omega

/-- A first acceptance is read from actual accepted records strictly after the setup prefix.
Histories are newest first, so post-setup records are the indicated initial segment. -/
def FirstAccepted {n : ℕ} (setup : ℕ) (m : Fin n) (h : List (Entry n)) : Prop :=
  ∃ w, some ((w, m), true) ∈ h.take (h.length - setup)

/-- Complete the ordinary market, give u and then v priority up to their first acceptances,
then resume the canonical full-market chooser. Displaced ordinary men wait during both phases. -/
noncomputable def stagedProtocol {n : ℕ} (u v : Fin n) : Protocol n := by
  classical
  exact fun h ↦ if h.length < n * n then activeProtocol (ordinaryEntrants u v) h else
    if ¬ FirstAccepted (n * n) u h then chooseFrom Finset.univ [u] (recordState h) else
      if ¬ FirstAccepted (n * n) v h then chooseFrom Finset.univ [v] (recordState h) else
        activeProtocol Finset.univ h

/-- The protocol is the ordinary-market chooser during every setup step. -/
theorem stagedProtocol_setup {n : ℕ} (u v : Fin n) (h : List (Entry n))
    (ht : h.length < n * n) :
    stagedProtocol u v h = activeProtocol (ordinaryEntrants u v) h := by
  classical
  simp only [stagedProtocol, ite_eq_left ht]

/-- During the first entrant's phase the protocol can select only u. -/
theorem stagedProtocol_first_phase {n : ℕ} (u v : Fin n) (h : List (Entry n))
    (ht : n * n ≤ h.length) (hu : ¬ FirstAccepted (n * n) u h) :
    stagedProtocol u v h = chooseFrom Finset.univ [u] (recordState h) := by
  classical
  simp only [stagedProtocol, ite_eq_right (not_lt_of_ge ht), ite_eq_left hu]

/-- After u's first acceptance, the second entrant has priority until his first acceptance. -/
theorem stagedProtocol_second_phase {n : ℕ} (u v : Fin n) (h : List (Entry n))
    (ht : n * n ≤ h.length) (hu : FirstAccepted (n * n) u h)
    (hv : ¬ FirstAccepted (n * n) v h) :
    stagedProtocol u v h = chooseFrom Finset.univ [v] (recordState h) := by
  classical
  simp [stagedProtocol, not_lt_of_ge ht, hu, hv]

/-- Once both first acceptances are visible, the protocol is the canonical full chooser. -/
theorem stagedProtocol_final_phase {n : ℕ} (u v : Fin n) (h : List (Entry n))
    (ht : n * n ≤ h.length) (hu : FirstAccepted (n * n) u h)
    (hv : FirstAccepted (n * n) v h) :
    stagedProtocol u v h = activeProtocol Finset.univ h := by
  classical
  simp [stagedProtocol, not_lt_of_ge ht, hu, hv]

/-- Equal visible choices produce equal recorded observations. -/
theorem observation_eq_of_choice_eq {n : ℕ} (C D : Protocol n) (P : Fin n → Equiv.Perm (Fin n))
    (x : Arrival.Edge n → ℝ) (h : List (Entry n)) (hCD : C h = D h) :
    observation C P x h = observation D P x h := by
  simp only [observation, nextEdge, selected, hCD]

/-- Protocols agreeing on every earlier visible history have the same finite transcript. -/
theorem profileTranscript_eq_of_prefix_choices {n : ℕ} (C D : Protocol n) (p : Profile n)
    (k : ℕ) (hCD : ∀ h, h.length < k → C h = D h) (t : ℕ) (ht : t ≤ k) :
    profileTranscript C p t = profileTranscript D p t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have heq := ih (by omega)
    change observation C p.manRank (profilePriorities p) (profileTranscript C p t) ::
      profileTranscript C p t = observation D p.manRank (profilePriorities p)
        (profileTranscript D p t) :: profileTranscript D p t
    rw [heq]
    rw [observation_eq_of_choice_eq C D _ _ _ (hCD _ (by
      simpa only [profileTranscript, transcript_length] using (show t < k by omega))) ]

/-- The staged execution has exactly the ordinary setup transcript at every setup prefix. -/
theorem stagedProtocol_setup_transcript {n : ℕ} (p : Profile n) (u v : Fin n) (t : ℕ)
    (ht : t ≤ n * n) :
    profileTranscript (stagedProtocol u v) p t =
      profileTranscript (activeProtocol (ordinaryEntrants u v)) p t :=
  profileTranscript_eq_of_prefix_choices _ _ p (n * n)
    (fun h hh ↦ stagedProtocol_setup u v h hh) t ht

/-- The staged setup reaches the exact ordinary-market terminal state. -/
theorem stagedProtocol_setup_state {n : ℕ} (p : Profile n) (u v : Fin n) :
    recordState (profileTranscript (stagedProtocol u v) p (n * n)) =
      Schedules.activeDeferredAcceptance p (ordinaryEntrants u v) := by
  rw [stagedProtocol_setup_transcript p u v _ le_rfl, activeProtocol_state]

/-- Every branch of the staged protocol chooses only a free, unexhausted man. -/
theorem stagedProtocol_choice_eligible {n : ℕ} (u v : Fin n) (h : List (Entry n))
    (m : Fin n) (hm : stagedProtocol u v h = some m) :
    (recordState h).next m < n ∧ ∀ w, (recordState h).held w ≠ some m := by
  classical
  unfold stagedProtocol at hm
  split_ifs at hm
  · exact (chooseFrom_some _ _ _ _ hm).2.2
  · exact (chooseFrom_some _ _ _ _ hm).2.2
  · exact (chooseFrom_some _ _ _ _ hm).2.2
  · exact (chooseFrom_some _ _ _ _ hm).2.2

/-- Sanitization changes none of the staged protocol's choices. -/
theorem selected_stagedProtocol {n : ℕ} (u v : Fin n) (h : List (Entry n)) :
    selected (stagedProtocol u v) h = stagedProtocol u v h := by
  cases hm : stagedProtocol u v h with
  | none => simp only [selected, hm, Option.filter_none]
  | some m => exact selected_eq_of_eligible _ _ m hm (stagedProtocol_choice_eligible u v h m hm)

/-- A singleton priority chooser selects its man whenever he is free and unexhausted. -/
theorem chooseFrom_singleton {n : ℕ} (s : ProposalState n) (m : Fin n)
    (hm : s.next m < n ∧ ∀ w, s.held w ≠ some m) :
    chooseFrom Finset.univ [m] s = some m := by
  simp [chooseFrom, hm]

/-- In any reachable equal-size market, a free man has not exhausted his strict list. -/
theorem reachable_free_next_lt {n : ℕ} (p : Profile n) {s : ProposalState n}
    (hs : Schedules.Reachable p Finset.univ s) (m : Fin n)
    (hfree : ∀ w, s.held w ≠ some m) : s.next m < n := by
  classical
  have hv := Schedules.reachable_valid p Finset.univ hs
  by_contra hn
  have heq : s.next m = n := Nat.le_antisymm (hv.next_le m) (Nat.le_of_not_gt hn)
  have hall (w : Fin n) : ∃ k, s.held w = some k := by
    have hp : HasProposed p s m w := by
      simp only [HasProposed, heq]
      exact (p.manRank m w).isLt
    obtain ⟨k, hk, _⟩ := (hv.best w).2 m hp
    exact ⟨k, hk⟩
  choose f hf using hall
  have hinj : Function.Injective f := by
    intro u v huv
    exact hv.held_injective u v (f u) (hf u) (by simpa [huv] using hf v)
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective hinj m
  exact hfree w (hw ▸ hf w)

/-- New accepted records are exactly the new possibilities for a first-acceptance flag. -/
theorem firstAccepted_cons {n : ℕ} (setup : ℕ) (m : Fin n) (h : List (Entry n))
    (entry : Entry n) (ht : setup ≤ h.length) :
    FirstAccepted setup m (entry :: h) ↔
      (∃ w, entry = some ((w, m), true)) ∨ FirstAccepted setup m h := by
  have hk : (entry :: h).length - setup = h.length - setup + 1 := by simp; omega
  simp only [FirstAccepted, hk, List.take_succ_cons, List.mem_cons]
  constructor
  · rintro ⟨w, hw | hw⟩
    · exact Or.inl ⟨w, hw.symm⟩
    · exact Or.inr ⟨w, hw⟩
  · rintro (⟨w, hw⟩ | ⟨w, hw⟩)
    · exact ⟨w, Or.inl hw.symm⟩
    · exact ⟨w, Or.inr hw⟩

/-- A man cannot become held without an accepted proposal bearing his own name. -/
theorem recordStep_unheld {n : ℕ} (s : ProposalState n) (entry : Entry n) (m : Fin n)
    (hfree : ∀ w, s.held w ≠ some m)
    (hno : ¬ ∃ w, entry = some ((w, m), true)) :
    ∀ w, (recordStep s entry).held w ≠ some m := by
  classical
  cases entry with
  | none => exact hfree
  | some entry =>
    rcases entry with ⟨⟨w, k⟩, a⟩
    cases a with
    | false => exact hfree
    | true =>
      have hkm : k ≠ m := by intro heq; exact hno ⟨w, by simp [heq]⟩
      intro v
      simp only [recordStep, ↓reduceIte, Function.update_apply]
      split_ifs
      · exact fun hh ↦ hkm (Option.some.inj hh)
      · exact hfree v

/-- A man initially unheld stays unheld until an actual post-setup accepted record appears. -/
theorem profile_unheld_of_notFirstAccepted {n : ℕ} (C : Protocol n) (p : Profile n)
    (setup : ℕ) (m : Fin n)
    (hfree : ∀ w, (recordState (profileTranscript C p setup)).held w ≠ some m) (k : ℕ)
    (hno : ¬ FirstAccepted setup m (profileTranscript C p (setup + k))) :
    ∀ w, (recordState (profileTranscript C p (setup + k))).held w ≠ some m := by
  induction k with
  | zero => exact hfree
  | succ k ih =>
    let h := profileTranscript C p (setup + k)
    let entry := observation C p.manRank (profilePriorities p) h
    have ht : setup ≤ h.length := by
      simp only [h, profileTranscript, transcript_length]
      omega
    have hn : ¬ ((∃ w, entry = some ((w, m), true)) ∨ FirstAccepted setup m h) :=
      fun ha ↦ hno ((firstAccepted_cons setup m h entry ht).mpr ha)
    exact recordStep_unheld (recordState h) entry m (ih (fun ha ↦ hn (Or.inr ha)))
      (fun ha ↦ hn (Or.inl ha))

/-- Both suspended entrants start the post-setup history unheld. -/
theorem stagedProtocol_setup_unheld {n : ℕ} (p : Profile n) (u v : Fin n) :
    (∀ w, (recordState (profileTranscript (stagedProtocol u v) p (n * n))).held w ≠ some u) ∧
      (∀ w, (recordState (profileTranscript (stagedProtocol u v) p (n * n))).held w ≠
        some v) := by
  rw [stagedProtocol_setup_transcript p u v _ le_rfl]
  exact (ordinary_setup_inactive p u v).2.2

/-- Until u's first acceptance, every post-setup step actually selects u. -/
theorem stagedProtocol_selects_first {n : ℕ} (p : Profile n) (u v : Fin n) (k : ℕ)
    (hu : ¬ FirstAccepted (n * n) u
      (profileTranscript (stagedProtocol u v) p (n * n + k))) :
    selected (stagedProtocol u v)
      (profileTranscript (stagedProtocol u v) p (n * n + k)) = some u := by
  have hf := profile_unheld_of_notFirstAccepted (stagedProtocol u v) p (n * n) u
    (stagedProtocol_setup_unheld p u v).1 k hu
  have hr := profileTranscript_reachable (stagedProtocol u v) p Finset.univ
    (n * n + k) (uses_univ _ _)
  rw [selected_stagedProtocol, stagedProtocol_first_phase u v _ (by
    simp only [profileTranscript, transcript_length]; omega) hu]
  exact chooseFrom_singleton _ u ⟨reachable_free_next_lt p hr u hf, hf⟩

/-- After u's first acceptance, every step before v's first acceptance actually selects v. -/
theorem stagedProtocol_selects_second {n : ℕ} (p : Profile n) (u v : Fin n) (k : ℕ)
    (hu : FirstAccepted (n * n) u
      (profileTranscript (stagedProtocol u v) p (n * n + k)))
    (hv : ¬ FirstAccepted (n * n) v
      (profileTranscript (stagedProtocol u v) p (n * n + k))) :
    selected (stagedProtocol u v)
      (profileTranscript (stagedProtocol u v) p (n * n + k)) = some v := by
  have hf := profile_unheld_of_notFirstAccepted (stagedProtocol u v) p (n * n) v
    (stagedProtocol_setup_unheld p u v).2 k hv
  have hr := profileTranscript_reachable (stagedProtocol u v) p Finset.univ
    (n * n + k) (uses_univ _ _)
  rw [selected_stagedProtocol, stagedProtocol_second_phase u v _ (by
    simp only [profileTranscript, transcript_length]; omega) hu hv]
  exact chooseFrom_singleton _ v ⟨reachable_free_next_lt p hr v hf, hf⟩

/-- Every sanitized protocol pauses at a full-market terminal state. -/
theorem selected_none_of_terminal {n : ℕ} (C : Protocol n) (h : List (Entry n))
    (ht : Schedules.Terminal Finset.univ (recordState h)) : selected C h = none := by
  cases hm : selected C h with
  | none => rfl
  | some m => exact False.elim (ht m ⟨Finset.mem_univ m, selected_some_spec C h m hm⟩)

/-- Full-market terminal states are unchanged at the next public protocol step. -/
theorem profile_terminal_succ {n : ℕ} (C : Protocol n) (p : Profile n) (t : ℕ)
    (ht : Schedules.Terminal Finset.univ (recordState (profileTranscript C p t))) :
    recordState (profileTranscript C p (t + 1)) = recordState (profileTranscript C p t) :=
  profile_state_succ_of_none C p t (selected_none_of_terminal C _ ht)

/-- After setup the staged protocol pauses exactly at full DA completion. -/
theorem stagedProtocol_none_iff_terminal {n : ℕ} (p : Profile n) (u v : Fin n) (k : ℕ) :
    selected (stagedProtocol u v)
      (profileTranscript (stagedProtocol u v) p (n * n + k)) = none ↔
        Schedules.Terminal Finset.univ
          (recordState (profileTranscript (stagedProtocol u v) p (n * n + k))) := by
  classical
  constructor
  · intro hn
    by_cases hu : FirstAccepted (n * n) u
        (profileTranscript (stagedProtocol u v) p (n * n + k))
    · by_cases hv : FirstAccepted (n * n) v
          (profileTranscript (stagedProtocol u v) p (n * n + k))
      · rw [selected_stagedProtocol, stagedProtocol_final_phase u v _ (by
          simp only [profileTranscript, transcript_length]; omega) hu hv,
          ← selected_activeProtocol] at hn
        exact (activeProtocol_none_iff_terminal Finset.univ _).mp hn
      · rw [stagedProtocol_selects_second p u v k hu hv] at hn
        contradiction
    · rw [stagedProtocol_selects_first p u v k hu] at hn
      contradiction
  · exact selected_none_of_terminal _ _

/-- Before full completion every public post-setup step adds a genuine proposal. -/
theorem stagedProtocol_time_le_or_terminal {n : ℕ} (p : Profile n) (u v : Fin n) (k : ℕ) :
    k ≤ potential (recordState (profileTranscript (stagedProtocol u v) p (n * n + k))) ∨
      Schedules.Terminal Finset.univ
        (recordState (profileTranscript (stagedProtocol u v) p (n * n + k))) := by
  induction k with
  | zero => exact Or.inl (Nat.zero_le _)
  | succ k ih =>
    rcases ih with htime | hterm
    · cases hm : selected (stagedProtocol u v)
          (profileTranscript (stagedProtocol u v) p (n * n + k)) with
      | none =>
        have ht := (stagedProtocol_none_iff_terminal p u v k).mp hm
        have heq := profile_terminal_succ (stagedProtocol u v) p (n * n + k) ht
        exact Or.inr (by simpa only [Nat.add_assoc] using heq.symm ▸ ht)
      | some m =>
        have hi := profile_potential_succ_lt (stagedProtocol u v) p (n * n + k) m hm
        exact Or.inl (by simpa only [Nat.add_assoc] using (show k + 1 ≤
          potential (recordState (profileTranscript (stagedProtocol u v) p
            (n * n + k + 1))) by omega))
    · have heq := profile_terminal_succ (stagedProtocol u v) p (n * n + k) hterm
      exact Or.inr (by simpa only [Nat.add_assoc] using heq.symm ▸ hterm)

/-- Both priority phases and full DA have completed by 2n² public steps. -/
theorem stagedProtocol_terminal {n : ℕ} (p : Profile n) (u v : Fin n) :
    Schedules.Terminal Finset.univ
      (recordState (profileTranscript (stagedProtocol u v) p (n * n + n * n))) := by
  rcases stagedProtocol_time_le_or_terminal p u v (n * n) with htime | hterm
  · cases hm : selected (stagedProtocol u v)
        (profileTranscript (stagedProtocol u v) p (n * n + n * n)) with
    | none => exact (stagedProtocol_none_iff_terminal p u v (n * n)).mp hm
    | some m =>
      have hi := profile_potential_succ_lt (stagedProtocol u v) p (n * n + n * n) m hm
      have hb := Schedules.reachable_potential_le p Finset.univ
        (profileTranscript_reachable (stagedProtocol u v) p Finset.univ
          (n * n + n * n + 1) (uses_univ _ _))
      omega
  · exact hterm

/-- Both entrants' first accepted records exist in the actual finite staged execution. -/
theorem stagedProtocol_bothFirstAccepted {n : ℕ} (p : Profile n) (u v : Fin n) :
    FirstAccepted (n * n) u
      (profileTranscript (stagedProtocol u v) p (n * n + n * n)) ∧
    FirstAccepted (n * n) v
      (profileTranscript (stagedProtocol u v) p (n * n + n * n)) := by
  classical
  have hr := profileTranscript_reachable (stagedProtocol u v) p Finset.univ
    (n * n + n * n) (uses_univ _ _)
  have ht := stagedProtocol_terminal p u v
  constructor
  · by_contra hu
    have hf := profile_unheld_of_notFirstAccepted (stagedProtocol u v) p (n * n) u
      (stagedProtocol_setup_unheld p u v).1 (n * n) hu
    obtain ⟨w, hw⟩ := Schedules.terminal_active_held p Finset.univ hr ht u (Finset.mem_univ u)
    exact hf w hw
  · by_contra hv
    have hf := profile_unheld_of_notFirstAccepted (stagedProtocol u v) p (n * n) v
      (stagedProtocol_setup_unheld p u v).2 (n * n) hv
    obtain ⟨w, hw⟩ := Schedules.terminal_active_held p Finset.univ hr ht v (Finset.mem_univ v)
    exact hf w hw

/-- The concrete two-entrant staged schedule realizes every counter and holder of exact PR. -/
theorem stagedProtocol_state {n : ℕ} (p : Profile n) (u v : Fin n) :
    recordState (profileTranscript (stagedProtocol u v) p (n * n + n * n)) =
      deferredAcceptance p :=
  profileTranscript_terminal_eq_pr _ p _ (stagedProtocol_terminal p u v)

/-- Public padding after completion cannot alter the exact PR terminal state. -/
theorem stagedProtocol_state_after {n : ℕ} (p : Profile n) (u v : Fin n) (k : ℕ) :
    recordState (profileTranscript (stagedProtocol u v) p (n * n + n * n + k)) =
      deferredAcceptance p := by
  induction k with
  | zero => exact stagedProtocol_state p u v
  | succ k ih =>
    have ht : Schedules.Terminal Finset.univ
        (recordState (profileTranscript (stagedProtocol u v) p (n * n + n * n + k))) := by
      rw [ih]
      exact (Schedules.pr_terminal p).2
    simpa only [Nat.add_assoc] using
      (profile_terminal_succ (stagedProtocol u v) p (n * n + n * n + k) ht).trans ih

/-- Distinct last entrants leave exactly two women empty at the ordinary setup boundary. -/
theorem ordinary_setup_empty_card {n : ℕ} (p : Profile n) (u v : Fin n) (huv : u ≠ v) :
    let s := recordState
      (profileTranscript (activeProtocol (ordinaryEntrants u v)) p (n * n))
    (Finset.univ.filter fun w ↦ s.held w = none).card = 2 := by
  classical
  let s := recordState (profileTranscript (activeProtocol (ordinaryEntrants u v)) p (n * n))
  have hr : Schedules.Reachable p (ordinaryEntrants u v) s :=
    profileTranscript_reachable _ p _ _ (activeProtocol_uses _ _)
  have hc : (RawSemantics.occupied s).card = n - 2 := by
    rw [RawSemantics.occupied_card_eq_heldMen_card p _ hr]
    exact ordinary_setup_held_card p u v huv
  have hfilter : (Finset.univ.filter fun w ↦ ¬ s.held w = none) =
      RawSemantics.occupied s := by
    ext w
    cases hw : s.held w <;> simp [RawSemantics.occupied, hw]
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun w ↦ s.held w = none)
  rw [hfilter, hc] at hsum
  have hn : 2 ≤ n := by
    have hh := Finset.card_le_card (show ({u, v} : Finset (Fin n)) ⊆ Finset.univ from
      Finset.subset_univ _)
    simpa [huv] using hh
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  change (Finset.univ.filter fun w ↦ s.held w = none).card = 2
  omega

/-- The staged setup has exactly the same two empty women as ordinary DA. -/
theorem stagedProtocol_setup_empty_card {n : ℕ} (p : Profile n) (u v : Fin n) (huv : u ≠ v) :
    (Finset.univ.filter fun w ↦
      (recordState (profileTranscript (stagedProtocol u v) p (n * n))).held w = none).card = 2 := by
  rw [stagedProtocol_setup_transcript p u v _ le_rfl]
  exact ordinary_setup_empty_card p u v huv

/-- An observed edge's proposer is precisely the actual sanitized selection. -/
theorem observation_map_man {n : ℕ} (C : Protocol n) (P : Fin n → Equiv.Perm (Fin n))
    (x : Arrival.Edge n → ℝ) (h : List (Entry n)) :
    (observation C P x h).map (fun e ↦ e.1.2) = selected C h := by
  simpa only [observation, Option.map_map, Function.comp_def] using nextEdge_map_man C P h

/-- An accepted second entrant record cannot precede the first entrant's first acceptance. -/
theorem stagedProtocol_firstAccepted_order {n : ℕ} (p : Profile n) (u v : Fin n)
    (huv : u ≠ v) (k : ℕ) :
    FirstAccepted (n * n) v
      (profileTranscript (stagedProtocol u v) p (n * n + k)) →
    FirstAccepted (n * n) u
      (profileTranscript (stagedProtocol u v) p (n * n + k)) := by
  induction k with
  | zero => simp [FirstAccepted, profileTranscript, transcript_length]
  | succ k ih =>
    let h := profileTranscript (stagedProtocol u v) p (n * n + k)
    let entry := observation (stagedProtocol u v) p.manRank (profilePriorities p) h
    have ht : n * n ≤ h.length := by
      simp only [h, profileTranscript, transcript_length]
      omega
    intro hv
    have hv' : (∃ w, entry = some ((w, v), true)) ∨ FirstAccepted (n * n) v h :=
      (firstAccepted_cons (n * n) v h entry ht).mp hv
    apply (firstAccepted_cons (n * n) u h entry ht).mpr
    rcases hv' with ⟨w, hw⟩ | hvold
    · by_cases hu : FirstAccepted (n * n) u h
      · exact Or.inr hu
      · have hs := stagedProtocol_selects_first p u v k hu
        have hm := observation_map_man (stagedProtocol u v) p.manRank (profilePriorities p) h
        have hm' : selected (stagedProtocol u v) h = some v := by
          rw [← hm]
          change entry.map (fun e ↦ e.1.2) = some v
          rw [hw]
          rfl
        exact False.elim (huv (Option.some.inj (hs.symm.trans hm')))
    · exact Or.inr (ih hvold)

end Ashlagi.Protocols
