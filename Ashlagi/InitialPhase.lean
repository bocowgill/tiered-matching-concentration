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

public import Ashlagi.PriorityProtocols
public import Ashlagi.ProfileHistories
public import Ashlagi.InitialRates
public import Ashlagi.HazardMoments
public import Ashlagi.InitialDrift
public import Ashlagi.SurvivalKernel

/-! # Actual first-acceptance stopping counts in the last-two priority phases

Both stopping times are defined from the original profile's actual staged protocol transcript.
The setup, priority choices and acceptance observations are those of the exact PR algorithm.
-/

@[expose] public section

namespace Ashlagi.InitialPhase

open StableMarriage MeasureTheory Ashlagi.Ordinal Protocols FiniteConditioning
open scoped ENNReal NNReal

/-- The actual visible history k observation steps after the completed ordinary setup. -/
noncomputable def history {n : ℕ} (p : Profile n) (u v : Fin n) (k : ℕ) : List (Entry n) :=
  profileTranscript (stagedProtocol u v) p (n * n + k)

/-- The corresponding exact ordinary DA state. -/
noncomputable def state {n : ℕ} (p : Profile n) (u v : Fin n) (k : ℕ) : ProposalState n :=
  recordState (history p u v k)

/-- The actual post-setup history has its exact public observation clock. -/
theorem history_length {n : ℕ} (p : Profile n) (u v : Fin n) (k : ℕ) :
    (history p u v k).length = n * n + k := transcript_length _ _ _ _

/-- One post-setup step prepends precisely the actual newly observed entry. -/
theorem history_succ {n : ℕ} (p : Profile n) (u v : Fin n) (k : ℕ) :
    history p u v (k + 1) =
      observation (stagedProtocol u v) p.manRank (profilePriorities p) (history p u v k) ::
        history p u v k := rfl

/-- A visible first-acceptance flag persists after the next actual observation. -/
theorem accepted_succ {n : ℕ} (p : Profile n) (u v m : Fin n) (k : ℕ)
    (ha : FirstAccepted (n * n) m (history p u v k)) :
    FirstAccepted (n * n) m (history p u v (k + 1)) := by
  rw [history_succ]
  apply (firstAccepted_cons (n * n) m _ _ (by rw [history_length]; omega)).mpr
  exact Or.inr ha

/-- First-acceptance visibility is monotone in actual post-setup time. -/
theorem accepted_mono {n : ℕ} (p : Profile n) (u v m : Fin n) {k l : ℕ}
    (hkl : k ≤ l) (ha : FirstAccepted (n * n) m (history p u v k)) :
    FirstAccepted (n * n) m (history p u v l) := by
  induction l, hkl using Nat.le_induction with
  | base => exact ha
  | succ l hkl ih => exact accepted_succ p u v m l ih

/-- The first entrant has an actual accepted record by the bounded staged horizon. -/
theorem first_exists {n : ℕ} (p : Profile n) (u v : Fin n) :
    ∃ k, FirstAccepted (n * n) u (history p u v k) :=
  ⟨n * n, (stagedProtocol_bothFirstAccepted p u v).1⟩

/-- The second entrant also has an actual accepted record by the bounded staged horizon. -/
theorem second_exists {n : ℕ} (p : Profile n) (u v : Fin n) :
    ∃ k, FirstAccepted (n * n) v (history p u v k) :=
  ⟨n * n, (stagedProtocol_bothFirstAccepted p u v).2⟩

/-- The genuine first-acceptance offset of u after setup. -/
noncomputable def firstOffset {n : ℕ} (p : Profile n) (u v : Fin n) : ℕ := by
  classical
  exact Nat.find (first_exists p u v)

/-- The genuine first-acceptance offset of v after setup. -/
noncomputable def secondOffset {n : ℕ} (p : Profile n) (u v : Fin n) : ℕ := by
  classical
  exact Nat.find (second_exists p u v)

/-- The u stopping offset is determined exactly by the already visible acceptance flag. -/
theorem firstOffset_le_iff {n : ℕ} (p : Profile n) (u v : Fin n) (k : ℕ) :
    firstOffset p u v ≤ k ↔ FirstAccepted (n * n) u (history p u v k) := by
  classical
  constructor
  · intro hk
    exact accepted_mono p u v u hk (Nat.find_spec (first_exists p u v))
  · intro ha
    exact Nat.find_min' (first_exists p u v) ha

/-- The v stopping offset is likewise an exact observable stopping time. -/
theorem secondOffset_le_iff {n : ℕ} (p : Profile n) (u v : Fin n) (k : ℕ) :
    secondOffset p u v ≤ k ↔ FirstAccepted (n * n) v (history p u v k) := by
  classical
  constructor
  · intro hk
    exact accepted_mono p u v v hk (Nat.find_spec (second_exists p u v))
  · intro ha
    exact Nat.find_min' (second_exists p u v) ha

/-- Setup itself contains no post-setup accepted record. -/
theorem not_accepted_zero {n : ℕ} (p : Profile n) (u v m : Fin n) :
    ¬ FirstAccepted (n * n) m (history p u v 0) := by
  simp only [FirstAccepted, history_length, Nat.add_zero, Nat.sub_self, List.take_zero,
    List.not_mem_nil, exists_false, not_false_eq_true]

/-- The first entrant's first acceptance requires at least one actual proposal. -/
theorem firstOffset_pos {n : ℕ} (p : Profile n) (u v : Fin n) : 0 < firstOffset p u v := by
  by_contra hn
  exact not_accepted_zero p u v u ((firstOffset_le_iff p u v 0).mp (by omega))

/-- The second entrant's first acceptance is also strictly after setup. -/
theorem secondOffset_pos {n : ℕ} (p : Profile n) (u v : Fin n) : 0 < secondOffset p u v := by
  by_contra hn
  exact not_accepted_zero p u v v ((secondOffset_le_iff p u v 0).mp (by omega))

/-- The concrete staged horizon bounds the first stopping offset. -/
theorem firstOffset_le_square {n : ℕ} (p : Profile n) (u v : Fin n) :
    firstOffset p u v ≤ n * n :=
  (firstOffset_le_iff p u v _).mpr (stagedProtocol_bothFirstAccepted p u v).1

/-- The same concrete horizon bounds the second stopping offset. -/
theorem secondOffset_le_square {n : ℕ} (p : Profile n) (u v : Fin n) :
    secondOffset p u v ≤ n * n :=
  (secondOffset_le_iff p u v _).mpr (stagedProtocol_bothFirstAccepted p u v).2

/-- Before its first acceptance the actual first phase selects u at every step. -/
theorem selects_first {n : ℕ} (p : Profile n) (u v : Fin n) (k : ℕ)
    (hk : k < firstOffset p u v) : selected (stagedProtocol u v) (history p u v k) = some u :=
  stagedProtocol_selects_first p u v k (fun ha ↦
    (not_le_of_gt hk) ((firstOffset_le_iff p u v k).mpr ha))

/-- For distinct entrants, v's first acceptance cannot precede u's. -/
theorem firstOffset_le_secondOffset {n : ℕ} (p : Profile n) (u v : Fin n) (huv : u ≠ v) :
    firstOffset p u v ≤ secondOffset p u v := by
  apply (firstOffset_le_iff p u v _).mpr
  apply stagedProtocol_firstAccepted_order p u v huv
  exact (secondOffset_le_iff p u v _).mp le_rfl

/-- Every step in the second priority phase actually selects v. -/
theorem selects_second {n : ℕ} (p : Profile n) (u v : Fin n) (k : ℕ)
    (hu : firstOffset p u v ≤ k) (hv : k < secondOffset p u v) :
    selected (stagedProtocol u v) (history p u v k) = some v :=
  stagedProtocol_selects_second p u v k ((firstOffset_le_iff p u v k).mp hu)
    (fun ha ↦ (not_le_of_gt hv) ((secondOffset_le_iff p u v k).mpr ha))

/-- A selected genuine proposal updates exactly its proposer's ordinary counter. -/
theorem state_next_succ {n : ℕ} (p : Profile n) (u v m : Fin n) (k : ℕ)
    (hs : selected (stagedProtocol u v) (history p u v k) = some m) :
    (state p u v (k + 1)).next =
      Function.update (state p u v k).next m ((state p u v k).next m + 1) := by
  change (recordStep (recordState (history p u v k))
    (observation (stagedProtocol u v) p.manRank (profilePriorities p) (history p u v k))).next = _
  rw [profile_recordStep_eq_propose _ p _ m hs]
  rfl

/-- Both designated entrants have zero counters at the exact completed setup boundary. -/
theorem setup_counters {n : ℕ} (p : Profile n) (u v : Fin n) :
    (state p u v 0).next u = 0 ∧ (state p u v 0).next v = 0 := by
  have hh := ordinary_setup_inactive p u v
  rw [← stagedProtocol_setup_transcript p u v _ le_rfl] at hh
  exact ⟨hh.1, hh.2.1⟩

/-- Until and including u's first acceptance, only u's counter changes, once per step. -/
theorem first_phase_counters {n : ℕ} (p : Profile n) (u v : Fin n) (k : ℕ)
    (hk : k ≤ firstOffset p u v) (m : Fin n) :
    (state p u v k).next m = if m = u then k else (state p u v 0).next m := by
  classical
  induction k with
  | zero =>
    by_cases hm : m = u
    · subst m
      simpa only [ite_true] using (setup_counters p u v).1
    · simp only [ite_eq_right hm]
  | succ k ih =>
    have hs := selects_first p u v k (by omega)
    rw [state_next_succ p u v u k hs]
    by_cases hm : m = u
    · subst m
      rw [Function.update_self, ih (by omega), ite_eq_left rfl, ite_eq_left rfl]
    · rw [Function.update_of_ne hm, ih (by omega), ite_eq_right hm, ite_eq_right hm]

/-- An acceptance first appearing at a positive offset is the actual newest accepted record. -/
theorem first_record {n : ℕ} (p : Profile n) (u v m : Fin n) (k : ℕ) (hk : 0 < k)
    (ha : FirstAccepted (n * n) m (history p u v k))
    (hprev : ¬ FirstAccepted (n * n) m (history p u v (k - 1))) :
    ∃ w, observation (stagedProtocol u v) p.manRank (profilePriorities p)
      (history p u v (k - 1)) = some ((w, m), true) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [history_succ] at ha
  have ht : n * n ≤ (history p u v j).length := by rw [history_length]; omega
  rcases (firstAccepted_cons (n * n) m _ _ ht).mp ha with hnew | hold
  · exact hnew
  · exact False.elim (hprev hold)

/-- The second entrant has made a positive number of proposals at his first acceptance. -/
theorem second_counter_pos {n : ℕ} (p : Profile n) (u v : Fin n) :
    0 < (state p u v (secondOffset p u v)).next v := by
  have hk := secondOffset_pos p u v
  have hprev : ¬ FirstAccepted (n * n) v (history p u v (secondOffset p u v - 1)) := by
    intro ha
    have hh := (secondOffset_le_iff p u v _).mpr ha
    omega
  obtain ⟨w, hw⟩ := first_record p u v v _ hk
    ((secondOffset_le_iff p u v _).mp le_rfl) hprev
  have hid : secondOffset p u v = (secondOffset p u v - 1) + 1 := by omega
  rw [hid, state, history_succ]
  change 0 < (recordStep (recordState (history p u v (secondOffset p u v - 1)))
    (observation (stagedProtocol u v) p.manRank (profilePriorities p)
      (history p u v (secondOffset p u v - 1)))).next v
  rw [hw]
  simp only [recordStep, Function.update_self]
  omega

/-- Distinct designated entrants have strictly ordered actual first acceptance times. -/
theorem firstOffset_lt_secondOffset {n : ℕ} (p : Profile n) (u v : Fin n) (huv : u ≠ v) :
    firstOffset p u v < secondOffset p u v := by
  have hle := firstOffset_le_secondOffset p u v huv
  by_contra hn
  have heq : secondOffset p u v = firstOffset p u v := by omega
  have hc := first_phase_counters p u v (firstOffset p u v) le_rfl v
  rw [ite_eq_right (Ne.symm huv), (setup_counters p u v).2] at hc
  have hp := second_counter_pos p u v
  rw [heq, hc] at hp
  omega

/-- The actual first acceptance count of u. -/
noncomputable def A1 {n : ℕ} (p : Profile n) (u v : Fin n) : ℕ :=
  (state p u v (firstOffset p u v)).next u

/-- The actual first acceptance count of v. -/
noncomputable def A2 {n : ℕ} (p : Profile n) (u v : Fin n) : ℕ :=
  (state p u v (secondOffset p u v)).next v

/-- The actual first u count equals its genuine priority observations through acceptance. -/
theorem A1_eq_firstOffset {n : ℕ} (p : Profile n) (u v : Fin n) : A1 p u v = firstOffset p u v := by
  exact (first_phase_counters p u v _ le_rfl u).trans (ite_eq_left rfl)

/-- Through v's first acceptance only the two priority counters can change; their increments
are exactly their elapsed genuine priority steps. -/
theorem phase_counters {n : ℕ} (p : Profile n) (u v : Fin n) (huv : u ≠ v) (k : ℕ)
    (hk : k ≤ secondOffset p u v) (m : Fin n) :
    (state p u v k).next m =
      if m = u then min k (firstOffset p u v) else
        if m = v then k - firstOffset p u v else (state p u v 0).next m := by
  classical
  induction k with
  | zero =>
    by_cases hmu : m = u
    · subst m
      simpa only [ite_true, Nat.zero_min] using (setup_counters p u v).1
    · rw [ite_eq_right hmu]
      by_cases hmv : m = v
      · subst m
        simpa only [ite_true, Nat.zero_sub] using (setup_counters p u v).2
      · simp only [ite_eq_right hmv]
  | succ k ih =>
    have hp := ih (by omega)
    by_cases hku : k < firstOffset p u v
    · rw [state_next_succ p u v u k (selects_first p u v k hku)]
      by_cases hmu : m = u
      · subst m
        rw [Function.update_self, hp]
        simp only [ite_true]
        omega
      · rw [Function.update_of_ne hmu, hp, ite_eq_right hmu, ite_eq_right hmu]
        by_cases hmv : m = v
        · simp only [ite_eq_left hmv]
          omega
        · simp only [ite_eq_right hmv]
    · have hsel := selects_second p u v k (by omega) (by omega)
      rw [state_next_succ p u v v k hsel]
      by_cases hmv : m = v
      · subst m
        rw [Function.update_self, hp]
        simp only [ite_eq_right (Ne.symm huv), ite_true]
        omega
      · rw [Function.update_of_ne hmv, hp]
        by_cases hmu : m = u
        · simp only [ite_eq_left hmu]
          omega
        · simp only [ite_eq_right hmu, ite_eq_right hmv]

/-- The actual second first-acceptance count equals the number of genuine v-priority steps. -/
theorem A2_eq_offset_sub {n : ℕ} (p : Profile n) (u v : Fin n) (huv : u ≠ v) :
    A2 p u v = secondOffset p u v - firstOffset p u v := by
  unfold A2
  rw [phase_counters p u v huv _ le_rfl v, ite_eq_right (Ne.symm huv)]
  simp only [ite_true]

/-- The first actual initial count lies between one and n, pointwise on every full profile. -/
theorem A1_bounds {n : ℕ} (p : Profile n) (u v : Fin n) : 1 ≤ A1 p u v ∧ A1 p u v ≤ n := by
  constructor
  · rw [A1_eq_firstOffset]
    exact firstOffset_pos p u v
  · exact profileTranscript_next_le (stagedProtocol u v) p _ u

/-- The second actual initial count has the same pointwise finite bound. -/
theorem A2_bounds {n : ℕ} (p : Profile n) (u v : Fin n) (huv : u ≠ v) :
    1 ≤ A2 p u v ∧ A2 p u v ≤ n := by
  constructor
  · rw [A2_eq_offset_sub p u v huv]
    exact Nat.sub_pos_of_lt (firstOffset_lt_secondOffset p u v huv)
  · exact profileTranscript_next_le (stagedProtocol u v) p _ v

/-- The actual public first-acceptance time of u. -/
noncomputable def firstTime {n : ℕ} (p : Profile n) (u v : Fin n) : ℕ :=
  n * n + firstOffset p u v

/-- The actual public first-acceptance time of v. -/
noncomputable def secondTime {n : ℕ} (p : Profile n) (u v : Fin n) : ℕ :=
  n * n + secondOffset p u v

/-- No pause or other proposer's attempt occurs during the first priority phase. -/
theorem firstTime_eq_setup_add_A1 {n : ℕ} (p : Profile n) (u v : Fin n) :
    firstTime p u v = n * n + A1 p u v := by rw [A1_eq_firstOffset]; rfl

/-- The second priority phase likewise has exactly A2 genuine observations. -/
theorem secondTime_eq_firstTime_add_A2 {n : ℕ} (p : Profile n) (u v : Fin n) (huv : u ≠ v) :
    secondTime p u v = firstTime p u v + A2 p u v := by
  rw [A2_eq_offset_sub p u v huv]
  have hh := firstOffset_le_secondOffset p u v huv
  unfold firstTime secondTime
  omega

/-- Every other man's genuine counter is unchanged throughout both initial phases. -/
theorem other_counter_unchanged {n : ℕ} (p : Profile n) (u v : Fin n) (huv : u ≠ v)
    (k : ℕ) (hk : k ≤ secondOffset p u v) (m : Fin n) (hmu : m ≠ u) (hmv : m ≠ v) :
    (state p u v k).next m = (state p u v 0).next m := by
  rw [phase_counters p u v huv k hk m, ite_eq_right hmu, ite_eq_right hmv]

/-- Literal chronological prefix consistency of the actual post-setup transcripts. -/
theorem history_drop {n : ℕ} (p : Profile n) (u v : Fin n) (k t : ℕ) :
    (history p u v (k + t)).drop t = history p u v k := by
  simpa only [history, Nat.add_assoc] using VisitBounds.profileTranscript_drop
    (stagedProtocol u v) p (n * n + k) t

/-- Sharing the complete first-u stopping prefix fixes the actual first-u stopping offset.
The stopping property is visible from the current flag and its immediately preceding prefix. -/
theorem firstOffset_eq_of_history_eq {n : ℕ} (p q : Profile n) (u v : Fin n)
    (he : history q u v (firstOffset p u v) = history p u v (firstOffset p u v)) :
    firstOffset q u v = firstOffset p u v := by
  have hk := firstOffset_pos p u v
  have ha : FirstAccepted (n * n) u (history q u v (firstOffset p u v)) := by
    rw [he]
    exact (firstOffset_le_iff p u v _).mp le_rfl
  have hqle := (firstOffset_le_iff q u v _).mpr ha
  have heprev : history q u v (firstOffset p u v - 1) =
      history p u v (firstOffset p u v - 1) := by
    have hh := congrArg (fun L : List (Entry n) ↦ L.drop 1) he
    have hid : firstOffset p u v = (firstOffset p u v - 1) + 1 := by omega
    rw [hid, history_drop, history_drop] at hh
    exact hh
  have hqnot : ¬ FirstAccepted (n * n) u (history q u v (firstOffset p u v - 1)) := by
    rw [heprev]
    intro hprev
    have hh := (firstOffset_le_iff p u v _).mpr hprev
    omega
  have hnle : ¬ firstOffset q u v ≤ firstOffset p u v - 1 :=
    fun hle ↦ hqnot ((firstOffset_le_iff q u v _).mp hle)
  omega

/-- The first-u stopping history is a literal finite original-profile history, not an
auxiliary outcome tree or a geometric reference variable. -/
noncomputable def firstHistory {n : ℕ} (p : Profile n) (u v : Fin n) :
    ProfileHistories.Hist n (n * n + n * n) :=
  ProfileHistories.Hist.encode (history p u v (firstOffset p u v)) (by
    rw [history_length]
    exact Nat.add_le_add_left (firstOffset_le_square p u v) _)

/-- Decoding returns the actual complete first-u acceptance prefix. -/
theorem decode_firstHistory {n : ℕ} (p : Profile n) (u v : Fin n) :
    ProfileHistories.Hist.decode (firstHistory p u v) = history p u v (firstOffset p u v) :=
  ProfileHistories.Hist.decode_encode _ _

/-- Its finite clock is the actual first-u stopping time. -/
theorem clock_firstHistory {n : ℕ} (p : Profile n) (u v : Fin n) :
    ProfileHistories.Hist.clock (firstHistory p u v) = firstTime p u v := by
  rw [firstHistory, ProfileHistories.Hist.clock_encode, history_length]
  rfl

/-- A profile always realizes its own complete first-u stopping prefix. -/
theorem mem_firstHistory {n : ℕ} (p : Profile n) (u v : Fin n) :
    p ∈ ProfileHistories.Hist.prefixEvent (stagedProtocol u v) (firstHistory p u v) := by
  rw [ProfileHistories.Hist.mem_prefixEvent_iff, clock_firstHistory, decode_firstHistory]
  rfl

/-- Any profile sharing that literal prefix has the same complete first-u stopping history. -/
theorem firstHistory_stable {n : ℕ} (p q : Profile n) (u v : Fin n)
    (hq : q ∈ ProfileHistories.Hist.prefixEvent (stagedProtocol u v) (firstHistory p u v)) :
    firstHistory q u v = firstHistory p u v := by
  have he : history q u v (firstOffset p u v) = history p u v (firstOffset p u v) := by
    simpa only [ProfileHistories.Hist.mem_prefixEvent_iff, clock_firstHistory,
      decode_firstHistory, firstTime, history] using hq
  have ht := firstOffset_eq_of_history_eq p q u v he
  apply ProfileHistories.Hist.decode_injective
  rw [decode_firstHistory, decode_firstHistory, ht]
  exact he

/-- The complete stopping prefix also fixes the setup history, with no future event imposed. -/
theorem setup_eq_of_firstHistory {n : ℕ} (p q : Profile n) (u v : Fin n)
    (hq : q ∈ ProfileHistories.Hist.prefixEvent (stagedProtocol u v) (firstHistory p u v)) :
    history q u v 0 = history p u v 0 := by
  have he : history q u v (firstOffset p u v) = history p u v (firstOffset p u v) := by
    simpa only [ProfileHistories.Hist.mem_prefixEvent_iff, clock_firstHistory,
      decode_firstHistory, firstTime, history] using hq
  have hh := congrArg (fun L : List (Entry n) ↦ L.drop (firstOffset p u v)) he
  have hdrop (r : Profile n) :
      (history r u v (firstOffset p u v)).drop (firstOffset p u v) = history r u v 0 :=
    by simpa only [Nat.zero_add] using history_drop r u v 0 (firstOffset p u v)
  rw [hdrop q, hdrop p] at hh
  exact hh

/-- The exact completed setup-prefix event under the original profile law. -/
def setupEvent {n : ℕ} (u v : Fin n) (h0 : List (Entry n)) : Set (Profile n) :=
  {p | history p u v 0 = h0}

/-- The original market conditioned only on its actual completed setup transcript. -/
noncomputable def setupLaw {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n)
    (h0 : List (Entry n)) : PMF (Profile n) := condition μ (setupEvent u v h0)

/-- The actual distribution of the complete first-u stopping history after revealing setup. -/
noncomputable def firstLaw {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n)
    (h0 : List (Entry n)) : PMF (ProfileHistories.Hist n (n * n + n * n)) :=
  (setupLaw μ u v h0).map (fun p ↦ firstHistory p u v)

/-- Future profiles are conditioned only on the literal complete first-u stopping prefix. -/
noncomputable def futureLaw {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n)
    (j : ProfileHistories.Hist n (n * n + n * n)) : PMF (Profile n) :=
  condition μ (ProfileHistories.Hist.prefixEvent (stagedProtocol u v) j)

/-- A realized first-u stopping prefix is exactly setup intersected with that observed stop
label. No future v count or future cap event occurs in this conditioning identity. -/
theorem firstHistory_event_eq {n : ℕ} (p : Profile n) (u v : Fin n) (h0 : List (Entry n))
    (hp : p ∈ setupEvent u v h0) :
    ProfileHistories.Hist.prefixEvent (stagedProtocol u v) (firstHistory p u v) =
      setupEvent u v h0 ∩ {q | firstHistory q u v = firstHistory p u v} := by
  ext q
  constructor
  · intro hq
    exact ⟨(setup_eq_of_firstHistory p q u v hq).trans hp, firstHistory_stable p q u v hq⟩
  · rintro ⟨hsetup, hj⟩
    have hh := mem_firstHistory q u v
    rw [hj] at hh
    exact hh

/-- Every positive stopping branch has the literal original-profile prefix refinement. -/
theorem firstHistory_refines {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n)
    (h0 : List (Entry n)) (hh : eventMass μ (setupEvent u v h0) ≠ 0)
    (j : ProfileHistories.Hist n (n * n + n * n)) (hj : firstLaw μ u v h0 j ≠ 0) :
    ProfileHistories.Hist.prefixEvent (stagedProtocol u v) j =
      setupEvent u v h0 ∩ {p | firstHistory p u v = j} := by
  obtain ⟨p, hp, he⟩ := (PMF.mem_support_map_iff (fun p ↦ firstHistory p u v)
    (setupLaw μ u v h0) j).mp hj
  have hs : p ∈ (condition μ (setupEvent u v h0)).support := hp
  rw [support_condition μ _ hh] at hs
  subst j
  exact firstHistory_event_eq p u v h0 hs.1

/-- A positive stopping branch has a nonnull original stopping-prefix event. -/
theorem firstHistory_nonnull {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n)
    (h0 : List (Entry n)) (hh : eventMass μ (setupEvent u v h0) ≠ 0)
    (j : ProfileHistories.Hist n (n * n + n * n)) (hj : firstLaw μ u v h0 j ≠ 0) :
    eventMass μ (ProfileHistories.Hist.prefixEvent (stagedProtocol u v) j) ≠ 0 := by
  rw [firstHistory_refines μ u v h0 hh j hj, ← eventMass_mul_conditional_event,
    eventMass_observation_fiber]
  exact mul_ne_zero hh hj

/-- Nested conditioning on the actual first-u history gives exactly its original-prefix law. -/
theorem condition_firstHistory {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n)
    (h0 : List (Entry n)) (hh : eventMass μ (setupEvent u v h0) ≠ 0)
    (j : ProfileHistories.Hist n (n * n + n * n)) (hj : firstLaw μ u v h0 j ≠ 0) :
    condition (setupLaw μ u v h0) {p | firstHistory p u v = j} = futureLaw μ u v j := by
  rw [setupLaw, futureLaw, firstHistory_refines μ u v h0 hh j hj]
  exact StoppedProcess.condition_inter μ _ _ (by
    rw [← firstHistory_refines μ u v h0 hh j hj]
    exact firstHistory_nonnull μ u v h0 hh j hj)

/-- Actual finite first-u stopping-history disintegration, derived from observed prefix fibers. -/
theorem first_disintegration {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n)
    (h0 : List (Entry n)) (hh : eventMass μ (setupEvent u v h0) ≠ 0) :
    (firstLaw μ u v h0).bind (futureLaw μ u v) = setupLaw μ u v h0 := by
  calc
    _ = (firstLaw μ u v h0).bind
        (fun j ↦ condition (setupLaw μ u v h0) {p | firstHistory p u v = j}) := by
      apply StoppedProcess.bind_congr_support
      intro j hj
      exact (condition_firstHistory μ u v h0 hh j hj).symm
    _ = setupLaw μ u v h0 := bind_condition_eq _ _

/-- The two priority entrants' actually visited women by the current initial-phase step. -/
noncomputable def visited {n : ℕ} (p : Profile n) (u v : Fin n) (k : ℕ) : Finset (Fin n) :=
  (manOrder (history p u v k) u).toFinset ∪ (manOrder (history p u v k) v).toFinset

/-- Either designated entrant's used destinations belong to the actual visited set. -/
theorem used_subset_visited {n : ℕ} (p : Profile n) (u v m : Fin n) (k : ℕ)
    (hm : m = u ∨ m = v) : (manOrder (history p u v k) m).toFinset ⊆ visited p u v k := by
  rcases hm with rfl | rfl
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

/-- The actual visited set has at most one new woman per genuine initial-phase step. -/
theorem card_visited_le {n : ℕ} (p : Profile n) (u v : Fin n) (huv : u ≠ v) (k : ℕ)
    (hk : k ≤ secondOffset p u v) : (visited p u v k).card ≤ k := by
  calc
    (visited p u v k).card ≤ (manOrder (history p u v k) u).toFinset.card +
        (manOrder (history p u v k) v).toFinset.card := Finset.card_union_le _ _
    _ ≤ (manOrder (history p u v k) u).length + (manOrder (history p u v k) v).length :=
      Nat.add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _)
    _ = (state p u v k).next u + (state p u v k).next v := by
      rw [length_manOrder, length_manOrder]
      rfl
    _ = k := by
      rw [phase_counters p u v huv k hk u, phase_counters p u v huv k hk v]
      simp only [ite_true, ite_eq_right (Ne.symm huv)]
      omega

/-- Actual seen-edge membership is exactly the PR candidate-rank counter prefix. -/
theorem seen_iff_rank_lt {n : ℕ} (p : Profile n) (u v : Fin n) (k : ℕ) (w m : Fin n) :
    (w, m) ∈ seenEdges (history p u v k) ↔ (p.manRank m w).val < (state p u v k).next m :=
  Protocols.seenEdges_iff_hasProposed (stagedProtocol u v) p.manRank _
    (transcript_valid (stagedProtocol u v) p.manRank (profilePriorities p) _) (w, m)

/-- Outside the actual visited women, no seen proposer edge has changed from completed setup. -/
theorem seen_eq_off_visited {n : ℕ} (p : Profile n) (u v : Fin n) (huv : u ≠ v) (k : ℕ)
    (hk : k ≤ secondOffset p u v) (w : Fin n) (hw : w ∉ visited p u v k) (m : Fin n) :
    ((w, m) ∈ seenEdges (history p u v k)) ↔ ((w, m) ∈ seenEdges (history p u v 0)) := by
  classical
  by_cases hmu : m = u
  · subst m
    have hnow : w ∉ manOrder (history p u v k) u := by
      intro hh
      exact hw (Finset.mem_union_left _ (List.mem_toFinset.mpr hh))
    have hpast : ¬ (w, u) ∈ seenEdges (history p u v 0) := by
      rw [seen_iff_rank_lt, (setup_counters p u v).1]
      omega
    simp only [← mem_manOrder_iff_seenEdges, hnow, hpast]
  · by_cases hmv : m = v
    · subst m
      have hnow : w ∉ manOrder (history p u v k) v := by
        intro hh
        exact hw (Finset.mem_union_right _ (List.mem_toFinset.mpr hh))
      have hpast : ¬ (w, v) ∈ seenEdges (history p u v 0) := by
        rw [seen_iff_rank_lt, (setup_counters p u v).2]
        omega
      simp only [← mem_manOrder_iff_seenEdges, hnow, hpast]
    · rw [seen_iff_rank_lt, seen_iff_rank_lt, other_counter_unchanged p u v huv k hk m hmu hmv]

/-- Thus the actual current seen-rate denominator agrees with its fixed setup value at every
unvisited woman; this is proved from actual protocol counters, not assumed as a drift premise. -/
theorem gamma_eq_off_visited {n : ℕ} (p : Profile n) (u v : Fin n) (huv : u ≠ v) (k : ℕ)
    (hk : k ≤ secondOffset p u v) (b : Fin n → ℝ≥0) (w : Fin n) (hw : w ∉ visited p u v k) :
    VisitBounds.gamma b (history p u v k) w = VisitBounds.gamma b (history p u v 0) w := by
  rw [VisitBounds.gamma_eq_filter, VisitBounds.gamma_eq_filter]
  apply Finset.sum_congr
  · ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact seen_eq_off_visited p u v huv k hk w hw m
  · intro m hm
    rfl

/-- The actual next accepted-u record at post-setup time t. -/
def firstSuccess {n : ℕ} (u v : Fin n) (t : ℕ) : Set (Profile n) :=
  {p | ∃ w, observation (stagedProtocol u v) p.manRank (profilePriorities p)
    (history p u v t) = some ((w, u), true)}

/-- The second phase's actual next accepted-v record, indexed from the first-u stopping time. -/
def secondSuccess {n : ℕ} (u v : Fin n) (t : ℕ) : Set (Profile n) :=
  {p | ∃ w, observation (stagedProtocol u v) p.manRank (profilePriorities p)
    (history p u v (firstOffset p u v + t)) = some ((w, v), true)}

/-- Survival of the genuine first count is visible in the current actual ordinal history. -/
theorem A1_survival_iff {n : ℕ} (p : Profile n) (u v : Fin n) (t : ℕ) :
    t < A1 p u v ↔ ¬ FirstAccepted (n * n) u (history p u v t) := by
  rw [A1_eq_firstOffset]
  constructor
  · exact fun ht ha ↦ (not_le_of_gt ht) ((firstOffset_le_iff p u v t).mpr ha)
  · intro ha
    exact Nat.lt_of_not_ge (fun hle ↦ ha ((firstOffset_le_iff p u v t).mp hle))

/-- First-count survival has the literal actual-success recursion, before probability is used. -/
theorem A1_survival_step {n : ℕ} (p : Profile n) (u v : Fin n) (t : ℕ) :
    t + 1 < A1 p u v ↔ t < A1 p u v ∧ p ∉ firstSuccess u v t := by
  rw [A1_survival_iff, A1_survival_iff, history_succ,
    firstAccepted_cons (n * n) u _ _ (by rw [history_length]; omega)]
  tauto

/-- Second-count survival is likewise visible, with time reset at the first-u stopping prefix. -/
theorem A2_survival_iff {n : ℕ} (p : Profile n) (u v : Fin n) (huv : u ≠ v) (t : ℕ) :
    t < A2 p u v ↔
      ¬ FirstAccepted (n * n) v (history p u v (firstOffset p u v + t)) := by
  rw [A2_eq_offset_sub p u v huv]
  have hle := firstOffset_le_secondOffset p u v huv
  constructor
  · intro ht ha
    have hh := (secondOffset_le_iff p u v _).mpr ha
    omega
  · intro ha
    have hh : ¬ secondOffset p u v ≤ firstOffset p u v + t :=
      fun hh ↦ ha ((secondOffset_le_iff p u v _).mp hh)
    omega

/-- The reset second phase also has the exact actual-success survival recursion. -/
theorem A2_survival_step {n : ℕ} (p : Profile n) (u v : Fin n) (huv : u ≠ v) (t : ℕ) :
    t + 1 < A2 p u v ↔ t < A2 p u v ∧ p ∉ secondSuccess u v t := by
  rw [A2_survival_iff p u v huv, A2_survival_iff p u v huv]
  have ht : firstOffset p u v + (t + 1) = (firstOffset p u v + t) + 1 := by omega
  rw [ht, history_succ, firstAccepted_cons (n * n) v _ _ (by rw [history_length]; omega)]
  tauto

/-- Every fixed-time actual current prefix refines the completed setup event literally. -/
theorem current_event_eq {n : ℕ} (p : Profile n) (u v : Fin n) (h0 : List (Entry n))
    (hp : p ∈ setupEvent u v h0) (t : ℕ) :
    ProfileHistories.event (stagedProtocol u v) (history p u v t) =
      setupEvent u v h0 ∩ {q | history q u v t = history p u v t} := by
  ext q
  constructor
  · intro hq
    have he : history q u v t = history p u v t := by
      change profileTranscript (stagedProtocol u v) q (history p u v t).length =
        history p u v t at hq
      rw [history_length] at hq
      exact hq
    have hs : history q u v 0 = history p u v 0 := by
      have hh := congrArg (fun L : List (Entry n) ↦ L.drop t) he
      have hd (r : Profile n) : (history r u v t).drop t = history r u v 0 := by
        simpa only [Nat.zero_add] using history_drop r u v 0 t
      rw [hd q, hd p] at hh
      exact hh
    exact ⟨hs.trans hp, he⟩
  · rintro ⟨hsetup, he⟩
    change profileTranscript (stagedProtocol u v) q (history p u v t).length = history p u v t
    rw [history_length]
    exact he

/-- A nonnull observed current history comes from an actual setup-compatible profile. -/
theorem current_witness {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n)
    (h0 : List (Entry n)) (hh : eventMass μ (setupEvent u v h0) ≠ 0) (t : ℕ)
    (r : List (Entry n))
    (hr : eventMass (setupLaw μ u v h0) {p | history p u v t = r} ≠ 0) :
    ∃ p, p ∈ setupEvent u v h0 ∧ history p u v t = r := by
  have hm : ((setupLaw μ u v h0).map (fun p ↦ history p u v t)) r ≠ 0 := by
    rwa [← eventMass_observation_fiber]
  obtain ⟨p, hp, he⟩ := (PMF.mem_support_map_iff (fun p ↦ history p u v t)
    (setupLaw μ u v h0) r).mp hm
  have hs : p ∈ (condition μ (setupEvent u v h0)).support := hp
  rw [support_condition μ _ hh] at hs
  exact ⟨p, hs.1, he⟩

/-- Conditional current-history fibers are exactly original finite-PR current-prefix laws. -/
theorem condition_current {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n)
    (h0 : List (Entry n)) (hh : eventMass μ (setupEvent u v h0) ≠ 0) (t : ℕ)
    (r : List (Entry n))
    (hr : eventMass (setupLaw μ u v h0) {p | history p u v t = r} ≠ 0) :
    condition (setupLaw μ u v h0) {p | history p u v t = r} =
      ProfileHistories.lawAt μ (stagedProtocol u v) r := by
  obtain ⟨p, hp, he⟩ := current_witness μ u v h0 hh t r hr
  subst r
  rw [setupLaw, ProfileHistories.lawAt, current_event_eq p u v h0 hp t]
  exact StoppedProcess.condition_inter μ _ _ (by
    rw [← eventMass_mul_conditional_event]
    exact mul_ne_zero hh hr)

/-- The baseline setup prefix event contains no extra future-count information. -/
theorem current_nonnull {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n)
    (h0 : List (Entry n)) (hh : eventMass μ (setupEvent u v h0) ≠ 0) (t : ℕ)
    (r : List (Entry n))
    (hr : eventMass (setupLaw μ u v h0) {p | history p u v t = r} ≠ 0) :
    eventMass μ (ProfileHistories.event (stagedProtocol u v) r) ≠ 0 := by
  obtain ⟨p, hp, he⟩ := current_witness μ u v h0 hh t r hr
  subst r
  rw [current_event_eq p u v h0 hp t, ← eventMass_mul_conditional_event]
  exact mul_ne_zero hh hr

/-- The fixed setup-baseline rate for a designated entrant under normalized destination weights. -/
noncomputable def baseline {n : ℕ} (a b : Fin n → ℝ≥0) (h0 : List (Entry n)) (m : Fin n) : ℝ :=
  SmoothRates.rate (InitialDrift.normalized a) (VisitBounds.gamma b h0) (b m : ℝ)

/-- A uniform safe drift constant for at most two cap-many visited destinations. -/
noncomputable def delta (n c : ℕ) (A : ℝ) : ℝ := 8 * A * c / n

/-- The genuine first-phase success hazard stays close to its fixed setup baseline, conditioned
only on a current visible history. Its visited-set hypotheses are conclusions of actual staging. -/
theorem first_local_drift {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 0 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (u v : Fin n) (huv : u ≠ v) (h0 : List (Entry n))
    (hh : eventMass (Continuation.market a b) (setupEvent u v h0) ≠ 0)
    (c t : ℕ) (ht : t < c) (hsmall : 2 * A * c / n ≤ 1 / 2)
    (r : List (Entry n))
    (hr : eventMass (setupLaw (Continuation.market a b) u v h0)
      {p | history p u v t = r} ≠ 0)
    (halive : ¬ FirstAccepted (n * n) u r) :
    |SurvivalKernel.probability
        (condition (setupLaw (Continuation.market a b) u v h0) {p | history p u v t = r})
        (firstSuccess u v t) - baseline a b h0 u| ≤ delta n c A := by
  classical
  obtain ⟨p, hsetup, he⟩ := current_witness (Continuation.market a b) u v h0 hh t r hr
  subst r
  have htu : t < firstOffset p u v := by
    exact Nat.lt_of_not_ge (fun hle ↦ halive ((firstOffset_le_iff p u v t).mp hle))
  have htv : t ≤ secondOffset p u v := (Nat.le_of_lt htu).trans
    (firstOffset_le_secondOffset p u v huv)
  let K := condition (setupLaw (Continuation.market a b) u v h0)
    {q | history q u v t = history p u v t}
  have hprob : SurvivalKernel.probability K (firstSuccess u v t) =
      (eventMass (Continuation.lawAt a b (stagedProtocol u v) (history p u v t))
        (InitialDrift.observedAcceptance (stagedProtocol u v) (history p u v t) u)).toReal := by
    have hevent := InitialDrift.eventMass_congr_support K (firstSuccess u v t)
      (InitialDrift.observedAcceptance (stagedProtocol u v) (history p u v t) u) (by
        intro q hq
        have hhist := (SurvivalKernel.condition_fiber_support
          (setupLaw (Continuation.market a b) u v h0) (fun q ↦ history q u v t)
          (history p u v t) hr q hq).2
        change (∃ w, _ = some ((w, u), true)) ↔ (∃ w, _ = some ((w, u), true))
        rw [hhist])
    unfold SurvivalKernel.probability
    rw [hevent]
    have hK : K = Continuation.lawAt a b (stagedProtocol u v) (history p u v t) :=
      condition_current (Continuation.market a b) u v h0 hh t (history p u v t) hr
    rw [hK]
  rw [hprob]
  have hG : ∀ w, 0 ≤ VisitBounds.gamma b h0 w := by
    intro w
    exact Finset.sum_nonneg fun k _ ↦ (b k.val).coe_nonneg
  apply InitialDrift.observed_acceptance_drift hn a b hA ha1 haA hb
    (stagedProtocol u v) (history p u v t)
    (current_nonnull (Continuation.market a b) u v h0 hh t (history p u v t) hr)
    u (selects_first p u v t htu) (VisitBounds.gamma b h0) hG (visited p u v t) c
  · exact used_subset_visited p u v u t (Or.inl rfl)
  · intro w hw
    change VisitBounds.gamma b (history p u v t) w = VisitBounds.gamma b h0 w
    rw [gamma_eq_off_visited p u v huv t htv b w hw]
    exact congrArg (fun h ↦ VisitBounds.gamma b h w) hsetup
  · exact (card_visited_le p u v huv t htv).trans (by omega)
  · exact hsmall

/-- Actual first-count survival brackets, derived from the current-history rate kernel. -/
theorem first_survival_recursion {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 0 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (u v : Fin n) (huv : u ≠ v) (h0 : List (Entry n))
    (hh : eventMass (Continuation.market a b) (setupEvent u v h0) ≠ 0)
    (c : ℕ) (hsmall : 2 * A * c / n ≤ 1 / 2) (t : ℕ) (ht : t < c) :
    (1 - baseline a b h0 u - delta n c A) *
        HazardMoments.survival (setupLaw (Continuation.market a b) u v h0) (fun p ↦ A1 p u v) t ≤
      HazardMoments.survival (setupLaw (Continuation.market a b) u v h0)
        (fun p ↦ A1 p u v) (t + 1) ∧
    HazardMoments.survival (setupLaw (Continuation.market a b) u v h0)
        (fun p ↦ A1 p u v) (t + 1) ≤
      (1 - baseline a b h0 u + delta n c A) *
        HazardMoments.survival (setupLaw (Continuation.market a b) u v h0)
          (fun p ↦ A1 p u v) t := by
  apply SurvivalKernel.survival_step_of_history_success
    (setupLaw (Continuation.market a b) u v h0) (fun p ↦ A1 p u v)
    (fun p ↦ history p u v t) {r | ¬ FirstAccepted (n * n) u r} (firstSuccess u v t)
    t (baseline a b h0 u) (delta n c A)
  · intro p hp
    exact A1_survival_iff p u v t
  · intro p hp
    exact A1_survival_step p u v t
  · intro r hr halive
    have hd := first_local_drift hn a b hA ha1 haA hb u v huv h0 hh c t ht hsmall r hr halive
    exact ⟨by linarith [(abs_le.mp hd).1], by linarith [(abs_le.mp hd).2]⟩

/-- Actual first-acceptance mean error with explicit finite-tail payment. -/
theorem first_mean_error {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 0 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (u v : Fin n) (huv : u ≠ v) (h0 : List (Entry n))
    (hh : eventMass (Continuation.market a b) (setupEvent u v h0) ≠ 0)
    (c : ℕ) (hsmall : 2 * A * c / n ≤ 1 / 2)
    (hδp : delta n c A < baseline a b h0 u)
    (hpδ : baseline a b h0 u + delta n c A ≤ 1) :
    |HazardMoments.mean (setupLaw (Continuation.market a b) u v h0) (fun p ↦ A1 p u v) -
        1 / baseline a b h0 u| ≤
      delta n c A / (baseline a b h0 u - delta n c A) ^ 2 +
      ((n : ℝ) + 1 / (baseline a b h0 u - delta n c A)) *
        (1 - baseline a b h0 u + delta n c A) ^ c := by
  apply HazardMoments.abs_mean_sub_inv_le
    (setupLaw (Continuation.market a b) u v h0) (fun p ↦ A1 p u v) n c
    (baseline a b h0 u) (delta n c A) (fun p ↦ (A1_bounds p u v).1) (fun p ↦ (A1_bounds p u v).2)
    (by unfold delta; positivity) hδp hpδ
  exact first_survival_recursion hn a b hA ha1 haA hb u v huv h0 hh c hsmall

/-- First-u stopping offsets are fixed by the complete observable stopping prefix. -/
theorem firstOffset_eq_of_prefix {n : ℕ} (p q : Profile n) (u v : Fin n)
    (hq : q ∈ ProfileHistories.Hist.prefixEvent (stagedProtocol u v) (firstHistory p u v)) :
    firstOffset q u v = firstOffset p u v := by
  have hh := congrArg ProfileHistories.Hist.clock (firstHistory_stable p q u v hq)
  rw [clock_firstHistory, clock_firstHistory] at hh
  exact Nat.add_left_cancel hh

/-- The complete current visible history t steps after the actual first-u stopping prefix. -/
noncomputable def afterFirstObservation {n : ℕ} (u v : Fin n) (t : ℕ) (p : Profile n) :
    List (Entry n) := history p u v (firstOffset p u v + t)

/-- A later visible prefix refines the first-u stopping prefix literally, because that earlier
stopping time is itself determined by the revealed shorter prefix. -/
theorem after_first_event_eq {n : ℕ} (p : Profile n) (u v : Fin n) (t : ℕ) :
    ProfileHistories.event (stagedProtocol u v) (afterFirstObservation u v t p) =
      ProfileHistories.Hist.prefixEvent (stagedProtocol u v) (firstHistory p u v) ∩
        {q | afterFirstObservation u v t q = afterFirstObservation u v t p} := by
  ext q
  constructor
  · intro hq
    have he : history q u v (firstOffset p u v + t) =
        history p u v (firstOffset p u v + t) := by
      change profileTranscript (stagedProtocol u v) q
        (history p u v (firstOffset p u v + t)).length = _ at hq
      rw [history_length] at hq
      exact hq
    have hshort : history q u v (firstOffset p u v) = history p u v (firstOffset p u v) := by
      have hh := congrArg (fun L : List (Entry n) ↦ L.drop t) he
      rw [history_drop, history_drop] at hh
      exact hh
    have hprefix : q ∈ ProfileHistories.Hist.prefixEvent
        (stagedProtocol u v) (firstHistory p u v) := by
      rw [ProfileHistories.Hist.mem_prefixEvent_iff, clock_firstHistory, decode_firstHistory]
      exact hshort
    refine ⟨hprefix, ?_⟩
    change history q u v (firstOffset q u v + t) = history p u v (firstOffset p u v + t)
    rw [firstOffset_eq_of_history_eq p q u v hshort]
    exact he
  · rintro ⟨hprefix, he⟩
    change profileTranscript (stagedProtocol u v) q
      (history p u v (firstOffset p u v + t)).length = _
    rw [history_length]
    change history q u v (firstOffset p u v + t) = _
    rw [← firstOffset_eq_of_prefix p q u v hprefix]
    exact he

/-- Every nonnull current observation after first-u acceptance has an actual realization
sharing that first-u stopping prefix. -/
theorem after_first_witness {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n) (p : Profile n)
    (hp : eventMass μ
      (ProfileHistories.Hist.prefixEvent (stagedProtocol u v) (firstHistory p u v)) ≠ 0)
    (t : ℕ) (r : List (Entry n))
    (hr : eventMass (futureLaw μ u v (firstHistory p u v))
      {q | afterFirstObservation u v t q = r} ≠ 0) :
    ∃ q, q ∈ ProfileHistories.Hist.prefixEvent (stagedProtocol u v) (firstHistory p u v) ∧
      afterFirstObservation u v t q = r := by
  have hm : ((futureLaw μ u v (firstHistory p u v)).map (afterFirstObservation u v t)) r ≠ 0 := by
    rwa [← eventMass_observation_fiber]
  obtain ⟨q, hq, he⟩ := (PMF.mem_support_map_iff (afterFirstObservation u v t)
    (futureLaw μ u v (firstHistory p u v)) r).mp hm
  have hs : q ∈ (condition μ
    (ProfileHistories.Hist.prefixEvent (stagedProtocol u v) (firstHistory p u v))).support := hq
  rw [support_condition μ _ hp] at hs
  exact ⟨q, hs.1, he⟩

/-- Legitimate past conditioning in the v phase: current histories are original-profile prefix
laws, with the first-u stopping history retained but no future-count event imposed. -/
theorem condition_after_first {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n) (p : Profile n)
    (hp : eventMass μ
      (ProfileHistories.Hist.prefixEvent (stagedProtocol u v) (firstHistory p u v)) ≠ 0)
    (t : ℕ) (r : List (Entry n))
    (hr : eventMass (futureLaw μ u v (firstHistory p u v))
      {q | afterFirstObservation u v t q = r} ≠ 0) :
    condition (futureLaw μ u v (firstHistory p u v)) {q | afterFirstObservation u v t q = r} =
      ProfileHistories.lawAt μ (stagedProtocol u v) r := by
  obtain ⟨q, hq, he⟩ := after_first_witness μ u v p hp t r hr
  subst r
  have hj := firstHistory_stable p q u v hq
  rw [futureLaw, ProfileHistories.lawAt, after_first_event_eq q u v t, hj]
  exact StoppedProcess.condition_inter μ _ _ (by
    rw [← eventMass_mul_conditional_event]
    exact mul_ne_zero hp hr)

/-- Nonnull current v-phase observations also have nonnull original current-prefix events. -/
theorem after_first_nonnull {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n) (p : Profile n)
    (hp : eventMass μ
      (ProfileHistories.Hist.prefixEvent (stagedProtocol u v) (firstHistory p u v)) ≠ 0)
    (t : ℕ) (r : List (Entry n))
    (hr : eventMass (futureLaw μ u v (firstHistory p u v))
      {q | afterFirstObservation u v t q = r} ≠ 0) :
    eventMass μ (ProfileHistories.event (stagedProtocol u v) r) ≠ 0 := by
  obtain ⟨q, hq, he⟩ := after_first_witness μ u v p hp t r hr
  subst r
  rw [after_first_event_eq q u v t, firstHistory_stable p q u v hq,
    ← eventMass_mul_conditional_event]
  exact mul_ne_zero hp hr

/-- The actual v-phase success hazard has the same setup baseline after conditioning on the
complete first-u stopping prefix. Only the already revealed A1≤cap restriction is used. -/
theorem second_local_drift {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 0 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (u v : Fin n) (huv : u ≠ v) (h0 : List (Entry n))
    (p0 : Profile n) (hsetup : p0 ∈ setupEvent u v h0)
    (hp : eventMass (Continuation.market a b)
      (ProfileHistories.Hist.prefixEvent (stagedProtocol u v) (firstHistory p0 u v)) ≠ 0)
    (c t : ℕ) (hgood : A1 p0 u v ≤ c) (ht : t < c) (hsmall : 2 * A * c / n ≤ 1 / 2)
    (r : List (Entry n))
    (hr : eventMass (futureLaw (Continuation.market a b) u v (firstHistory p0 u v))
      {p | afterFirstObservation u v t p = r} ≠ 0)
    (halive : ¬ FirstAccepted (n * n) v r) :
    |SurvivalKernel.probability
        (condition (futureLaw (Continuation.market a b) u v (firstHistory p0 u v))
          {p | afterFirstObservation u v t p = r}) (secondSuccess u v t) -
      baseline a b h0 v| ≤ delta n c A := by
  classical
  obtain ⟨p, hprefix, he⟩ := after_first_witness (Continuation.market a b) u v p0 hp t r hr
  subst r
  have hk : firstOffset p u v + t < secondOffset p u v :=
    Nat.lt_of_not_ge (fun hle ↦ halive ((secondOffset_le_iff p u v _).mp hle))
  have hpcap : firstOffset p u v ≤ c := by
    rw [firstOffset_eq_of_prefix p0 p u v hprefix, ← A1_eq_firstOffset]
    exact hgood
  have hpsetup : history p u v 0 = h0 := (setup_eq_of_firstHistory p0 p u v hprefix).trans hsetup
  let K := condition (futureLaw (Continuation.market a b) u v (firstHistory p0 u v))
    {q | afterFirstObservation u v t q = afterFirstObservation u v t p}
  have hprob : SurvivalKernel.probability K (secondSuccess u v t) =
      (eventMass (Continuation.lawAt a b (stagedProtocol u v) (afterFirstObservation u v t p))
        (InitialDrift.observedAcceptance (stagedProtocol u v)
          (afterFirstObservation u v t p) v)).toReal := by
    have hevent := InitialDrift.eventMass_congr_support K (secondSuccess u v t)
      (InitialDrift.observedAcceptance (stagedProtocol u v) (afterFirstObservation u v t p) v) (by
        intro q hq
        have hhist := (SurvivalKernel.condition_fiber_support
          (futureLaw (Continuation.market a b) u v (firstHistory p0 u v))
          (afterFirstObservation u v t) (afterFirstObservation u v t p) hr q hq).2
        change (∃ w, _ = some ((w, v), true)) ↔ (∃ w, _ = some ((w, v), true))
        change afterFirstObservation u v t q = afterFirstObservation u v t p at hhist
        change (∃ w, observation (stagedProtocol u v) q.manRank (profilePriorities q)
          (afterFirstObservation u v t q) = some ((w, v), true)) ↔ _
        rw [hhist])
    unfold SurvivalKernel.probability
    rw [hevent]
    have hK : K = Continuation.lawAt a b (stagedProtocol u v) (afterFirstObservation u v t p) :=
      condition_after_first (Continuation.market a b) u v p0 hp t (afterFirstObservation u v t p) hr
    rw [hK]
  rw [hprob]
  have hG : ∀ w, 0 ≤ VisitBounds.gamma b h0 w := by
    intro w
    exact Finset.sum_nonneg fun k _ ↦ (b k.val).coe_nonneg
  apply InitialDrift.observed_acceptance_drift hn a b hA ha1 haA hb
    (stagedProtocol u v) (afterFirstObservation u v t p)
    (after_first_nonnull (Continuation.market a b) u v p0 hp t (afterFirstObservation u v t p) hr)
    v (selects_second p u v _ (by omega) hk) (VisitBounds.gamma b h0) hG
    (visited p u v (firstOffset p u v + t)) c
  · exact used_subset_visited p u v v _ (Or.inr rfl)
  · intro w hw
    change VisitBounds.gamma b (history p u v (firstOffset p u v + t)) w = VisitBounds.gamma b h0 w
    rw [gamma_eq_off_visited p u v huv _ (Nat.le_of_lt hk) b w hw, hpsetup]
  · exact (card_visited_le p u v huv _ (Nat.le_of_lt hk)).trans (by omega)
  · exact hsmall

/-- Actual reset v-count survival brackets under a positive first-u stopping-history law. -/
theorem second_survival_recursion {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 0 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (u v : Fin n) (huv : u ≠ v) (h0 : List (Entry n))
    (p0 : Profile n) (hsetup : p0 ∈ setupEvent u v h0)
    (hp : eventMass (Continuation.market a b)
      (ProfileHistories.Hist.prefixEvent (stagedProtocol u v) (firstHistory p0 u v)) ≠ 0)
    (c : ℕ) (hgood : A1 p0 u v ≤ c) (hsmall : 2 * A * c / n ≤ 1 / 2)
    (t : ℕ) (ht : t < c) :
    (1 - baseline a b h0 v - delta n c A) *
        HazardMoments.survival (futureLaw (Continuation.market a b) u v (firstHistory p0 u v))
          (fun p ↦ A2 p u v) t ≤
      HazardMoments.survival (futureLaw (Continuation.market a b) u v (firstHistory p0 u v))
        (fun p ↦ A2 p u v) (t + 1) ∧
    HazardMoments.survival (futureLaw (Continuation.market a b) u v (firstHistory p0 u v))
        (fun p ↦ A2 p u v) (t + 1) ≤
      (1 - baseline a b h0 v + delta n c A) *
        HazardMoments.survival (futureLaw (Continuation.market a b) u v (firstHistory p0 u v))
          (fun p ↦ A2 p u v) t := by
  apply SurvivalKernel.survival_step_of_history_success
    (futureLaw (Continuation.market a b) u v (firstHistory p0 u v)) (fun p ↦ A2 p u v)
    (afterFirstObservation u v t) {r | ¬ FirstAccepted (n * n) v r} (secondSuccess u v t)
    t (baseline a b h0 v) (delta n c A)
  · intro p hp
    exact A2_survival_iff p u v huv t
  · intro p hp
    exact A2_survival_step p u v huv t
  · intro r hr halive
    have hd := second_local_drift hn a b hA ha1 haA hb u v huv h0 p0 hsetup hp
      c t hgood ht hsmall r hr halive
    exact ⟨by linarith [(abs_le.mp hd).1], by linarith [(abs_le.mp hd).2]⟩

/-- The actual conditional v-count mean is close to the SAME setup baseline on every good
first-u stopping history, with explicit tail error and no future A2 cap conditioning. -/
theorem second_mean_error_after_first {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 0 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (u v : Fin n) (huv : u ≠ v) (h0 : List (Entry n))
    (p0 : Profile n) (hsetup : p0 ∈ setupEvent u v h0)
    (hp : eventMass (Continuation.market a b)
      (ProfileHistories.Hist.prefixEvent (stagedProtocol u v) (firstHistory p0 u v)) ≠ 0)
    (c : ℕ) (hgood : A1 p0 u v ≤ c) (hsmall : 2 * A * c / n ≤ 1 / 2)
    (hδp : delta n c A < baseline a b h0 v)
    (hpδ : baseline a b h0 v + delta n c A ≤ 1) :
    |HazardMoments.mean (futureLaw (Continuation.market a b) u v (firstHistory p0 u v))
        (fun p ↦ A2 p u v) - 1 / baseline a b h0 v| ≤
      delta n c A / (baseline a b h0 v - delta n c A) ^ 2 +
      ((n : ℝ) + 1 / (baseline a b h0 v - delta n c A)) *
        (1 - baseline a b h0 v + delta n c A) ^ c := by
  apply HazardMoments.abs_mean_sub_inv_le
    (futureLaw (Continuation.market a b) u v (firstHistory p0 u v)) (fun p ↦ A2 p u v) n c
    (baseline a b h0 v) (delta n c A) (fun p ↦ (A2_bounds p u v huv).1)
    (fun p ↦ (A2_bounds p u v huv).2) (by unfold delta; positivity) hδp hpδ
  exact second_survival_recursion hn a b hA ha1 haA hb u v huv h0 p0 hsetup hp c hgood hsmall

local instance {n : ℕ} : MeasurableSpace (ProfileHistories.Hist n (n * n + n * n)) := ⊤

/-- The first count is a function of the already revealed first-u stopping history. -/
noncomputable def firstCount {n : ℕ} (u : Fin n)
    (j : ProfileHistories.Hist n (n * n + n * n)) : ℝ :=
  (recordState (ProfileHistories.Hist.decode j)).next u

/-- This observable is exactly the actual count on every realized stopping prefix. -/
theorem firstCount_firstHistory {n : ℕ} (p : Profile n) (u v : Fin n) :
    firstCount u (firstHistory p u v) = (A1 p u v : ℝ) := by
  unfold firstCount
  rw [decode_firstHistory]
  rfl

/-- Positive observed first-u histories have actual setup-compatible realizations. -/
theorem firstHistory_witness {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n)
    (h0 : List (Entry n)) (hh : eventMass μ (setupEvent u v h0) ≠ 0)
    (j : ProfileHistories.Hist n (n * n + n * n)) (hj : firstLaw μ u v h0 j ≠ 0) :
    ∃ p, p ∈ setupEvent u v h0 ∧ firstHistory p u v = j := by
  obtain ⟨p, hp, he⟩ := (PMF.mem_support_map_iff (fun p ↦ firstHistory p u v)
    (setupLaw μ u v h0) j).mp hj
  have hs : p ∈ (condition μ (setupEvent u v h0)).support := hp
  rw [support_condition μ _ hh] at hs
  exact ⟨p, hs.1, he⟩

/-- The actual stopping-history/future joint law is the observed original profile law. -/
theorem first_joint_law {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n)
    (h0 : List (Entry n)) (hh : eventMass μ (setupEvent u v h0) ≠ 0) :
    HazardMoments.historyFuture (firstLaw μ u v h0) (futureLaw μ u v) =
      (setupLaw μ u v h0).map (fun p ↦ (firstHistory p u v, p)) := by
  exact SurvivalKernel.joint_refined_condition μ (setupEvent u v h0) hh
    (fun p ↦ firstHistory p u v)
    (fun j ↦ ProfileHistories.Hist.prefixEvent (stagedProtocol u v) j)
    (firstHistory_refines μ u v h0 hh)

/-- The observable first-count mean is the actual setup-conditioned A1 mean. -/
theorem firstCount_mean {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n) (h0 : List (Entry n)) :
    (∫ j, firstCount u j ∂(firstLaw μ u v h0).toMeasure) =
      HazardMoments.mean (setupLaw μ u v h0) (fun p ↦ A1 p u v) := by
  have hm : Measurable (fun p : Profile n ↦ firstHistory p u v) := measurable_of_finite _
  rw [firstLaw, ← PMF.toMeasure_map _ _ hm,
    integral_map hm.aemeasurable (measurable_of_finite _).aestronglyMeasurable]
  simp only [firstCount_firstHistory]
  rfl

/-- The bad stopping-history mass is exactly the actual setup-conditioned large-A1 probability. -/
theorem first_bad_mass {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n)
    (h0 : List (Entry n)) (c : ℕ) :
    (firstLaw μ u v h0).toMeasure.real {j | (c : ℝ) < firstCount u j} =
      (setupLaw μ u v h0).toMeasure.real {p | c < A1 p u v} := by
  have hm : Measurable (fun p : Profile n ↦ firstHistory p u v) := measurable_of_finite _
  change ((firstLaw μ u v h0).toMeasure {j | (c : ℝ) < firstCount u j}).toReal = _
  rw [firstLaw, ← PMF.toMeasure_map _ _ hm, Measure.map_apply hm (by trivial)]
  have he : (fun p : Profile n ↦ firstHistory p u v) ⁻¹'
      {j | (c : ℝ) < firstCount u j} = {p | c < A1 p u v} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, firstCount_firstHistory, Nat.cast_lt]
  rw [he]
  rfl

/-- The covariance in stopping-history coordinates is exactly the actual A1/A2 covariance
under the original setup-conditioned profile law. -/
theorem covariance_first_joint {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n)
    (h0 : List (Entry n)) (hh : eventMass μ (setupEvent u v h0) ≠ 0) :
    ProbabilityTheory.covariance (fun z : ProfileHistories.Hist n (n * n + n * n) × Profile n ↦
        firstCount u z.1) (fun z ↦ (A2 z.2 u v : ℝ))
      (HazardMoments.historyFuture (firstLaw μ u v h0) (futureLaw μ u v)).toMeasure =
      ProbabilityTheory.covariance (fun p ↦ (A1 p u v : ℝ)) (fun p ↦ (A2 p u v : ℝ))
        (setupLaw μ u v h0).toMeasure := by
  have hm : Measurable (fun p : Profile n ↦ (firstHistory p u v, p)) := measurable_of_finite _
  rw [first_joint_law μ u v h0 hh, ← PMF.toMeasure_map _ _ hm,
    ProbabilityTheory.covariance_map_fun (measurable_of_finite _).aestronglyMeasurable
      (measurable_of_finite _).aestronglyMeasurable hm.aemeasurable]
  simp only [firstCount_firstHistory]

/-- Explicit finite-tail mean error from the actual local drift. -/
noncomputable def error (n c : ℕ) (p δ : ℝ) : ℝ :=
  δ / (p - δ) ^ 2 + ((n : ℝ) + 1 / (p - δ)) * (1 - p + δ) ^ c

/-- The error formula is nonnegative under the stated deterministic baseline conditions. -/
theorem error_nonneg (n c : ℕ) {p δ : ℝ} (hδ : 0 ≤ δ) (hδp : δ < p) (hpδ : p + δ ≤ 1) :
    0 ≤ error n c p δ := by
  have hminus : 0 < p - δ := sub_pos.mpr hδp
  have hbase : 0 ≤ 1 - p + δ := by linarith
  unfold error
  positivity

/-- The actual first-count upper tail is bounded by its derived geometric survival bracket. -/
theorem first_tail_bound {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 0 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (u v : Fin n) (huv : u ≠ v) (h0 : List (Entry n))
    (hh : eventMass (Continuation.market a b) (setupEvent u v h0) ≠ 0)
    (c : ℕ) (hsmall : 2 * A * c / n ≤ 1 / 2)
    (hpδ : baseline a b h0 u + delta n c A ≤ 1) :
    (setupLaw (Continuation.market a b) u v h0).toMeasure.real {p | c < A1 p u v} ≤
      (1 - baseline a b h0 u + delta n c A) ^ c := by
  exact (HazardMoments.survival_geometric_bounds
    (setupLaw (Continuation.market a b) u v h0) (fun p ↦ A1 p u v) c
    (baseline a b h0 u) (delta n c A) (fun p ↦ (A1_bounds p u v).1)
    (by unfold delta; positivity) hpδ
    (first_survival_recursion hn a b hA ha1 haA hb u v huv h0 hh c hsmall) c le_rfl).2

/-- The conditional v-count estimate holds on every positive good observed stopping history. -/
theorem second_mean_error_good_history {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 0 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (u v : Fin n) (huv : u ≠ v) (h0 : List (Entry n))
    (hh : eventMass (Continuation.market a b) (setupEvent u v h0) ≠ 0)
    (c : ℕ) (hsmall : 2 * A * c / n ≤ 1 / 2)
    (hδp : delta n c A < baseline a b h0 v) (hpδ : baseline a b h0 v + delta n c A ≤ 1)
    (j : ProfileHistories.Hist n (n * n + n * n))
    (hj : firstLaw (Continuation.market a b) u v h0 j ≠ 0) (hgood : firstCount u j ≤ c) :
    |HazardMoments.mean (futureLaw (Continuation.market a b) u v j) (fun p ↦ A2 p u v) -
        1 / baseline a b h0 v| ≤ error n c (baseline a b h0 v) (delta n c A) := by
  obtain ⟨p, hp, he⟩ := firstHistory_witness (Continuation.market a b) u v h0 hh j hj
  subst j
  have hc : A1 p u v ≤ c := by
    rw [firstCount_firstHistory] at hgood
    exact_mod_cast hgood
  exact second_mean_error_after_first hn a b hA ha1 haA hb u v huv h0 p hp
    (firstHistory_nonnull (Continuation.market a b) u v h0 hh _ hj)
    c hc hsmall hδp hpδ

/-- Positive stopping-history labels have the same genuine finite first-count bounds. -/
theorem firstCount_bounds {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n)
    (h0 : List (Entry n)) (hh : eventMass μ (setupEvent u v h0) ≠ 0)
    (j : ProfileHistories.Hist n (n * n + n * n)) (hj : firstLaw μ u v h0 j ≠ 0) :
    0 ≤ firstCount u j ∧ firstCount u j ≤ n := by
  obtain ⟨p, hp, he⟩ := firstHistory_witness μ u v h0 hh j hj
  subst j
  rw [firstCount_firstHistory]
  exact ⟨Nat.cast_nonneg _, by exact_mod_cast (A1_bounds p u v).2⟩

/-- The first stopping-history mean bound is derived from the actual first-phase mean estimate. -/
theorem firstCount_mean_upper {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 0 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (u v : Fin n) (huv : u ≠ v) (h0 : List (Entry n))
    (hh : eventMass (Continuation.market a b) (setupEvent u v h0) ≠ 0)
    (c : ℕ) (hsmall : 2 * A * c / n ≤ 1 / 2)
    (hδp : delta n c A < baseline a b h0 u) (hpδ : baseline a b h0 u + delta n c A ≤ 1) :
    (∫ j, firstCount u j ∂(firstLaw (Continuation.market a b) u v h0).toMeasure) ≤
      1 / baseline a b h0 u + error n c (baseline a b h0 u) (delta n c A) := by
  rw [firstCount_mean]
  have hd := first_mean_error hn a b hA ha1 haA hb u v huv h0 hh c hsmall hδp hpδ
  exact (sub_le_iff_le_add.mp (abs_le.mp hd).2).trans_eq (add_comm _ _)

/-- The actual initial counts have the reviewed covariance lower bound, derived only from
past-conditioned local hazards. The bad first-count term is retained explicitly. -/
theorem initial_covariance_lower {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 0 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (u v : Fin n) (huv : u ≠ v) (h0 : List (Entry n))
    (hh : eventMass (Continuation.market a b) (setupEvent u v h0) ≠ 0)
    (c : ℕ) (hsmall : 2 * A * c / n ≤ 1 / 2)
    (hδu : delta n c A < baseline a b h0 u) (hpu : baseline a b h0 u + delta n c A ≤ 1)
    (hδv : delta n c A < baseline a b h0 v) (hpv : baseline a b h0 v + delta n c A ≤ 1)
    (hvn : 1 / baseline a b h0 v ≤ n) :
    -2 * (1 / baseline a b h0 u + error n c (baseline a b h0 u) (delta n c A)) *
        error n c (baseline a b h0 v) (delta n c A) -
      2 * (n : ℝ) ^ 2 * (setupLaw (Continuation.market a b) u v h0).toMeasure.real
        {p | c < A1 p u v} ≤
      ProbabilityTheory.covariance (fun p ↦ (A1 p u v : ℝ)) (fun p ↦ (A2 p u v : ℝ))
        (setupLaw (Continuation.market a b) u v h0).toMeasure := by
  have hδ : 0 ≤ delta n c A := by unfold delta; positivity
  have hpv0 : 0 < baseline a b h0 v := lt_of_le_of_lt hδ hδv
  have hcov := SurvivalKernel.initial_covariance_lower_support
    (firstLaw (Continuation.market a b) u v h0) (futureLaw (Continuation.market a b) u v)
    (firstCount u) (fun _ p ↦ (A2 p u v : ℝ)) (n : ℝ)
    (1 / baseline a b h0 u + error n c (baseline a b h0 u) (delta n c A))
    (error n c (baseline a b h0 v) (delta n c A)) (1 / baseline a b h0 v) (c : ℝ)
    (Nat.cast_nonneg _) (error_nonneg n c hδ hδv hpv)
    (firstCount_bounds (Continuation.market a b) u v h0 hh)
    (fun j hj p hp ↦ ⟨Nat.cast_nonneg _, by exact_mod_cast (A2_bounds p u v huv).2⟩)
    ⟨(one_div_pos.mpr hpv0).le, hvn⟩
    (firstCount_mean_upper hn a b hA ha1 haA hb u v huv h0 hh c hsmall hδu hpu)
    (second_mean_error_good_history hn a b hA ha1 haA hb u v huv h0 hh c hsmall hδv hpv)
  rw [covariance_first_joint (Continuation.market a b) u v h0 hh,
    first_bad_mass (Continuation.market a b) u v h0 c] at hcov
  exact hcov

/-- A finite real mean close on positive good labels pays only a bounded bad-label tail. -/
theorem mean_error_of_close_support {H : Type*} [Fintype H] [MeasurableSpace H]
    [MeasurableSingletonClass H] (ν : PMF H) (f : H → ℝ) (good : Set H) (N ε c : ℝ)
    (hε : 0 ≤ ε) (hf : ∀ h, ν h ≠ 0 → 0 ≤ f h ∧ f h ≤ N)
    (hc : 0 ≤ c ∧ c ≤ N) (hclose : ∀ h, ν h ≠ 0 → h ∈ good → |f h - c| ≤ ε) :
    |(∫ h, f h ∂ν.toMeasure) - c| ≤ ε + N * ν.toMeasure.real goodᶜ := by
  classical
  have hi (g : H → ℝ) : Integrable g ν.toMeasure :=
    (G2Deconditioning.memLp_finite ν.toMeasure g).integrable one_le_two
  have hpoint : ∀ᵐ h ∂ν.toMeasure, |f h - c| ≤ ε + goodᶜ.indicator (fun _ ↦ N) h := by
    filter_upwards [SurvivalKernel.ae_positive_support ν] with h hh
    by_cases hg : h ∈ good
    · have hn : h ∉ goodᶜ := by simpa only [Set.mem_compl_iff, not_not] using hg
      rw [Set.indicator_of_notMem hn, add_zero]
      exact hclose h hh hg
    · rw [Set.indicator_of_mem hg]
      have habs : |f h - c| ≤ N := abs_le.mpr ⟨by linarith [(hf h hh).1],
        by linarith [(hf h hh).2]⟩
      linarith
  have hbound := integral_mono_ae (hi _) (hi _) hpoint
  rw [integral_add (integrable_const ε) (hi _), integral_const,
    integral_indicator_const N (Set.toFinite goodᶜ).measurableSet] at hbound
  simp only [probReal_univ, smul_eq_mul, one_mul, mul_comm (ν.toMeasure.real goodᶜ) N] at hbound
  have he : (∫ h, f h - c ∂ν.toMeasure) = (∫ h, f h ∂ν.toMeasure) - c := by
    rw [integral_sub (hi _) (integrable_const c), integral_const]
    simp only [probReal_univ, one_smul]
  rw [← he]
  exact abs_integral_le_integral_abs.trans hbound

/-- The unconditional actual v-count mean pays explicitly for large first-u histories. No
future A2 event is conditioned upon, and null stopping labels impose no estimate. -/
theorem second_mean_error {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 0 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (u v : Fin n) (huv : u ≠ v) (h0 : List (Entry n))
    (hh : eventMass (Continuation.market a b) (setupEvent u v h0) ≠ 0)
    (c : ℕ) (hsmall : 2 * A * c / n ≤ 1 / 2)
    (hδv : delta n c A < baseline a b h0 v) (hpv : baseline a b h0 v + delta n c A ≤ 1)
    (hvn : 1 / baseline a b h0 v ≤ n) :
    |HazardMoments.mean (setupLaw (Continuation.market a b) u v h0) (fun p ↦ A2 p u v) -
        1 / baseline a b h0 v| ≤ error n c (baseline a b h0 v) (delta n c A) +
      (n : ℝ) * (setupLaw (Continuation.market a b) u v h0).toMeasure.real {p | c < A1 p u v} := by
  let μ := Continuation.market a b
  let ν := firstLaw μ u v h0
  let f := fun j ↦ HazardMoments.mean (futureLaw μ u v j) (fun p ↦ A2 p u v)
  have hδ : 0 ≤ delta n c A := by unfold delta; positivity
  have hpv0 : 0 < baseline a b h0 v := lt_of_le_of_lt hδ hδv
  have hbound := mean_error_of_close_support ν f {j | firstCount u j ≤ (c : ℝ)} (n : ℝ)
    (error n c (baseline a b h0 v) (delta n c A)) (1 / baseline a b h0 v)
    (error_nonneg n c hδ hδv hpv)
    (fun j hj ↦ SurvivalKernel.integral_bounds_support (futureLaw μ u v j)
      (fun p ↦ (A2 p u v : ℝ)) (n : ℝ)
      (fun p hp ↦ ⟨Nat.cast_nonneg _, by exact_mod_cast (A2_bounds p u v huv).2⟩))
    ⟨(one_div_pos.mpr hpv0).le, hvn⟩
    (second_mean_error_good_history hn a b hA ha1 haA hb u v huv h0 hh c hsmall hδv hpv)
  have hmean : HazardMoments.mean (setupLaw μ u v h0) (fun p ↦ A2 p u v) =
      ∫ j, f j ∂ν.toMeasure := by
    unfold HazardMoments.mean
    rw [← first_disintegration μ u v h0 hh]
    exact G2Deconditioning.integral_bind ν (futureLaw μ u v) (fun p ↦ (A2 p u v : ℝ))
  have hbad : ({j | firstCount u j ≤ (c : ℝ)} : Set (ProfileHistories.Hist n (n * n + n * n)))ᶜ =
      {j | (c : ℝ) < firstCount u j} := by
    ext j
    simp
  rw [hbad] at hbound
  change |(∫ j, f j ∂ν.toMeasure) - 1 / baseline a b h0 v| ≤ _ at hbound
  rw [← hmean, first_bad_mass μ u v h0 c] at hbound
  exact hbound

/-- An entirely numerical actual second-count mean error, using the derived first-count tail. -/
theorem second_mean_error_geometric_tail {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 0 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (u v : Fin n) (huv : u ≠ v) (h0 : List (Entry n))
    (hh : eventMass (Continuation.market a b) (setupEvent u v h0) ≠ 0)
    (c : ℕ) (hsmall : 2 * A * c / n ≤ 1 / 2)
    (hpu : baseline a b h0 u + delta n c A ≤ 1)
    (hδv : delta n c A < baseline a b h0 v) (hpv : baseline a b h0 v + delta n c A ≤ 1)
    (hvn : 1 / baseline a b h0 v ≤ n) :
    |HazardMoments.mean (setupLaw (Continuation.market a b) u v h0) (fun p ↦ A2 p u v) -
        1 / baseline a b h0 v| ≤ error n c (baseline a b h0 v) (delta n c A) +
      (n : ℝ) * (1 - baseline a b h0 u + delta n c A) ^ c := by
  exact (second_mean_error hn a b hA ha1 haA hb u v huv h0 hh c hsmall hδv hpv hvn).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (first_tail_bound hn a b hA ha1 haA hb u v huv h0 hh c hsmall hpu) (Nat.cast_nonneg n)))

/-- An entirely numerical actual covariance lower bound, with the first-count bad history
controlled by its independently derived survival tail. -/
theorem initial_covariance_lower_geometric_tail {n : ℕ} (hn : 0 < n)
    (a b : Fin n → ℝ≥0) {A : ℝ} (hA : 0 ≤ A)
    (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (u v : Fin n) (huv : u ≠ v) (h0 : List (Entry n))
    (hh : eventMass (Continuation.market a b) (setupEvent u v h0) ≠ 0)
    (c : ℕ) (hsmall : 2 * A * c / n ≤ 1 / 2)
    (hδu : delta n c A < baseline a b h0 u) (hpu : baseline a b h0 u + delta n c A ≤ 1)
    (hδv : delta n c A < baseline a b h0 v) (hpv : baseline a b h0 v + delta n c A ≤ 1)
    (hvn : 1 / baseline a b h0 v ≤ n) :
    -2 * (1 / baseline a b h0 u + error n c (baseline a b h0 u) (delta n c A)) *
        error n c (baseline a b h0 v) (delta n c A) -
      2 * (n : ℝ) ^ 2 * (1 - baseline a b h0 u + delta n c A) ^ c ≤
      ProbabilityTheory.covariance (fun p ↦ (A1 p u v : ℝ)) (fun p ↦ (A2 p u v : ℝ))
        (setupLaw (Continuation.market a b) u v h0).toMeasure := by
  have hcov := initial_covariance_lower hn a b hA ha1 haA hb u v huv h0 hh c hsmall
    hδu hpu hδv hpv hvn
  have htail := first_tail_bound hn a b hA ha1 haA hb u v huv h0 hh c hsmall hpu
  have he := mul_le_mul_of_nonneg_left htail (show 0 ≤ 2 * (n : ℝ) ^ 2 by positivity)
  linarith

end Ashlagi.InitialPhase
