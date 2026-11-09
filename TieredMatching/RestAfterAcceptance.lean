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

public import TieredMatching.InitialPhase
public import TieredMatching.RestBounds
public import TieredMatching.LowDestinations

/-! # Actual rest means after the two staged first acceptances

Both first-acceptance prefixes are literal stopping observations under the original staged
setup law. Smooth high destinations use the proved held-target rest theorem. Low destinations
and large ordinary ranks are paid under the original law, never conditioned away.
-/

@[expose] public section

namespace TieredMatching.RestAfterAcceptance

open StableMarriage MeasureTheory TieredMatching.Ordinal Protocols FiniteConditioning
open scoped ENNReal NNReal

/-- The two incoming men in the staged insertion protocol. -/
inductive Side where
  | first
  | second
  deriving DecidableEq

/-- The selected entrant's fixed label. -/
def man {n : ℕ} : Side → Fin n → Fin n → Fin n
  | .first, u, _ => u
  | .second, _, v => v

/-- The actual first-acceptance offset of either incoming man. -/
noncomputable def offset {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) : ℕ :=
  match side with
  | .first => InitialPhase.firstOffset p u v
  | .second => InitialPhase.secondOffset p u v

/-- The actual proposal count through that entrant's first acceptance. -/
noncomputable def initialCount {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) : ℕ :=
  match side with
  | .first => InitialPhase.A1 p u v
  | .second => InitialPhase.A2 p u v

/-- The exact original PR terminal proposal counter of either entrant. -/
noncomputable def rank {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) : ℕ :=
  (deferredAcceptance p).next (man side u v)

/-- The exact remaining ordinary proposals after the entrant's first acceptance. -/
noncomputable def rest {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) : ℕ :=
  rank side p u v - initialCount side p u v

/-- A stopping offset is visible exactly through the entrant's accepted record flag. -/
theorem offset_le_iff {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) (k : ℕ) :
    offset side p u v ≤ k ↔
      FirstAccepted (n * n) (man side u v) (InitialPhase.history p u v k) := by
  cases side with
  | first => exact InitialPhase.firstOffset_le_iff p u v k
  | second => exact InitialPhase.secondOffset_le_iff p u v k

/-- Both actual first acceptances occur strictly after the staged setup. -/
theorem offset_pos {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) :
    0 < offset side p u v := by
  cases side with
  | first => exact InitialPhase.firstOffset_pos p u v
  | second => exact InitialPhase.secondOffset_pos p u v

/-- The bounded staged protocol horizon includes both first acceptances. -/
theorem offset_le_square {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) :
    offset side p u v ≤ n * n := by
  cases side with
  | first => exact InitialPhase.firstOffset_le_square p u v
  | second => exact InitialPhase.secondOffset_le_square p u v

/-- Each initial count is exactly the entrant's replayed counter at the accepted prefix. -/
theorem initialCount_eq_counter {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) :
    initialCount side p u v =
      (InitialPhase.state p u v (offset side p u v)).next (man side u v) := by
  cases side <;> rfl

/-- The first-acceptance count is bounded by the unchanged PR terminal counter. -/
theorem initialCount_le_rank {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) :
    initialCount side p u v ≤ rank side p u v := by
  rw [initialCount_eq_counter]
  apply Continuation.profile_counter_le_pr (stagedProtocol u v) p
    (InitialPhase.history p u v (offset side p u v)) _ (man side u v)
  rw [InitialPhase.history_length]
  rfl

/-- Initial proposals plus actual rest proposals give the exact terminal rank. -/
theorem rank_eq_initial_add_rest {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) :
    rank side p u v = initialCount side p u v + rest side p u v := by
  exact (Nat.add_sub_of_le (initialCount_le_rank side p u v)).symm

/-- Every actual rest count is bounded by the complete preference-list length. -/
theorem rest_le_n {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) : rest side p u v ≤ n :=
  (Nat.sub_le _ _).trans (terminal_next_le p (man side u v))

/-- At either first acceptance, the literal newest record is that entrant's accepted edge. -/
theorem accepted_head {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) :
    ∃ w, InitialPhase.history p u v (offset side p u v) = some ((w, man side u v), true) ::
      InitialPhase.history p u v (offset side p u v - 1) := by
  have hk := offset_pos side p u v
  have ha := (offset_le_iff side p u v _).mp le_rfl
  have hprev : ¬ FirstAccepted (n * n) (man side u v)
      (InitialPhase.history p u v (offset side p u v - 1)) := by
    intro hp
    have hh := (offset_le_iff side p u v _).mpr hp
    omega
  obtain ⟨w, hw⟩ := InitialPhase.first_record p u v (man side u v)
    (offset side p u v) hk ha hprev
  refine ⟨w, ?_⟩
  calc
    _ = InitialPhase.history p u v ((offset side p u v - 1) + 1) := by congr 1; omega
    _ = _ := by rw [InitialPhase.history_succ, hw]

/-- The first-accepted destination is read solely from the actual stopping prefix. -/
def targetOfHistory {n : ℕ} (fallback : Fin n) (h : List (Entry n)) : Fin n :=
  match h.head? with
  | some (some ((w, _), true)) => w
  | _ => fallback

/-- Either incoming man's actual first-accepted destination. -/
noncomputable def target {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) : Fin n :=
  targetOfHistory u (InitialPhase.history p u v (offset side p u v))

/-- The target is held at its first-accepted destination under the exact raw ordinal replay. -/
theorem held_at_acceptance {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) :
    (InitialPhase.state p u v (offset side p u v)).held (target side p u v) =
      some (man side u v) := by
  obtain ⟨w, hw⟩ := accepted_head side p u v
  simp only [InitialPhase.state, target, hw, targetOfHistory, List.head?_cons]
  simp only [recordState, recordStep, ite_true, Function.update_self]

/-- Equality of a complete acceptance prefix determines that entrant's first stopping time. -/
theorem offset_eq_of_history_eq {n : ℕ} (side : Side) (p q : Profile n) (u v : Fin n)
    (he : InitialPhase.history q u v (offset side p u v) =
      InitialPhase.history p u v (offset side p u v)) : offset side q u v = offset side p u v := by
  have hk := offset_pos side p u v
  have ha : FirstAccepted (n * n) (man side u v)
      (InitialPhase.history q u v (offset side p u v)) := by
    rw [he]
    exact (offset_le_iff side p u v _).mp le_rfl
  have hqle := (offset_le_iff side q u v _).mpr ha
  have heprev : InitialPhase.history q u v (offset side p u v - 1) =
      InitialPhase.history p u v (offset side p u v - 1) := by
    have hh := congrArg (fun L : List (Entry n) ↦ L.drop 1) he
    have hid : offset side p u v = (offset side p u v - 1) + 1 := by omega
    rw [hid, InitialPhase.history_drop, InitialPhase.history_drop] at hh
    exact hh
  have hqnot : ¬ FirstAccepted (n * n) (man side u v)
      (InitialPhase.history q u v (offset side p u v - 1)) := by
    rw [heprev]
    intro hp
    have hh := (offset_le_iff side p u v _).mpr hp
    omega
  have hnle : ¬ offset side q u v ≤ offset side p u v - 1 :=
    fun hle ↦ hqnot ((offset_le_iff side q u v _).mp hle)
  omega

/-- A canonical actual first-acceptance prefix for either entrant. -/
noncomputable def acceptanceHistory {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) :
    ProfileHistories.Hist n (n * n + n * n) :=
  ProfileHistories.Hist.encode (InitialPhase.history p u v (offset side p u v)) (by
    rw [InitialPhase.history_length]
    exact Nat.add_le_add_left (offset_le_square side p u v) _)

/-- The literal stopping prefix decodes exactly. -/
theorem decode_acceptanceHistory {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) :
    ProfileHistories.Hist.decode (acceptanceHistory side p u v) =
      InitialPhase.history p u v (offset side p u v) := ProfileHistories.Hist.decode_encode _ _

/-- Its clock is the exact complete first-acceptance observation time. -/
theorem clock_acceptanceHistory {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) :
    ProfileHistories.Hist.clock (acceptanceHistory side p u v) = n * n + offset side p u v := by
  rw [acceptanceHistory, ProfileHistories.Hist.clock_encode, InitialPhase.history_length]

/-- Every actual profile realizes its own first-acceptance prefix. -/
theorem mem_acceptanceHistory {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) :
    p ∈ ProfileHistories.Hist.prefixEvent (stagedProtocol u v) (acceptanceHistory side p u v) := by
  rw [ProfileHistories.Hist.mem_prefixEvent_iff, clock_acceptanceHistory, decode_acceptanceHistory]
  rfl

/-- Sharing that complete stopping prefix fixes the original actual stopping label. -/
theorem acceptanceHistory_stable {n : ℕ} (side : Side) (p q : Profile n) (u v : Fin n)
    (hq : q ∈ ProfileHistories.Hist.prefixEvent (stagedProtocol u v)
      (acceptanceHistory side p u v)) :
    acceptanceHistory side q u v = acceptanceHistory side p u v := by
  have he : InitialPhase.history q u v (offset side p u v) =
      InitialPhase.history p u v (offset side p u v) := by
    simpa only [ProfileHistories.Hist.mem_prefixEvent_iff, clock_acceptanceHistory,
      decode_acceptanceHistory, InitialPhase.history] using hq
  have ht := offset_eq_of_history_eq side p q u v he
  apply ProfileHistories.Hist.decode_injective
  rw [decode_acceptanceHistory, decode_acceptanceHistory, ht]
  exact he

/-- A complete first-acceptance prefix retains the original staged setup. -/
theorem setup_eq_of_acceptanceHistory {n : ℕ} (side : Side) (p q : Profile n) (u v : Fin n)
    (hq : q ∈ ProfileHistories.Hist.prefixEvent (stagedProtocol u v)
      (acceptanceHistory side p u v)) :
    InitialPhase.history q u v 0 = InitialPhase.history p u v 0 := by
  have he : InitialPhase.history q u v (offset side p u v) =
      InitialPhase.history p u v (offset side p u v) := by
    simpa only [ProfileHistories.Hist.mem_prefixEvent_iff, clock_acceptanceHistory,
      decode_acceptanceHistory, InitialPhase.history] using hq
  have hh := congrArg (fun L : List (Entry n) ↦ L.drop (offset side p u v)) he
  have hdrop (r : Profile n) :
      (InitialPhase.history r u v (offset side p u v)).drop (offset side p u v) =
        InitialPhase.history r u v 0 := by
    simpa only [Nat.zero_add] using InitialPhase.history_drop r u v 0 (offset side p u v)
  rw [hdrop q, hdrop p] at hh
  exact hh

/-- The actual distribution of either entrant's first accepted prefix under original setup. -/
noncomputable def acceptanceLaw {n : ℕ} (μ : PMF (Profile n)) (side : Side) (u v : Fin n)
    (h0 : List (Entry n)) : PMF (ProfileHistories.Hist n (n * n + n * n)) :=
  (InitialPhase.setupLaw μ u v h0).map (fun p ↦ acceptanceHistory side p u v)

/-- Each actual accepted prefix is literally the setup event intersected with its stop label. -/
theorem acceptanceHistory_event_eq {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n)
    (h0 : List (Entry n)) (hp : p ∈ InitialPhase.setupEvent u v h0) :
    ProfileHistories.Hist.prefixEvent (stagedProtocol u v) (acceptanceHistory side p u v) =
      InitialPhase.setupEvent u v h0 ∩
        {q | acceptanceHistory side q u v = acceptanceHistory side p u v} := by
  ext q
  constructor
  · intro hq
    exact ⟨(setup_eq_of_acceptanceHistory side p q u v hq).trans hp,
      acceptanceHistory_stable side p q u v hq⟩
  · rintro ⟨_, hq⟩
    rw [← hq]
    exact mem_acceptanceHistory side q u v

/-- Every positive first-acceptance label has its exact original-law prefix refinement. -/
theorem acceptanceHistory_refines {n : ℕ} (μ : PMF (Profile n)) (side : Side)
    (u v : Fin n) (h0 : List (Entry n))
    (hh : eventMass μ (InitialPhase.setupEvent u v h0) ≠ 0)
    (r : ProfileHistories.Hist n (n * n + n * n)) (hr : acceptanceLaw μ side u v h0 r ≠ 0) :
    ProfileHistories.Hist.prefixEvent (stagedProtocol u v) r =
      InitialPhase.setupEvent u v h0 ∩ {p | acceptanceHistory side p u v = r} := by
  obtain ⟨p, hp, he⟩ := (PMF.mem_support_map_iff (fun p ↦ acceptanceHistory side p u v)
    (InitialPhase.setupLaw μ u v h0) r).mp hr
  have hs : p ∈ (condition μ (InitialPhase.setupEvent u v h0)).support := hp
  rw [support_condition _ _ hh] at hs
  subst r
  exact acceptanceHistory_event_eq side p u v h0 hs.1

/-- The actual finite first-acceptance prefix tower holds for either incoming man. -/
theorem acceptance_disintegration {n : ℕ} (μ : PMF (Profile n)) (side : Side)
    (u v : Fin n) (h0 : List (Entry n))
    (hh : eventMass μ (InitialPhase.setupEvent u v h0) ≠ 0) :
    (acceptanceLaw μ side u v h0).bind (InitialPhase.futureLaw μ u v) =
      InitialPhase.setupLaw μ u v h0 := by
  exact SurvivalKernel.bind_refined_condition μ (InitialPhase.setupEvent u v h0) hh
    (fun p ↦ acceptanceHistory side p u v)
    (ProfileHistories.Hist.prefixEvent (stagedProtocol u v))
    (acceptanceHistory_refines μ side u v h0 hh)

/-- Both acceptance offsets are reached no later than the second entrant's first acceptance. -/
theorem offset_le_second {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) (huv : u ≠ v) :
    offset side p u v ≤ InitialPhase.secondOffset p u v := by
  cases side with
  | first => exact InitialPhase.firstOffset_le_secondOffset p u v huv
  | second => exact le_rfl

/-- The two visible entrant counters add up to either first-acceptance offset. -/
theorem counters_sum_eq_offset {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) (huv : u ≠ v) :
    (InitialPhase.state p u v (offset side p u v)).next u +
      (InitialPhase.state p u v (offset side p u v)).next v = offset side p u v := by
  rw [InitialPhase.phase_counters p u v huv _ (offset_le_second side p u v huv) u,
    InitialPhase.phase_counters p u v huv _ (offset_le_second side p u v huv) v]
  simp only [ite_true, ite_eq_right (Ne.symm huv)]
  omega

/-- At every actual acceptance prefix, either entrant's exposed counter is below its exact
ordinary PR terminal counter, independently of later scheduling. -/
theorem counter_at_acceptance_le_rank {n : ℕ} (side : Side) (p : Profile n)
    (u v m : Fin n) :
    (InitialPhase.state p u v (offset side p u v)).next m ≤ (deferredAcceptance p).next m := by
  apply Continuation.profile_counter_le_pr (stagedProtocol u v) p
    (InitialPhase.history p u v (offset side p u v)) _ m
  rw [InitialPhase.history_length]
  rfl

/-- If both exact final ranks are below cap, each first acceptance occurs before 2*cap. -/
theorem offset_le_twice_cap_of_ranks {n : ℕ} (side : Side) (p : Profile n)
    (u v : Fin n) (huv : u ≠ v) (cap : ℕ)
    (hu : (deferredAcceptance p).next u ≤ cap) (hv : (deferredAcceptance p).next v ≤ cap) :
    offset side p u v ≤ 2 * cap := by
  have hsum := counters_sum_eq_offset side p u v huv
  have hcu := (counter_at_acceptance_le_rank side p u v u).trans hu
  have hcv := (counter_at_acceptance_le_rank side p u v v).trans hv
  omega

/-- The actual accepted observation at either first stopping time has its visible target. -/
theorem observation_at_acceptance {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) :
    observation (stagedProtocol u v) p.manRank (profilePriorities p)
      (InitialPhase.history p u v (offset side p u v - 1)) =
      some ((target side p u v, man side u v), true) := by
  obtain ⟨w, hw⟩ := accepted_head side p u v
  have hk := offset_pos side p u v
  have hh : InitialPhase.history p u v (offset side p u v) =
      observation (stagedProtocol u v) p.manRank (profilePriorities p)
        (InitialPhase.history p u v (offset side p u v - 1)) ::
          InitialPhase.history p u v (offset side p u v - 1) := by
    have he : offset side p u v = (offset side p u v - 1) + 1 := by omega
    conv_lhs => rw [he, InitialPhase.history_succ]
  have hobs := (List.cons.inj (hh.symm.trans hw)).1
  have ht : target side p u v = w := by simp only [target, hw, targetOfHistory, List.head?_cons]
  rw [ht]
  exact hobs

/-- The selected proposer immediately before either first acceptance is exactly that entrant. -/
theorem selection_at_acceptance {n : ℕ} (side : Side) (p : Profile n) (u v : Fin n) :
    selected (stagedProtocol u v) (InitialPhase.history p u v (offset side p u v - 1)) =
      some (man side u v) := by
  have hn := ((observation_eq_some_iff _ _ _ _ _ _).mp (observation_at_acceptance side p u v)).1
  have hm := nextEdge_map_man (stagedProtocol u v) p.manRank
    (InitialPhase.history p u v (offset side p u v - 1))
  simpa only [hn, Option.map_some] using hm.symm

/-- Every visible pre-acceptance counter is bounded by its final ordinary PR counter. -/
theorem current_counter_le_rank {n : ℕ} (p : Profile n) (u v : Fin n) (t : ℕ) (m : Fin n) :
    (InitialPhase.state p u v t).next m ≤ (deferredAcceptance p).next m := by
  apply Continuation.profile_counter_le_pr (stagedProtocol u v) p (InitialPhase.history p u v t) _ m
  rw [InitialPhase.history_length]
  rfl

/-- Actual finite event probabilities respect inclusion on positive original outcomes. -/
theorem probability_mono_support {Ω : Type*} [Fintype Ω] (μ : PMF Ω) (E F : Set Ω)
    (hEF : ∀ p, μ p ≠ 0 → p ∈ E → p ∈ F) :
    (eventMass μ E).toReal ≤ (eventMass μ F).toReal := by
  classical
  rw [← VisitBounds.expectation_indicator_one, ← VisitBounds.expectation_indicator_one]
  apply Continuation.expectation_mono_support
  intro p hp
  by_cases he : p ∈ E
  · have hf := hEF p hp he
    simp only [Set.indicator_of_mem he, Set.indicator_of_mem hf, le_refl]
  · simp only [Set.indicator_of_notMem he]
    by_cases hf : p ∈ F <;> simp only [Set.indicator_apply, hf, ↓reduceIte] <;> norm_num

/-- The actual finite union bound, with no independence hypothesis. -/
theorem probability_union_le {Ω : Type*} [Fintype Ω] (μ : PMF Ω) (E F : Set Ω) :
    (eventMass μ (E ∪ F)).toReal ≤ (eventMass μ E).toReal + (eventMass μ F).toReal := by
  classical
  rw [← VisitBounds.expectation_indicator_one, ← VisitBounds.expectation_indicator_one,
    ← VisitBounds.expectation_indicator_one, ← Continuation.expectation_add]
  apply Continuation.expectation_mono_support
  intro p hp
  by_cases he : p ∈ E <;> by_cases hf : p ∈ F <;>
    simp only [Set.indicator_apply, Set.mem_union, he, hf, or_self, true_or, false_or,
      ↓reduceIte] <;> norm_num

/-- Deterministic smooth assumptions at the actual original staged setup boundary. -/
structure SmoothSetup (n : ℕ) where
  a : Fin n → ℝ≥0
  b : Fin n → ℝ≥0
  u : Fin n
  v : Fin n
  distinct : u ≠ v
  h0 : List (Entry n)
  A : ℝ
  B : ℝ
  C : ℝ
  κ : ℝ
  ζ : ℝ
  low : Finset (Fin n)
  n_ge : 8 ≤ n
  log_ge : 1 ≤ Real.log n
  A_ge : 1 ≤ A
  B_ge : 1 ≤ B
  C_nonneg : 0 ≤ C
  κ_pos : 0 < κ
  ζ_pos : 0 < ζ
  a_ge : ∀ w, 1 ≤ (a w : ℝ)
  a_le : ∀ w, (a w : ℝ) ≤ A
  b_ge : ∀ m, 1 ≤ (b m : ℝ)
  b_le : ∀ m, (b m : ℝ) ≤ B
  nonnull : eventMass (Continuation.market a b) (InitialPhase.setupEvent u v h0) ≠ 0
  total : (potential (recordState h0) : ℝ) ≤ C * n * Real.log n
  low_card : (low.card : ℝ) ≤ (n : ℝ) ^ (1 - κ)
  high : ∀ w, w ∉ low → ζ * Real.log n ≤ VisitBounds.gamma b h0 w

namespace SmoothSetup

variable {n : ℕ} (S : SmoothSetup n)

/-- The unchanged original profile market. -/
noncomputable def market : PMF (Profile n) := Continuation.market S.a S.b

/-- The actual original staged setup conditional law. -/
noncomputable def law : PMF (Profile n) := InitialPhase.setupLaw S.market S.u S.v S.h0

/-- A positive staged setup fiber has a genuine profile witness. -/
theorem exists_profile : ∃ p : Profile n, InitialPhase.history p S.u S.v 0 = S.h0 := by
  obtain ⟨p, hp⟩ := S.law.support_nonempty
  have hs : p ∈ (condition S.market (InitialPhase.setupEvent S.u S.v S.h0)).support := hp
  dsimp only [market] at hs
  rw [support_condition _ _ S.nonnull] at hs
  exact ⟨p, hs.1⟩

/-- The visible setup prefix has exactly the completed setup clock. -/
theorem setup_length : S.h0.length = n * n := by
  obtain ⟨p, hp⟩ := S.exists_profile
  rw [← hp, InitialPhase.history_length, Nat.add_zero]

/-- The completed original setup has zero counters for both incoming men. -/
theorem setup_counters : (recordState S.h0).next S.u = 0 ∧ (recordState S.h0).next S.v = 0 := by
  obtain ⟨p, hp⟩ := S.exists_profile
  simpa only [InitialPhase.state, ← hp] using InitialPhase.setup_counters p S.u S.v

/-- The actual staged setup has exactly two empty women. -/
theorem setup_empty : (VisitBounds.emptyWomen S.h0).card = 2 := by
  obtain ⟨p, hp⟩ := S.exists_profile
  rw [← hp]
  exact stagedProtocol_setup_empty_card p S.u S.v S.distinct

/-- The source Continuation setup event equals the original staged setup event literally. -/
theorem setup_event_eq : Continuation.historyEvent (stagedProtocol S.u S.v) S.h0 =
    InitialPhase.setupEvent S.u S.v S.h0 := by
  ext p
  simp only [Continuation.historyEvent, InitialPhase.setupEvent, InitialPhase.history,
    Set.mem_ofPred_eq, S.setup_length, Nat.add_zero]

/-- The source continuation instance at the original staged setup, for either entrant. -/
noncomputable def rootSetting (side : Side) : Continuation.Setting n where
  a := S.a
  b := S.b
  setupProtocol := stagedProtocol S.u S.v
  setup := S.h0
  man := man side S.u S.v
  A := S.A
  B := S.B
  C := S.C
  K := ContinuationAsymptotics.globalCoefficient S.A 4
  L := Real.log n
  n_ge := S.n_ge
  A_ge := S.A_ge
  B_ge := S.B_ge
  C_nonneg := S.C_nonneg
  K_nonneg := by unfold ContinuationAsymptotics.globalCoefficient; nlinarith [S.A_ge]
  L_ge := S.log_ge
  a_ge := S.a_ge
  a_le := S.a_le
  b_ge := S.b_ge
  b_le := S.b_le
  setup_nonnull := by rw [S.setup_event_eq]; exact S.nonnull
  setup_total := S.total
  setup_quarter := by
    have hn : (0 : ℝ) < n := by have := S.n_ge; exact_mod_cast (by omega : 0 < n)
    cases side <;> simp only [man, S.setup_counters.1, S.setup_counters.2, Nat.cast_zero]
    all_goals exact div_pos hn (by norm_num)
  setup_empty := S.setup_empty.le

/-- The continuation source law is precisely the original staged setup conditional law. -/
theorem rootSetting_law (side : Side) :
    Continuation.lawAt (S.rootSetting side).a (S.rootSetting side).b
      (S.rootSetting side).setupProtocol (S.rootSetting side).setup = S.law := by
  change condition S.market (Continuation.historyEvent (stagedProtocol S.u S.v) S.h0) = _
  rw [S.setup_event_eq]
  rfl

/-- The initial counters are zero, so the root continuation count is the exact final PR rank. -/
theorem rootSetting_count (side : Side) (p : Profile n) :
    (S.rootSetting side).ordinaryCount p = rank side p S.u S.v := by
  change (deferredAcceptance p).next (man side S.u S.v) -
    (recordState S.h0).next (man side S.u S.v) = _
  cases side <;> simp only [man, S.setup_counters.1, S.setup_counters.2, Nat.sub_zero, rank]

/-- The fixed squared-logarithm ordinary rank cap used for all exceptional branches. -/
noncomputable def cap : ℕ := ContinuationAsymptotics.threshold
  (ContinuationAsymptotics.tailCoefficient S.A S.B S.C 4) n

/-- Actual final-rank exceptions, under the original law rather than a future-conditioned law. -/
def rankBad : Set (Profile n) :=
  {p | S.cap ≤ rank .first p S.u S.v ∨ S.cap ≤ rank .second p S.u S.v}

/-- Both actual ordinary rank tails bound the entire original-law rank exception. -/
theorem rankBad_probability_le {ε : ℝ}
    (hfirst : (eventMass S.law {p | S.cap ≤ rank .first p S.u S.v}).toReal ≤ ε)
    (hsecond : (eventMass S.law {p | S.cap ≤ rank .second p S.u S.v}).toReal ≤ ε) :
    (eventMass S.law S.rankBad).toReal ≤ 2 * ε := by
  have he : S.rankBad = {p | S.cap ≤ rank .first p S.u S.v} ∪
      {p | S.cap ≤ rank .second p S.u S.v} := by ext p; rfl
  rw [he]
  exact (probability_union_le _ _ _).trans (by linarith)

/-- Either entrant's actual first accepted destination belongs to the deterministic low set. -/
def lowTarget (side : Side) : Set (Profile n) := {p | target side p S.u S.v ∈ S.low}

/-- A low first-accepted target before the rank exceptions is a guarded actual low visit by
2*cap. The rank event is used only for this pathwise union inclusion, never for conditioning. -/
theorem lowTarget_subset_union (side : Side) :
    S.lowTarget side ⊆ LowDestinations.futureEvent (stagedProtocol S.u S.v) S.h0
      (2 * S.cap) S.low (2 * S.cap) ∪ S.rankBad := by
  intro p hp
  by_cases hbad : p ∈ S.rankBad
  · exact Or.inr hbad
  have hu : (deferredAcceptance p).next S.u < S.cap := by
    by_contra hn
    exact hbad (Or.inl (Nat.le_of_not_gt hn))
  have hv : (deferredAcceptance p).next S.v < S.cap := by
    by_contra hn
    exact hbad (Or.inr (Nat.le_of_not_gt hn))
  have htime := offset_le_twice_cap_of_ranks side p S.u S.v S.distinct S.cap hu.le hv.le
  have hpos := offset_pos side p S.u S.v
  refine Or.inl ⟨offset side p S.u S.v - 1, by omega, ?_⟩
  rw [S.setup_length]
  change LowDestinations.hit (stagedProtocol S.u S.v)
    (InitialPhase.history p S.u S.v (offset side p S.u S.v - 1)) (2 * S.cap) S.low p
  refine ⟨?_, target side p S.u S.v, hp, man side S.u S.v, ?_⟩
  · intro m hm
    have hsel := selection_at_acceptance side p S.u S.v
    have heq : m = man side S.u S.v := Option.some.inj (hm.symm.trans hsel)
    subst m
    have hb := current_counter_le_rank p S.u S.v (offset side p S.u S.v - 1) (man side S.u S.v)
    change (InitialPhase.state p S.u S.v (offset side p S.u S.v - 1)).next
      (man side S.u S.v) ≤ 2 * S.cap
    cases side <;> simp only [man] at hb ⊢ <;> omega
  · exact ((observation_eq_some_iff _ _ _ _ _ _).mp (observation_at_acceptance side p S.u S.v)).1

/-- The original staged setup law agrees with the general literal-history conditional law. -/
theorem law_eq_history : S.law = ProfileHistories.lawAt (VisitBounds.profileLaw S.a S.b)
    (stagedProtocol S.u S.v) S.h0 := by
  change condition S.market (InitialPhase.setupEvent S.u S.v S.h0) =
    condition (VisitBounds.profileLaw S.a S.b)
      (ProfileHistories.event (stagedProtocol S.u S.v) S.h0)
  rw [← S.setup_event_eq]
  rfl

/-- The selected-counter guarded low-visit bound applies to the exact original setup law. -/
theorem lowVisit_probability_le (hsmall : S.A * (2 * S.cap : ℕ) / n ≤ 1 / 2) :
    (eventMass S.law (LowDestinations.futureEvent (stagedProtocol S.u S.v) S.h0
      (2 * S.cap) S.low (2 * S.cap))).toReal ≤
        4 * S.cap * LowDestinations.lowMass S.a S.low := by
  have hn : 0 < n := by have := S.n_ge; omega
  have hp : eventMass (VisitBounds.profileLaw S.a S.b)
      (ProfileHistories.event (stagedProtocol S.u S.v) S.h0) ≠ 0 := by
    change eventMass (Continuation.market S.a S.b)
      (Continuation.historyEvent (stagedProtocol S.u S.v) S.h0) ≠ 0
    rw [S.setup_event_eq]
    exact S.nonnull
  rw [S.law_eq_history]
  have hb := LowDestinations.future_probability_le hn S.a S.b S.A_ge S.a_ge S.a_le
    (fun m ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (S.b_ge m))
    (stagedProtocol S.u S.v) S.h0 hp (2 * S.cap) S.low hsmall (2 * S.cap)
  convert hb using 1
  push_cast
  ring

/-- The low accepted-target probability pays the predictable low-visit bound and only the
two actual ordinary rank-tail exceptions. -/
theorem lowTarget_probability_le (side : Side)
    (hsmall : S.A * (2 * S.cap : ℕ) / n ≤ 1 / 2) {ε : ℝ}
    (hfirst : (eventMass S.law {p | S.cap ≤ rank .first p S.u S.v}).toReal ≤ ε)
    (hsecond : (eventMass S.law {p | S.cap ≤ rank .second p S.u S.v}).toReal ≤ ε) :
    (eventMass S.law (S.lowTarget side)).toReal ≤
      4 * S.cap * LowDestinations.lowMass S.a S.low + 2 * ε := by
  apply (probability_mono_support S.law _ _ (fun p _ hp ↦ S.lowTarget_subset_union side hp)).trans
  exact (probability_union_le _ _ _).trans
    (add_le_add (S.lowVisit_probability_le hsmall) (S.rankBad_probability_le hfirst hsecond))

/-- The actual first-acceptance label law, for either entrant. -/
noncomputable def acceptanceLaw (side : Side) : PMF (ProfileHistories.Hist n (n * n + n * n)) :=
  RestAfterAcceptance.acceptanceLaw S.market side S.u S.v S.h0

/-- The original profile law conditioned on the literal actual first-acceptance prefix. -/
noncomputable def futureLaw (r : ProfileHistories.Hist n (n * n + n * n)) : PMF (Profile n) :=
  InitialPhase.futureLaw S.market S.u S.v r

/-- All good-branch conditions are properties of the already revealed accepted prefix. -/
def goodLabels : Set (ProfileHistories.Hist n (n * n + n * n)) :=
  {r | (recordState (ProfileHistories.Hist.decode r)).next S.u ≤ S.cap ∧
    (recordState (ProfileHistories.Hist.decode r)).next S.v ≤ S.cap ∧
      targetOfHistory S.u (ProfileHistories.Hist.decode r) ∉ S.low}

/-- Positive stopping labels have a literal realized setup/profile witness. -/
theorem label_witness (side : Side) (r : ProfileHistories.Hist n (n * n + n * n))
    (hr : S.acceptanceLaw side r ≠ 0) :
    ∃ p, InitialPhase.history p S.u S.v 0 = S.h0 ∧ acceptanceHistory side p S.u S.v = r := by
  obtain ⟨p, hp, he⟩ :=
    (PMF.mem_support_map_iff (fun p ↦ acceptanceHistory side p S.u S.v) S.law r).mp hr
  have hs : p ∈ (condition S.market (InitialPhase.setupEvent S.u S.v S.h0)).support := hp
  have hpos : eventMass S.market (InitialPhase.setupEvent S.u S.v S.h0) ≠ 0 := S.nonnull
  rw [support_condition _ _ hpos] at hs
  exact ⟨p, hs.1, he⟩

/-- Every positive accepted prefix has positive original event mass. -/
theorem label_nonnull (side : Side) (r : ProfileHistories.Hist n (n * n + n * n))
    (hr : S.acceptanceLaw side r ≠ 0) :
    eventMass S.market (ProfileHistories.Hist.prefixEvent (stagedProtocol S.u S.v) r) ≠ 0 := by
  rw [RestAfterAcceptance.acceptanceHistory_refines S.market side S.u S.v S.h0 S.nonnull r hr]
  exact SurvivalKernel.refined_event_nonnull S.market _ S.nonnull _ _ hr

/-- Genuine staged proposal totals increase by at most one per revealed entry. -/
theorem potential_history_le (p : Profile n) (hp : InitialPhase.history p S.u S.v 0 = S.h0)
    (t : ℕ) :
    potential (InitialPhase.state p S.u S.v t) ≤ potential (recordState S.h0) + t := by
  induction t with
  | zero => simp only [InitialPhase.state, hp, Nat.add_zero, le_refl]
  | succ t ih =>
    change potential (recordState (InitialPhase.history p S.u S.v (t + 1))) ≤ _
    rw [InitialPhase.history_succ]
    cases he : observation (stagedProtocol S.u S.v) p.manRank (profilePriorities p)
        (InitialPhase.history p S.u S.v t) with
    | none => exact ih.trans (by omega)
    | some e =>
      obtain ⟨q, accepted⟩ := e
      rw [Continuation.potential_record]
      change potential (recordState (InitialPhase.history p S.u S.v t)) ≤ _ at ih
      omega

/-- The good stopping labels satisfy every deterministic held/high continuation hypothesis. -/
theorem good_label_properties (side : Side) (r : ProfileHistories.Hist n (n * n + n * n))
    (hr : S.acceptanceLaw side r ≠ 0) (hg : r ∈ S.goodLabels) :
    let h := ProfileHistories.Hist.decode r
    let w := targetOfHistory S.u h
    (recordState h).held w = some (man side S.u S.v) ∧ S.h0.IsSuffix h ∧
      (recordState h).next (man side S.u S.v) ≤ S.cap ∧
      potential (recordState h) ≤ potential (recordState S.h0) + 2 * S.cap ∧
      (VisitBounds.emptyWomen h).card ≤ 2 ∧ S.ζ * Real.log n ≤ VisitBounds.gamma S.b h w := by
  obtain ⟨p, hp, he⟩ := S.label_witness side r hr
  subst r
  change (recordState (ProfileHistories.Hist.decode
    (acceptanceHistory side p S.u S.v))).held _ = _ ∧ _
  change (recordState (ProfileHistories.Hist.decode
    (acceptanceHistory side p S.u S.v))).next S.u ≤ S.cap ∧
    (recordState (ProfileHistories.Hist.decode
      (acceptanceHistory side p S.u S.v))).next S.v ≤ S.cap ∧
      targetOfHistory S.u (ProfileHistories.Hist.decode
        (acceptanceHistory side p S.u S.v)) ∉ S.low at hg
  rw [decode_acceptanceHistory] at hg ⊢
  have hsuffix : S.h0.IsSuffix (InitialPhase.history p S.u S.v (offset side p S.u S.v)) := by
    have hh := Continuation.profileTranscript_suffix (stagedProtocol S.u S.v) p (n * n)
      (offset side p S.u S.v)
    have hh0 : profileTranscript (stagedProtocol S.u S.v) p (n * n) = S.h0 := hp
    simpa only [hh0, InitialPhase.history] using hh
  have ht : offset side p S.u S.v ≤ 2 * S.cap := by
    have hsum := counters_sum_eq_offset side p S.u S.v S.distinct
    have hu := hg.1
    have hv := hg.2.1
    change (InitialPhase.state p S.u S.v (offset side p S.u S.v)).next S.u ≤ S.cap at hu
    change (InitialPhase.state p S.u S.v (offset side p S.u S.v)).next S.v ≤ S.cap at hv
    omega
  refine ⟨held_at_acceptance side p S.u S.v, hsuffix, ?_, ?_, ?_, ?_⟩
  · cases side with
    | first => exact hg.1
    | second => exact hg.2.1
  · exact (S.potential_history_le p hp _).trans (Nat.add_le_add_left ht _)
  · exact (Finset.card_le_card (Continuation.emptyWomen_suffix_subset _ _ hsuffix)).trans
      S.setup_empty.le
  · have hdrop : (InitialPhase.history p S.u S.v (offset side p S.u S.v)).drop
        (offset side p S.u S.v) = S.h0 := by
      simpa only [Nat.zero_add, hp] using
        InitialPhase.history_drop p S.u S.v 0 (offset side p S.u S.v)
    have hmono := VisitBounds.gamma_drop_le S.b
      (InitialPhase.history p S.u S.v (offset side p S.u S.v))
      (targetOfHistory S.u (InitialPhase.history p S.u S.v (offset side p S.u S.v)))
      (offset side p S.u S.v)
    rw [hdrop] at hmono
    exact (S.high _ hg.2.2).trans hmono

/-- A good actually revealed acceptance prefix is a genuine held-target continuation setup. -/
noncomputable def goodSetting (side : Side) (r : ProfileHistories.Hist n (n * n + n * n))
    (hr : S.acceptanceLaw side r ≠ 0) (hg : r ∈ S.goodLabels)
    (hquarter : (S.cap : ℝ) < (n : ℝ) / 4) (htime : 2 * (S.cap : ℝ) ≤ n * Real.log n) :
    Continuation.Setting n where
  a := S.a
  b := S.b
  setupProtocol := stagedProtocol S.u S.v
  setup := ProfileHistories.Hist.decode r
  man := man side S.u S.v
  A := S.A
  B := S.B
  C := S.C + 1
  K := 3 * S.A
  L := Real.log n
  n_ge := S.n_ge
  A_ge := S.A_ge
  B_ge := S.B_ge
  C_nonneg := by linarith [S.C_nonneg]
  K_nonneg := by linarith [S.A_ge]
  L_ge := S.log_ge
  a_ge := S.a_ge
  a_le := S.a_le
  b_ge := S.b_ge
  b_le := S.b_le
  setup_nonnull := S.label_nonnull side r hr
  setup_total := by
    have hp := (S.good_label_properties side r hr hg).2.2.2.1
    have hp' : (potential (recordState (ProfileHistories.Hist.decode r)) : ℝ) ≤
        (potential (recordState S.h0) : ℝ) + 2 * S.cap := by exact_mod_cast hp
    nlinarith [S.total]
  setup_quarter := by
    have hc : ((recordState (ProfileHistories.Hist.decode r)).next
        (man side S.u S.v) : ℝ) ≤ S.cap := by
      exact_mod_cast (S.good_label_properties side r hr hg).2.2.1
    linarith
  setup_empty := (S.good_label_properties side r hr hg).2.2.2.2.1

/-- The good continuation's source law is exactly the original first-acceptance prefix law. -/
theorem goodSetting_law (side : Side) (r : ProfileHistories.Hist n (n * n + n * n))
    (hr : S.acceptanceLaw side r ≠ 0) (hg : r ∈ S.goodLabels)
    (hquarter : (S.cap : ℝ) < (n : ℝ) / 4) (htime : 2 * (S.cap : ℝ) ≤ n * Real.log n) :
    let T := S.goodSetting side r hr hg hquarter htime
    Continuation.lawAt T.a T.b T.setupProtocol T.setup = S.futureLaw r := rfl

/-- On positive accepted-prefix support, the actual remaining count is the child continuation
counter. No terminal-rank event is added to this conditioning identity. -/
theorem rest_eq_child_count (side : Side) (r : ProfileHistories.Hist n (n * n + n * n))
    (hr : S.acceptanceLaw side r ≠ 0) (hg : r ∈ S.goodLabels)
    (hquarter : (S.cap : ℝ) < (n : ℝ) / 4) (htime : 2 * (S.cap : ℝ) ≤ n * Real.log n)
    (p : Profile n) (hp : S.futureLaw r p ≠ 0) :
    rest side p S.u S.v = (S.goodSetting side r hr hg hquarter htime).ordinaryCount p := by
  have he := SurvivalKernel.refined_support_observation S.market
    (InitialPhase.setupEvent S.u S.v S.h0)
    S.nonnull (fun p ↦ acceptanceHistory side p S.u S.v)
    (ProfileHistories.Hist.prefixEvent (stagedProtocol S.u S.v)) r hr
    (RestAfterAcceptance.acceptanceHistory_refines S.market side S.u S.v S.h0 S.nonnull r hr) p hp
  have hc : initialCount side p S.u S.v =
      (recordState (ProfileHistories.Hist.decode r)).next (man side S.u S.v) := by
    rw [← he, decode_acceptanceHistory]
    exact initialCount_eq_counter side p S.u S.v
  change rank side p S.u S.v - initialCount side p S.u S.v =
    (deferredAcceptance p).next (man side S.u S.v) - _
  rw [hc]
  rfl

/-- The full ordinary low-set probability mass is small under the deterministic smooth setup. -/
theorem lowMass_le : LowDestinations.lowMass S.a S.low ≤ S.A * (n : ℝ) ^ (-S.κ) := by
  have hn : 0 < n := by have := S.n_ge; omega
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ S.A * S.low.card / n := LowDestinations.lowMass_le_card hn S.a S.A_ge S.a_ge S.a_le S.low
    _ ≤ S.A * (n : ℝ) ^ (1 - S.κ) / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left S.low_card (by linarith [S.A_ge])) hN.le
    _ = _ := by
      rw [sub_eq_add_neg, Real.rpow_add hN, Real.rpow_one]
      field_simp

/-- Positive literal accepted-prefix support fixes the actually observed stopping label. -/
theorem prefix_support_label (side : Side) (r : ProfileHistories.Hist n (n * n + n * n))
    (hr : S.acceptanceLaw side r ≠ 0) (p : Profile n) (hp : S.futureLaw r p ≠ 0) :
    acceptanceHistory side p S.u S.v = r := by
  exact SurvivalKernel.refined_support_observation S.market
    (InitialPhase.setupEvent S.u S.v S.h0) S.nonnull
    (fun p ↦ acceptanceHistory side p S.u S.v)
    (ProfileHistories.Hist.prefixEvent (stagedProtocol S.u S.v)) r hr
    (RestAfterAcceptance.acceptanceHistory_refines S.market side S.u S.v S.h0 S.nonnull r hr) p hp

/-- The original-law expectation tower over actual first-acceptance prefixes. -/
theorem expectation_acceptance (side : Side) (f : Profile n → ℝ) :
    VisitBounds.expectation S.law f = ∑ r, (S.acceptanceLaw side r).toReal *
      VisitBounds.expectation (S.futureLaw r) f := by
  change VisitBounds.expectation (InitialPhase.setupLaw S.market S.u S.v S.h0) f = _
  conv_lhs =>
    rw [← RestAfterAcceptance.acceptance_disintegration S.market side S.u S.v S.h0 S.nonnull]
  rw [ProfileHistories.expectation_bind]
  rfl

/-- The part of the actual rest count carried by already revealed good accepted prefixes. -/
noncomputable def goodRest (side : Side) : Profile n → ℝ :=
  {p | acceptanceHistory side p S.u S.v ∈ S.goodLabels}.indicator
    (fun p ↦ (rest side p S.u S.v : ℝ))

/-- Actual good-prefix conditional means integrate to a bound under the original setup law. -/
theorem goodRest_mean_le (side : Side) {K : ℝ} (hK : 0 ≤ K)
    (hmean : ∀ r, S.acceptanceLaw side r ≠ 0 → r ∈ S.goodLabels →
      VisitBounds.expectation (S.futureLaw r) (fun p ↦ (rest side p S.u S.v : ℝ)) ≤ K) :
    VisitBounds.expectation S.law (S.goodRest side) ≤ K := by
  classical
  rw [S.expectation_acceptance side]
  calc
    _ ≤ ∑ r, (S.acceptanceLaw side r).toReal * K := by
      apply Finset.sum_le_sum
      intro r _
      by_cases hr : S.acceptanceLaw side r = 0
      · simp only [hr, ENNReal.toReal_zero, zero_mul, le_refl]
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      by_cases hg : r ∈ S.goodLabels
      · have he : VisitBounds.expectation (S.futureLaw r) (S.goodRest side) =
            VisitBounds.expectation (S.futureLaw r) (fun p ↦ (rest side p S.u S.v : ℝ)) := by
          apply Continuation.expectation_congr_support
          intro p hp
          have hl := S.prefix_support_label side r hr p hp
          simp only [goodRest, Set.indicator_of_mem (show p ∈
            {p | acceptanceHistory side p S.u S.v ∈ S.goodLabels} from by
              change acceptanceHistory side p S.u S.v ∈ S.goodLabels
              rw [hl]
              exact hg)]
        rw [he]
        exact hmean r hr hg
      · have he : VisitBounds.expectation (S.futureLaw r) (S.goodRest side) = 0 := by
          calc
            _ = VisitBounds.expectation (S.futureLaw r) (fun _ ↦ 0) := by
              apply Continuation.expectation_congr_support
              intro p hp
              have hl := S.prefix_support_label side r hr p hp
              simp only [goodRest, Set.indicator_of_notMem (show p ∉
                {p | acceptanceHistory side p S.u S.v ∈ S.goodLabels} from fun hm ↦ hg (hl ▸ hm))]
            _ = 0 := Continuation.expectation_const _ _
        rw [he]
        exact hK
    _ = K := by rw [← Finset.sum_mul, Continuation.sum_mass_real, one_mul]

/-- The bad-prefix remainder pays a small low-target event and the ordinary-rank exceptions.
The good branch itself uses only visible prefix information. -/
theorem rest_le_goodRest_add (side : Side) (p : Profile n) :
    (rest side p S.u S.v : ℝ) ≤ S.goodRest side p +
      (S.cap : ℝ) * (S.lowTarget side).indicator (fun _ ↦ (1 : ℝ)) p +
      (n : ℝ) * S.rankBad.indicator (fun _ ↦ (1 : ℝ)) p := by
  classical
  have hrest : (0 : ℝ) ≤ rest side p S.u S.v := Nat.cast_nonneg _
  have hgood : 0 ≤ S.goodRest side p := Set.indicator_nonneg (fun _ _ ↦ Nat.cast_nonneg _) p
  have hlow : 0 ≤ (S.cap : ℝ) * (S.lowTarget side).indicator (fun _ ↦ (1 : ℝ)) p :=
    mul_nonneg (Nat.cast_nonneg _) (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) p)
  by_cases hb : p ∈ S.rankBad
  · rw [Set.indicator_of_mem hb]
    have hn : (rest side p S.u S.v : ℝ) ≤ n := by exact_mod_cast rest_le_n side p S.u S.v
    nlinarith
  by_cases hg : acceptanceHistory side p S.u S.v ∈ S.goodLabels
  · have he : S.goodRest side p = (rest side p S.u S.v : ℝ) := by
      apply Set.indicator_of_mem
      exact hg
    rw [he, Set.indicator_of_notMem hb]
    nlinarith
  have hu : (deferredAcceptance p).next S.u < S.cap := by
    by_contra hn
    exact hb (Or.inl (Nat.le_of_not_gt hn))
  have hv : (deferredAcceptance p).next S.v < S.cap := by
    by_contra hn
    exact hb (Or.inr (Nat.le_of_not_gt hn))
  have hlowp : p ∈ S.lowTarget side := by
    by_contra hnl
    apply hg
    change _ ≤ S.cap ∧ _ ≤ S.cap ∧ _ ∉ S.low
    rw [decode_acceptanceHistory]
    refine ⟨(current_counter_le_rank p S.u S.v _ S.u).trans hu.le,
      (current_counter_le_rank p S.u S.v _ S.v).trans hv.le, ?_⟩
    exact hnl
  have hrc : (rest side p S.u S.v : ℝ) ≤ S.cap := by
    have hr : rest side p S.u S.v ≤ rank side p S.u S.v := Nat.sub_le _ _
    cases side <;> simp only [rank, man] at hr ⊢
    · exact_mod_cast hr.trans hu.le
    · exact_mod_cast hr.trans hv.le
  rw [Set.indicator_of_mem hlowp, Set.indicator_of_notMem hb]
  nlinarith

/-- Integrating the actual prefix split gives the original-law rest bound. -/
theorem rest_mean_le_split (side : Side) {K : ℝ} (hK : 0 ≤ K)
    (hmean : ∀ r, S.acceptanceLaw side r ≠ 0 → r ∈ S.goodLabels →
      VisitBounds.expectation (S.futureLaw r) (fun p ↦ (rest side p S.u S.v : ℝ)) ≤ K) :
    VisitBounds.expectation S.law (fun p ↦ (rest side p S.u S.v : ℝ)) ≤ K +
      (S.cap : ℝ) * (eventMass S.law (S.lowTarget side)).toReal +
      (n : ℝ) * (eventMass S.law S.rankBad).toReal := by
  have hb := Continuation.expectation_mono_support S.law
    (fun p ↦ (rest side p S.u S.v : ℝ)) _ (fun p _ ↦ S.rest_le_goodRest_add side p)
  rw [Continuation.expectation_add, Continuation.expectation_add,
    Continuation.expectation_const_mul, Continuation.expectation_const_mul,
    VisitBounds.expectation_indicator_one, VisitBounds.expectation_indicator_one] at hb
  linarith [S.goodRest_mean_le side hK hmean]

end SmoothSetup


open Filter in
/-- Both ordinary PR ranks have the uniform actual continuation tail directly from setup.
No initial-phase survival or terminal good event is used to establish this bound. -/
theorem eventually_rank_tails {A B C : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ S : SmoothSetup n, S.A = A → S.B = B → S.C = C → ∀ side : Side,
      (eventMass S.law {p | S.cap ≤ rank side p S.u S.v}).toReal ≤ 4 * (n : ℝ) ^ (-(4 : ℝ)) := by
  filter_upwards [ContinuationAsymptotics.eventually_uniform_canonical_bounds hA hB hC
    (by norm_num : (0 : ℝ) ≤ 4)]
    with n htail S hSA hSB hSC side
  have hs :=
    (htail (S.rootSetting side) hSA hSB hSC (by simp only [SmoothSetup.rootSetting, hSA]) rfl).2
  rw [S.rootSetting_law] at hs
  simpa only [S.rootSetting_count, SmoothSetup.cap, hSA, hSB, hSC] using hs

open Filter in
/-- Actual good acceptance prefixes have a uniformly bounded future rest mean. The child
law is the original market law conditioned on precisely that already observed prefix. -/
theorem eventually_good_prefix_means {A B C ζ : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C) (hζ : 0 < ζ) :
    ∀ᶠ n : ℕ in atTop, ∀ S : SmoothSetup n, S.A = A → S.B = B → S.C = C → S.ζ = ζ →
      ∀ side : Side, ∀ r, S.acceptanceLaw side r ≠ 0 → r ∈ S.goodLabels →
        VisitBounds.expectation (S.futureLaw r) (fun p ↦ (rest side p S.u S.v : ℝ)) ≤
          RestBounds.restConstant A B (C + 1) (3 * A) ζ := by
  have hApos : 0 < A := by linarith
  have hCp : 0 ≤ C + 1 := by linarith
  have hD := (ContinuationAsymptotics.coefficients_pos hA hB hC (by norm_num : (0 : ℝ) ≤ 4)).2.1
  filter_upwards [RestBounds.eventually_uniform_rest_mean_constant hA hB hCp (le_refl (3 * A)) hζ,
    LowDestinations.eventually_threshold_guards hApos hD]
    with n hrest hguard S hSA hSB hSC hSζ side r hr hg
  have hcap : S.cap = ContinuationAsymptotics.threshold
      (ContinuationAsymptotics.tailCoefficient A B C 4) n := by
    simp only [SmoothSetup.cap, hSA, hSB, hSC]
  have hquarter : (S.cap : ℝ) < (n : ℝ) / 4 := by
    have hcnat : S.cap < n / 4 := by simpa only [hcap] using hguard.2.1
    have hc : (S.cap : ℝ) < (n / 4 : ℕ) := by exact_mod_cast hcnat
    exact hc.trans_le (Nat.cast_div_le (α := ℝ))
  have htime : 2 * (S.cap : ℝ) ≤ n * Real.log n := by simpa only [hcap] using hguard.1
  let T := S.goodSetting side r hr hg hquarter htime
  have hprops := S.good_label_properties side r hr hg
  have hm := hrest T hSA hSB (by change S.C + 1 = C + 1; rw [hSC])
    (by change 3 * S.A = 3 * A; rw [hSA]) rfl
    (targetOfHistory S.u (ProfileHistories.Hist.decode r)) hprops.1
    (by change ζ * Real.log n ≤ VisitBounds.gamma S.b (ProfileHistories.Hist.decode r) _
        simpa only [hSζ] using hprops.2.2.2.2.2)
  have he : VisitBounds.expectation (S.futureLaw r) (fun p ↦ (rest side p S.u S.v : ℝ)) =
      VisitBounds.expectation (Continuation.lawAt T.a T.b T.setupProtocol T.setup)
        (fun p ↦ (T.ordinaryCount p : ℝ)) := by
    rw [S.goodSetting_law side r hr hg hquarter htime]
    apply Continuation.expectation_congr_support
    intro p hp
    exact_mod_cast S.rest_eq_child_count side r hr hg hquarter htime p hp
  exact he.trans_le hm

/-- Explicit uniform bound for each entrant's proposals after his first accepted proposal. -/
noncomputable def restMeanConstant (A B C ζ : ℝ) : ℝ :=
  RestBounds.restConstant A B (C + 1) (3 * A) ζ + 1

/-- The uniform rest-mean coefficient is positive. -/
theorem restMeanConstant_pos {A B C ζ : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C) (hζ : 0 < ζ) :
    0 < restMeanConstant A B C ζ := by
  have hp := RestBounds.restConstant_pos hA hB (by linarith : 0 ≤ C + 1) (le_refl (3 * A)) hζ
  unfold restMeanConstant
  linarith

open Filter in
/-- Under the deterministic smooth setup conditions, both actual entrants have uniformly
bounded expected rest counts under the original staged setup law. The first-acceptance
mixture uses only literal visible prefixes, and its exceptional probabilities are bounded
by the exact next-destination kernel and ordinary continuation rank tails. -/
theorem eventually_uniform_rest_means {A B C κ ζ : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∀ᶠ n : ℕ in atTop, ∀ S : SmoothSetup n,
      S.A = A → S.B = B → S.C = C → S.κ = κ → S.ζ = ζ → ∀ side : Side,
        VisitBounds.expectation S.law (fun p ↦ (rest side p S.u S.v : ℝ)) ≤
          restMeanConstant A B C ζ := by
  have hApos : 0 < A := by linarith
  have hD := (ContinuationAsymptotics.coefficients_pos hA hB hC (by norm_num : (0 : ℝ) ≤ 4)).2.1
  have hK := (RestBounds.restConstant_pos hA hB (by linarith : 0 ≤ C + 1)
    (le_refl (3 * A)) hζ).le
  filter_upwards [eventually_rank_tails hA hB hC, eventually_good_prefix_means hA hB hC hζ,
    LowDestinations.eventually_threshold_guards hApos hD,
    LowDestinations.eventually_rest_error_le_one hApos hD hκ] with n htail hmean hguard herr
      S hSA hSB hSC hSκ hSζ side
  have hcap : S.cap = ContinuationAsymptotics.threshold
      (ContinuationAsymptotics.tailCoefficient A B C 4) n := by
    simp only [SmoothSetup.cap, hSA, hSB, hSC]
  have hsmall : S.A * (2 * S.cap : ℕ) / n ≤ 1 / 2 := by
    simpa only [hSA, hcap] using hguard.2.2
  have hf := htail S hSA hSB hSC Side.first
  have hs := htail S hSA hSB hSC Side.second
  have hm := S.rest_mean_le_split side hK (hmean S hSA hSB hSC hSζ side)
  have hl := S.lowTarget_probability_le side hsmall hf hs
  have hb := S.rankBad_probability_le hf hs
  have hmass : 0 ≤ LowDestinations.lowMass S.a S.low := by
    unfold LowDestinations.lowMass LowDestinations.totalWeight
    positivity
  have hu : LowDestinations.lowMass S.a S.low ≤ A * (n : ℝ) ^ (-κ) := by
    simpa only [hSA, hSκ] using S.lowMass_le
  have he := herr (LowDestinations.lowMass S.a S.low) hmass hu
  rw [← hcap] at he
  have hcn : (0 : ℝ) ≤ S.cap := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have herrnonneg : 0 ≤ (n : ℝ) * (n : ℝ) ^ (-(4 : ℝ)) := by positivity
  have hcl := mul_le_mul_of_nonneg_left hl hcn
  have hnb := mul_le_mul_of_nonneg_left hb hn
  unfold restMeanConstant
  nlinarith

open Filter in
/-- Integral form of the original-setup-law rest bound, for either actual entrant. -/
theorem eventually_uniform_rest_integrals {A B C κ ζ : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∀ᶠ n : ℕ in atTop, ∀ S : SmoothSetup n,
      S.A = A → S.B = B → S.C = C → S.κ = κ → S.ζ = ζ → ∀ side : Side,
        (∫ p, (rest side p S.u S.v : ℝ) ∂S.law.toMeasure) ≤ restMeanConstant A B C ζ := by
  filter_upwards [eventually_uniform_rest_means hA hB hC hκ hζ] with n hn S hSA hSB hSC hSκ hSζ side
  simpa only [VisitBounds.expectation_eq_integral] using hn S hSA hSB hSC hSκ hSζ side

end TieredMatching.RestAfterAcceptance
