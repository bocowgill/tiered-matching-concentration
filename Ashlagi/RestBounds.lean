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

public import Ashlagi.ContinuationAsymptotics
public import Ashlagi.SurvivalKernel
public import Ashlagi.PriorityProtocols

/-! # Actual rest counts after a protected target is held

A literal first-displacement prefix supports exact conditioning under the original profile law.
The target's counter is unchanged up to that prefix. Uniform actual continuation bounds are
then weighted by the proved displacement probability, with late displacements charged only
to the ordinary global-cap error.
-/

@[expose] public section

namespace Ashlagi.RestBounds

open StableMarriage MeasureTheory Ashlagi.Ordinal Protocols FiniteConditioning
open scoped ENNReal NNReal

variable {n : ℕ} (S : Continuation.Setting n)

/-- The actual ordinary continuation history at offset t after the visible setup. -/
noncomputable def history (p : Profile n) (t : ℕ) : List (Entry n) :=
  profileTranscript S.protocol p (S.setup.length + t)

/-- Stop at the first displacement of the protected holder, or at the deterministic global
cap if no displacement has yet occurred. -/
abbrev Reached (w : Fin n) (p : Profile n) (t : ℕ) : Prop :=
  t = S.caps.global ∨ (recordState (history S p t)).held w ≠ some S.man

/-- The deterministic cap guarantees a finite first stopping offset on every profile. -/
theorem exists_reached (w : Fin n) (p : Profile n) : ∃ t, Reached S w p t :=
  ⟨S.caps.global, Or.inl rfl⟩

/-- Actual first displacement offset, capped at the ordinary global proposal budget. -/
noncomputable def offset (w : Fin n) (p : Profile n) : ℕ := Nat.find (exists_reached S w p)

/-- The actual first stopping offset never exceeds its explicit global cap. -/
theorem offset_le (w : Fin n) (p : Profile n) : offset S w p ≤ S.caps.global :=
  Nat.find_min' _ (Or.inl rfl)

/-- At the first stopping prefix, either the cap or an actual displacement has occurred. -/
theorem offset_spec (w : Fin n) (p : Profile n) : Reached S w p (offset S w p) :=
  Nat.find_spec _

/-- At every earlier actual history the designated man still occupies the protected woman. -/
theorem held_before (w : Fin n) (p : Profile n) (t : ℕ) (ht : t < offset S w p) :
    (recordState (history S p t)).held w = some S.man := by
  by_contra hn
  exact Nat.find_min (exists_reached S w p) ht (Or.inr hn)

/-- Every actual later history retains its earlier literal chronological prefix. -/
theorem history_drop (p : Profile n) (s t : ℕ) :
    (history S p (s + t)).drop t = history S p s := by
  simpa only [history, Nat.add_assoc] using VisitBounds.profileTranscript_drop
    S.protocol p (S.setup.length + s) t

/-- Equality of one complete visible prefix fixes each earlier continuation prefix. -/
theorem earlier_history_eq (p q : Profile n) (t k : ℕ) (hk : k ≤ t)
    (he : history S q t = history S p t) : history S q k = history S p k := by
  have ht : t = k + (t - k) := by omega
  have hq := history_drop S q k (t - k)
  have hp := history_drop S p k (t - k)
  rw [← ht] at hq hp
  exact hq.symm.trans ((congrArg (fun L : List (Entry n) ↦ L.drop (t - k)) he).trans hp)

/-- The first displacement/cap offset is visible from its complete prefix, with no future
terminal event or raw preference suffix included. -/
theorem offset_eq_of_history_eq (w : Fin n) (p q : Profile n)
    (he : history S q (offset S w p) = history S p (offset S w p)) :
    offset S w q = offset S w p := by
  have hqreached : Reached S w q (offset S w p) := by
    rcases offset_spec S w p with hc | hd
    · exact Or.inl hc
    · exact Or.inr (by simpa only [he] using hd)
  have hqle : offset S w q ≤ offset S w p := Nat.find_min' _ hqreached
  apply le_antisymm hqle
  by_contra hn
  have hlt : offset S w q < offset S w p := by omega
  have hprefix := earlier_history_eq S p q (offset S w p) (offset S w q) hqle he
  have hpreached : Reached S w p (offset S w q) := by
    rcases offset_spec S w q with hc | hd
    · exact Or.inl hc
    · exact Or.inr (by simpa only [hprefix] using hd)
  exact Nat.find_min (exists_reached S w p) hlt hpreached

/-- The first displacement/cap prefix is a finite canonical history label of the actual
profile, not a future terminal classification. -/
noncomputable def stoppingHistory (w : Fin n) (p : Profile n) :
    ProfileHistories.Hist n (S.setup.length + S.caps.global) :=
  ProfileHistories.Hist.encode (history S p (offset S w p)) (by
    have hl : (history S p (offset S w p)).length = S.setup.length + offset S w p :=
      transcript_length _ _ _ _
    rw [hl]
    exact Nat.add_le_add_left (offset_le S w p) _)

/-- The encoded first stopping history is exactly the actual observed prefix. -/
theorem decode_stoppingHistory (w : Fin n) (p : Profile n) :
    ProfileHistories.Hist.decode (stoppingHistory S w p) = history S p (offset S w p) :=
  ProfileHistories.Hist.decode_encode _ _

/-- The stopping label's clock is the full actual public observation prefix length. -/
theorem clock_stoppingHistory (w : Fin n) (p : Profile n) :
    ProfileHistories.Hist.clock (stoppingHistory S w p) = S.setup.length + offset S w p := by
  rw [stoppingHistory, ProfileHistories.Hist.clock_encode]
  exact transcript_length _ _ _ _

/-- Each profile realizes its own literal first stopping prefix. -/
theorem mem_stoppingHistory (w : Fin n) (p : Profile n) :
    p ∈ ProfileHistories.Hist.prefixEvent S.protocol (stoppingHistory S w p) := by
  rw [ProfileHistories.Hist.mem_prefixEvent_iff, clock_stoppingHistory, decode_stoppingHistory]
  rfl

/-- Sharing a complete first stopping prefix fixes its stopping history label. -/
theorem stoppingHistory_stable (w : Fin n) (p q : Profile n)
    (hq : q ∈ ProfileHistories.Hist.prefixEvent S.protocol (stoppingHistory S w p)) :
    stoppingHistory S w q = stoppingHistory S w p := by
  have he : history S q (offset S w p) = history S p (offset S w p) := by
    simpa only [ProfileHistories.Hist.mem_prefixEvent_iff, clock_stoppingHistory,
      decode_stoppingHistory, history] using hq
  have ht := offset_eq_of_history_eq S w p q he
  apply ProfileHistories.Hist.decode_injective
  rw [decode_stoppingHistory, decode_stoppingHistory, ht]
  exact he

/-- The first stopping prefix also fixes the original visible setup history. -/
theorem setup_eq_of_stoppingHistory (w : Fin n) (p q : Profile n)
    (hq : q ∈ ProfileHistories.Hist.prefixEvent S.protocol (stoppingHistory S w p)) :
    history S q 0 = history S p 0 := by
  have he : history S q (offset S w p) = history S p (offset S w p) := by
    simpa only [ProfileHistories.Hist.mem_prefixEvent_iff, clock_stoppingHistory,
      decode_stoppingHistory, history] using hq
  exact earlier_history_eq S p q _ 0 (Nat.zero_le _) he

/-- While a man is held, the exact sanitized proposer protocol cannot select him, so his
counter is unchanged at the next actual observation. -/
theorem counter_step_eq_of_held (w : Fin n) (p : Profile n) (t : ℕ)
    (hw : (recordState (history S p t)).held w = some S.man) :
    (recordState (history S p (t + 1))).next S.man =
      (recordState (history S p t)).next S.man := by
  change (recordStep (recordState (history S p t))
    (Protocols.observation S.protocol p.manRank (profilePriorities p) (history S p t))).next S.man
      = _
  cases hm : selected S.protocol (history S p t) with
  | none =>
    simp only [Protocols.observation, Protocols.nextEdge, hm, Option.map_none, recordStep]
  | some u =>
    have hne : u ≠ S.man := by
      intro heq
      subst u
      exact (selected_some_spec S.protocol (history S p t) S.man hm).2 w hw
    rw [profile_recordStep_eq_propose S.protocol p (history S p t) u hm]
    exact Function.update_of_ne (Ne.symm hne) _ _

/-- Up to and including the first displacement, the target's actual proposal counter still
equals its setup counter. No extra designated rank-cap error is needed at that prefix. -/
theorem counter_unchanged_until (w : Fin n) (p : Profile n)
    (hp : profileTranscript S.protocol p S.setup.length = S.setup) (t : ℕ)
    (ht : t ≤ offset S w p) :
    (recordState (history S p t)).next S.man = (recordState S.setup).next S.man := by
  induction t with
  | zero => simp only [history, Nat.add_zero, hp]
  | succ t ih =>
    rw [counter_step_eq_of_held S w p t (held_before S w p t (by omega)), ih (by omega)]

/-- The actual first stopping history has precisely the unchanged designated setup counter. -/
theorem counter_stoppingHistory (w : Fin n) (p : Profile n)
    (hp : profileTranscript S.protocol p S.setup.length = S.setup) :
    (recordState (ProfileHistories.Hist.decode (stoppingHistory S w p))).next S.man =
      (recordState S.setup).next S.man := by
  rw [decode_stoppingHistory]
  exact counter_unchanged_until S w p hp _ le_rfl

/-- Positive original setup-conditioned stopping-history fibers are exactly the literal
original-law prefix events. No future displacement or terminal event is added to the fiber. -/
theorem stoppingHistory_refines (w : Fin n)
    (r : ProfileHistories.Hist n (S.setup.length + S.caps.global))
    (hr : ((Continuation.lawAt S.a S.b S.protocol S.setup).map (stoppingHistory S w)) r ≠ 0) :
    ProfileHistories.Hist.prefixEvent S.protocol r =
      Continuation.historyEvent S.protocol S.setup ∩ {p | stoppingHistory S w p = r} := by
  obtain ⟨p, hp, he⟩ := (PMF.mem_support_map_iff (stoppingHistory S w)
    (Continuation.lawAt S.a S.b S.protocol S.setup) r).mp hr
  have hs : p ∈ (condition (Continuation.market S.a S.b)
      (Continuation.historyEvent S.protocol S.setup)).support := hp
  rw [support_condition _ _ S.setup_nonnull_protocol] at hs
  subst r
  ext q
  constructor
  · intro hq
    refine ⟨?_, stoppingHistory_stable S w p q hq⟩
    have hsetup := setup_eq_of_stoppingHistory S w p q hq
    change profileTranscript S.protocol q S.setup.length = S.setup
    simp only [history, Nat.add_zero] at hsetup
    exact hsetup.trans hs.1
  · rintro ⟨_, hq⟩
    rw [← hq]
    exact mem_stoppingHistory S w q

/-- The literal first-displacement/cap observation disintegrates the actual original
setup-conditioned profile law. This is the finite stopping-prefix tower. -/
theorem bind_stoppingHistory (w : Fin n) :
    ((Continuation.lawAt S.a S.b S.protocol S.setup).map (stoppingHistory S w)).bind
      (fun r ↦ condition (Continuation.market S.a S.b)
        (ProfileHistories.Hist.prefixEvent S.protocol r)) =
      Continuation.lawAt S.a S.b S.protocol S.setup := by
  exact SurvivalKernel.bind_refined_condition (Continuation.market S.a S.b)
    (Continuation.historyEvent S.protocol S.setup) S.setup_nonnull_protocol
    (stoppingHistory S w) (ProfileHistories.Hist.prefixEvent S.protocol)
    (stoppingHistory_refines S w)

/-- Current genuine proposals grow by at most one per actual continuation observation. -/
theorem potential_history_le (p : Profile n)
    (hp : profileTranscript S.protocol p S.setup.length = S.setup) (t : ℕ) :
    potential (recordState (history S p t)) ≤ potential (recordState S.setup) + t := by
  induction t with
  | zero => simp only [history, Nat.add_zero, hp, Nat.add_zero, le_refl]
  | succ t ih =>
    change potential (recordState
      (ProfileHistories.nextObservation S.protocol (history S p t) p :: history S p t)) ≤ _
    cases he : ProfileHistories.nextObservation S.protocol (history S p t) p with
    | none => exact ih.trans (by omega)
    | some e =>
      obtain ⟨q, accepted⟩ := e
      rw [Continuation.potential_record]
      omega

/-- Every stopping prefix on the actual setup support still contains that setup. -/
theorem setup_suffix_stoppingHistory (w : Fin n) (p : Profile n)
    (hp : profileTranscript S.protocol p S.setup.length = S.setup) :
    S.setup.IsSuffix (ProfileHistories.Hist.decode (stoppingHistory S w p)) := by
  rw [decode_stoppingHistory]
  have hs := Continuation.profileTranscript_suffix S.protocol p S.setup.length (offset S w p)
  simpa only [hp, history] using hs

/-- Each positive stopping-history branch has a nonnull literal original prefix event. -/
theorem stoppingHistory_nonnull (w : Fin n)
    (r : ProfileHistories.Hist n (S.setup.length + S.caps.global))
    (hr : ((Continuation.lawAt S.a S.b S.protocol S.setup).map (stoppingHistory S w)) r ≠ 0) :
    eventMass (Continuation.market S.a S.b) (ProfileHistories.Hist.prefixEvent S.protocol r) ≠ 0
      := by
  rw [stoppingHistory_refines S w r hr]
  exact SurvivalKernel.refined_event_nonnull _ _ S.setup_nonnull_protocol _ _ hr

/-- Positive stopping labels preserve the designated counter, setup suffix, bounded genuine
total, and at-most-two empty women needed by the actual continuation theorem. -/
theorem stoppingHistory_properties (w : Fin n)
    (r : ProfileHistories.Hist n (S.setup.length + S.caps.global))
    (hr : ((Continuation.lawAt S.a S.b S.protocol S.setup).map (stoppingHistory S w)) r ≠ 0) :
    let h := ProfileHistories.Hist.decode r
    S.setup.IsSuffix h ∧ (recordState h).next S.man = (recordState S.setup).next S.man ∧
      potential (recordState h) ≤ potential (recordState S.setup) + S.caps.global ∧
      (VisitBounds.emptyWomen h).card ≤ 2 := by
  obtain ⟨p, hp, he⟩ := (PMF.mem_support_map_iff (stoppingHistory S w)
    (Continuation.lawAt S.a S.b S.protocol S.setup) r).mp hr
  have hs : p ∈ (condition (Continuation.market S.a S.b)
      (Continuation.historyEvent S.protocol S.setup)).support := hp
  rw [support_condition _ _ S.setup_nonnull_protocol] at hs
  subst r
  refine ⟨setup_suffix_stoppingHistory S w p hs.1, counter_stoppingHistory S w p hs.1, ?_, ?_⟩
  · rw [decode_stoppingHistory]
    exact (potential_history_le S p hs.1 _).trans (Nat.add_le_add_left (offset_le S w p) _)
  · exact S.empty_card_le_two _ (setup_suffix_stoppingHistory S w p hs.1)

/-- The original law at a literal first-displacement/cap prefix. -/
noncomputable def prefixLaw (r : ProfileHistories.Hist n (S.setup.length + S.caps.global)) :
    PMF (Profile n) :=
  condition (Continuation.market S.a S.b) (ProfileHistories.Hist.prefixEvent S.protocol r)

/-- Every positive stopping prefix is a genuine admissible continuation setup. The target's
unchanged counter gives its rank bound automatically, rather than paying a rank-cap error. -/
noncomputable def childSetting (w : Fin n)
    (r : ProfileHistories.Hist n (S.setup.length + S.caps.global))
    (hr : ((Continuation.lawAt S.a S.b S.protocol S.setup).map (stoppingHistory S w)) r ≠ 0)
    (futureK : ℝ) (hK : 0 ≤ futureK) : Continuation.Setting n where
  a := S.a
  b := S.b
  setupProtocol := S.protocol
  setup := ProfileHistories.Hist.decode r
  man := S.man
  A := S.A
  B := S.B
  C := S.C + S.K + 1
  K := futureK
  L := S.L
  n_ge := S.n_ge
  A_ge := S.A_ge
  B_ge := S.B_ge
  C_nonneg := by linarith [S.C_nonneg, S.K_nonneg]
  K_nonneg := hK
  L_ge := S.L_ge
  a_ge := S.a_ge
  a_le := S.a_le
  b_ge := S.b_ge
  b_le := S.b_le
  setup_nonnull := stoppingHistory_nonnull S w r hr
  setup_total := Continuation.capped_total_bound (by have := S.n_ge; omega)
    S.K_nonneg S.L_ge _ _ S.setup_total (stoppingHistory_properties S w r hr).2.2.1
  setup_quarter := by rw [(stoppingHistory_properties S w r hr).2.1]; exact S.setup_quarter
  setup_empty := (stoppingHistory_properties S w r hr).2.2.2

/-- The child continuation's source conditioning law is exactly the literal original prefix law. -/
theorem childSetting_law (w : Fin n)
    (r : ProfileHistories.Hist n (S.setup.length + S.caps.global))
    (hr : ((Continuation.lawAt S.a S.b S.protocol S.setup).map (stoppingHistory S w)) r ≠ 0)
    (futureK : ℝ) (hK : 0 ≤ futureK) :
    let T := childSetting S w r hr futureK hK
    Continuation.lawAt T.a T.b T.setupProtocol T.setup = prefixLaw S r := rfl

/-- The child's additional PR counter is the same original rest count on every profile,
not only after conditioning on future successful survival. -/
theorem childSetting_count (w : Fin n)
    (r : ProfileHistories.Hist n (S.setup.length + S.caps.global))
    (hr : ((Continuation.lawAt S.a S.b S.protocol S.setup).map (stoppingHistory S w)) r ≠ 0)
    (futureK : ℝ) (hK : 0 ≤ futureK) (p : Profile n) :
    (childSetting S w r hr futureK hK).ordinaryCount p = S.ordinaryCount p := by
  change (deferredAcceptance p).next S.man -
    (recordState (ProfileHistories.Hist.decode r)).next S.man = _
  rw [(stoppingHistory_properties S w r hr).2.1]
  rfl

/-- Fixed future global coefficient for the logarithmic continuation mean after displacement. -/
noncomputable def futureCoefficient : ℝ :=
  ContinuationAsymptotics.globalCoefficient S.A 0

/-- The actual finite continuation-mean endpoint for each first stopping prefix. -/
noncomputable def budget : ℝ := ContinuationAsymptotics.meanBound S.A
  (ContinuationAsymptotics.acceptanceConstant S.A S.B (S.C + S.K + 1) (futureCoefficient S))
  (CompetingHazards.potential S.A 2) (futureCoefficient S) n

/-- The chosen future coefficient is a genuine nonnegative fixed constant. -/
theorem futureCoefficient_nonneg : 0 ≤ futureCoefficient S := by
  unfold futureCoefficient ContinuationAsymptotics.globalCoefficient
  nlinarith [S.A_ge]

/-- Each actual nonnull first stopping prefix has the proved uniform continuation-mean
endpoint. This estimate is a conclusion, not an assumed conditional mean. -/
theorem prefix_mean_le_budget (w : Fin n)
    (r : ProfileHistories.Hist n (S.setup.length + S.caps.global))
    (hr : ((Continuation.lawAt S.a S.b S.protocol S.setup).map (stoppingHistory S w)) r ≠ 0)
    (hL : S.L = Real.log n) :
    VisitBounds.expectation (prefixLaw S r) (fun p ↦ (S.ordinaryCount p : ℝ)) ≤ budget S := by
  let T := childSetting S w r hr (futureCoefficient S) (futureCoefficient_nonneg S)
  have hm := ContinuationAsymptotics.setting_mean_le_meanBound T rfl rfl rfl rfl hL
  rw [T.setup_law_eq] at hm
  change VisitBounds.expectation (prefixLaw S r) (fun p ↦
    ((childSetting S w r hr (futureCoefficient S) (futureCoefficient_nonneg S)).ordinaryCount p :
      ℝ)) ≤
      budget S at hm
  simpa only [childSetting_count] using hm

/-- The continuation-mean endpoint is nonnegative. -/
theorem budget_nonneg (hL : S.L = Real.log n) : 0 ≤ budget S := by
  obtain ⟨r, hr⟩ := ((Continuation.lawAt S.a S.b S.protocol S.setup).map
    (stoppingHistory S S.man)).support_nonempty
  have hz := Continuation.expectation_mono_support (prefixLaw S r) (fun _ ↦ (0 : ℝ))
    (fun p ↦ (S.ordinaryCount p : ℝ)) (fun p _ ↦ Nat.cast_nonneg _)
  rw [Continuation.expectation_const] at hz
  exact hz.trans (prefix_mean_le_budget S S.man r hr hL)

/-- Displacement by H is a property of the actual first stopping label. -/
def displacedLabels (w : Fin n) :
    Set (ProfileHistories.Hist n (S.setup.length + S.caps.global)) :=
  {r | (recordState (ProfileHistories.Hist.decode r)).held w ≠ some S.man}

/-- The actual event of displacement before or at the finite global cap. -/
def displacedEvent (w : Fin n) : Set (Profile n) :=
  stoppingHistory S w ⁻¹' displacedLabels S w

/-- The first stopping label records exactly whether any displacement has occurred by H. -/
theorem displacedEvent_iff (w : Fin n) (p : Profile n) :
    p ∈ displacedEvent S w ↔ VisitBounds.displacedBy S.protocol p S.setup.length S.caps.global w
      S.man := by
  change (recordState (ProfileHistories.Hist.decode (stoppingHistory S w p))).held w ≠ some S.man
    ↔ _
  rw [decode_stoppingHistory]
  constructor
  · intro hf
    exact ⟨offset S w p, offset_le S w p, hf⟩
  · rintro ⟨t, ht, hfail⟩
    by_contra hnone
    have hh : (recordState (history S p (offset S w p))).held w = some S.man := by
      simpa only [not_not] using hnone
    have hcap : offset S w p = S.caps.global := (offset_spec S w p).resolve_right (fun hne ↦ hne
      hnone)
    have htle : offset S w p ≤ t := by
      exact Nat.find_min' (exists_reached S w p) (Or.inr hfail)
    have he : t = offset S w p := by omega
    exact hfail (by simpa only [he, history] using hh)

/-- The actual protected-displacement probability has the source's high-weight bound. -/
theorem displacement_probability_le (w : Fin n) (hw : (recordState S.setup).held w = some S.man)
    {g : ℝ} (hg : 0 < g) (hgamma : g ≤ VisitBounds.gamma S.b S.setup w) :
    (eventMass (Continuation.lawAt S.a S.b S.protocol S.setup) (displacedEvent S w)).toReal ≤
      S.A * 2 * S.B / g := by
  have he : displacedEvent S w =
      {p | VisitBounds.displacedBy S.protocol p S.setup.length S.caps.global w S.man} := by
    ext p
    exact displacedEvent_iff S w p
  rw [he]
  let A : ℝ≥0 := ⟨S.A, by linarith [S.A_ge]⟩
  exact VisitBounds.displacement_probability_le S.a S.b
    (fun v ↦ by exact_mod_cast S.a_ge v)
    (fun m ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (S.b_ge m)) A
    (fun v ↦ by exact_mod_cast S.a_le v) S.protocol S.setup S.setup_nonnull_protocol
    S.caps.global 2 S.setup_empty w S.man hw S.B g hg S.b_le hgamma

/-- The exact real finite stopping-prefix expectation tower. -/
theorem expectation_stoppingHistory (w : Fin n) (f : Profile n → ℝ) :
    VisitBounds.expectation (Continuation.lawAt S.a S.b S.protocol S.setup) f =
      ∑ r, (((Continuation.lawAt S.a S.b S.protocol S.setup).map (stoppingHistory S w)) r).toReal *
        VisitBounds.expectation (prefixLaw S r) f := by
  conv_lhs => rw [← bind_stoppingHistory S w]
  rw [ProfileHistories.expectation_bind]
  rfl

/-- On positive literal child-prefix support the observed stopping label is fixed. -/
theorem prefix_support_label (w : Fin n)
    (r : ProfileHistories.Hist n (S.setup.length + S.caps.global))
    (hr : ((Continuation.lawAt S.a S.b S.protocol S.setup).map (stoppingHistory S w)) r ≠ 0)
    (p : Profile n) (hp : prefixLaw S r p ≠ 0) : stoppingHistory S w p = r := by
  exact SurvivalKernel.refined_support_observation (Continuation.market S.a S.b)
    (Continuation.historyEvent S.protocol S.setup) S.setup_nonnull_protocol
    (stoppingHistory S w) (ProfileHistories.Hist.prefixEvent S.protocol) r hr
    (stoppingHistory_refines S w r hr) p hp

/-- The actual original count on the event whose first stopping prefix already records a
protected displacement. -/
noncomputable def displacedCount (w : Fin n) : Profile n → ℝ :=
  (displacedEvent S w).indicator (fun p ↦ (S.ordinaryCount p : ℝ))

/-- Integrating literal first-displacement prefix means pays their actual displacement mass,
not an independent survival mark or a terminal-event conditional mean. -/
theorem displacedCount_mean_le (w : Fin n) (hL : S.L = Real.log n) :
    VisitBounds.expectation (Continuation.lawAt S.a S.b S.protocol S.setup) (displacedCount S w) ≤
      budget S * (eventMass (Continuation.lawAt S.a S.b S.protocol S.setup)
        (displacedEvent S w)).toReal := by
  classical
  let μ := Continuation.lawAt S.a S.b S.protocol S.setup
  let ν := μ.map (stoppingHistory S w)
  have hbranch (r : ProfileHistories.Hist n (S.setup.length + S.caps.global)) (hr : ν r ≠ 0) :
      VisitBounds.expectation (prefixLaw S r) (displacedCount S w) ≤
        budget S * (displacedLabels S w).indicator (fun _ ↦ (1 : ℝ)) r := by
    by_cases hd : r ∈ displacedLabels S w
    · rw [Set.indicator_of_mem hd, mul_one]
      have he : VisitBounds.expectation (prefixLaw S r) (displacedCount S w) =
          VisitBounds.expectation (prefixLaw S r) (fun p ↦ (S.ordinaryCount p : ℝ)) := by
        apply Continuation.expectation_congr_support
        intro p hp
        have hlabel := prefix_support_label S w r hr p hp
        have hpD : p ∈ displacedEvent S w := by
          change stoppingHistory S w p ∈ displacedLabels S w
          rw [hlabel]
          exact hd
        exact Set.indicator_of_mem hpD _
      rw [he]
      exact prefix_mean_le_budget S w r hr hL
    · rw [Set.indicator_of_notMem hd, mul_zero]
      have he : VisitBounds.expectation (prefixLaw S r) (displacedCount S w) = 0 := by
        have heq : VisitBounds.expectation (prefixLaw S r) (displacedCount S w) =
            VisitBounds.expectation (prefixLaw S r) (fun _ ↦ (0 : ℝ)) := by
          apply Continuation.expectation_congr_support
          intro p hp
          have hlabel := prefix_support_label S w r hr p hp
          have hpD : p ∉ displacedEvent S w := by
            change stoppingHistory S w p ∉ displacedLabels S w
            rw [hlabel]
            exact hd
          exact Set.indicator_of_notMem hpD _
        rw [heq, Continuation.expectation_const]
      exact he.le
  rw [expectation_stoppingHistory S w]
  calc
    _ ≤ ∑ r, (ν r).toReal *
        (budget S * (displacedLabels S w).indicator (fun _ ↦ (1 : ℝ)) r) := by
      apply Finset.sum_le_sum
      intro r hr
      by_cases hz : ν r = 0
      · dsimp only [ν, μ] at hz ⊢
        simp only [hz, ENNReal.toReal_zero, zero_mul, le_refl]
      · exact mul_le_mul_of_nonneg_left (hbranch r hz) ENNReal.toReal_nonneg
    _ = budget S * VisitBounds.expectation ν ((displacedLabels S w).indicator (fun _ ↦ (1 : ℝ)))
      := by
      unfold VisitBounds.expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = budget S * (eventMass μ (displacedEvent S w)).toReal := by
      rw [Continuation.expectation_map]
      have heq : (fun p ↦ (displacedLabels S w).indicator (fun _ ↦ (1 : ℝ)) (stoppingHistory S w
        p)) =
          (displacedEvent S w).indicator (fun _ ↦ (1 : ℝ)) := by
        funext p
        by_cases hp : stoppingHistory S w p ∈ displacedLabels S w <;>
          simp only [Set.indicator_apply, displacedEvent, Set.mem_preimage, hp, ↓reduceIte]
      rw [heq, VisitBounds.expectation_indicator_one]

/-- If the target was not displaced by H and the ordinary continuation has completed by H,
its entire additional ordinary PR counter is zero. -/
theorem ordinaryCount_zero_of_no_displacement (w : Fin n) (p : Profile n)
    (hp : profileTranscript S.protocol p S.setup.length = S.setup)
    (hd : p ∉ displacedEvent S w) (hg : p ∉ S.globalError) : S.ordinaryCount p = 0 := by
  have hn : ¬ (recordState (history S p (offset S w p))).held w ≠ some S.man := by
    simpa only [displacedEvent, Set.mem_preimage, displacedLabels, Set.mem_ofPred_eq,
      decode_stoppingHistory] using hd
  have ht : offset S w p = S.caps.global := (offset_spec S w p).resolve_right hn
  have hcounter := counter_unchanged_until S w p hp S.caps.global (by rw [ht])
  let h := history S p S.caps.global
  have hlen : h.length = S.setup.length + S.caps.global := transcript_length _ _ _ _
  have hreal : profileTranscript S.protocol p h.length = h := by rw [hlen]; rfl
  have hbase : S.setup.IsSuffix h := by
    have hh := Continuation.profileTranscript_suffix S.protocol p S.setup.length S.caps.global
    change S.setup.IsSuffix (profileTranscript S.protocol p (S.setup.length + S.caps.global))
    simpa only [hp] using hh
  have hzero : (VisitBounds.emptyWomen h).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact hg ⟨v, (Finset.mem_filter.mp hv).2⟩
  have hpr := S.state_eq_pr_of_complete h p hreal hbase (Or.inl hzero)
  change (deferredAcceptance p).next S.man - (recordState S.setup).next S.man = 0
  rw [← hpr, hcounter]
  omega

/-- Every proposal after a late first displacement is charged to the actual global
incompletion event. No additional rank-cap exceptional event is introduced. -/
theorem ordinaryCount_le_displaced_add_global (w : Fin n) (p : Profile n)
    (hp : profileTranscript S.protocol p S.setup.length = S.setup) :
    (S.ordinaryCount p : ℝ) ≤ displacedCount S w p +
      (n : ℝ) * S.globalError.indicator (fun _ ↦ (1 : ℝ)) p := by
  classical
  by_cases hd : p ∈ displacedEvent S w
  · rw [displacedCount, Set.indicator_of_mem hd]
    have hn : 0 ≤ (n : ℝ) * S.globalError.indicator (fun _ ↦ (1 : ℝ)) p := by
      by_cases hg : p ∈ S.globalError <;>
        simp only [Set.indicator_apply, hg, ↓reduceIte, mul_one, mul_zero, le_refl]
      exact Nat.cast_nonneg _
    linarith
  · rw [displacedCount, Set.indicator_of_notMem hd, zero_add]
    by_cases hg : p ∈ S.globalError
    · rw [Set.indicator_of_mem hg, mul_one]
      exact_mod_cast S.ordinaryCount_le p
    · rw [Set.indicator_of_notMem hg, mul_zero, ordinaryCount_zero_of_no_displacement S w p hp hd
      hg]
      norm_num

/-- Actual finite-n rest mean after a high-weight protected target is held. All conditional
continuation and displacement bounds are derived, with only the global cap paid on late paths. -/
theorem rest_mean_le (w : Fin n) (hw : (recordState S.setup).held w = some S.man)
    {g : ℝ} (hg : 0 < g) (hgamma : g ≤ VisitBounds.gamma S.b S.setup w)
    (hL : S.L = Real.log n) :
    VisitBounds.expectation (Continuation.lawAt S.a S.b S.protocol S.setup)
      (fun p ↦ (S.ordinaryCount p : ℝ)) ≤ budget S * (S.A * 2 * S.B / g) +
        n * (2 * Real.exp (-(S.caps.global : ℝ) / (S.A * n))) := by
  have hbound (p : Profile n) (hp : Continuation.lawAt S.a S.b S.protocol S.setup p ≠ 0) :
      (S.ordinaryCount p : ℝ) ≤ displacedCount S w p +
        (n : ℝ) * S.globalError.indicator (fun _ ↦ (1 : ℝ)) p := by
    have hs : p ∈ (condition (Continuation.market S.a S.b)
        (Continuation.historyEvent S.protocol S.setup)).support := hp
    rw [support_condition _ _ S.setup_nonnull_protocol] at hs
    exact ordinaryCount_le_displaced_add_global S w p hs.1
  have hpoint := Continuation.expectation_mono_support
    (Continuation.lawAt S.a S.b S.protocol S.setup) _ _ hbound
  rw [Continuation.expectation_add, Continuation.expectation_const_mul,
    VisitBounds.expectation_indicator_one] at hpoint
  have hmasked := displacedCount_mean_le S w hL
  have hdisp := displacement_probability_le S w hw hg hgamma
  have hscale := mul_le_mul_of_nonneg_left hdisp (budget_nonneg S hL)
  have hglobal := mul_le_mul_of_nonneg_left S.global_cap_error (Nat.cast_nonneg (α := ℝ) n)
  dsimp only [Continuation.Setting.globalError] at hpoint
  linarith

/-- The finite rest bound conditions on precisely the original staged setup event. -/
theorem rest_mean_le_source (w : Fin n) (hw : (recordState S.setup).held w = some S.man)
    {g : ℝ} (hg : 0 < g) (hgamma : g ≤ VisitBounds.gamma S.b S.setup w)
    (hL : S.L = Real.log n) :
    VisitBounds.expectation (Continuation.lawAt S.a S.b S.setupProtocol S.setup)
      (fun p ↦ (S.ordinaryCount p : ℝ)) ≤ budget S * (S.A * 2 * S.B / g) +
        n * (2 * Real.exp (-(S.caps.global : ℝ) / (S.A * n))) := by
  rw [← S.setup_law_eq]
  exact rest_mean_le S w hw hg hgamma hL

open Filter in
/-- Uniform actual rest mean over every sufficiently large admissible held setup, with an
explicit high-weight factor and only the actual global-cap error. -/
theorem eventually_uniform_rest_mean {A B C K : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C) (hK : 3 * A ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ S : Continuation.Setting n,
      S.A = A → S.B = B → S.C = C → S.K = K → S.L = Real.log n →
      ∀ w : Fin n, (recordState S.setup).held w = some S.man → ∀ g : ℝ, 0 < g →
      g ≤ VisitBounds.gamma S.b S.setup w →
      VisitBounds.expectation (Continuation.lawAt S.a S.b S.setupProtocol S.setup)
        (fun p ↦ (S.ordinaryCount p : ℝ)) ≤
          ContinuationAsymptotics.meanCoefficient A B (C + K + 1) 0 * Real.log n *
            (A * 2 * B / g) + n * (2 * Real.exp (-(S.caps.global : ℝ) / (A * n))) := by
  have hApos : 0 < A := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hC' : 0 ≤ C + K + 1 := by linarith
  have hfuture : 0 ≤ ContinuationAsymptotics.globalCoefficient A 0 := by
    unfold ContinuationAsymptotics.globalCoefficient
    nlinarith
  have hc := ContinuationAsymptotics.acceptanceConstant_pos hApos (by linarith : 0 ≤ B) hC' hfuture
  have hq := CompetingHazards.potential_pos hApos.le 2
  have hthree : 3 * A ≤ ContinuationAsymptotics.globalCoefficient A 0 := by
    unfold ContinuationAsymptotics.globalCoefficient
    nlinarith
  filter_upwards [ContinuationAsymptotics.eventually_meanBound_le_log hApos hc hq hthree]
    with n hmean S hSA hSB hSC hSK hSL w hw g hg hgamma
  have hbudget : budget S ≤
      ContinuationAsymptotics.meanCoefficient A B (C + K + 1) 0 * Real.log n := by
    simpa only [budget, futureCoefficient, hSA, hSB, hSC, hSK,
      ContinuationAsymptotics.meanCoefficient] using hmean
  have hb := rest_mean_le_source S w hw hg hgamma hSL
  have hδ : 0 ≤ A * 2 * B / g := div_nonneg (by positivity) hg.le
  have hs := mul_le_mul_of_nonneg_right hbudget hδ
  rw [hSA, hSB] at hb
  linarith

/-- An explicit n-independent rest-mean bound when the protected woman has logarithmic score. -/
noncomputable def restConstant (A B C K cg : ℝ) : ℝ :=
  ContinuationAsymptotics.meanCoefficient A B (C + K + 1) 0 * (A * 2 * B / cg) + 1

/-- The explicit uniform rest-mean constant is positive for the source parameter bounds. -/
theorem restConstant_pos {A B C K cg : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hC : 0 ≤ C) (hK : 3 * A ≤ K) (hcg : 0 < cg) : 0 < restConstant A B C K cg := by
  have hC' : 0 ≤ C + K + 1 := by nlinarith
  have hR := (ContinuationAsymptotics.coefficients_pos hA hB hC' (le_refl (0 : ℝ))).2.2
  have hd : 0 ≤ A * 2 * B / cg := by positivity
  unfold restConstant
  nlinarith [mul_nonneg hR.le hd]

open Filter in
/-- If the current protected score is at least cg*log n, the actual additional ordinary rest
count has uniformly bounded conditional mean. No terminal good-event conditioning is used. -/
theorem eventually_uniform_rest_mean_constant {A B C K cg : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C) (hK : 3 * A ≤ K) (hcg : 0 < cg) :
    ∀ᶠ n : ℕ in atTop, ∀ S : Continuation.Setting n,
      S.A = A → S.B = B → S.C = C → S.K = K → S.L = Real.log n →
      ∀ w : Fin n, (recordState S.setup).held w = some S.man →
      cg * Real.log n ≤ VisitBounds.gamma S.b S.setup w →
      VisitBounds.expectation (Continuation.lawAt S.a S.b S.setupProtocol S.setup)
        (fun p ↦ (S.ordinaryCount p : ℝ)) ≤ restConstant A B C K cg := by
  have hApos : 0 < A := by linarith
  filter_upwards [eventually_uniform_rest_mean hA hB hC hK,
    ContinuationAsymptotics.eventually_mean_errors_le_one hApos zero_lt_one zero_lt_one hK,
    ContinuationAsymptotics.eventually_one_le_log] with n hmean herr hlog S hSA hSB hSC hSK hSL w
      hw hgamma
  have hlogpos : 0 < Real.log n := by linarith
  have hm := hmean S hSA hSB hSC hSK hSL w hw (cg * Real.log n)
    (mul_pos hcg hlogpos) hgamma
  have hglobal : (n : ℝ) * (2 * Real.exp
      (-(ContinuationAsymptotics.globalCap K n : ℝ) / (A * n))) ≤ 1 := by
    have hnonneg : 0 ≤ (n : ℝ) * (2 * Real.exp
        (-((1 / Real.log n) * 1 / 2) * ContinuationAsymptotics.individualCap n)) := by positivity
    nlinarith
  have hcap : S.caps.global = ContinuationAsymptotics.globalCap K n := by
    simp only [Continuation.Setting.caps, ContinuationAsymptotics.globalCap, hSK, hSL]
  rw [hcap] at hm
  have heq : ContinuationAsymptotics.meanCoefficient A B (C + K + 1) 0 * Real.log n *
      (A * 2 * B / (cg * Real.log n)) =
      ContinuationAsymptotics.meanCoefficient A B (C + K + 1) 0 * (A * 2 * B / cg) := by
    field_simp
  rw [heq] at hm
  exact hm.trans (by unfold restConstant; linarith)

end Ashlagi.RestBounds
