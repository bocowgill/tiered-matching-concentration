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

public import Ashlagi.GlobalDraws
public import Ashlagi.CouponLowerTail
public import Ashlagi.RepeatMoments
public import Ashlagi.RankTail
public import Ashlagi.RepeatAccounting

/-! # Actual leave-two-out setup estimates

The partial global-draw bridge is proved for actual raw histories. Dummy tape reads after an
absorbing pause may add hits but cannot remove earlier actual hits. No good-setup stochastic
conclusion is assumed.
-/

@[expose] public section

namespace Ashlagi.SmoothSetup

open StableMarriage MeasureTheory
open scoped NNReal ENNReal

/-- The canonical raw active-set protocol selects only active entrants. -/
theorem activeProtocol_supports {n : ℕ} (A : Finset (Fin n)) :
    RawBridge.Supports (GlobalDraws.activeProtocol A) A := by
  intro h m hm
  rw [GlobalDraws.selected_activeProtocol] at hm
  exact (Protocols.chooseFrom_some A (List.finRange n) (Raw.state h) m hm).2.1

/-- A pause remains a pause at the next actual raw time step for a pause-stable protocol. -/
theorem selected_none_succ {n : ℕ} (C : Raw.Protocol n) (hs : GlobalDraws.PauseStable C)
    (streams : Fin n → ℕ → Fin n) (female : Arrival.Edge n → ℝ) (t : ℕ)
    (ht : Raw.selected C (Raw.transcript C streams female t) = none) :
    Raw.selected C (Raw.transcript C streams female (t + 1)) = none := by
  rw [Raw.transcript]
  have ho : Raw.observation C streams female (Raw.transcript C streams female t) = none := by
    simp [Raw.observation, Raw.nextEdge, ht]
  rw [ho]
  exact hs _ ht

/-- Once an actual raw execution pauses it remains paused, regardless of dummy tape reads. -/
theorem selected_none_mono {n : ℕ} (C : Raw.Protocol n) (hs : GlobalDraws.PauseStable C)
    (streams : Fin n → ℕ → Fin n) (female : Arrival.Edge n → ℝ) {s t : ℕ} (hst : s ≤ t)
    (hstart : Raw.selected C (Raw.transcript C streams female s) = none) :
    Raw.selected C (Raw.transcript C streams female t) = none := by
  induction t with
  | zero =>
    have he : s = 0 := by omega
    simpa only [he] using hstart
  | succ t ih =>
    by_cases he : s = t + 1
    · simpa only [← he] using hstart
    · exact selected_none_succ C hs streams female t (ih (by omega))

/-- An active current selector certifies that every earlier raw step was also active. -/
theorem no_earlier_pause {n : ℕ} (C : Raw.Protocol n) (hs : GlobalDraws.PauseStable C)
    (streams : Fin n → ℕ → Fin n) (female : Arrival.Edge n → ℝ) (H : ℕ)
    (hactive : Raw.selected C (Raw.transcript C streams female H) ≠ none) :
    ∀ t < H, Raw.selected C (Raw.transcript C streams female t) ≠ none := by
  intro t ht hnone
  exact hactive (selected_none_mono C hs streams female (by omega) hnone)

/-- Before the first pause the literal raw trace uses every global time step. -/
theorem active_trace_length {n : ℕ} (C : Raw.Protocol n) (hs : GlobalDraws.PauseStable C)
    (streams : Fin n → ℕ → Fin n) (female : Arrival.Edge n → ℝ) (H : ℕ)
    (hactive : Raw.selected C (Raw.transcript C streams female H) ≠ none) :
    (RawBridge.trace (Raw.transcript C streams female H)).length = H :=
  GlobalDraws.trace_length_of_no_pause C female streams H
    (no_earlier_pause C hs streams female H hactive)

/-- Every actually visited woman lies in the global tape prefix, even after the absorbing
pause. Dummy post-pause reads can only add tape hits. -/
theorem actual_hit_implies_tape_hit {n : ℕ} [NeZero n] (C : Raw.Protocol n)
    (hs : GlobalDraws.PauseStable C) (female : Arrival.Edge n → ℝ)
    (x : (Fin n × ℕ) → Fin n) (H : ℕ) (w : Fin n) :
    (∃ m, (w, m) ∈ RawBridge.trace (Raw.transcript C (Function.curry x) female H)) →
      ∃ t < H, GlobalDraws.tape C female x t = w := by
  induction H with
  | zero => simp [Raw.transcript, RawBridge.trace]
  | succ H ih =>
    let h := Raw.transcript C (Function.curry x) female H
    rw [Raw.transcript, GlobalDraws.observation_eq_respond_tape C hs female x H]
    cases hm : Raw.selected C h with
    | none =>
      have hr : GlobalDraws.respond C female h (GlobalDraws.tape C female x H) = none :=
        GlobalDraws.respond_eq_none C female h _ hm
      rw [hr]
      intro hh
      obtain ⟨t, ht, he⟩ := ih hh
      exact ⟨t, by omega, he⟩
    | some m =>
      have hr : RawBridge.trace
          (GlobalDraws.respond C female h (GlobalDraws.tape C female x H) :: h) =
          (GlobalDraws.tape C female x H, m) :: RawBridge.trace h := by
        simp only [GlobalDraws.respond, hm, Option.map_some, RawBridge.trace]
      rw [hr]
      rintro ⟨k, hk⟩
      rcases List.mem_cons.mp hk with he | he
      · exact ⟨H, by omega, (congrArg Prod.fst he).symm⟩
      · obtain ⟨t, ht, he⟩ := ih ⟨k, he⟩
        exact ⟨t, by omega, he⟩

/-- Missing tape coupons and actually hit women are disjoint, including after partial-market
completion. The claim is deterministic and does not assume IID sampling. -/
theorem missing_disjoint_actual_hits {n : ℕ} [NeZero n] (C : Raw.Protocol n)
    (hs : GlobalDraws.PauseStable C) (female : Arrival.Edge n → ℝ)
    (x : (Fin n × ℕ) → Fin n) (H : ℕ) :
    Disjoint (Coupon.missingCoupons H (CouponLowerTail.samplePrefix H
      (GlobalDraws.tape C female x)))
      (RawSemantics.hitWomen (RawBridge.trace (Raw.transcript C (Function.curry x) female H))) := by
  classical
  rw [Finset.disjoint_left]
  intro w hw hm
  have hmiss : ∀ i : Fin H, GlobalDraws.tape C female x i ≠ w := by
    have hr : CouponLowerTail.samplePrefix H (GlobalDraws.tape C female x) ∈
        Coupon.missing H w := (Finset.mem_filter.mp hw).2
    exact hr
  have hhit : ∃ m, (w, m) ∈ RawBridge.trace (Raw.transcript C (Function.curry x) female H) := by
    simpa [RawSemantics.hitWomen] using hm
  obtain ⟨t, ht, he⟩ := actual_hit_implies_tape_hit C hs female x H w hhit
  exact hmiss ⟨t, ht⟩ he

/-- Partial DA completion with at least `n-2` active men forces at most two missing tape
coupons. No reverse hit equivalence is asserted after the partial protocol pauses. -/
theorem partial_terminal_missing_le_two {n : ℕ} [NeZero n] (A : Finset (Fin n))
    (hcard : n ≤ A.card + 2) (female : Arrival.Edge n → ℝ)
    (x : (Fin n × ℕ) → Fin n) (p : Profile n)
    (horders : ∀ m, Function.curry x m ∈ IIDRanking.rankEvent (p.manRank m))
    (hcompare : ∀ w m old, p.womanRank w m < p.womanRank w old ↔
      female (w, m) < female (w, old)) (H : ℕ)
    (hterm : Schedules.Terminal A
      (Raw.state (Raw.transcript (GlobalDraws.activeProtocol A) (Function.curry x) female H))) :
    CouponLowerTail.missingCount H
      (GlobalDraws.tape (GlobalDraws.activeProtocol A) female x) ≤ 2 := by
  classical
  let C := GlobalDraws.activeProtocol A
  have hb := RawBridge.transcript_admissible_replay C (Function.curry x) female p A
    (activeProtocol_supports A) horders hcompare H
  have hhit : (RawSemantics.hitWomen
      (RawBridge.trace (Raw.transcript C (Function.curry x) female H))).card = A.card := by
    rw [hb.2] at hterm
    exact (RawSemantics.terminal_iff_hitWomen_card p A hb.1).mp hterm
  have hd := missing_disjoint_actual_hits C (GlobalDraws.activeProtocol_pauseStable A) female x H
  have hc := Finset.card_le_card (Finset.subset_univ
    (Coupon.missingCoupons H (CouponLowerTail.samplePrefix H (GlobalDraws.tape C female x)) ∪
      RawSemantics.hitWomen (RawBridge.trace (Raw.transcript C (Function.curry x) female H))))
  rw [Finset.card_union_of_disjoint hd, Finset.card_univ, Fintype.card_fin, hhit] at hc
  have hm : (Coupon.missingCoupons H
      (CouponLowerTail.samplePrefix H (GlobalDraws.tape C female x))).card ≤ 2 := by omega
  change Coupon.missingCount H _ ≤ 2
  rw [Coupon.missingCount_eq_card]
  exact_mod_cast hm

/-- Literal missing-coupon statistics are measurable functions of the global source tape. -/
theorem measurable_missingCount {n : ℕ} (H : ℕ) :
    Measurable (CouponLowerTail.missingCount (α := Fin n) H) :=
  Measurable.of_discrete.comp (CouponLowerTail.measurable_prefix H)

/-- Under the exact raw input law, partial completion forces at most two missing source-tape
coupons almost surely. The only exceptional inputs are the already-proved ranking/tie null sets. -/
theorem ae_partial_terminal_missing {n : ℕ} [NeZero n] (A : Finset (Fin n))
    (hcard : n ≤ A.card + 2) (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hQ : ∀ m w, 0 < Q m w) (H : ℕ) :
    ∀ᵐ z ∂rawInputLaw (fun _ ↦ a) Q,
      Raw.selected (GlobalDraws.activeProtocol A)
        (RawBridge.history (GlobalDraws.activeProtocol A) z H) = none →
      CouponLowerTail.missingCount H
        (GlobalDraws.sourceTape (GlobalDraws.activeProtocol A) z) ≤ 2 := by
  filter_upwards [RawBridge.ae_source_orders (fun _ ↦ a) Q (fun _ ↦ ha),
    RawBridge.ae_source_female_injective (fun _ ↦ a) Q hQ] with z horders hcomp
  intro hz
  apply partial_terminal_missing_le_two A hcard (RawBridge.sourceFemale z)
    (Function.uncurry z.1) (RawBridge.sourceProfile z) horders
    (fun w m old ↦ exponentialRank_lt_iff (z.2 w) (hcomp w) m old) H
  exact (GlobalDraws.activeProtocol_none_iff_terminal A _).mp hz

/-- The exact early-partial-completion probability is bounded by the literal IID missing
coupon event. This is the required partial-market global-tape bridge. -/
theorem early_terminal_probability_le_missing {n : ℕ} [NeZero n] (A : Finset (Fin n))
    (hcard : n ≤ A.card + 2) (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hQ : ∀ m w, 0 < Q m w) (H : ℕ) :
    (rawInputLaw (fun _ ↦ a) Q).real {z |
      Raw.selected (GlobalDraws.activeProtocol A)
        (RawBridge.history (GlobalDraws.activeProtocol A) z H) = none} ≤
      (FirstFresh.iidStream (RandomRanking.ofWeights a)).real
        {x | CouponLowerTail.missingCount H x ≤ 2} := by
  let C := GlobalDraws.activeProtocol A
  let E : Set (ℕ → Fin n) := {x | CouponLowerTail.missingCount H x ≤ 2}
  have hE : MeasurableSet E := measurableSet_le (measurable_missingCount H) measurable_const
  have hmap := GlobalDraws.sourceTape_law C (GlobalDraws.activeProtocol_pauseStable A) a Q hQ
  have hm : (rawInputLaw (fun _ ↦ a) Q) ((GlobalDraws.sourceTape C) ⁻¹' E) =
      (FirstFresh.iidStream (RandomRanking.ofWeights a)) E := by
    rw [← hmap, Measure.map_apply
      (GlobalDraws.measurable_sourceTape C (GlobalDraws.activeProtocol_pauseStable A)) hE]
  have hsub : ∀ᵐ z ∂rawInputLaw (fun _ ↦ a) Q,
      z ∈ {z | Raw.selected C (RawBridge.history C z H) = none} →
        z ∈ (GlobalDraws.sourceTape C) ⁻¹' E :=
    ae_partial_terminal_missing A hcard a Q ha hQ H
  have hh := measure_mono_ae hsub
  change (rawInputLaw (fun _ ↦ a) Q) {z | Raw.selected C (RawBridge.history C z H) = none} ≤
    (rawInputLaw (fun _ ↦ a) Q) ((GlobalDraws.sourceTape C) ⁻¹' E) at hh
  rw [hm] at hh
  exact ENNReal.toReal_mono (measure_ne_top _ _) hh

/-- The actual partial setup's early-completion probability at the source coupon horizon
has the explicit bound `4/n^(3/4)`. -/
theorem early_terminal_probability_le {n : ℕ} [NeZero n] (Aset : Finset (Fin n))
    (hcard : n ≤ Aset.card + 2) (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0)
    (ha1 : ∀ w, 1 ≤ a w) (hQ : ∀ m w, 0 < Q m w) (A : ℝ) (hA : 0 < A)
    (hupper : ∀ w, (a w : ℝ) ≤ A) (hnA : 2 * A ≤ n)
    (hlarge : 4 ≤ (n : ℝ) ^ (3 / 4 : ℝ)) :
    (rawInputLaw (fun _ ↦ a) Q).real {z |
      Raw.selected (GlobalDraws.activeProtocol Aset)
        (RawBridge.history (GlobalDraws.activeProtocol Aset) z
          ⌊(n : ℝ) * Real.log n / (8 * A)⌋₊) = none} ≤
      4 / (n : ℝ) ^ (3 / 4 : ℝ) := by
  apply (early_terminal_probability_le_missing Aset hcard a Q
    (fun w ↦ lt_of_lt_of_le (by norm_num) (ha1 w)) hQ _).trans
  exact CouponLowerTail.ofWeights_floor_missing_le_two a ha1 A hA hupper hnA hlarge

/-- The literal finite completed setup history for any active entrant subset. -/
noncomputable def setupHistory {n : ℕ} (A : Finset (Fin n)) (p : Profile n) :
    List (Ordinal.Entry n) :=
  Protocols.profileTranscript (Protocols.activeProtocol A) p (n * n)

/-- Current total genuine setup proposals under the exact active-market DA semantics. -/
noncomputable def setupTotal {n : ℕ} (A : Finset (Fin n)) (p : Profile n) : ℕ :=
  potential (Schedules.activeDeferredAcceptance p A)

/-- Actual accumulated proposer score at a woman in the completed finite setup history. -/
noncomputable def setupWeight {n : ℕ} (A : Finset (Fin n)) (b : Fin n → ℝ≥0)
    (p : Profile n) (w : Fin n) : ℝ := VisitBounds.gamma b (setupHistory A p) w

/-- The finite setup history has precisely the canonical completed active-market state. -/
theorem setupHistory_state {n : ℕ} (A : Finset (Fin n)) (p : Profile n) :
    Ordinal.recordState (setupHistory A p) = Schedules.activeDeferredAcceptance p A :=
  Protocols.activeProtocol_state A p

/-- The setup score is exactly the sum of scores of distinct actual proposers, not raw
repeat multiplicities and not a score statistic on an assumed independent matching. -/
theorem setupWeight_eq_sum {n : ℕ} (A : Finset (Fin n)) (b : Fin n → ℝ≥0)
    (p : Profile n) (w : Fin n) :
    setupWeight A b p w = ∑ m with HasProposed p (Schedules.activeDeferredAcceptance p A) m w,
      (b m : ℝ) := by
  classical
  rw [setupWeight, VisitBounds.gamma_eq_filter]
  have hv := Protocols.transcript_valid (Protocols.activeProtocol A) p.manRank
    (Ordinal.profilePriorities p) (n * n)
  have hiff (m : Fin n) : (w, m) ∈ Ordinal.seenEdges (setupHistory A p) ↔
      HasProposed p (Schedules.activeDeferredAcceptance p A) m w := by
    rw [Protocols.seenEdges_iff_hasProposed (Protocols.activeProtocol A) p.manRank
      (setupHistory A p) hv]
    change HasProposed p (Ordinal.recordState (setupHistory A p)) m w ↔ _
    rw [setupHistory_state]
  simp only [hiff]

/-- Every genuine setup counter is bounded by its full-market original PR counter. -/
theorem setup_counter_le_full {n : ℕ} (A : Finset (Fin n)) (p : Profile n) (m : Fin n) :
    (Schedules.activeDeferredAcceptance p A).next m ≤ (deferredAcceptance p).next m := by
  apply RepeatMoments.reachable_next_le_pr
  exact Schedules.reachable_mono_active p (Finset.subset_univ A)
    (Schedules.activeDeferredAcceptance_spec p A).1

/-- The actual total setup proposals are no more than the exact full PR total. -/
theorem setupTotal_le_full {n : ℕ} (A : Finset (Fin n)) (p : Profile n) :
    setupTotal A p ≤ RankTail.total p := by
  change (∑ m, (Schedules.activeDeferredAcceptance p A).next m) ≤
    ∑ m, (deferredAcceptance p).next m
  exact Finset.sum_le_sum fun m _ ↦ setup_counter_le_full A p m

/-- The actual completed setup inherits the proved full-market coupon total tail. -/
theorem setupTotal_tail {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) (Aset : Finset (Fin n))
    (A : ℝ) (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (H : ℕ) :
    (FiniteConditioning.eventMass (VisitBounds.profileLaw a b) {p | H < setupTotal Aset p}).toReal ≤
      n * Real.exp (-(H : ℝ) / (A * n)) := by
  apply le_trans _ (RankTail.total_tail hn a b hA ha1 haA hb H)
  exact RankTail.probability_mono _ (fun p hp ↦ lt_of_lt_of_le hp (setupTotal_le_full Aset p))

/-- Every distinct edge in an admissible raw setup prefix also occurs in the completed setup. -/
theorem raw_edge_in_setup {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    (L : List (RawSemantics.Edge n)) (hL : RawSemantics.RawAdmissible p A L)
    (w m : Fin n) (he : (w, m) ∈ L) :
    HasProposed p (Schedules.activeDeferredAcceptance p A) m w := by
  apply Schedules.reachable_proposals_subset_larger_terminal p (Finset.Subset.refl A)
    (RawSemantics.replay_reachable p A hL)
    (Schedules.activeDeferredAcceptance_spec p A).1
    (Schedules.activeDeferredAcceptance_spec p A).2 m w
  exact (RawSemantics.mem_trace_iff_hasProposed p A hL w m).mp he

/-- Distinct prefix proposers are bounded by the completed setup's actual accumulated score. -/
theorem raw_distinct_le_setupWeight {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    (b : Fin n → ℝ≥0) (hb : ∀ m, 1 ≤ (b m : ℝ))
    (L : List (RawSemantics.Edge n)) (hL : RawSemantics.RawAdmissible p A L) (w : Fin n) :
    ((Finset.univ.filter (fun m ↦ (w, m) ∈ L)).card : ℝ) ≤ setupWeight A b p w := by
  classical
  rw [setupWeight_eq_sum]
  calc
    _ = ∑ _m ∈ Finset.univ.filter (fun m ↦ (w, m) ∈ L), (1 : ℝ) := by simp
    _ ≤ ∑ m ∈ Finset.univ.filter (fun m ↦ (w, m) ∈ L), (b m : ℝ) :=
      Finset.sum_le_sum fun m _ ↦ hb m
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          raw_edge_in_setup p A L hL w m (Finset.mem_filter.mp hm).2⟩
      · intro m _ _
        exact (b m).coe_nonneg

/-- Any actual raw ordinal protocol stays below a cap on the original full PR ranks.
This extends the rank-cap bridge to partial active populations and arbitrary pauses. -/
theorem ae_rankCap_implies_noCap {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hQ : ∀ m w, 0 < Q m w)
    (C : Raw.Protocol n) (cap H : ℕ) :
    ∀ᵐ z ∂rawInputLaw (fun _ ↦ a) Q,
      z ∈ RepeatMoments.RankCap cap → z ∈ RepeatBounds.NoCap C cap H := by
  filter_upwards [RawBridge.ae_reachable (fun _ ↦ a) Q (fun _ ↦ ha) hQ
    C Finset.univ (RawBridge.supports_univ _)] with z hz
  intro hcap t _ m
  exact (RepeatMoments.reachable_next_le_pr _ _ (hz t) m).trans (hcap m)

/-- The exact raw market law is a probability measure for positive comparison scores. -/
theorem raw_probability {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) :
    IsProbabilityMeasure (rawInputLaw (fun _ ↦ a) Q) := by
  have (w m : Fin n) : IsProbabilityMeasure
      (ProbabilityTheory.expMeasure (Q m w : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by exact_mod_cast hQ m w)
  unfold rawInputLaw
  infer_instance

/-- Partial-protocol cap failure costs no more than the exact full PR rank-cap failure. -/
theorem noCap_failure_le_rankCap {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hQ : ∀ m w, 0 < Q m w)
    (C : Raw.Protocol n) (cap H : ℕ) :
    (rawInputLaw (fun _ ↦ a) Q).real (RepeatBounds.NoCap C cap H)ᶜ ≤
      (rawInputLaw (fun _ ↦ a) Q).real (RepeatMoments.RankCap cap)ᶜ := by
  have : IsProbabilityMeasure (rawInputLaw (fun _ ↦ a) Q) := raw_probability a Q hQ
  have hsub : ∀ᵐ z ∂rawInputLaw (fun _ ↦ a) Q,
      z ∈ (RepeatBounds.NoCap C cap H)ᶜ → z ∈ (RepeatMoments.RankCap cap)ᶜ := by
    filter_upwards [ae_rankCap_implies_noCap a Q ha hQ C cap H] with z hz
    exact fun hh hr ↦ hh (hz hr)
  have hh := measure_mono_ae hsub
  change rawInputLaw (fun _ ↦ a) Q (RepeatBounds.NoCap C cap H)ᶜ ≤
    rawInputLaw (fun _ ↦ a) Q (RepeatMoments.RankCap cap)ᶜ at hh
  exact ENNReal.toReal_mono (measure_ne_top _ _) hh

/-- The actual raw repeat tail for a partial protocol is bounded by full-rank-cap failure
plus its proved predictable repeat compensator. -/
theorem repeats_probability_le {n : ℕ} [NeZero n]
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    (A : ℝ) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (C : Raw.Protocol n) (cap H : ℕ) (R : ℝ) (hR : 0 < R) :
    (rawInputLaw (fun _ ↦ a) Q).real {z | R ≤ (RepeatBounds.repeats C H z : ℝ)} ≤
      (rawInputLaw (fun _ ↦ a) Q).real (RepeatMoments.RankCap cap)ᶜ +
        ((H : ℝ) * A * cap / n) / R := by
  have : IsProbabilityMeasure (rawInputLaw (fun _ ↦ a) Q) := raw_probability a Q hQ
  have ha : ∀ w, 0 < a w := fun w ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (ha1 w)
  have hA : 0 ≤ A := (a 0).coe_nonneg.trans (haA 0)
  have he : {z | R ≤ (RepeatBounds.repeats C H z : ℝ)} =
      {z | ENNReal.ofReal R ≤ (RepeatBounds.repeats C H z : ℝ≥0∞)} := by
    ext z
    simp only [Set.mem_ofPred_eq, ← ENNReal.ofReal_natCast]
    exact (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)).symm
  rw [measureReal_def, he]
  have hh := RepeatBounds.measure_repeats_ge_le_cap_failure a Q hQ ha1 haA C cap H
    (ENNReal.ofReal R) (ENNReal.ofReal_ne_zero_iff.mpr hR) ENNReal.ofReal_ne_top
  have hr := ENNReal.toReal_mono (by finiteness) hh
  rw [ENNReal.toReal_add (measure_ne_top _ _) (by finiteness), ENNReal.toReal_div,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (H : ℝ) * A * cap / n),
    ENNReal.toReal_ofReal hR.le] at hr
  exact hr.trans (add_le_add (noCap_failure_le_rankCap a Q ha hQ C cap H) le_rfl)

/-- Before any pause, each woman's actual raw multiplicity equals her literal global-tape
hit count. The equality includes repeats; it does not identify them with distinct proposers. -/
theorem rawHits_eq_tape_count {n : ℕ} [NeZero n] (C : Raw.Protocol n)
    (hs : GlobalDraws.PauseStable C) (female : Arrival.Edge n → ℝ)
    (x : (Fin n × ℕ) → Fin n) (H : ℕ)
    (hactive : ∀ t < H, Raw.selected C (Raw.transcript C (Function.curry x) female t) ≠ none)
    (w : Fin n) :
    (RepeatAccounting.rawHits
      (RawBridge.trace (Raw.transcript C (Function.curry x) female H)) w : ℝ) =
      CouponLowerTail.hitCount w H (GlobalDraws.tape C female x) := by
  classical
  induction H with
  | zero => simp [Raw.transcript, RawBridge.trace, RepeatAccounting.rawHits,
      CouponLowerTail.hitCount_eq_sum_range]
  | succ H ih =>
    have hi := ih (fun t ht ↦ hactive t (by omega))
    let h := Raw.transcript C (Function.curry x) female H
    obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp (hactive H (by omega))
    have htrace : RawBridge.trace (Raw.transcript C (Function.curry x) female (H + 1)) =
        (GlobalDraws.tape C female x H, m) :: RawBridge.trace h := by
      rw [Raw.transcript, GlobalDraws.observation_eq_respond_tape C hs female x H]
      simp only [GlobalDraws.respond, hm, Option.map_some, RawBridge.trace]
      rfl
    rw [htrace]
    rw [CouponLowerTail.hitCount_eq_sum_range] at hi ⊢
    rw [Finset.sum_range_succ]
    simp only [RepeatAccounting.rawHits, List.countP_cons, Nat.cast_add] at hi ⊢
    simp only [h]
    by_cases he : GlobalDraws.tape C female x H = w <;> simp [he] <;> linarith

/-- A current active partial protocol has the exact literal tape hit count at every woman. -/
theorem active_rawHits_eq_tape_count {n : ℕ} [NeZero n] (A : Finset (Fin n))
    (female : Arrival.Edge n → ℝ) (x : (Fin n × ℕ) → Fin n) (H : ℕ)
    (hactive : Raw.selected (GlobalDraws.activeProtocol A)
      (Raw.transcript (GlobalDraws.activeProtocol A) (Function.curry x) female H) ≠ none)
    (w : Fin n) :
    (RepeatAccounting.rawHits (RawBridge.trace (Raw.transcript (GlobalDraws.activeProtocol A)
      (Function.curry x) female H)) w : ℝ) =
      CouponLowerTail.hitCount w H (GlobalDraws.tape (GlobalDraws.activeProtocol A) female x) :=
  rawHits_eq_tape_count _ (GlobalDraws.activeProtocol_pauseStable A) female x H
    (no_earlier_pause _ (GlobalDraws.activeProtocol_pauseStable A) _ female H hactive) w

/-- Number of women with a literal IID prefix hit count below a deterministic threshold. -/
noncomputable def lowHitCount {n : ℕ} (H : ℕ) (r : ℝ) (x : ℕ → Fin n) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun w ↦ CouponLowerTail.hitCount w H x < r)).card : ℝ)

/-- A low-hit count is exactly the sum of its visible finite family of event indicators. -/
theorem lowHitCount_eq_sum {n : ℕ} (H : ℕ) (r : ℝ) (x : ℕ → Fin n) :
    lowHitCount H r x = ∑ w : Fin n,
      {x | CouponLowerTail.hitCount w H x < r}.indicator (fun _ ↦ (1 : ℝ)) x := by
  classical
  simp [lowHitCount, Set.indicator, Finset.sum_boole]

/-- Low-hit count is a measurable bounded statistic of the literal coupon prefix. -/
theorem measurable_lowHitCount {n : ℕ} (H : ℕ) (r : ℝ) :
    Measurable (lowHitCount (n := n) H r) := by
  have he : lowHitCount (n := n) H r = fun x ↦ ∑ w : Fin n,
      {x | CouponLowerTail.hitCount w H x < r}.indicator (fun _ ↦ (1 : ℝ)) x :=
    funext (lowHitCount_eq_sum H r)
  rw [he]
  apply Finset.measurable_sum
  intro w _
  exact measurable_const.indicator
    (measurableSet_lt (CouponLowerTail.measurable_hitCount w H) measurable_const)

/-- Low-hit counts lie between zero and the number of women. -/
theorem lowHitCount_bounds {n : ℕ} (H : ℕ) (r : ℝ) (x : ℕ → Fin n) :
    0 ≤ lowHitCount H r x ∧ lowHitCount H r x ≤ n := by
  classical
  constructor
  · exact Nat.cast_nonneg _
  · change ((Finset.univ.filter (fun w ↦ CouponLowerTail.hitCount w H x < r)).card : ℝ) ≤ n
    have hh := Finset.card_le_card (Finset.filter_subset
      (fun w : Fin n ↦ CouponLowerTail.hitCount w H x < r) Finset.univ)
    simp only [Finset.card_univ, Fintype.card_fin] at hh
    exact_mod_cast hh

/-- Low-hit count is integrable under its actual IID stream law. -/
theorem integrable_lowHitCount {n : ℕ} (p : PMF (Fin n)) (H : ℕ) (r : ℝ) :
    Integrable (lowHitCount (n := n) H r) (FirstFresh.iidStream p) := by
  apply (integrable_const (μ := FirstFresh.iidStream p) (n : ℝ)).mono'
    (measurable_lowHitCount H r).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (lowHitCount_bounds H r x).1]
  exact (lowHitCount_bounds H r x).2

/-- The exact mean low-hit count is the sum of its individual coupon lower-tail probabilities. -/
theorem integral_lowHitCount {n : ℕ} (p : PMF (Fin n)) (H : ℕ) (r : ℝ) :
    (∫ x, lowHitCount H r x ∂FirstFresh.iidStream p) =
      ∑ w : Fin n, (FirstFresh.iidStream p).real {x | CouponLowerTail.hitCount w H x < r} := by
  simp_rw [lowHitCount_eq_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro w _
    rw [integral_indicator_const]
    · simp
    · exact measurableSet_lt (CouponLowerTail.measurable_hitCount w H) measurable_const
  · intro w _
    exact (integrable_const (1 : ℝ)).indicator
      (measurableSet_lt (CouponLowerTail.measurable_hitCount w H) measurable_const)

/-- A proved individual coupon lower tail yields the finite low-hit-count Markov bound. -/
theorem lowHitCount_tail {n : ℕ} (p : PMF (Fin n)) (H : ℕ) (r R q : ℝ) (hR : 0 < R)
    (hp : ∀ w, (FirstFresh.iidStream p).real {x | CouponLowerTail.hitCount w H x < r} ≤ q) :
    (FirstFresh.iidStream p).real {x | R ≤ lowHitCount H r x} ≤ (n : ℝ) * q / R := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun x ↦ (lowHitCount_bounds H r x).1)
    (integrable_lowHitCount p H r) R
  have he : (∫ x, lowHitCount H r x ∂FirstFresh.iidStream p) ≤ (n : ℝ) * q := by
    rw [integral_lowHitCount]
    calc
      _ ≤ ∑ _w : Fin n, q := Finset.sum_le_sum fun w _ ↦ hp w
      _ = _ := by simp
  apply (le_div_iff₀ hR).mpr
  nlinarith

/-- Actual normalized-score source-tape lower tails control the number of low-hit women,
with all constants uniform in tier shares. -/
theorem sourceTape_lowHitCount_tail {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w)
    (ha : ∀ w, 1 ≤ a w) (A : ℝ) (hA : 0 < A) (hupper : ∀ w, (a w : ℝ) ≤ A)
    (hlarge : 16 * A ≤ (n : ℝ) * Real.log n) (C : Raw.Protocol n)
    (hs : GlobalDraws.PauseStable C) (R : ℝ) (hR : 0 < R) :
    (rawInputLaw (fun _ ↦ a) Q).real {z | R ≤ lowHitCount
      ⌊(n : ℝ) * Real.log n / (8 * A)⌋₊ (Real.log n / (32 * A ^ 2))
        (GlobalDraws.sourceTape C z)} ≤ (n : ℝ) * (n : ℝ) ^ (-(1 / (192 * A ^ 2))) / R := by
  let H := ⌊(n : ℝ) * Real.log n / (8 * A)⌋₊
  let r := Real.log n / (32 * A ^ 2)
  have hE : MeasurableSet {x : ℕ → Fin n | R ≤ lowHitCount H r x} :=
    measurableSet_le measurable_const (measurable_lowHitCount H r)
  have he : rawInputLaw (fun _ ↦ a) Q {z | R ≤ lowHitCount H r (GlobalDraws.sourceTape C z)} =
      FirstFresh.iidStream (RandomRanking.ofWeights a) {x | R ≤ lowHitCount H r x} := by
    rw [← GlobalDraws.sourceTape_law C hs a Q hQ,
      Measure.map_apply (GlobalDraws.measurable_sourceTape C hs) hE]
    rfl
  rw [measureReal_def, he]
  apply lowHitCount_tail _ H r R _ hR
  intro w
  apply le_trans (measureReal_mono (μ := FirstFresh.iidStream (RandomRanking.ofWeights a))
    (show {x | CouponLowerTail.hitCount w H x < r} ⊆
      {x | CouponLowerTail.hitCount w H x ≤ r} from fun x hx ↦ by
        change CouponLowerTail.hitCount w H x < r at hx
        exact hx.le))
  simpa only [Fintype.card_fin] using
    CouponLowerTail.ofWeights_floor_small_hit_tail a ha A hA hupper w
      (by simpa only [Fintype.card_fin] using hlarge)

/-- Number of women below a specified actual completed-setup accumulated-score threshold. -/
noncomputable def badSetupCount {n : ℕ} (A : Finset (Fin n)) (b : Fin n → ℝ≥0)
    (p : Profile n) (c : ℝ) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun w ↦ setupWeight A b p w < c)).card : ℝ)

/-- Exact deterministic setup comparison: low actual setup score can arise only from a
low literal raw hit count or from repeated edges. The global source tape is used only
before pause. -/
theorem badSetupCount_le_raw_low_add_repeats {n : ℕ} [NeZero n]
    (A : Finset (Fin n)) (b : Fin n → ℝ≥0) (hb : ∀ m, 1 ≤ (b m : ℝ))
    (z : Raw.Sources n) (H : ℕ) (c : ℝ) (hc : 0 < c)
    (hL : RawSemantics.RawAdmissible (RawBridge.sourceProfile z) A
      (RawBridge.trace (RawBridge.history (GlobalDraws.activeProtocol A) z H)))
    (hactive : Raw.selected (GlobalDraws.activeProtocol A)
      (RawBridge.history (GlobalDraws.activeProtocol A) z H) ≠ none) :
    badSetupCount A b (RawBridge.sourceProfile z) c ≤
      lowHitCount H (2 * c) (GlobalDraws.sourceTape (GlobalDraws.activeProtocol A) z) +
        (RepeatBounds.repeats (GlobalDraws.activeProtocol A) H z : ℝ) / c := by
  classical
  let L := RawBridge.trace (RawBridge.history (GlobalDraws.activeProtocol A) z H)
  have hd (w : Fin n) : (RepeatAccounting.distinctHits L w : ℝ) ≤
      setupWeight A b (RawBridge.sourceProfile z) w := by
    rw [RepeatAccounting.distinctHits_eq_card_men]
    exact raw_distinct_le_setupWeight _ A b hb L hL w
  have hsub : Finset.univ.filter (fun w ↦ setupWeight A b (RawBridge.sourceProfile z) w < c) ⊆
      Finset.univ.filter (fun w ↦ (RepeatAccounting.distinctHits L w : ℝ) < c) := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      lt_of_le_of_lt (hd w) (Finset.mem_filter.mp hw).2⟩
  have hr (w : Fin n) : (RepeatAccounting.rawHits L w : ℝ) =
      CouponLowerTail.hitCount w H (GlobalDraws.sourceTape (GlobalDraws.activeProtocol A) z) := by
    exact active_rawHits_eq_tape_count A (RawBridge.sourceFemale z) (Function.uncurry z.1)
      H hactive w
  have hcard :
      ((Finset.univ.filter (fun w ↦ (RepeatAccounting.rawHits L w : ℝ) < 2 * c)).card : ℝ) =
      lowHitCount H (2 * c) (GlobalDraws.sourceTape (GlobalDraws.activeProtocol A) z) := by
    simp only [hr]
    rfl
  calc
    _ ≤ ((Finset.univ.filter (fun w ↦ (RepeatAccounting.distinctHits L w : ℝ) < c)).card : ℝ) :=
      by
        change ((Finset.univ.filter
          (fun w ↦ setupWeight A b (RawBridge.sourceProfile z) w < c)).card : ℝ) ≤ _
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((Finset.univ.filter (fun w ↦ (RepeatAccounting.rawHits L w : ℝ) < 2 * c)).card : ℝ) +
        (RawSemantics.repeatCount L : ℝ) / c :=
      RepeatAccounting.badDistinct_card_le_badRaw_add_repeats_div L hc
    _ = _ := by rw [hcard, RepeatMoments.repeats_eq_trace_repeatCount]

/-- The completed original profile has the exact PR law under the actual raw market inputs. -/
theorem sourceProfile_law {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (ha : ∀ w, 0 < a w) (hQ : ∀ m w, 0 < Q m w) :
    Measure.map RawBridge.sourceProfile (rawInputLaw (fun _ ↦ a) Q) =
      (RandomRanking.profile (fun _ ↦ a) Q).toMeasure :=
  iid_raw_profile_law (fun _ ↦ a) Q (fun _ ↦ ha) hQ

/-- Exact profile-event transfer from the finite original PR law to the actual raw sources. -/
theorem profile_event_eq_raw {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (ha : ∀ w, 0 < a w) (hQ : ∀ m w, 0 < Q m w)
    (E : Set (Profile n)) :
    ((RandomRanking.profile (fun _ ↦ a) Q).toMeasure).real E =
      (rawInputLaw (fun _ ↦ a) Q).real (RawBridge.sourceProfile ⁻¹' E) := by
  rw [measureReal_def, measureReal_def, ← sourceProfile_law a Q ha hQ,
    Measure.map_apply RepeatMoments.measurable_sourceProfile (by trivial)]

/-- Exact finite setup decomposition: bad completed setup scores require early completion,
too many low literal tape counts, or too many actual repeated edges. -/
theorem badSetupCount_probability_le_three {n : ℕ} [NeZero n]
    (a b : Fin n → ℝ≥0) (ha : ∀ w, 0 < a w) (hb : ∀ m, 1 ≤ (b m : ℝ))
    (Aset : Finset (Fin n)) (H : ℕ) (c D : ℝ) (hc : 0 < c) :
    ((VisitBounds.profileLaw a b).toMeasure).real {p | D ≤ badSetupCount Aset b p c} ≤
      (rawInputLaw (fun _ ↦ a) (fun m _ ↦ b m)).real {z |
        Raw.selected (GlobalDraws.activeProtocol Aset)
          (RawBridge.history (GlobalDraws.activeProtocol Aset) z H) = none} +
      (rawInputLaw (fun _ ↦ a) (fun m _ ↦ b m)).real {z |
        D / 2 ≤ lowHitCount H (2 * c)
          (GlobalDraws.sourceTape (GlobalDraws.activeProtocol Aset) z)} +
      (rawInputLaw (fun _ ↦ a) (fun m _ ↦ b m)).real {z |
        c * D / 2 ≤ (RepeatBounds.repeats (GlobalDraws.activeProtocol Aset) H z : ℝ)} := by
  have hbpos : ∀ m, 0 < b m := fun m ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (hb m)
  have : IsProbabilityMeasure (rawInputLaw (fun _ ↦ a) (fun m _ ↦ b m)) :=
    raw_probability a _ (fun m _ ↦ hbpos m)
  let μ := rawInputLaw (fun _ ↦ a) (fun m _ ↦ b m)
  let C := GlobalDraws.activeProtocol Aset
  let E0 : Set (Raw.Sources n) := {z | Raw.selected C (RawBridge.history C z H) = none}
  let E1 : Set (Raw.Sources n) := {z | D / 2 ≤ lowHitCount H (2 * c) (GlobalDraws.sourceTape C z)}
  let E2 : Set (Raw.Sources n) := {z | c * D / 2 ≤ (RepeatBounds.repeats C H z : ℝ)}
  change ((RandomRanking.profile (fun _ ↦ a) (fun m _ ↦ b m)).toMeasure).real _ ≤ _
  rw [profile_event_eq_raw a _ ha (fun m _ ↦ hbpos m)]
  have hsub : ∀ᵐ z ∂μ,
      z ∈ RawBridge.sourceProfile ⁻¹' {p | D ≤ badSetupCount Aset b p c} →
        z ∈ E0 ∪ (E1 ∪ E2) := by
    filter_upwards [RawBridge.ae_transcript_bridge (fun _ ↦ a) (fun m _ ↦ b m)
      (fun _ ↦ ha) (fun m _ ↦ hbpos m) C Aset (activeProtocol_supports Aset)] with z hz
    intro hbad
    by_cases h0 : z ∈ E0
    · exact Or.inl h0
    · by_cases h1 : z ∈ E1
      · exact Or.inr (Or.inl h1)
      · by_cases h2 : z ∈ E2
        · exact Or.inr (Or.inr h2)
        · have hcomparison := badSetupCount_le_raw_low_add_repeats Aset b hb z H c hc
            (hz H).1 h0
          have hl : lowHitCount H (2 * c) (GlobalDraws.sourceTape C z) < D / 2 :=
            lt_of_not_ge h1
          have hr : (RepeatBounds.repeats C H z : ℝ) / c < D / 2 :=
            (div_lt_iff₀ hc).mpr (by
              have hh : (RepeatBounds.repeats C H z : ℝ) < c * D / 2 := lt_of_not_ge h2
              nlinarith)
          change D ≤ badSetupCount Aset b (RawBridge.sourceProfile z) c at hbad
          dsimp [C] at hl hr
          exact False.elim (not_lt_of_ge hbad (by linarith))
  have hh := measure_mono_ae hsub
  change μ (RawBridge.sourceProfile ⁻¹' {p | D ≤ badSetupCount Aset b p c}) ≤
    μ (E0 ∪ (E1 ∪ E2)) at hh
  calc
    _ ≤ μ.real (E0 ∪ (E1 ∪ E2)) := ENNReal.toReal_mono (measure_ne_top _ _) hh
    _ ≤ μ.real E0 + μ.real (E1 ∪ E2) := measureReal_union_le _ _
    _ ≤ μ.real E0 + (μ.real E1 + μ.real E2) :=
      add_le_add le_rfl (measureReal_union_le _ _)
    _ = _ := by ring

/-- All probabilistic ingredients of actual setup smoothness, with the full-rank cap still
visible as an actual PR error event. The next uniform step pays for it using RankTail. -/
theorem badSetupCount_probability_le_finite {n : ℕ} [NeZero n]
    (a b : Fin n → ℝ≥0) (ha1 : ∀ w, 1 ≤ a w) (hb1 : ∀ m, 1 ≤ (b m : ℝ))
    (Aset : Finset (Fin n)) (hcard : n ≤ Aset.card + 2)
    (A : ℝ) (hA : 0 < A) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hnA : 2 * A ≤ n) (hsize : 4 ≤ (n : ℝ) ^ (3 / 4 : ℝ))
    (hlarge : 16 * A ≤ (n : ℝ) * Real.log n) (hlog : 0 < Real.log n)
    (cap : ℕ) (D : ℝ) (hD : 0 < D) :
    let H := ⌊(n : ℝ) * Real.log n / (8 * A)⌋₊
    let c := Real.log n / (64 * A ^ 2)
    ((VisitBounds.profileLaw a b).toMeasure).real {p | D ≤ badSetupCount Aset b p c} ≤
      4 / (n : ℝ) ^ (3 / 4 : ℝ) +
      (n : ℝ) * (n : ℝ) ^ (-(1 / (192 * A ^ 2))) / (D / 2) +
      (rawInputLaw (fun _ ↦ a) (fun m _ ↦ b m)).real (RepeatMoments.RankCap cap)ᶜ +
      ((H : ℝ) * A * cap / n) / (c * D / 2) := by
  dsimp only
  let H := ⌊(n : ℝ) * Real.log n / (8 * A)⌋₊
  let c := Real.log n / (64 * A ^ 2)
  have hc : 0 < c := div_pos hlog (by positivity)
  have ha : ∀ w, 0 < a w := fun w ↦ lt_of_lt_of_le (by norm_num) (ha1 w)
  have hb : ∀ m, 0 < b m := fun m ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (hb1 m)
  have hbound := badSetupCount_probability_le_three a b ha hb1 Aset H c D hc
  have h0 := early_terminal_probability_le Aset hcard a (fun m _ ↦ b m) ha1
    (fun m _ ↦ hb m) A hA haA hnA hsize
  have h1 := sourceTape_lowHitCount_tail a (fun m _ ↦ b m) (fun m _ ↦ hb m) ha1 A hA haA
    hlarge (GlobalDraws.activeProtocol Aset) (GlobalDraws.activeProtocol_pauseStable Aset)
    (D / 2) (by positivity)
  have he : 2 * c = Real.log n / (32 * A ^ 2) := by dsimp [c]; ring
  rw [← he] at h1
  have h2 := repeats_probability_le a (fun m _ ↦ b m) (fun m _ ↦ hb m) A
    (fun w ↦ by exact_mod_cast ha1 w) haA (GlobalDraws.activeProtocol Aset) cap H
    (c * D / 2) (by positivity)
  exact hbound.trans (by linarith)

/-- Uniform total-setup tail with an explicit coefficient, inherited from the proved full
PR coupon tail rather than assumed as a good-setup event. -/
theorem bad_setup_total_probability {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0)
    (Aset : Finset (Fin n)) {A r : ℝ} (hA : 1 ≤ A) (hr : 0 ≤ r) (hlog : 1 ≤ Real.log n)
    (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A) (hb : ∀ m, 0 < b m) :
    SurvivalKernel.probability (VisitBounds.profileLaw a b)
      {p | ¬(setupTotal Aset p : ℝ) ≤ RankTail.setupCoefficient A r * n * Real.log n} ≤
        (n : ℝ) ^ (-(r + 1)) := by
  have hApos : 0 < A := by linarith
  have hK : 0 ≤ A * (r + 2) := mul_nonneg hApos.le (by linarith)
  have hceil := Continuation.globalCap_le (show 1 ≤ n by omega) hK hlog
  have hsub : {p | ¬(setupTotal Aset p : ℝ) ≤
      RankTail.setupCoefficient A r * n * Real.log n} ⊆
      {p | ContinuationAsymptotics.globalCap (A * (r + 2)) n < RankTail.total p} := by
    intro p hp
    have hs : (setupTotal Aset p : ℝ) ≤ RankTail.total p := by
      exact_mod_cast setupTotal_le_full Aset p
    have hc : (ContinuationAsymptotics.globalCap (A * (r + 2)) n : ℝ) ≤
        RankTail.setupCoefficient A r * n * Real.log n := hceil
    have ht : (ContinuationAsymptotics.globalCap (A * (r + 2)) n : ℝ) < RankTail.total p := by
      change ¬(setupTotal Aset p : ℝ) ≤ _ at hp
      linarith
    exact_mod_cast ht
  apply (RankTail.probability_mono (VisitBounds.profileLaw a b) hsub).trans
  have ht := RankTail.total_tail hn a b hA ha1 haA hb
    (ContinuationAsymptotics.globalCap (A * (r + 2)) n)
  have hg := ContinuationAsymptotics.global_exp_le hApos hn (by linarith : 0 ≤ Real.log n)
    (le_refl (A * (r + 2)))
  rw [ContinuationAsymptotics.exp_neg_log_eq_rpow hn (r + 2)] at hg
  have hp : (n : ℝ) * (n : ℝ) ^ (-(r + 2)) = (n : ℝ) ^ (-(r + 1)) := by
    rw [show -(r + 2) = -((r + 1) + 1) by ring]
    exact RankTail.nat_mul_rpow hn (r + 1)
  exact ht.trans ((mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg n)).trans_eq hp)

/-- Rank-cap failure of the actual raw partial execution is no larger than the proved
finite PR event that some completed rank reaches the same integer threshold. -/
theorem rankCap_failure_le_rank_event {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (cap : ℕ) :
    (rawInputLaw (fun _ ↦ a) (fun m _ ↦ b m)).real (RepeatMoments.RankCap cap)ᶜ ≤
      (FiniteConditioning.eventMass (VisitBounds.profileLaw a b)
        {p | ∃ m, cap ≤ RankTail.rank p m}).toReal := by
  rw [RepeatMoments.rankCap_compl_real_eq_profile a _ ha (fun m _ ↦ hb m) cap,
    FiniteConditioning.eventMass_eq_toMeasure _ _ (by trivial)]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  rintro p ⟨m, hm⟩
  exact ⟨m, le_of_lt hm⟩

/-- Scaled logarithmic squares are eventually smaller than every positive power, with a
threshold depending only on the fixed numerical constants. -/
theorem eventually_scaled_log_sq_le {K s : ℝ} (hK : 0 < K) (hs : 0 < s) :
    ∀ᶠ n : ℕ in Filter.atTop, K * (Real.log n) ^ 2 ≤ (n : ℝ) ^ s := by
  have hr := (isLittleO_log_rpow_rpow_atTop (s := s) 2 hs).comp_tendsto
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop)
  filter_upwards [hr.def (show 0 < 1 / K by positivity)] with n hn
  have hn' : (Real.log n) ^ 2 ≤ (1 / K) * (n : ℝ) ^ s := by
    simpa only [Function.comp_apply, Real.rpow_two, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (Real.log (n : ℝ))),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s)] using hn
  have hh := mul_le_mul_of_nonneg_left hn' hK.le
  simpa only [← mul_assoc, mul_one_div_cancel hK.ne', one_mul] using hh

/-- The repeat compensator simplifies to a squared logarithm divided by the allowed number
of exceptional women. All floor and ceiling errors are explicit here. -/
theorem repeat_compensator_simplify {n H cap : ℕ} {A C D L T : ℝ}
    (hn : 0 < n) (hA : 0 < A) (hC : 0 < C) (hL : 1 ≤ L) (hT : 0 < T)
    (hH : (H : ℝ) ≤ (n : ℝ) * L / (8 * A))
    (hcap : (cap : ℝ) ≤ (D + 1) * L ^ 2) :
    ((H : ℝ) * A * cap / n) / (C * L * T / 2) ≤
      ((D + 1) / (4 * C)) * L ^ 2 / T := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hLpos : 0 < L := by linarith
  have hden : 0 < C * L * T / 2 := by positivity
  have he : ((n : ℝ) * L / (8 * A)) * (A / n) = L / 8 := by field_simp
  have hscale := mul_le_mul_of_nonneg_right hH (div_nonneg hA.le hnR.le)
  rw [he] at hscale
  have hnum : (H : ℝ) * A * cap / n ≤ (L / 8) * cap := by
    have hh := mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg cap : (0 : ℝ) ≤ cap)
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh
  calc
    _ ≤ ((L / 8) * cap) / (C * L * T / 2) := div_le_div_of_nonneg_right hnum hden.le
    _ = (cap : ℝ) / (4 * C * T) := by field_simp; ring
    _ ≤ ((D + 1) * L ^ 2) / (4 * C * T) :=
      div_le_div_of_nonneg_right hcap (by positivity)
    _ = _ := by ring

/-- Fixed accumulated-score coefficient for setup smoothness. -/
noncomputable def gammaCoefficient (A : ℝ) : ℝ := 1 / (64 * A ^ 2)

/-- Fixed exceptional-woman and failure exponent for setup smoothness. -/
noncomputable def setupExponent (A : ℝ) : ℝ := 1 / (768 * A ^ 2)

/-- The setup coefficients are uniformly positive and the exponent is safely below one half. -/
theorem setup_constants {A : ℝ} (hA : 1 ≤ A) :
    0 < gammaCoefficient A ∧ 0 < setupExponent A ∧ setupExponent A ≤ 1 / 4 := by
  have hAsq : 1 ≤ A ^ 2 := by nlinarith
  have hd : 0 < 768 * A ^ 2 := by positivity
  refine ⟨by unfold gammaCoefficient; positivity, by unfold setupExponent; positivity, ?_⟩
  unfold setupExponent
  exact (div_le_iff₀ hd).mpr (by nlinarith)

/-- Exact relation between the fixed raw-coupon Chernoff exponent and the setup exponent. -/
theorem raw_exponent_eq_four (A : ℝ) : 1 / (192 * A ^ 2) = 4 * setupExponent A := by
  unfold setupExponent
  ring

/-- The low-raw-count Markov term has polynomial decay at the fixed setup exponent. -/
theorem low_raw_power_le {n : ℕ} (hn : 0 < n) {κ : ℝ} (hκ : 0 ≤ κ) :
    (n : ℝ) * (n : ℝ) ^ (-(4 * κ)) / ((n : ℝ) ^ (1 - κ) / 2) ≤
      2 * (n : ℝ) ^ (-κ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he : (n : ℝ) * (n : ℝ) ^ (-(4 * κ)) = (n : ℝ) ^ (1 - 4 * κ) := by
    rw [Real.rpow_sub hnR, Real.rpow_one]
    rw [Real.rpow_neg hnR.le]
    ring
  calc
    _ = 2 * (((n : ℝ) * (n : ℝ) ^ (-(4 * κ))) / (n : ℝ) ^ (1 - κ)) := by ring
    _ = 2 * ((n : ℝ) ^ (1 - 4 * κ) / (n : ℝ) ^ (1 - κ)) := by rw [he]
    _ = 2 * (n : ℝ) ^ (-(3 * κ)) := by
      rw [← Real.rpow_sub hnR]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) (by norm_num)

/-- At the fixed source setup horizon and a proved log-squared rank cap, the actual repeat
compensator is eventually at most the desired polynomial failure probability. -/
theorem eventually_repeat_compensator_le {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∀ᶠ n : ℕ in Filter.atTop,
      let H := ⌊(n : ℝ) * Real.log n / (8 * A)⌋₊
      let cap := Nat.ceil (RankTail.rankCoefficient A B 3 * (Real.log n) ^ 2)
      ((H : ℝ) * A * cap / n) /
        ((Real.log n / (64 * A ^ 2)) * (n : ℝ) ^ (1 - setupExponent A) / 2) ≤
        (n : ℝ) ^ (-setupExponent A) := by
  let κ := setupExponent A
  let C := gammaCoefficient A
  let D := RankTail.rankCoefficient A B 3
  let K := (D + 1) / (4 * C)
  have hκ := setup_constants hA
  have hC : 0 < C := hκ.1
  have hD : 0 < D := RankTail.rankCoefficient_pos hA hB (by norm_num)
  have hK : 0 < K := div_pos (by dsimp [D]; linarith [hD]) (by positivity)
  have hs : 0 < 1 - 2 * κ := by dsimp [κ]; linarith [hκ.2.2]
  filter_upwards [eventually_scaled_log_sq_le hK hs,
    ContinuationAsymptotics.eventually_one_le_log, Filter.eventually_ge_atTop 1]
    with n hscaled hlog hn
  dsimp only
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hApos : 0 < A := by linarith
  have hT : 0 < (n : ℝ) ^ (1 - κ) := Real.rpow_pos_of_pos hnR _
  have hcap : (Nat.ceil (D * (Real.log n) ^ 2) : ℝ) ≤ (D + 1) * (Real.log n) ^ 2 := by
    have hh := (Nat.ceil_lt_add_one (mul_nonneg hD.le (sq_nonneg (Real.log n)))).le
    nlinarith
  have hh := repeat_compensator_simplify hn0 hApos hC hlog hT
    (CouponLowerTail.floor_setup_horizon_upper n A hApos) hcap
  have he : C * Real.log n = Real.log n / (64 * A ^ 2) := by dsimp [C, gammaCoefficient]; ring
  rw [he] at hh
  apply hh.trans
  have hratio := div_le_div_of_nonneg_right hscaled hT.le
  have heq : (n : ℝ) ^ (1 - 2 * κ) / (n : ℝ) ^ (1 - κ) = (n : ℝ) ^ (-κ) := by
    rw [← Real.rpow_sub hnR]
    congr 1
    ring
  rw [heq] at hratio
  exact hratio

/-- Uniform actual setup accumulated-score smoothness. All stochastic inputs have been
proved under the original profile/raw laws; the constants depend only on fixed score bounds. -/
theorem eventually_badSetupCount_probability {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (a b : Fin n → ℝ≥0),
      (∀ w, 1 ≤ (a w : ℝ)) → (∀ w, (a w : ℝ) ≤ A) →
      (∀ m, 1 ≤ (b m : ℝ)) → (∀ m, (b m : ℝ) ≤ B) →
      ∀ Aset : Finset (Fin n), n ≤ Aset.card + 2 →
      ((VisitBounds.profileLaw a b).toMeasure).real {p |
        (n : ℝ) ^ (1 - setupExponent A) ≤
          badSetupCount Aset b p (Real.log n / (64 * A ^ 2))} ≤
            12 * (n : ℝ) ^ (-setupExponent A) := by
  have hApos : 0 < A := by linarith
  have hk := setup_constants hA
  have hncast : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hpowers := (tendsto_rpow_atTop (by norm_num : 0 < (3 / 4 : ℝ))).comp hncast
  filter_upwards [RankTail.eventually_max_rank_tail hA hB (by norm_num : (0 : ℝ) ≤ 3),
    eventually_repeat_compensator_le hA hB, CouponLowerTail.eventually_setup_large A,
    ContinuationAsymptotics.eventually_one_le_log, hncast.eventually_ge_atTop (2 * A),
    hpowers.eventually_ge_atTop 4, Filter.eventually_ge_atTop 1]
    with n hmax hrep hlarge hlog hnA hsize hn a b ha1 haA hb1 hbB Aset hcard
  have hn0 : 0 < n := by omega
  have : NeZero n := ⟨Nat.ne_of_gt hn0⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  change 4 ≤ (n : ℝ) ^ (3 / 4 : ℝ) at hsize
  let cap := Nat.ceil (RankTail.rankCoefficient A B 3 * (Real.log n) ^ 2)
  have ha : ∀ w, 0 < a w := fun w ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (ha1 w)
  have hb : ∀ m, 0 < b m := fun m ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (hb1 m)
  have hrank : (rawInputLaw (fun _ ↦ a) (fun m _ ↦ b m)).real
      (RepeatMoments.RankCap cap)ᶜ ≤ 5 * (n : ℝ) ^ (-(3 : ℝ)) :=
    (rankCap_failure_le_rank_event a b ha hb cap).trans (hmax a b ha1 haA hb1 hbB)
  have hbound := badSetupCount_probability_le_finite a b
    (fun w ↦ by exact_mod_cast ha1 w) hb1 Aset hcard A hApos haA hnA hsize hlarge
    (by linarith : 0 < Real.log n) cap ((n : ℝ) ^ (1 - setupExponent A))
    (Real.rpow_pos_of_pos hnR _)
  dsimp only at hbound
  have hlow := low_raw_power_le hn0 hk.2.1.le
  rw [← raw_exponent_eq_four A] at hlow
  have hearly : 4 / (n : ℝ) ^ (3 / 4 : ℝ) ≤ 4 * (n : ℝ) ^ (-setupExponent A) := by
    calc
      _ = 4 * (n : ℝ) ^ (-(3 / 4 : ℝ)) := by rw [Real.rpow_neg hnR.le]; rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [hk.2.2])) (by norm_num)
  have hrank' : 5 * (n : ℝ) ^ (-(3 : ℝ)) ≤ 5 * (n : ℝ) ^ (-setupExponent A) :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [hk.2.2])) (by norm_num)
  dsimp only at hrep
  dsimp [cap] at hrank
  exact hbound.trans (by linarith)

/-- Uniform actual smooth setup for any population missing at most two entrants. The total
coefficient is `5*A+1`, the score coefficient is `1/(64*A^2)`, and the fixed positive exponent
is `1/(768*A^2)`. The failure bound is `13*n^(-exponent)`. -/
theorem eventually_smooth_setup {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (a b : Fin n → ℝ≥0),
      (∀ w, 1 ≤ (a w : ℝ)) → (∀ w, (a w : ℝ) ≤ A) →
      (∀ m, 1 ≤ (b m : ℝ)) → (∀ m, (b m : ℝ) ≤ B) →
      ∀ Aset : Finset (Fin n), n ≤ Aset.card + 2 →
      ((VisitBounds.profileLaw a b).toMeasure).real {p | ¬(
        (setupTotal Aset p : ℝ) ≤ RankTail.setupCoefficient A 3 * n * Real.log n ∧
        badSetupCount Aset b p (Real.log n / (64 * A ^ 2)) ≤
          (n : ℝ) ^ (1 - setupExponent A))} ≤ 13 * (n : ℝ) ^ (-setupExponent A) := by
  filter_upwards [eventually_badSetupCount_probability hA hB,
    ContinuationAsymptotics.eventually_one_le_log, Filter.eventually_ge_atTop 1]
    with n hbad hlog hn a b ha1 haA hb1 hbB Aset hcard
  have hn0 : 0 < n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb : ∀ m, 0 < b m := fun m ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (hb1 m)
  have ht := bad_setup_total_probability hn0 a b Aset hA (by norm_num : (0 : ℝ) ≤ 3)
    hlog ha1 haA hb
  change (FiniteConditioning.eventMass (VisitBounds.profileLaw a b) _).toReal ≤ _ at ht
  rw [FiniteConditioning.eventMass_eq_toMeasure _ _ (by trivial)] at ht
  change ((VisitBounds.profileLaw a b).toMeasure).real
    {p | ¬(setupTotal Aset p : ℝ) ≤ RankTail.setupCoefficient A 3 * n * Real.log n} ≤
      (n : ℝ) ^ (-(3 + 1 : ℝ)) at ht
  have hscore := hbad a b ha1 haA hb1 hbB Aset hcard
  have hsub : {p : Profile n | ¬(
      (setupTotal Aset p : ℝ) ≤ RankTail.setupCoefficient A 3 * n * Real.log n ∧
      badSetupCount Aset b p (Real.log n / (64 * A ^ 2)) ≤
        (n : ℝ) ^ (1 - setupExponent A))} ⊆
      {p | ¬(setupTotal Aset p : ℝ) ≤ RankTail.setupCoefficient A 3 * n * Real.log n} ∪
      {p | (n : ℝ) ^ (1 - setupExponent A) ≤
        badSetupCount Aset b p (Real.log n / (64 * A ^ 2))} := by
    intro p hp
    by_cases hh : (setupTotal Aset p : ℝ) ≤ RankTail.setupCoefficient A 3 * n * Real.log n
    · right
      exact le_of_lt (lt_of_not_ge (fun hs ↦ hp ⟨hh, hs⟩))
    · exact Or.inl hh
  have hpow : (n : ℝ) ^ (-(3 + 1 : ℝ)) ≤ (n : ℝ) ^ (-setupExponent A) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [(setup_constants hA).2.2])
  calc
    _ ≤ ((VisitBounds.profileLaw a b).toMeasure).real
        ({p | ¬(setupTotal Aset p : ℝ) ≤ RankTail.setupCoefficient A 3 * n * Real.log n} ∪
        {p | (n : ℝ) ^ (1 - setupExponent A) ≤
          badSetupCount Aset b p (Real.log n / (64 * A ^ 2))}) := measureReal_mono hsub
    _ ≤ _ + _ := measureReal_union_le _ _
    _ ≤ 13 * (n : ℝ) ^ (-setupExponent A) := by linarith

/-- Suspending two distinct entrants leaves an active set of size exactly `n-2`. -/
theorem ordinaryEntrants_near_full {n : ℕ} (u v : Fin n) (huv : u ≠ v) :
    n ≤ (Protocols.ordinaryEntrants u v).card + 2 := by
  have hu := u.isLt
  have hv := v.isLt
  have hval : u.val ≠ v.val := fun hh ↦ huv (Fin.ext hh)
  simp only [Protocols.ordinaryEntrants, Finset.card_erase_of_mem (Finset.mem_erase.mpr
    ⟨Ne.symm huv, Finset.mem_univ v⟩), Finset.card_erase_of_mem (Finset.mem_univ u),
    Finset.card_univ, Fintype.card_fin]
  omega

/-- The exact leave-two-out setup used in the source satisfies uniform quantitative smoothness
under the unchanged PR law. The positive constants are fixed by the public score bounds. -/
theorem eventually_leave_two_smooth_setup {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (a b : Fin n → ℝ≥0),
      (∀ w, 1 ≤ (a w : ℝ)) → (∀ w, (a w : ℝ) ≤ A) →
      (∀ m, 1 ≤ (b m : ℝ)) → (∀ m, (b m : ℝ) ≤ B) →
      ∀ u v : Fin n, u ≠ v →
      ((VisitBounds.profileLaw a b).toMeasure).real {p | ¬(
        (setupTotal (Protocols.ordinaryEntrants u v) p : ℝ) ≤
          RankTail.setupCoefficient A 3 * n * Real.log n ∧
        badSetupCount (Protocols.ordinaryEntrants u v) b p (Real.log n / (64 * A ^ 2)) ≤
          (n : ℝ) ^ (1 - setupExponent A))} ≤ 13 * (n : ℝ) ^ (-setupExponent A) := by
  filter_upwards [eventually_smooth_setup hA hB] with n hn a b ha1 haA hb1 hbB u v huv
  exact hn a b ha1 haA hb1 hbB (Protocols.ordinaryEntrants u v) (ordinaryEntrants_near_full u v huv)

end Ashlagi.SmoothSetup
