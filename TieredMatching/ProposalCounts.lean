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

public import TieredMatching.LabelSymmetry
public import TieredMatching.DestinationMartingale
public import TieredMatching.TierConcentration
public import TieredMatching.SmoothSetup

/-! # Exact raw-to-genuine proposal count comparisons

The actual completed canonical raw trace realizes the original PR proposal relation. Filtering
that trace by proposer subset and destination exposes exactly the local and global repeats.
-/

@[expose] public section

namespace TieredMatching.ProposalCounts

open StableMarriage MeasureTheory
open scoped ENNReal NNReal

/-- Raw multiplicity of edges satisfying a fixed property. -/
noncomputable def rawCount {n : ℕ} (P : Arrival.Edge n → Prop)
    (L : List (Arrival.Edge n)) : ℕ := by
  classical
  exact (L.filter fun q ↦ P q).length

/-- Number of distinct queried edges satisfying that same property. -/
noncomputable def distinctCount {n : ℕ} (P : Arrival.Edge n → Prop)
    (L : List (Arrival.Edge n)) : ℕ := by
  classical
  exact (L.toFinset.filter P).card

/-- Repeated edges satisfying a property, counted in the literal newest-first raw trace. -/
noncomputable def repeatsWhere {n : ℕ} (P : Arrival.Edge n → Prop) :
    List (Arrival.Edge n) → ℕ
  | [] => 0
  | q :: L => by classical exact repeatsWhere P L + if P q ∧ q ∈ L then 1 else 0

/-- Raw filtered multiplicity is exactly its distinct count plus the matching repeats. -/
theorem rawCount_eq_distinct_add_repeats {n : ℕ} (P : Arrival.Edge n → Prop)
    (L : List (Arrival.Edge n)) : rawCount P L = distinctCount P L + repeatsWhere P L := by
  classical
  induction L with
  | nil => simp [rawCount, distinctCount, repeatsWhere]
  | cons q L ih =>
    by_cases hP : P q
    · by_cases hq : q ∈ L
      · have hm : q ∈ L.toFinset.filter P := by simp [hq, hP]
        simp only [rawCount, List.filter_cons, hP, decide_true, ↓reduceIte, List.length_cons,
          distinctCount, List.toFinset_cons, Finset.filter_insert,
          Finset.insert_eq_of_mem hm, repeatsWhere, hq, and_self] at *
        omega
      · have hm : q ∉ L.toFinset.filter P := by simp [hq]
        simp only [rawCount, List.filter_cons, hP, decide_true, ↓reduceIte, List.length_cons,
          distinctCount, List.toFinset_cons, Finset.filter_insert,
          Finset.card_insert_of_notMem hm, repeatsWhere, hq, and_false] at *
        omega
    · simp only [rawCount, List.filter_cons, hP, decide_false, ↓reduceIte,
        distinctCount, List.toFinset_cons, Finset.filter_insert,
        repeatsWhere, false_and, add_zero] at *
      exact ih

/-- Any filtered repeat correction is bounded by the complete repeated-edge count. -/
theorem repeatsWhere_le_total {n : ℕ} (P : Arrival.Edge n → Prop) (L : List (Arrival.Edge n)) :
    repeatsWhere P L ≤ RawSemantics.repeatCount L := by
  classical
  induction L with
  | nil => simp [repeatsWhere, RawSemantics.repeatCount, RawSemantics.distinctCount]
  | cons q L ih =>
    rw [repeatsWhere, RepeatMoments.repeatCount_cons]
    by_cases hq : q ∈ L <;> by_cases hP : P q <;> simp [hq, hP] <;> omega

/-- A filtered repeat correction supported on one woman is bounded by her local repeats. -/
theorem repeatsWhere_le_local {n : ℕ} (P : Arrival.Edge n → Prop) (L : List (Arrival.Edge n))
    (w : Fin n) (hP : ∀ q, P q → q.1 = w) :
    repeatsWhere P L ≤ LabelSymmetry.localRepeats L w := by
  classical
  induction L with
  | nil => rfl
  | cons q L ih =>
    rw [repeatsWhere, LabelSymmetry.localRepeats]
    by_cases hq : q ∈ L <;> by_cases hp : P q <;> simp [hq, hp, hP q] <;> omega

/-- A filtered raw count dominates its distinct count, with a controlled global repeat gap. -/
theorem filtered_count_bounds {n : ℕ} (P : Arrival.Edge n → Prop) (L : List (Arrival.Edge n)) :
    distinctCount P L ≤ rawCount P L ∧
      rawCount P L - distinctCount P L ≤ RawSemantics.repeatCount L := by
  rw [rawCount_eq_distinct_add_repeats]
  exact ⟨Nat.le_add_right _ _, by simpa using repeatsWhere_le_total P L⟩

/-- The same gap for a destination-supported property is controlled by that woman's repeats. -/
theorem filtered_woman_count_bounds {n : ℕ} (P : Arrival.Edge n → Prop)
    (L : List (Arrival.Edge n)) (w : Fin n) (hP : ∀ q, P q → q.1 = w) :
    distinctCount P L ≤ rawCount P L ∧
      rawCount P L - distinctCount P L ≤ LabelSymmetry.localRepeats L w := by
  rw [rawCount_eq_distinct_add_repeats]
  exact ⟨Nat.le_add_right _ _, by simpa using repeatsWhere_le_local P L w hP⟩

/-- Raw subset multiplicity in a revealed history equals its actual consumed-row counters. -/
theorem rawCount_trace_tier {n : ℕ} (J : Finset (Fin n)) (h : List (Raw.Entry n)) :
    rawCount (fun q ↦ q.2 ∈ J) (RawBridge.trace h) = ∑ m ∈ J, Raw.rawCounter h m := by
  classical
  induction h with
  | nil => simp [rawCount, RawBridge.trace, Raw.rawCounter, Raw.drawOrder]
  | cons e h ih =>
    rw [DestinationMartingale.rawCounter_sum_cons]
    cases e with
    | none => simpa [RawBridge.trace, DestinationMartingale.tierValue] using ih
    | some e =>
      rcases e with ⟨q, tag⟩
      by_cases hq : q.2 ∈ J <;>
        simp [RawBridge.trace, rawCount, DestinationMartingale.tierValue, hq,
          rawCount] at * <;> omega

/-- Raw woman/subset multiplicity equals the actual destination counts in the men's raw lists. -/
theorem rawCount_trace_woman {n : ℕ} (J : Finset (Fin n)) (w : Fin n)
    (h : List (Raw.Entry n)) :
    rawCount (fun q ↦ q.2 ∈ J ∧ q.1 = w) (RawBridge.trace h) =
      ∑ m ∈ J, (Raw.drawOrder h m).count w := by
  classical
  induction h with
  | nil => simp [rawCount, RawBridge.trace, Raw.drawOrder]
  | cons e h ih =>
    rw [DestinationMartingale.drawOrder_count_sum_cons]
    cases e with
    | none => simpa [RawBridge.trace, DestinationMartingale.womanValue] using ih
    | some e =>
      rcases e with ⟨q, tag⟩
      by_cases hq : q.2 ∈ J ∧ q.1 = w <;>
        simp [RawBridge.trace, rawCount, DestinationMartingale.womanValue, hq,
          rawCount] at * <;> omega

/-- The literal time-sum tier count equals the corresponding filtered raw trace multiplicity. -/
theorem rawTierCount_eq_trace {n : ℕ} (C : Raw.Protocol n) (J : Finset (Fin n))
    (H : ℕ) (z : Raw.Sources n) :
    DestinationMartingale.rawTierCount C J H z =
      rawCount (fun q ↦ q.2 ∈ J) (RawBridge.trace (Raw.inputTranscript C H z)) := by
  rw [DestinationMartingale.rawTierCount_eq_rawCounter_sum, rawCount_trace_tier]

/-- The literal time-sum woman-tier count equals the filtered raw trace multiplicity. -/
theorem rawWomanTierCount_eq_trace {n : ℕ} (C : Raw.Protocol n) (J : Finset (Fin n))
    (w : Fin n) (H : ℕ) (z : Raw.Sources n) :
    DestinationMartingale.rawWomanTierCount C J w H z =
      rawCount (fun q ↦ q.2 ∈ J ∧ q.1 = w) (RawBridge.trace (Raw.inputTranscript C H z)) := by
  rw [DestinationMartingale.rawWomanTierCount_eq_drawOrder_count_sum, rawCount_trace_woman]

/-- Exact original PR proposal count received by one woman from a fixed men's subset. -/
noncomputable def genuineWomanCount {n : ℕ} (p : Profile n) (J : Finset (Fin n))
    (w : Fin n) : ℕ := by
  classical
  exact (J.filter fun m ↦ HasProposed p (deferredAcceptance p) m w).card

/-- Exact original PR proposal total for a fixed men's subset, in natural count form. -/
noncomputable def genuineTierCount {n : ℕ} (p : Profile n) (J : Finset (Fin n)) : ℕ :=
  ∑ m ∈ J, (deferredAcceptance p).next m

/-- The generic subset woman count is the repository's exact tier proposalCount definition. -/
theorem genuineWomanCount_eq_proposalCount {n k : ℕ} (p : Profile n)
    (manTier : Fin n → Fin k) (j : Fin k) (w : Fin n) :
    genuineWomanCount p (Finset.univ.filter fun m ↦ manTier m = j) w =
      TieredMatching.proposalCount manTier j p w := by
  simp only [genuineWomanCount, TieredMatching.proposalCount, Finset.filter_filter]

/-- The generic natural tier count is exactly the existing real TierConcentration total. -/
theorem genuineTierCount_cast {n : ℕ} (p : Profile n) (J : Finset (Fin n)) :
    (genuineTierCount p J : ℝ) = TierConcentration.tierTotal J p := by
  simp only [genuineTierCount, TierConcentration.tierTotal, RankTail.rank, Nat.cast_sum]

/-- Filtering the exact PR queried relation by one woman recovers her original subset count. -/
theorem distinctCount_woman_eq {n : ℕ} (p : Profile n) (J : Finset (Fin n)) (w : Fin n)
    (L : List (Arrival.Edge n))
    (hL : L.toFinset = Finset.univ.filter (fun q : Arrival.Edge n ↦
      HasProposed p (deferredAcceptance p) q.2 q.1)) :
    distinctCount (fun q ↦ q.2 ∈ J ∧ q.1 = w) L = genuineWomanCount p J w := by
  classical
  unfold distinctCount genuineWomanCount
  rw [hL]
  apply Finset.card_bij (fun q _ ↦ q.2)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact ⟨hq.2.1, hq.2.2 ▸ hq.1⟩
  · intro q hq v hv heq
    simp only [Finset.mem_filter] at hq hv
    exact Prod.ext (hq.2.2.trans hv.2.2.symm) heq
  · intro m hm
    refine ⟨(w, m), ?_, rfl⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, and_true] using
      And.intro (Finset.mem_filter.mp hm).2 (Finset.mem_filter.mp hm).1

/-- Filtering the exact PR queried relation by men recovers their terminal counter total. -/
theorem distinctCount_tier_eq {n : ℕ} (p : Profile n) (J : Finset (Fin n))
    (L : List (Arrival.Edge n))
    (hL : L.toFinset = Finset.univ.filter (fun q : Arrival.Edge n ↦
      HasProposed p (deferredAcceptance p) q.2 q.1)) :
    distinctCount (fun q ↦ q.2 ∈ J) L = genuineTierCount p J := by
  classical
  rw [distinctCount, hL]
  simp only [Finset.filter_filter, Finset.card_filter, Fintype.sum_prod_type, genuineTierCount]
  rw [Finset.sum_comm]
  calc
    _ = ∑ m : Fin n, if m ∈ J then (deferredAcceptance p).next m else 0 := by
      apply Finset.sum_congr rfl
      intro m _
      by_cases hm : m ∈ J
      · simp only [hm, and_true, ite_true]
        simpa only [Finset.card_filter] using proposed_prefix_card p m
      · simp only [hm, and_false, ite_false, Finset.sum_const_zero]
    _ = _ := by rw [← Finset.sum_filter]; simp

/-- At the actual raw completion clock the queried relation is exactly the original PR relation,
the canonical process has paused, and the repeat correction is the actual completed-run total. -/
theorem ae_completed_spec {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) :
    ∀ᵐ z ∂LabelSymmetry.sourceLaw a b,
      (LabelSymmetry.completedTrace z).toFinset =
        Finset.univ.filter (fun q : Arrival.Edge n ↦ HasProposed (RawBridge.sourceProfile z)
          (deferredAcceptance (RawBridge.sourceProfile z)) q.2 q.1) ∧
      Raw.selected (GlobalDraws.activeProtocol Finset.univ)
        (Raw.inputTranscript (GlobalDraws.activeProtocol Finset.univ) (GlobalDraws.rawClock z) z) =
          none ∧
      RawSemantics.repeatCount (LabelSymmetry.completedTrace z) = RepeatMoments.totalRepeats z := by
  filter_upwards [RawBridge.ae_transcript_bridge (fun _ ↦ a) (fun m _ ↦ b m)
    (fun _ w ↦ ha w) (fun m _ ↦ hb m) (GlobalDraws.activeProtocol Finset.univ) Finset.univ
      (RawBridge.supports_univ _),
    RawBridge.ae_source_orders (fun _ ↦ a) (fun m _ ↦ b m) (fun _ ↦ ha),
    RawBridge.ae_source_female_injective (fun _ ↦ a) (fun m _ ↦ b m) (fun m _ ↦ hb m),
    GlobalDraws.ae_sourceTape_completes (GlobalDraws.activeProtocol Finset.univ)
      (GlobalDraws.activeProtocol_pauseStable Finset.univ) a (fun m _ ↦ b m) ha
        (fun m _ ↦ hb m),
    GlobalDraws.ae_rawClock_decomposition a (fun m _ ↦ b m) ha (fun m _ ↦ hb m)]
    with z hbridge horders hfemale hcomplete hdecomp
  have ht := (GlobalDraws.terminal_iff_tape_covers (RawBridge.sourceFemale z)
    (Function.uncurry z.1) (RawBridge.sourceProfile z) horders
    (fun w m old ↦ exponentialRank_lt_iff (z.2 w) (hfemale w) m old)
      (GlobalDraws.rawClock z)).mpr (CouponMoments.covers_time hcomplete)
  have hbr := hbridge (GlobalDraws.rawClock z)
  have hr : RawSemantics.replay (RawBridge.sourceProfile z) (LabelSymmetry.completedTrace z) =
      deferredAcceptance (RawBridge.sourceProfile z) := by
    apply Schedules.terminal_state_eq_pr _ (RawSemantics.replay_reachable _ _ hbr.1)
    rw [← hbr.2]
    exact ht
  have hrel := RawSemantics.toFinset_eq_proposedPairs _ _ hbr.1
  change (LabelSymmetry.completedTrace z).toFinset = Finset.univ.filter
    (fun q : Arrival.Edge n ↦ HasProposed (RawBridge.sourceProfile z)
      (RawSemantics.replay (RawBridge.sourceProfile z) (LabelSymmetry.completedTrace z)) q.2 q.1)
    at hrel
  rw [hr] at hrel
  refine ⟨hrel, (GlobalDraws.activeProtocol_none_iff_terminal Finset.univ _).mpr ht, ?_⟩
  change GlobalDraws.rawClock z = numProposals (RawBridge.sourceProfile z) +
    RawSemantics.repeatCount (LabelSymmetry.completedTrace z) at hdecomp
  unfold RepeatMoments.totalRepeats
  omega

/-- At actual completion the raw woman-tier and tier counts dominate exact PR counts, and their
natural differences are bounded by the actual local and total repeat corrections. -/
theorem ae_completed_count_bounds {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) :
    ∀ᵐ z ∂LabelSymmetry.sourceLaw a b, ∀ (J : Finset (Fin n)) (w : Fin n),
      (genuineWomanCount (RawBridge.sourceProfile z) J w ≤
        DestinationMartingale.rawWomanTierCount (GlobalDraws.activeProtocol Finset.univ)
          J w (GlobalDraws.rawClock z) z ∧
      DestinationMartingale.rawWomanTierCount (GlobalDraws.activeProtocol Finset.univ)
        J w (GlobalDraws.rawClock z) z - genuineWomanCount (RawBridge.sourceProfile z) J w ≤
          LabelSymmetry.repeatAtWoman z w) ∧
      (genuineTierCount (RawBridge.sourceProfile z) J ≤
        DestinationMartingale.rawTierCount (GlobalDraws.activeProtocol Finset.univ)
          J (GlobalDraws.rawClock z) z ∧
      DestinationMartingale.rawTierCount (GlobalDraws.activeProtocol Finset.univ)
        J (GlobalDraws.rawClock z) z - genuineTierCount (RawBridge.sourceProfile z) J ≤
          RepeatMoments.totalRepeats z) := by
  filter_upwards [ae_completed_spec a b ha hb] with z hz
  intro J w
  have hw := filtered_woman_count_bounds (fun q : Arrival.Edge n ↦ q.2 ∈ J ∧ q.1 = w)
    (LabelSymmetry.completedTrace z) w (fun _ hq ↦ hq.2)
  have ht := filtered_count_bounds (fun q : Arrival.Edge n ↦ q.2 ∈ J)
    (LabelSymmetry.completedTrace z)
  rw [distinctCount_woman_eq _ J w _ hz.1] at hw
  rw [distinctCount_tier_eq _ J _ hz.1, hz.2.2] at ht
  have hrw := rawWomanTierCount_eq_trace (GlobalDraws.activeProtocol Finset.univ) J w
    (GlobalDraws.rawClock z) z
  have hrt := rawTierCount_eq_trace (GlobalDraws.activeProtocol Finset.univ) J
    (GlobalDraws.rawClock z) z
  change DestinationMartingale.rawWomanTierCount _ _ _ _ _ =
    rawCount _ (LabelSymmetry.completedTrace z) at hrw
  change DestinationMartingale.rawTierCount _ _ _ _ =
    rawCount _ (LabelSymmetry.completedTrace z) at hrt
  rw [← hrw] at hw
  rw [← hrt] at ht
  exact ⟨hw, ht⟩

/-- Every statistic ignoring pause records freezes after an absorbing actual protocol pause. -/
theorem statistic_freeze {n : ℕ} {α : Type*} (C : Raw.Protocol n)
    (hs : GlobalDraws.PauseStable C) (F : List (Raw.Entry n) → α)
    (hF : ∀ h, F (none :: h) = F h) (z : Raw.Sources n) {s t : ℕ} (hst : s ≤ t)
    (hstart : Raw.selected C (Raw.inputTranscript C s z) = none) :
    F (Raw.inputTranscript C t z) = F (Raw.inputTranscript C s z) := by
  induction t, hst using Nat.le_induction with
  | base => rfl
  | succ t hst ih =>
    have hpause := SmoothSetup.selected_none_mono C hs z.1 (Function.uncurry z.2) hst hstart
    change Raw.selected C (Raw.inputTranscript C t z) = none at hpause
    have ho : Raw.observation C z.1 (Function.uncurry z.2) (Raw.inputTranscript C t z) = none := by
      simp only [Raw.observation, Raw.nextEdge, hpause, Option.map_none]
    change F (Raw.observation C z.1 (Function.uncurry z.2) (Raw.inputTranscript C t z) ::
      Raw.inputTranscript C t z) = _
    rw [ho, hF, ih]

/-- Actual raw counters freeze at every deterministic horizon after completion; all raw tier
and woman-tier time sums freeze at that same clock. -/
theorem ae_counts_freeze {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) :
    ∀ᵐ z ∂LabelSymmetry.sourceLaw a b, ∀ H, GlobalDraws.rawClock z ≤ H →
      (∀ m, Raw.rawCounter
        (Raw.inputTranscript (GlobalDraws.activeProtocol Finset.univ) H z) m =
          Raw.rawCounter (Raw.inputTranscript (GlobalDraws.activeProtocol Finset.univ)
            (GlobalDraws.rawClock z) z) m) ∧
      ∀ (J : Finset (Fin n)) (w : Fin n),
        DestinationMartingale.rawTierCount (GlobalDraws.activeProtocol Finset.univ) J H z =
          DestinationMartingale.rawTierCount (GlobalDraws.activeProtocol Finset.univ)
            J (GlobalDraws.rawClock z) z ∧
        DestinationMartingale.rawWomanTierCount (GlobalDraws.activeProtocol Finset.univ) J w H z =
          DestinationMartingale.rawWomanTierCount (GlobalDraws.activeProtocol Finset.univ)
            J w (GlobalDraws.rawClock z) z := by
  filter_upwards [ae_completed_spec a b ha hb] with z hz
  intro H hH
  have htrace := statistic_freeze (GlobalDraws.activeProtocol Finset.univ)
    (GlobalDraws.activeProtocol_pauseStable Finset.univ) RawBridge.trace (fun _ ↦ rfl)
      z hH hz.2.1
  constructor
  · intro m
    exact statistic_freeze (GlobalDraws.activeProtocol Finset.univ)
      (GlobalDraws.activeProtocol_pauseStable Finset.univ) (fun h ↦ Raw.rawCounter h m)
        (fun _ ↦ rfl) z hH hz.2.1
  · intro J w
    constructor
    · rw [rawTierCount_eq_trace, rawTierCount_eq_trace, htrace]
    · rw [rawWomanTierCount_eq_trace, rawWomanTierCount_eq_trace, htrace]

/-- A deterministic algebraic transfer from raw destination deviations to genuine deviations. -/
theorem abs_deviation_transfer {S U X Y Rw R q : ℝ} (hq : 0 ≤ q)
    (hW : S ≤ X) (hW' : X ≤ S + Rw) (hT : U ≤ Y) (hT' : Y ≤ U + R) :
    |S - q * U| ≤ |X - q * Y| + Rw + q * R := by
  have hw : |S - X| ≤ Rw := by rw [abs_of_nonpos (by linarith)]; linarith
  have ht : |q * (Y - U)| ≤ q * R := by
    rw [abs_of_nonneg (mul_nonneg hq (by linarith))]
    exact mul_le_mul_of_nonneg_left (by linarith) hq
  calc
    _ = |((X - q * Y) + (S - X)) + q * (Y - U)| := by congr 1; ring
    _ ≤ |(X - q * Y) + (S - X)| + |q * (Y - U)| := abs_add_le _ _
    _ ≤ (|X - q * Y| + |S - X|) + |q * (Y - U)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by linarith

/-- On the actual raw-clock good event, a deterministic-horizon raw deviation controls the
exact original PR woman-tier deviation with local repeat plus pi times total repeat noise. -/
theorem ae_deviation_transfer {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (H : ℕ) :
    ∀ᵐ z ∂LabelSymmetry.sourceLaw a b, GlobalDraws.rawClock z ≤ H →
      ∀ (J : Finset (Fin n)) (w : Fin n) (q : ℝ), 0 ≤ q →
        |(genuineWomanCount (RawBridge.sourceProfile z) J w : ℝ) -
          q * TierConcentration.tierTotal J (RawBridge.sourceProfile z)| ≤
        |(DestinationMartingale.rawWomanTierCount (GlobalDraws.activeProtocol Finset.univ)
          J w H z : ℝ) - q * DestinationMartingale.rawTierCount
            (GlobalDraws.activeProtocol Finset.univ) J H z| +
          (LabelSymmetry.repeatAtWoman z w : ℝ) + q * RepeatMoments.totalRepeats z := by
  filter_upwards [ae_completed_count_bounds a b ha hb, ae_counts_freeze a b ha hb]
    with z hcounts hfreeze
  intro hH J w q hq
  have hc := hcounts J w
  have hf := (hfreeze H hH).2 J w
  rw [← hf.2] at hc
  rw [← hf.1] at hc
  have hW : (genuineWomanCount (RawBridge.sourceProfile z) J w : ℝ) ≤
      DestinationMartingale.rawWomanTierCount (GlobalDraws.activeProtocol Finset.univ) J w H z := by
    exact_mod_cast hc.1.1
  have hW' : (DestinationMartingale.rawWomanTierCount (GlobalDraws.activeProtocol Finset.univ)
      J w H z : ℝ) ≤ (genuineWomanCount (RawBridge.sourceProfile z) J w : ℝ) +
        LabelSymmetry.repeatAtWoman z w := by
    exact_mod_cast (show DestinationMartingale.rawWomanTierCount
      (GlobalDraws.activeProtocol Finset.univ) J w H z ≤
        genuineWomanCount (RawBridge.sourceProfile z) J w +
          LabelSymmetry.repeatAtWoman z w by omega)
  have hT : (genuineTierCount (RawBridge.sourceProfile z) J : ℝ) ≤
      DestinationMartingale.rawTierCount (GlobalDraws.activeProtocol Finset.univ) J H z := by
    exact_mod_cast hc.2.1
  have hT' : (DestinationMartingale.rawTierCount
      (GlobalDraws.activeProtocol Finset.univ) J H z : ℝ) ≤
      (genuineTierCount (RawBridge.sourceProfile z) J : ℝ) + RepeatMoments.totalRepeats z := by
    exact_mod_cast (show DestinationMartingale.rawTierCount
      (GlobalDraws.activeProtocol Finset.univ) J H z ≤
        genuineTierCount (RawBridge.sourceProfile z) J + RepeatMoments.totalRepeats z by omega)
  rw [genuineTierCount_cast] at hT hT'
  exact abs_deviation_transfer hq hW hW' hT hT'

/-- The exact public-tier proposalCount API satisfies the actual raw-count deviation transfer. -/
theorem ae_proposalCount_deviation_transfer {n k : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (manTier : Fin n → Fin k)
    (j : Fin k) (w : Fin n) (H : ℕ) :
    ∀ᵐ z ∂LabelSymmetry.sourceLaw a b, GlobalDraws.rawClock z ≤ H →
      |(TieredMatching.proposalCount manTier j (RawBridge.sourceProfile z) w : ℝ) -
        DestinationMartingale.destinationProbability a w * TierConcentration.tierTotal
          (Finset.univ.filter fun m ↦ manTier m = j) (RawBridge.sourceProfile z)| ≤
      |(DestinationMartingale.rawWomanTierCount (GlobalDraws.activeProtocol Finset.univ)
        (Finset.univ.filter fun m ↦ manTier m = j) w H z : ℝ) -
        DestinationMartingale.destinationProbability a w * DestinationMartingale.rawTierCount
          (GlobalDraws.activeProtocol Finset.univ)
            (Finset.univ.filter fun m ↦ manTier m = j) H z| +
        (LabelSymmetry.repeatAtWoman z w : ℝ) +
          DestinationMartingale.destinationProbability a w * RepeatMoments.totalRepeats z := by
  filter_upwards [ae_deviation_transfer a b ha hb H] with z hz
  intro hH
  have ht := hz hH (Finset.univ.filter fun m ↦ manTier m = j) w
    (DestinationMartingale.destinationProbability a w)
    (DestinationMartingale.destinationProbability_mem_Icc a w).1
  simpa only [genuineWomanCount_eq_proposalCount] using ht

end TieredMatching.ProposalCounts
