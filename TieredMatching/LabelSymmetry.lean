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

public import TieredMatching.RepeatMoments
public import TieredMatching.AdaptiveExposure

/-! # Actual within-score-class symmetry of completed-run repeats

Women are relabeled in every raw stream and priority row of the original independent source.
The actual canonical DA transcript and its raw completion clock transform under the same map.
-/

@[expose] public section

namespace TieredMatching.LabelSymmetry

open StableMarriage MeasureTheory
open scoped ENNReal NNReal

/-- Relabel only the woman coordinate of an edge. -/
def edgePerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Arrival.Edge n) :=
  σ.prodCongr (Equiv.refl _)

/-- Relabel the destination of an ordinary revealed record, preserving its acceptance bit. -/
def ordinalEntry {n : ℕ} (σ : Equiv.Perm (Fin n)) (e : Ordinal.Entry n) : Ordinal.Entry n :=
  e.map fun v ↦ (edgePerm σ v.1, v.2)

/-- Relabel the destination of a raw record, preserving repeat and acceptance tags. -/
def rawEntry {n : ℕ} (σ : Equiv.Perm (Fin n)) (e : Raw.Entry n) : Raw.Entry n :=
  e.map fun v ↦ (edgePerm σ v.1, v.2)

/-- Relabel every visible raw record. -/
def rawHistory {n : ℕ} (σ : Equiv.Perm (Fin n)) (h : List (Raw.Entry n)) :=
  h.map (rawEntry σ)

/-- Proposal counters retain their man labels; holdings move with woman labels. -/
def statePerm {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : ProposalState n) : ProposalState n :=
  ⟨s.next, fun w ↦ s.held (σ.symm w)⟩

/-- Visible coordinate updates commute with a permutation of their coordinate labels. -/
theorem update_perm {n : ℕ} {α : Type*} (σ : Equiv.Perm (Fin n))
    (f : Fin n → α) (w : Fin n) (v : α) :
    Function.update (fun k ↦ f (σ.symm k)) (σ w) v =
      fun k ↦ Function.update f w v (σ.symm k) := by
  funext k
  have he : σ.symm k = w ↔ k = σ w := by
    constructor
    · intro h
      simpa using congrArg σ h
    · intro h
      simp [h]
  simp only [Function.update_apply, he]

/-- One revealed ordinal update commutes exactly with the label permutation. -/
theorem recordStep_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : ProposalState n)
    (e : Ordinal.Entry n) :
    Ordinal.recordStep (statePerm σ s) (ordinalEntry σ e) =
      statePerm σ (Ordinal.recordStep s e) := by
  cases e with
  | none => rfl
  | some e =>
    rcases e with ⟨⟨w, m⟩, accepted⟩
    cases accepted with
    | false => rfl
    | true =>
      change ProposalState.mk _ (Function.update (fun k ↦ s.held (σ.symm k)) (σ w) (some m)) =
        ProposalState.mk _ (fun k ↦ Function.update s.held w (some m) (σ.symm k))
      rw [update_perm]
      rfl

/-- Repeat erasure respects the same destination relabeling. -/
theorem ordinary_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (h : List (Raw.Entry n)) :
    Raw.ordinary (rawHistory σ h) = (Raw.ordinary h).map (ordinalEntry σ) := by
  induction h with
  | nil => rfl
  | cons e h ih =>
    simp only [rawHistory, Raw.ordinary, List.map_cons] at *
    rw [ih]
    congr 1
    cases e with
    | none => rfl
    | some e =>
      rcases e with ⟨q, tag⟩
      cases tag <;> rfl

/-- The replayed ordinary state is conjugate under woman-label permutations. -/
theorem recordState_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (h : List (Ordinal.Entry n)) :
    Ordinal.recordState (h.map (ordinalEntry σ)) = statePerm σ (Ordinal.recordState h) := by
  induction h with
  | nil => rfl
  | cons e h ih =>
    rw [List.map_cons, Ordinal.recordState, ih, recordStep_perm]
    rfl

/-- Raw replay counters and holdings transform under the same visible relabeling. -/
theorem raw_state_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (h : List (Raw.Entry n)) :
    Raw.state (rawHistory σ h) = statePerm σ (Raw.state h) := by
  rw [Raw.state, ordinary_perm, recordState_perm]
  rfl

/-- The canonical first-free-man choice does not depend on woman labels. -/
theorem chooseFrom_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (L : List (Fin n)) (s : ProposalState n) :
    Protocols.chooseFrom A L (statePerm σ s) = Protocols.chooseFrom A L s := by
  have hfree (m : Fin n) : (∀ w, s.held (σ.symm w) ≠ some m) ↔
      ∀ w, s.held w ≠ some m := by
    constructor
    · intro h w
      simpa using h (σ w)
    · intro h w
      exact h (σ.symm w)
  simp only [Protocols.chooseFrom, statePerm, hfree]

/-- Actual sanitized proposer selection is invariant under relabeling women. -/
theorem selected_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (h : List (Raw.Entry n)) :
    Raw.selected (GlobalDraws.activeProtocol A) (rawHistory σ h) =
      Raw.selected (GlobalDraws.activeProtocol A) h := by
  rw [GlobalDraws.selected_activeProtocol, raw_state_perm, chooseFrom_perm,
    GlobalDraws.selected_activeProtocol]

/-- Seen genuine edges move bijectively with their woman labels. -/
theorem ordinal_seen_perm {n : ℕ} (σ : Equiv.Perm (Fin n))
    (h : List (Ordinal.Entry n)) :
    Ordinal.seenEdges (h.map (ordinalEntry σ)) = (Ordinal.seenEdges h).image (edgePerm σ) := by
  classical
  induction h with
  | nil => simp [Ordinal.seenEdges]
  | cons e h ih =>
    cases e with
    | none => exact ih
    | some e =>
      rcases e with ⟨q, accepted⟩
      simpa only [List.map_cons, ordinalEntry, Option.map_some, Ordinal.seenEdges,
        Finset.image_insert] using congrArg (insert (edgePerm σ q)) ih

/-- Every seen-edge membership test is unchanged after relabeling its edge and history. -/
theorem raw_seen_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (h : List (Raw.Entry n))
    (q : Arrival.Edge n) :
    edgePerm σ q ∈ Raw.seenEdges (rawHistory σ h) ↔ q ∈ Raw.seenEdges h := by
  classical
  rw [Raw.seenEdges, ordinary_perm, ordinal_seen_perm]
  constructor
  · intro hq
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hq
    exact (edgePerm σ).injective heq ▸ he
  · intro hq
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩

/-- Each man's chronological raw list is relabeled coordinatewise. -/
theorem drawOrder_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (h : List (Raw.Entry n)) (m : Fin n) :
    Raw.drawOrder (rawHistory σ h) m = (Raw.drawOrder h m).map σ := by
  induction h with
  | nil => rfl
  | cons e h ih =>
    cases e with
    | none => exact ih
    | some e =>
      simp only [rawHistory] at ih
      rcases e with ⟨⟨w, k⟩, tag⟩
      simp only [rawHistory, List.map_cons, rawEntry, Option.map_some, Raw.drawOrder,
        edgePerm, Equiv.prodCongr_apply]
      by_cases hkm : k = m <;> simp [hkm, ih, List.map_append]

/-- Raw row-consumption counters retain exactly their original values. -/
theorem rawCounter_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (h : List (Raw.Entry n)) (m : Fin n) :
    Raw.rawCounter (rawHistory σ h) m = Raw.rawCounter h m := by
  simp only [Raw.rawCounter, drawOrder_perm, List.length_map]

/-- Relabel the independent female-priority rows. -/
def femalePerm {n : ℕ} (σ : Equiv.Perm (Fin n)) (female : Arrival.Edge n → ℝ) :
    Arrival.Edge n → ℝ := fun q ↦ female (σ.symm q.1, q.2)

/-- The exact acceptance comparison is invariant when both state and priority rows move. -/
theorem accept_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (female : Arrival.Edge n → ℝ)
    (s : ProposalState n) (q : Arrival.Edge n) :
    Ordinal.accept (femalePerm σ female) (statePerm σ s) (edgePerm σ q) =
      Ordinal.accept female s q := by
  rcases q with ⟨w, m⟩
  simp [Ordinal.accept, femalePerm, statePerm, edgePerm]

/-- Raw classification and acceptance commute with relabeling the original sources. -/
theorem observation_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (streams : Fin n → ℕ → Fin n) (female : Arrival.Edge n → ℝ) (h : List (Raw.Entry n)) :
    Raw.observation (GlobalDraws.activeProtocol A) (fun m t ↦ σ (streams m t))
      (femalePerm σ female) (rawHistory σ h) =
        rawEntry σ (Raw.observation (GlobalDraws.activeProtocol A) streams female h) := by
  classical
  simp only [Raw.observation, Raw.nextEdge, selected_perm]
  cases hs : Raw.selected (GlobalDraws.activeProtocol A) h with
  | none => rfl
  | some m =>
    simp only [Option.map_some, rawCounter_perm]
    let q := (streams m (Raw.rawCounter h m), m)
    change some (edgePerm σ q, if edgePerm σ q ∈ Raw.seenEdges (rawHistory σ h) then none
      else some (Ordinal.accept (femalePerm σ female) (Raw.state (rawHistory σ h))
        (edgePerm σ q))) = rawEntry σ
          (some (q, if q ∈ Raw.seenEdges h then none else some (Ordinal.accept female
            (Raw.state h) q)))
    simp only [raw_seen_perm, raw_state_perm, accept_perm, rawEntry, Option.map_some]

/-- The entire actual canonical raw transcript transforms record by record. -/
theorem transcript_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (streams : Fin n → ℕ → Fin n) (female : Arrival.Edge n → ℝ) (t : ℕ) :
    Raw.transcript (GlobalDraws.activeProtocol A) (fun m k ↦ σ (streams m k))
      (femalePerm σ female) t =
        rawHistory σ (Raw.transcript (GlobalDraws.activeProtocol A) streams female t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [Raw.transcript, ih]
    change _ = rawEntry σ (Raw.observation (GlobalDraws.activeProtocol A) streams female
      (Raw.transcript (GlobalDraws.activeProtocol A) streams female t)) ::
        rawHistory σ (Raw.transcript (GlobalDraws.activeProtocol A) streams female t)
    rw [observation_perm]

/-- A supplied global destination has the same covariant raw response. -/
theorem respond_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (female : Arrival.Edge n → ℝ) (h : List (Raw.Entry n)) (w : Fin n) :
    GlobalDraws.respond (GlobalDraws.activeProtocol A) (femalePerm σ female)
      (rawHistory σ h) (σ w) =
        rawEntry σ (GlobalDraws.respond (GlobalDraws.activeProtocol A) female h w) := by
  classical
  simp only [GlobalDraws.respond, selected_perm]
  cases hs : Raw.selected (GlobalDraws.activeProtocol A) h with
  | none => rfl
  | some m =>
    simp only [Option.map_some]
    change some (edgePerm σ (w, m), if edgePerm σ (w, m) ∈ Raw.seenEdges (rawHistory σ h)
      then none else some (Ordinal.accept (femalePerm σ female) (Raw.state (rawHistory σ h))
        (edgePerm σ (w, m)))) = rawEntry σ
          (some ((w, m), if (w, m) ∈ Raw.seenEdges h then none else some (Ordinal.accept female
            (Raw.state h) (w, m))))
    simp only [raw_seen_perm, raw_state_perm, accept_perm, rawEntry, Option.map_some]

/-- Global-word replay is equivariant before and after the absorbing canonical pause. -/
theorem replayValues_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (female : Arrival.Edge n → ℝ) (L : List (Fin n)) :
    GlobalDraws.replayValues (GlobalDraws.activeProtocol A) (femalePerm σ female) (L.map σ) =
      rawHistory σ (GlobalDraws.replayValues (GlobalDraws.activeProtocol A) female L) := by
  induction L with
  | nil => rfl
  | cons w L ih =>
    simp only [List.map_cons, GlobalDraws.replayValues, ih]
    change _ = rawEntry σ (GlobalDraws.respond (GlobalDraws.activeProtocol A) female
      (GlobalDraws.replayValues (GlobalDraws.activeProtocol A) female L) w) ::
        rawHistory σ (GlobalDraws.replayValues (GlobalDraws.activeProtocol A) female L)
    rw [respond_perm]

/-- Query keys retain their man and slot; only the observed woman value changes. -/
def queryEntry {n : ℕ} (σ : Equiv.Perm (Fin n)) (e : ((Fin n × ℕ) × Fin n)) :=
  (e.1, σ e.2)

/-- Relabeling observations leaves every raw row-slot count unchanged, including dummy reads. -/
theorem slotCount_perm {n : ℕ} (σ : Equiv.Perm (Fin n))
    (h : List ((Fin n × ℕ) × Fin n)) (m : Fin n) :
    AdaptiveSampling.slotCount (h.map (queryEntry σ)) m = AdaptiveSampling.slotCount h m := by
  induction h with
  | nil => rfl
  | cons e h ih =>
    rcases e with ⟨q, w⟩
    simp only [List.map_cons, queryEntry, AdaptiveSampling.slotCount_cons]
    rw [ih]

/-- The visible raw replay of a relabeled adaptive query history has the same covariance. -/
theorem replayQueries_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (female : Arrival.Edge n → ℝ) (h : List ((Fin n × ℕ) × Fin n)) :
    GlobalDraws.replayQueries (GlobalDraws.activeProtocol A) (femalePerm σ female)
      (h.map (queryEntry σ)) =
        rawHistory σ (GlobalDraws.replayQueries (GlobalDraws.activeProtocol A) female h) := by
  have hm : (h.map (queryEntry σ)).map Prod.snd = (h.map Prod.snd).map σ := by
    simp only [List.map_map, Function.comp_def, queryEntry]
  simp only [GlobalDraws.replayQueries, hm]
  exact replayValues_perm σ A female _

/-- The adaptive query chooses the same man and slot under woman relabeling. -/
theorem query_perm {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (female : Arrival.Edge n → ℝ) (h : List ((Fin n × ℕ) × Fin n)) :
    GlobalDraws.query (GlobalDraws.activeProtocol A) (femalePerm σ female)
      (h.map (queryEntry σ)) = GlobalDraws.query (GlobalDraws.activeProtocol A) female h := by
  have hc : GlobalDraws.choose (GlobalDraws.activeProtocol A) (femalePerm σ female)
      (h.map (queryEntry σ)) = GlobalDraws.choose (GlobalDraws.activeProtocol A) female h := by
    simp only [GlobalDraws.choose, replayQueries_perm, selected_perm]
  simp only [GlobalDraws.query, AdaptiveSampling.slotPolicy, hc, slotCount_perm]

/-- Every adaptive globally supplied raw value is relabeled without altering its query key. -/
theorem queryHistory_perm {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (female : Arrival.Edge n → ℝ) (x : (Fin n × ℕ) → Fin n) (t : ℕ) :
    queryHistory (GlobalDraws.query (GlobalDraws.activeProtocol A) (femalePerm σ female))
      (fun q ↦ σ (x q)) t =
        (queryHistory (GlobalDraws.query (GlobalDraws.activeProtocol A) female) x t).map
          (queryEntry σ) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [queryHistory, ih, query_perm, List.map_cons, queryEntry]

/-- The complete iid tape, including independent reads after completion, is relabeled exactly. -/
theorem tape_perm {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (female : Arrival.Edge n → ℝ) (x : (Fin n × ℕ) → Fin n) :
    GlobalDraws.tape (GlobalDraws.activeProtocol A) (femalePerm σ female) (fun q ↦ σ (x q)) =
      fun t ↦ σ (GlobalDraws.tape (GlobalDraws.activeProtocol A) female x t) := by
  funext t
  simp only [GlobalDraws.tape, AdaptiveSampling.observationStream, queryHistory_perm, query_perm]

/-- Relabeling the entire original source keeps all man labels and exponential row coordinates. -/
def sourcePerm {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : Raw.Sources n) : Raw.Sources n :=
  (fun m t ↦ σ (z.1 m t), fun w m ↦ z.2 (σ.symm w) m)

/-- The actual global source tape transforms coordinatewise. -/
theorem sourceTape_perm {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (z : Raw.Sources n) :
    GlobalDraws.sourceTape (GlobalDraws.activeProtocol A) (sourcePerm σ z) =
      fun t ↦ σ (GlobalDraws.sourceTape (GlobalDraws.activeProtocol A) z t) :=
  tape_perm σ A (RawBridge.sourceFemale z) (Function.uncurry z.1)

/-- Covering every woman is invariant under a bijection of her label set. -/
theorem covers_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : ℕ → Fin n) (t : ℕ) :
    CouponMoments.covers (fun j ↦ σ (x j)) t ↔ CouponMoments.covers x t := by
  constructor
  · intro h w
    obtain ⟨j, hj, he⟩ := h (σ w)
    exact ⟨j, hj, σ.injective he⟩
  · intro h w
    obtain ⟨j, hj, he⟩ := h (σ.symm w)
    exact ⟨j, hj, by simp [he]⟩

/-- The actual coupon completion time is unchanged by destination relabeling. -/
theorem couponTime_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : ℕ → Fin n) :
    CouponMoments.time (fun j ↦ σ (x j)) = CouponMoments.time x := by
  classical
  have hc : CouponMoments.completes (fun j ↦ σ (x j)) ↔ CouponMoments.completes x := by
    simp only [CouponMoments.completes, covers_perm]
  by_cases hx : CouponMoments.completes x
  · have hy := hc.mpr hx
    apply Nat.le_antisymm
    · apply (CouponMoments.time_le_iff hy _).mpr
      exact (covers_perm σ x _).mpr (CouponMoments.covers_time hx)
    · apply (CouponMoments.time_le_iff hx _).mpr
      exact (covers_perm σ x _).mp (CouponMoments.covers_time hy)
  · simp only [CouponMoments.time, dite_eq_right hx, dite_eq_right (mt hc.mp hx)]

/-- The actual completed-run raw clock is invariant under the whole-source relabeling. -/
theorem rawClock_perm {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) (z : Raw.Sources n) :
    GlobalDraws.rawClock (sourcePerm σ z) = GlobalDraws.rawClock z := by
  rw [GlobalDraws.rawClock, sourceTape_perm, couponTime_perm]
  rfl

/-- Relabeling the destination space preserves a categorical law with invariant public scores. -/
theorem categorical_perm {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n))
    (a : Fin n → ℝ≥0) (ha : ∀ w, 0 < a w) (hσ : ∀ w, a (σ w) = a w) :
    (RandomRanking.ofWeights a).map σ = RandomRanking.ofWeights a := by
  classical
  have hsum : ∑ w, a w ≠ 0 := ne_of_gt (Finset.sum_pos (fun w _ ↦ ha w)
    Finset.univ_nonempty)
  ext w
  have he (v : Fin n) : w = σ v ↔ v = σ.symm w := by
    constructor
    · intro h
      simpa using (congrArg σ.symm h).symm
    · intro h
      simp [h]
  simp only [PMF.map_apply, tsum_fintype, he]
  rw [Finset.sum_eq_single (σ.symm w)]
  · simp only [ite_true]
    rw [RandomRanking.ofWeights_apply a hsum, RandomRanking.ofWeights_apply a hsum]
    have hw : a (σ.symm w) = a w := by simpa using (hσ (σ.symm w)).symm
    rw [hw]
  · intro v _ hv
    simp [hv]
  · simp

/-- The relabeling preserves the one-destination categorical probability measure. -/
theorem categorical_measurePreserving {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n))
    (a : Fin n → ℝ≥0) (ha : ∀ w, 0 < a w) (hσ : ∀ w, a (σ w) = a w) :
    MeasurePreserving σ (RandomRanking.ofWeights a).toMeasure
      (RandomRanking.ofWeights a).toMeasure := by
  refine ⟨measurable_of_countable _, ?_⟩
  rw [PMF.toMeasure_map σ _ (measurable_of_countable _), categorical_perm σ a ha hσ]

/-- Relabeling all values of a raw iid row preserves its full infinite product law. -/
theorem stream_measurePreserving {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n))
    (a : Fin n → ℝ≥0) (ha : ∀ w, 0 < a w) (hσ : ∀ w, a (σ w) = a w) :
    MeasurePreserving (fun x : ℕ → Fin n ↦ fun t ↦ σ (x t))
      (FirstFresh.iidStream (RandomRanking.ofWeights a))
      (FirstFresh.iidStream (RandomRanking.ofWeights a)) := by
  have hp := categorical_measurePreserving σ a ha hσ
  refine ⟨by fun_prop, ?_⟩
  change Measure.map _
    (Measure.infinitePi fun _ : ℕ ↦ (RandomRanking.ofWeights a).toMeasure) = _
  rw [Measure.infinitePi_map_pi (fun _ : ℕ ↦ (RandomRanking.ofWeights a).toMeasure)
    (fun _ ↦ hp.measurable)]
  simp_rw [hp.map_eq]
  rfl

/-- The whole original source relabeling is a measurable bijection. -/
def sourceEquiv {n : ℕ} (σ : Equiv.Perm (Fin n)) : Raw.Sources n ≃ᵐ Raw.Sources n where
  toEquiv :=
    { toFun := sourcePerm σ
      invFun := sourcePerm σ.symm
      left_inv := by intro z; ext <;> simp [sourcePerm]
      right_inv := by intro z; ext <;> simp [sourcePerm] }
  measurable_toFun := by change Measurable (sourcePerm σ); unfold sourcePerm; fun_prop
  measurable_invFun := by change Measurable (sourcePerm σ.symm); unfold sourcePerm; fun_prop

/-- The exact original raw market measure with common women's scores and man-only priority rates. -/
noncomputable def sourceLaw {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0) :
    Measure (Raw.Sources n) :=
  rawInputLaw (fun _ ↦ a) (fun m _ ↦ b m)

/-- The full infinite raw market law is preserved, including all independent female rows. -/
theorem source_measurePreserving {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n))
    (a b : Fin n → ℝ≥0) (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m)
    (hσ : ∀ w, a (σ w) = a w) :
    MeasurePreserving (sourceEquiv σ) (sourceLaw a b) (sourceLaw a b) := by
  have (m : Fin n) : IsProbabilityMeasure (ProbabilityTheory.expMeasure (b m : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by exact_mod_cast hb m)
  let μM := Measure.pi fun _ : Fin n ↦ FirstFresh.iidStream (RandomRanking.ofWeights a)
  let μW := Measure.pi fun _ : Fin n ↦ Measure.pi fun m : Fin n ↦
    ProbabilityTheory.expMeasure (b m : ℝ)
  have hM : MeasurePreserving (fun x : Fin n → ℕ → Fin n ↦ fun m t ↦ σ (x m t))
      μM μM :=
    measurePreserving_pi _ _ (fun _ ↦ stream_measurePreserving σ a ha hσ)
  have hW : MeasurePreserving (fun x : Fin n → Fin n → ℝ ↦ fun w m ↦ x (σ.symm w) m)
      μW μW := by
    have hp := measurePreserving_piCongrLeft
      (fun _ : Fin n ↦ Measure.pi fun m : Fin n ↦ ProbabilityTheory.expMeasure (b m : ℝ)) σ
    convert hp using 1
    funext x w
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  exact hM.prod hW

/-- Repeated edges in a raw trace are assigned to their actual destination woman. -/
def localRepeats {n : ℕ} : List (Arrival.Edge n) → Fin n → ℕ
  | [], _ => 0
  | q :: L, w => localRepeats L w + if q.1 = w ∧ q ∈ L then 1 else 0

/-- Assigning every repeated edge to its woman gives exactly the total repeat count. -/
theorem sum_localRepeats {n : ℕ} (L : List (Arrival.Edge n)) :
    ∑ w, localRepeats L w = RawSemantics.repeatCount L := by
  classical
  induction L with
  | nil => simp [localRepeats, RawSemantics.repeatCount, RawSemantics.distinctCount]
  | cons q L ih =>
    simp only [localRepeats, Finset.sum_add_distrib, ih, RepeatMoments.repeatCount_cons,
      List.mem_toFinset]
    by_cases hq : q ∈ L <;> simp [hq, eq_comm]

/-- A local repeated-edge count never exceeds the number of raw attempts in its trace. -/
theorem localRepeats_le_length {n : ℕ} (L : List (Arrival.Edge n)) (w : Fin n) :
    localRepeats L w ≤ L.length := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    simp only [localRepeats, List.length_cons]
    split_ifs <;> omega

/-- Erasing paused records cannot increase the number of raw entries. -/
theorem trace_length_le {n : ℕ} (h : List (Raw.Entry n)) :
    (RawBridge.trace h).length ≤ h.length := by
  induction h with
  | nil => rfl
  | cons e h ih =>
    cases e with
    | none => exact ih.trans (Nat.le_succ _)
    | some e => exact Nat.succ_le_succ ih

/-- Trace edges are relabeled by the same bijection as the raw records. -/
theorem trace_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (h : List (Raw.Entry n)) :
    RawBridge.trace (rawHistory σ h) = (RawBridge.trace h).map (edgePerm σ) := by
  induction h with
  | nil => rfl
  | cons e h ih =>
    cases e with
    | none => exact ih
    | some e =>
      rcases e with ⟨q, tag⟩
      exact congrArg (List.cons (edgePerm σ q)) ih

/-- Relabeled traces have exactly the corresponding local repeat counts. -/
theorem localRepeats_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (L : List (Arrival.Edge n))
    (w : Fin n) : localRepeats (L.map (edgePerm σ)) (σ w) = localRepeats L w := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    have hm : edgePerm σ q ∈ L.map (edgePerm σ) ↔ q ∈ L := by
      constructor
      · intro hq
        obtain ⟨v, hv, he⟩ := List.mem_map.mp hq
        exact (edgePerm σ).injective he ▸ hv
      · exact fun hq ↦ List.mem_map.mpr ⟨q, hq, rfl⟩
    have hw : (edgePerm σ q).1 = σ w ↔ q.1 = w := σ.injective.eq_iff
    simp only [List.map_cons, localRepeats, ih, hm, hw]

/-- The literal completed-run raw trace on the original source. -/
noncomputable def completedTrace {n : ℕ} [NeZero n] (z : Raw.Sources n) : List (Arrival.Edge n) :=
  RawBridge.trace (RawBridge.history (GlobalDraws.activeProtocol Finset.univ) z
    (GlobalDraws.rawClock z))

/-- The actual fixed-woman completed-run repeat count. -/
noncomputable def repeatAtWoman {n : ℕ} [NeZero n] (z : Raw.Sources n) (w : Fin n) : ℕ :=
  localRepeats (completedTrace z) w

/-- Full histories at the invariant completion clock are relabeled exactly. -/
theorem completedTrace_perm {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) (z : Raw.Sources n) :
    completedTrace (sourcePerm σ z) = (completedTrace z).map (edgePerm σ) := by
  unfold completedTrace
  rw [rawClock_perm]
  have ht := transcript_perm σ Finset.univ z.1 (RawBridge.sourceFemale z)
    (GlobalDraws.rawClock z)
  change RawBridge.trace _ = _
  rw [show RawBridge.history (GlobalDraws.activeProtocol Finset.univ) (sourcePerm σ z)
      (GlobalDraws.rawClock z) = rawHistory σ
        (RawBridge.history (GlobalDraws.activeProtocol Finset.univ) z (GlobalDraws.rawClock z))
      from ht, trace_perm]

/-- Whole-source relabeling moves each actual local repeat statistic to its relabeled woman. -/
theorem repeatAtWoman_perm {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n))
    (z : Raw.Sources n) (w : Fin n) :
    repeatAtWoman (sourcePerm σ z) (σ w) = repeatAtWoman z w := by
  rw [repeatAtWoman, completedTrace_perm, localRepeats_perm]
  rfl

/-- Every local repeat statistic is bounded by the actual raw completion clock. -/
theorem repeatAtWoman_le_clock {n : ℕ} [NeZero n] (z : Raw.Sources n) (w : Fin n) :
    repeatAtWoman z w ≤ GlobalDraws.rawClock z := by
  apply (localRepeats_le_length (completedTrace z) w).trans
  apply (trace_length_le _).trans
  exact le_of_eq (Raw.transcript_length _ _ _ _)

/-- The actual local completed-run statistic is measurable, including its random completion time. -/
theorem measurable_repeatAtWoman {n : ℕ} [NeZero n] (w : Fin n) :
    Measurable (fun z : Raw.Sources n ↦ repeatAtWoman z w) := by
  let : MeasurableSpace (List (Raw.Entry n)) := ⊤
  have hfixed (t : ℕ) : Measurable (fun z : Raw.Sources n ↦
      RawBridge.history (GlobalDraws.activeProtocol Finset.univ) z t) :=
    (Raw.measurable_transcript _ t).comp
      (show Measurable (fun z : Raw.Sources n ↦ (z.1, RawBridge.sourceFemale z)) by
        unfold RawBridge.sourceFemale
        fun_prop)
  have hjoint : Measurable (fun zt : Raw.Sources n × ℕ ↦
      RawBridge.history (GlobalDraws.activeProtocol Finset.univ) zt.1 zt.2) :=
    measurable_from_prod_countable_left hfixed
  exact (measurable_of_countable (fun h : List (Raw.Entry n) ↦
    localRepeats (RawBridge.trace h) w)).comp
      (hjoint.comp (measurable_id.prodMk RepeatMoments.measurable_rawClock))

/-- Actual local repeats are integrable by domination by the checked L2 raw completion clock. -/
theorem repeatAtWoman_memLp {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (w : Fin n) :
    MemLp (fun z ↦ (repeatAtWoman z w : ℝ)) 2 (sourceLaw a b) := by
  apply (GlobalDraws.rawClock_memLp a (fun m _ ↦ b m) ha (fun m _ ↦ hb m)).mono'
    ((measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp
      (measurable_repeatAtWoman w)).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  change (repeatAtWoman z w : ℝ) ≤ (GlobalDraws.rawClock z : ℝ)
  exact_mod_cast repeatAtWoman_le_clock z w

/-- Summing local repeat counts gives the actual total completed-run repeats almost surely. -/
theorem ae_sum_repeatAtWoman {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) :
    ∀ᵐ z ∂sourceLaw a b, ∑ w, repeatAtWoman z w = RepeatMoments.totalRepeats z := by
  filter_upwards [GlobalDraws.ae_rawClock_decomposition a (fun m _ ↦ b m) ha
    (fun m _ ↦ hb m)] with z hz
  have hs := sum_localRepeats (completedTrace z)
  change (∑ w, localRepeats (completedTrace z) w) = _
  rw [hs]
  unfold RepeatMoments.totalRepeats
  change GlobalDraws.rawClock z = numProposals (RawBridge.sourceProfile z) +
    RawSemantics.repeatCount (completedTrace z) at hz
  omega

/-- The actual expectation is invariant when the protected woman moves with the entire source. -/
theorem integral_repeatAtWoman_perm {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n))
    (a b : Fin n → ℝ≥0) (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m)
    (hσ : ∀ w, a (σ w) = a w) (w : Fin n) :
    (∫ z, (repeatAtWoman z (σ w) : ℝ) ∂sourceLaw a b) =
      ∫ z, (repeatAtWoman z w : ℝ) ∂sourceLaw a b := by
  have hi := (source_measurePreserving σ a b ha hb hσ).integral_comp'
    (fun z ↦ (repeatAtWoman z (σ w) : ℝ))
  change (∫ z, (repeatAtWoman (sourcePerm σ z) (σ w) : ℝ) ∂sourceLaw a b) = _ at hi
  simpa only [repeatAtWoman_perm] using hi.symm

/-- Two women with equal public scores have equal actual local-repeat expectations. -/
theorem integral_repeatAtWoman_eq {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (w v : Fin n) (hwv : a w = a v) :
    (∫ z, (repeatAtWoman z w : ℝ) ∂sourceLaw a b) =
      ∫ z, (repeatAtWoman z v : ℝ) ∂sourceLaw a b := by
  have hσ : ∀ k, a (Equiv.swap w v k) = a k := by
    intro k
    by_cases hkw : k = w
    · subst k
      simpa using hwv.symm
    · by_cases hkv : k = v
      · subst k
        simpa using hwv
      · simp [Equiv.swap_apply_of_ne_of_ne hkw hkv]
  have hi := integral_repeatAtWoman_perm (Equiv.swap w v) a b ha hb hσ w
  simpa only [Equiv.swap_apply_left] using hi.symm

/-- Actual local-repeat expectations sum to the checked completed-run total-repeat expectation. -/
theorem sum_integral_repeatAtWoman {n : ℕ} [NeZero n] (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) :
    (∑ w, ∫ z, (repeatAtWoman z w : ℝ) ∂sourceLaw a b) =
      ∫ z, (RepeatMoments.totalRepeats z : ℝ) ∂sourceLaw a b := by
  have : IsProbabilityMeasure (sourceLaw a b) :=
    Raw.isProbabilityMeasure_rawInputLaw (fun _ ↦ a) (fun m _ ↦ b m) (fun m _ ↦ hb m)
  rw [← integral_finsetSum Finset.univ
    (fun w _ ↦ (repeatAtWoman_memLp a b ha hb w).integrable one_le_two)]
  apply integral_congr_ae
  filter_upwards [ae_sum_repeatAtWoman a b ha hb] with z hz
  exact_mod_cast hz

/-- A fixed woman's actual repeat mean is at most the total-repeat mean divided by the size
of any equal-score tier containing her. This uses proved whole-law symmetry. -/
theorem integral_repeatAtWoman_le_total_div_tier {n : ℕ} [NeZero n]
    (a b : Fin n → ℝ≥0) (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m)
    (T : Finset (Fin n)) (w : Fin n) (hw : w ∈ T) (hT : ∀ v ∈ T, a v = a w) :
    (∫ z, (repeatAtWoman z w : ℝ) ∂sourceLaw a b) ≤
      (∫ z, (RepeatMoments.totalRepeats z : ℝ) ∂sourceLaw a b) / T.card := by
  have hnonneg (v : Fin n) : 0 ≤ ∫ z, (repeatAtWoman z v : ℝ) ∂sourceLaw a b :=
    integral_nonneg (fun _ ↦ Nat.cast_nonneg _)
  have hsum : (∑ v ∈ T, ∫ z, (repeatAtWoman z v : ℝ) ∂sourceLaw a b) =
      (T.card : ℝ) * ∫ z, (repeatAtWoman z w : ℝ) ∂sourceLaw a b := by
    calc
      _ = ∑ _v ∈ T, ∫ z, (repeatAtWoman z w : ℝ) ∂sourceLaw a b := by
        apply Finset.sum_congr rfl
        intro v hv
        exact integral_repeatAtWoman_eq a b ha hb v w (hT v hv)
      _ = _ := by simp [nsmul_eq_mul]
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    (fun v _ _ ↦ hnonneg v)
  rw [hsum, sum_integral_repeatAtWoman a b ha hb] at hle
  have hcard : (0 : ℝ) < T.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨w, hw⟩
  apply (le_div_iff₀ hcard).mpr
  simpa only [mul_comm] using hle

/-- All women with the protected woman's public score. -/
noncomputable def sameScore {n : ℕ} (a : Fin n → ℝ≥0) (w : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun v ↦ a v = a w

/-- The entire equal-score class gives the strongest direct tier-averaging estimate. -/
theorem integral_repeatAtWoman_le_total_div_sameScore {n : ℕ} [NeZero n]
    (a b : Fin n → ℝ≥0) (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (w : Fin n) :
    (∫ z, (repeatAtWoman z w : ℝ) ∂sourceLaw a b) ≤
      (∫ z, (RepeatMoments.totalRepeats z : ℝ) ∂sourceLaw a b) / (sameScore a w).card :=
  integral_repeatAtWoman_le_total_div_tier a b ha hb (sameScore a w) w (by simp [sameScore])
    (fun _ hv ↦ (Finset.mem_filter.mp hv).2)

end TieredMatching.LabelSymmetry
