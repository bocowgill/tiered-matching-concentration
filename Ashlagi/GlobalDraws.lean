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

public import Ashlagi.AdaptiveSampling
public import Ashlagi.RawBridge
public import Ashlagi.PriorityProtocols
public import Ashlagi.CouponMoments

/-! # Global iid destinations obtained from the actual raw proposal streams -/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace Ashlagi.GlobalDraws

/-- First eligible proposer among a fixed active population, using only the visible raw state. -/
def activeProtocol {n : ℕ} (A : Finset (Fin n)) : Raw.Protocol n :=
  fun h ↦ Protocols.activeProtocol A (Raw.ordinary h)

/-- A terminal pause is absorbing. This permits independent dummy reads after completion. -/
def PauseStable {n : ℕ} (C : Raw.Protocol n) : Prop :=
  ∀ h, Raw.selected C h = none → Raw.selected C (none :: h) = none

/-- The visible raw selector is the same eligible-state selector as ordinary active DA. -/
theorem selected_activeProtocol {n : ℕ} (A : Finset (Fin n)) (h : List (Raw.Entry n)) :
    Raw.selected (activeProtocol A) h = Protocols.chooseFrom A (List.finRange n) (Raw.state h) := by
  change Protocols.selected (Protocols.activeProtocol A) (Raw.ordinary h) = _
  exact Protocols.selected_activeProtocol A (Raw.ordinary h)

/-- The canonical active proposer rule cannot reactivate after a pause. -/
theorem activeProtocol_pauseStable {n : ℕ} (A : Finset (Fin n)) :
    PauseStable (activeProtocol A) := by
  intro h hh
  rw [selected_activeProtocol] at hh ⊢
  exact hh

/-- Replay one globally supplied destination. Repeats preserve the ordinary state. -/
noncomputable def respond {n : ℕ} (C : Raw.Protocol n) (female : Arrival.Edge n → ℝ)
    (h : List (Raw.Entry n)) (w : Fin n) : Raw.Entry n :=
  (Raw.selected C h).map fun m ↦ ((w, m),
    if (w, m) ∈ Raw.seenEdges h then none else some (Ordinal.accept female (Raw.state h) (w, m)))

/-- A global value word drives the actual visible raw updates, in chronological order. -/
noncomputable def replayValues {n : ℕ} (C : Raw.Protocol n)
    (female : Arrival.Edge n → ℝ) : List (Fin n) → List (Raw.Entry n)
  | [] => []
  | w :: L => let h := replayValues C female L; respond C female h w :: h

/-- The visible raw history determined by an adaptive query history. -/
noncomputable def replayQueries {n : ℕ} (C : Raw.Protocol n)
    (female : Arrival.Edge n → ℝ) (h : List (((Fin n) × ℕ) × Fin n)) :=
  replayValues C female (h.map Prod.snd)

/-- Query a real proposer while active and a harmless fixed row after the absorbing pause. -/
noncomputable def choose {n : ℕ} [NeZero n] (C : Raw.Protocol n)
    (female : Arrival.Edge n → ℝ) (h : List (((Fin n) × ℕ) × Fin n)) : Fin n :=
  (Raw.selected C (replayQueries C female h)).getD 0

/-- Every row read consumes its next unused coordinate, including dummy reads. -/
noncomputable def query {n : ℕ} [NeZero n] (C : Raw.Protocol n)
    (female : Arrival.Edge n → ℝ) := AdaptiveSampling.slotPolicy (choose C female)

/-- Responding to a real selection increases exactly that man's raw counter. -/
theorem rawCounter_respond {n : ℕ} (C : Raw.Protocol n) (female : Arrival.Edge n → ℝ)
    (h : List (Raw.Entry n)) (w m k : Fin n) (hm : Raw.selected C h = some m) :
    Raw.rawCounter (respond C female h w :: h) k =
      if m = k then Raw.rawCounter h k + 1 else Raw.rawCounter h k := by
  classical
  simp only [respond, hm, Option.map_some, Raw.rawCounter, Raw.drawOrder]
  split_ifs <;> simp_all

/-- A skipped global draw changes no actual raw counter. -/
theorem respond_eq_none {n : ℕ} (C : Raw.Protocol n) (female : Arrival.Edge n → ℝ)
    (h : List (Raw.Entry n)) (w : Fin n) (hm : Raw.selected C h = none) :
    respond C female h w = none := by simp only [respond, hm, Option.map_none]

/-- Until the absorbing pause, virtual query slots equal the actual consumed row counters. -/
theorem rawCounter_replayQueries {n : ℕ} [NeZero n] (C : Raw.Protocol n)
    (hs : PauseStable C) (female : Arrival.Edge n → ℝ)
    (h : List (((Fin n) × ℕ) × Fin n))
    (hc : AdaptiveSampling.Coherent (query C female) h)
    (ha : Raw.selected C (replayQueries C female h) ≠ none) (k : Fin n) :
    Raw.rawCounter (replayQueries C female h) k = AdaptiveSampling.slotCount h k := by
  induction h with
  | nil => rfl
  | cons entry h ih =>
    rcases entry with ⟨q, w⟩
    change AdaptiveSampling.Coherent (query C female) h ∧ q = query C female h at hc
    change Raw.selected C
      (respond C female (replayQueries C female h) w :: replayQueries C female h) ≠ none at ha
    have hprev : Raw.selected C (replayQueries C female h) ≠ none := by
      intro hz
      rw [respond_eq_none C female _ w hz] at ha
      exact ha (hs _ hz)
    obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp hprev
    have hq : q.1 = m := by
      rw [hc.2]
      simp only [query, AdaptiveSampling.slotPolicy, choose, hm, Option.getD_some]
    change Raw.rawCounter
      (respond C female (replayQueries C female h) w :: replayQueries C female h) k = _
    rw [rawCounter_respond C female _ w m k hm, AdaptiveSampling.slotCount_cons, hq,
      ih hc.1 hprev]
    split_ifs <;> omega

/-- The globally driven replay reads the same destinations as the actual per-man raw streams. -/
theorem transcript_eq_replayQueries {n : ℕ} [NeZero n] (C : Raw.Protocol n)
    (hs : PauseStable C) (female : Arrival.Edge n → ℝ)
    (x : (Fin n × ℕ) → Fin n) (t : ℕ) :
    Raw.transcript C (Function.curry x) female t =
      replayQueries C female (queryHistory (query C female) x t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [Raw.transcript, queryHistory, replayQueries, List.map_cons, replayValues]
    rw [ih]
    congr 1
    generalize hh : queryHistory (query C female) x t = h
    have hc : AdaptiveSampling.Coherent (query C female) h :=
      hh ▸ AdaptiveSampling.coherent_queryHistory (query C female) x t
    cases hm : Raw.selected C (replayQueries C female h) with
    | none =>
      change Raw.observation C (Function.curry x) female (replayQueries C female h) =
        respond C female (replayQueries C female h) _
      simp only [Raw.observation, Raw.nextEdge, hm, Option.map_none, respond]
    | some m =>
      have hk := rawCounter_replayQueries C hs female h hc (by simp [hm]) m
      change Raw.observation C (Function.curry x) female (replayQueries C female h) =
        respond C female (replayQueries C female h) _
      simp only [Raw.observation, Raw.nextEdge, hm, Option.map_some, respond,
        query, AdaptiveSampling.slotPolicy, choose, Option.getD_some, Function.curry, hk]

/-- The complete global destination tape, with unused independent draws after the final pause. -/
noncomputable def tape {n : ℕ} [NeZero n] (C : Raw.Protocol n)
    (female : Arrival.Edge n → ℝ) (x : (Fin n × ℕ) → Fin n) : ℕ → Fin n :=
  AdaptiveSampling.observationStream (query C female) x

/-- For every fixed female priority context, the actual global read tape is exactly iid. -/
theorem tape_law {n : ℕ} [NeZero n] (C : Raw.Protocol n)
    (female : Arrival.Edge n → ℝ) (p : PMF (Fin n)) :
    Measure.map (tape C female) (Measure.infinitePi fun _ : Fin n × ℕ ↦ p.toMeasure) =
      FirstFresh.iidStream p :=
  AdaptiveSampling.slotPolicy_stream_law (choose C female) p

/-- The iid global tape is independent of any initially independent finite priority context. -/
theorem context_tape_law {n : ℕ} [NeZero n] {K : Type*} [Fintype K]
    [MeasurableSpace K] [MeasurableSingletonClass K] (ν : PMF K) (C : Raw.Protocol n)
    (female : K → Arrival.Edge n → ℝ) (p : PMF (Fin n)) :
    Measure.map (fun z : K × ((Fin n × ℕ) → Fin n) ↦ (z.1, tape C (female z.1) z.2))
      (ν.toMeasure.prod (Measure.infinitePi fun _ : Fin n × ℕ ↦ p.toMeasure)) =
      ν.toMeasure.prod (FirstFresh.iidStream p) :=
  AdaptiveSampling.context_observationStream_law ν
    (fun c ↦ query C (female c))
    (fun c ↦ AdaptiveSampling.fresh_slotPolicy (choose C (female c))) p

/-- The full actual querying history is jointly measurable in priorities and row streams. -/
theorem measurable_queryHistory {n : ℕ} [NeZero n] (C : Raw.Protocol n)
    (hs : PauseStable C) (t : ℕ) :
    @Measurable ((Arrival.Edge n → ℝ) × ((Fin n × ℕ) → Fin n))
      (List (((Fin n) × ℕ) × Fin n)) inferInstance ⊤
      (fun z ↦ queryHistory (query C z.1) z.2 t) := by
  let : MeasurableSpace (List (Raw.Entry n)) := ⊤
  let : MeasurableSpace (List (((Fin n) × ℕ) × Fin n)) := ⊤
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have htrans : Measurable (fun z : (Arrival.Edge n → ℝ) × ((Fin n × ℕ) → Fin n) ↦
        Raw.transcript C (Function.curry z.2) z.1 t) :=
      (Raw.measurable_transcript C t).comp
        ((show Measurable (fun z : (Arrival.Edge n → ℝ) × ((Fin n × ℕ) → Fin n) ↦
          Function.curry z.2) by fun_prop).prodMk measurable_fst)
    have hm := (measurable_of_countable fun h : List (Raw.Entry n) ↦
      (Raw.selected C h).getD 0).comp htrans
    have hk := (measurable_of_countable fun h :
        List (((Fin n) × ℕ) × Fin n) × Fin n ↦
          AdaptiveSampling.slotCount h.1 h.2).comp (ih.prodMk hm)
    have hquery : Measurable (fun z : (Arrival.Edge n → ℝ) × ((Fin n × ℕ) → Fin n) ↦
        query C z.1 (queryHistory (query C z.1) z.2 t)) := by
      convert hm.prodMk hk using 1
      funext z
      simp only [Function.comp_def]
      rw [transcript_eq_replayQueries C hs]
      rfl
    have heval : Measurable (fun z : ((Fin n × ℕ) → Fin n) × (Fin n × ℕ) ↦ z.1 z.2) :=
      measurable_from_prod_countable_left fun i ↦ measurable_pi_apply i
    have hval := heval.comp (measurable_snd.prodMk hquery)
    exact (measurable_of_countable fun h :
      (((Fin n × ℕ) × Fin n) × List (((Fin n) × ℕ) × Fin n)) ↦
        h.1 :: h.2).comp ((hquery.prodMk hval).prodMk ih)

/-- Measurability includes the entire infinite tape and the original continuous priorities. -/
theorem measurable_tape {n : ℕ} [NeZero n] (C : Raw.Protocol n) (hs : PauseStable C) :
    Measurable (fun z : (Arrival.Edge n → ℝ) × ((Fin n × ℕ) → Fin n) ↦
      tape C z.1 z.2) := by
  apply Measurable.of_eval
  intro t
  let : MeasurableSpace (List (Raw.Entry n)) := ⊤
  let : MeasurableSpace (List (((Fin n) × ℕ) × Fin n)) := ⊤
  have htrans := (Raw.measurable_transcript C t).comp
    ((show Measurable (fun z : (Arrival.Edge n → ℝ) × ((Fin n × ℕ) → Fin n) ↦
      Function.curry z.2) by fun_prop).prodMk measurable_fst)
  have hm := (measurable_of_countable fun h : List (Raw.Entry n) ↦
    (Raw.selected C h).getD 0).comp htrans
  have hk := (measurable_of_countable fun h :
    List (((Fin n) × ℕ) × Fin n) × Fin n ↦
      AdaptiveSampling.slotCount h.1 h.2).comp ((measurable_queryHistory C hs t).prodMk hm)
  have heval : Measurable (fun z : ((Fin n × ℕ) → Fin n) × (Fin n × ℕ) ↦ z.1 z.2) :=
    measurable_from_prod_countable_left fun i ↦ measurable_pi_apply i
  convert heval.comp (measurable_snd.prodMk (hm.prodMk hk)) using 1
  funext z
  simp only [Function.comp_def]
  rw [transcript_eq_replayQueries C hs]
  rfl

/-- Mixing arbitrary independent continuous female priorities leaves the global tape iid. -/
theorem priority_mixture_tape_law {n : ℕ} [NeZero n] (C : Raw.Protocol n)
    (hs : PauseStable C) (ν : Measure (Arrival.Edge n → ℝ)) [IsProbabilityMeasure ν]
    (p : PMF (Fin n)) :
    Measure.map (fun z : (Arrival.Edge n → ℝ) × ((Fin n × ℕ) → Fin n) ↦
      tape C z.1 z.2) (ν.prod (Measure.infinitePi fun _ : Fin n × ℕ ↦ p.toMeasure)) =
      FirstFresh.iidStream p := by
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply (measurable_tape C hs) hE,
    Measure.prod_apply (hE.preimage (measurable_tape C hs))]
  have hsection (female : Arrival.Edge n → ℝ) :
      (Measure.infinitePi fun _ : Fin n × ℕ ↦ p.toMeasure)
        (Prod.mk female ⁻¹' ((fun z :
          (Arrival.Edge n → ℝ) × ((Fin n × ℕ) → Fin n) ↦ tape C z.1 z.2) ⁻¹' E)) =
        FirstFresh.iidStream p E := by
    change (Measure.infinitePi fun _ : Fin n × ℕ ↦ p.toMeasure) (tape C female ⁻¹' E) = _
    have ht : Measurable (tape C female) :=
      AdaptiveSampling.measurable_observationStream (query C female)
    have he := congrArg (fun μ : Measure (ℕ → Fin n) ↦ μ E) (tape_law C female p)
    rw [Measure.map_apply ht hE] at he
    exact he
  simp_rw [hsection]
  simp

/-- Flattening independent equal-law male rows gives the same iid coordinate array. -/
theorem flatten_male_rows_law {n : ℕ} (p : PMF (Fin n)) :
    Measure.map Function.uncurry
      (Measure.pi fun _ : Fin n ↦ FirstFresh.iidStream p) =
      Measure.infinitePi fun _ : Fin n × ℕ ↦ p.toMeasure := by
  change Measure.map (MeasurableEquiv.curry (Fin n) ℕ (Fin n)).symm
    (Measure.pi fun _ : Fin n ↦ Measure.infinitePi fun _ : ℕ ↦ p.toMeasure) = _
  rw [← Measure.infinitePi_eq_pi]
  exact Measure.infinitePi_map_curry_symm (fun _ _ ↦ p.toMeasure)

/-- The global destination tape on the original iid/exponential raw source. -/
noncomputable def sourceTape {n : ℕ} [NeZero n] (C : Raw.Protocol n)
    (z : (Fin n → ℕ → Fin n) × (Fin n → Fin n → ℝ)) : ℕ → Fin n :=
  tape C (RawBridge.sourceFemale z) (Function.uncurry z.1)

/-- The full global tape has the exact iid categorical law under the original raw market law. -/
theorem sourceTape_law {n : ℕ} [NeZero n] (C : Raw.Protocol n) (hs : PauseStable C)
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) :
    Measure.map (sourceTape C) (rawInputLaw (fun _ ↦ a) Q) =
      FirstFresh.iidStream (RandomRanking.ofWeights a) := by
  let p := RandomRanking.ofWeights a
  let μM := Measure.pi fun _ : Fin n ↦ FirstFresh.iidStream p
  let μW := Measure.pi fun w : Fin n ↦ Measure.pi fun m : Fin n ↦
    ProbabilityTheory.expMeasure (Q m w : ℝ)
  have (w m : Fin n) : IsProbabilityMeasure (ProbabilityTheory.expMeasure (Q m w : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by exact_mod_cast hQ m w)
  let ν := Measure.map Function.uncurry μW
  have : IsProbabilityMeasure ν := inferInstance
  have hprod : Measure.map
      (fun z : (Fin n → ℕ → Fin n) × (Fin n → Fin n → ℝ) ↦
        (Function.uncurry z.2, Function.uncurry z.1)) (μM.prod μW) =
      ν.prod (Measure.infinitePi fun _ : Fin n × ℕ ↦ p.toMeasure) := by
    rw [← Measure.prod_swap]
    rw [Measure.map_map (by fun_prop) measurable_swap]
    change Measure.map (Prod.map Function.uncurry Function.uncurry) (μW.prod μM) = _
    rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
    exact congrArg (ν.prod) (flatten_male_rows_law p)
  rw [show sourceTape C = (fun z :
      (Arrival.Edge n → ℝ) × ((Fin n × ℕ) → Fin n) ↦ tape C z.1 z.2) ∘
        (fun z ↦ (Function.uncurry z.2, Function.uncurry z.1)) from rfl,
    ← Measure.map_map (measurable_tape C hs) (by fun_prop)]
  change Measure.map _ (Measure.map _ (μM.prod μW)) = _
  rw [hprod]
  exact priority_mixture_tape_law C hs ν p

/-- The next supplied global value gives exactly the actual raw observation. -/
theorem observation_eq_respond_tape {n : ℕ} [NeZero n] (C : Raw.Protocol n)
    (hs : PauseStable C) (female : Arrival.Edge n → ℝ)
    (x : (Fin n × ℕ) → Fin n) (t : ℕ) :
    Raw.observation C (Function.curry x) female
      (Raw.transcript C (Function.curry x) female t) =
      respond C female (Raw.transcript C (Function.curry x) female t) (tape C female x t) := by
  have he := transcript_eq_replayQueries C hs female x (t + 1)
  simp only [Raw.transcript, queryHistory, replayQueries, List.map_cons, replayValues] at he
  change Raw.observation C (Function.curry x) female
      (Raw.transcript C (Function.curry x) female t) ::
        Raw.transcript C (Function.curry x) female t =
    respond C female (replayQueries C female (queryHistory (query C female) x t))
      (tape C female x t) :: replayQueries C female (queryHistory (query C female) x t) at he
  rw [← transcript_eq_replayQueries C hs female x t] at he
  exact (List.cons.inj he).1

/-- The raw first-eligible selector pauses exactly at a terminal active-market state. -/
theorem activeProtocol_none_iff_terminal {n : ℕ} (A : Finset (Fin n))
    (h : List (Raw.Entry n)) :
    Raw.selected (activeProtocol A) h = none ↔ Schedules.Terminal A (Raw.state h) := by
  rw [selected_activeProtocol]
  exact Protocols.chooseFrom_finRange_none A _

/-- Before or after completion, every woman hit by the tape is hit by the actual full-market run.
After completion all women have already been hit, so independent dummy reads do not change this.
-/
theorem hit_iff_tape_prefix {n : ℕ} [NeZero n]
    (female : Arrival.Edge n → ℝ) (x : (Fin n × ℕ) → Fin n)
    (p : StableMarriage.Profile n)
    (horders : ∀ m, Function.curry x m ∈ IIDRanking.rankEvent (p.manRank m))
    (hcompare : ∀ w m old, p.womanRank w m < p.womanRank w old ↔
      female (w, m) < female (w, old)) (t : ℕ) (w : Fin n) :
    (∃ m, (w, m) ∈ RawBridge.trace
      (Raw.transcript (activeProtocol Finset.univ) (Function.curry x) female t)) ↔
      ∃ j < t, tape (activeProtocol Finset.univ) female x j = w := by
  let C := activeProtocol (Finset.univ : Finset (Fin n))
  have hs := activeProtocol_pauseStable (Finset.univ : Finset (Fin n))
  change (∃ m, (w, m) ∈ RawBridge.trace (Raw.transcript C (Function.curry x) female t)) ↔ _
  induction t with
  | zero => simp [Raw.transcript, RawBridge.trace]
  | succ t ih =>
    let h := Raw.transcript C (Function.curry x) female t
    have hb := RawBridge.transcript_admissible_replay C (Function.curry x) female p
      Finset.univ (RawBridge.supports_univ C) horders hcompare t
    cases hm : Raw.selected C h with
    | none =>
      have ht : Schedules.Terminal Finset.univ (Raw.state h) :=
        (activeProtocol_none_iff_terminal Finset.univ h).mp hm
      have hall : ∀ v, ∃ m, (v, m) ∈ RawBridge.trace h := by
        rw [hb.2] at ht
        exact (RawSemantics.terminal_univ_iff_all_hit p hb.1).mp ht
      have hobs : Raw.observation C (Function.curry x) female h = none := by
        simp only [Raw.observation, Raw.nextEdge, hm, Option.map_none]
      have hprev := ih.mp (hall w)
      constructor
      · intro _
        obtain ⟨j, hj, he⟩ := hprev
        exact ⟨j, by omega, he⟩
      · intro _
        change ∃ m, (w, m) ∈ RawBridge.trace
          (Raw.observation C (Function.curry x) female h :: h)
        rw [hobs]
        exact hall w
    | some m =>
      have htrace : RawBridge.trace
          (Raw.transcript C (Function.curry x) female (t + 1)) =
          (tape C female x t, m) :: RawBridge.trace h := by
        rw [Raw.transcript, observation_eq_respond_tape C hs female x t]
        change RawBridge.trace (respond C female h (tape C female x t) :: h) = _
        simp only [respond, hm, Option.map_some, RawBridge.trace]
      rw [htrace]
      constructor
      · rintro ⟨k, hk⟩
        rcases List.mem_cons.mp hk with he | he
        · have hw := congrArg Prod.fst he
          exact ⟨t, by omega, hw.symm⟩
        · obtain ⟨j, hj, he⟩ := ih.mp ⟨k, he⟩
          exact ⟨j, by omega, he⟩
      · rintro ⟨j, hj, he⟩
        by_cases hjt : j = t
        · subst j
          exact ⟨m, List.mem_cons.mpr (Or.inl (by rw [he]))⟩
        · obtain ⟨k, hk⟩ := ih.mpr ⟨j, by omega, he⟩
          exact ⟨k, List.mem_cons_of_mem _ hk⟩

/-- Full-market termination occurs at exactly the global tape's coupon-cover prefixes. -/
theorem terminal_iff_tape_covers {n : ℕ} [NeZero n]
    (female : Arrival.Edge n → ℝ) (x : (Fin n × ℕ) → Fin n)
    (p : StableMarriage.Profile n)
    (horders : ∀ m, Function.curry x m ∈ IIDRanking.rankEvent (p.manRank m))
    (hcompare : ∀ w m old, p.womanRank w m < p.womanRank w old ↔
      female (w, m) < female (w, old)) (t : ℕ) :
    Schedules.Terminal Finset.univ
      (Raw.state (Raw.transcript (activeProtocol Finset.univ) (Function.curry x) female t)) ↔
      CouponMoments.covers (tape (activeProtocol Finset.univ) female x) t := by
  have hb := RawBridge.transcript_admissible_replay (activeProtocol Finset.univ)
    (Function.curry x) female p Finset.univ (RawBridge.supports_univ _) horders hcompare t
  rw [hb.2, RawSemantics.terminal_univ_iff_all_hit p hb.1]
  exact forall_congr' fun w ↦ hit_iff_tape_prefix female x p horders hcompare t w

/-- An unpaused raw prefix has exactly one genuine raw attempt per public time step. -/
theorem trace_length_of_no_pause {n : ℕ} (C : Raw.Protocol n)
    (female : Arrival.Edge n → ℝ) (streams : Fin n → ℕ → Fin n) (t : ℕ)
    (ht : ∀ k < t, Raw.selected C (Raw.transcript C streams female k) ≠ none) :
    (RawBridge.trace (Raw.transcript C streams female t)).length = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp := ih (fun k hk ↦ ht k (by omega))
    obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp (ht t (by omega))
    simp only [Raw.transcript, Raw.observation, Raw.nextEdge, hm, Option.map_some,
      RawBridge.trace, List.length_cons, hp]

/-- At the least coupon-cover time, the actual raw attempt count equals that time exactly. -/
theorem coupon_time_trace_length {n : ℕ} [NeZero n]
    (female : Arrival.Edge n → ℝ) (x : (Fin n × ℕ) → Fin n)
    (p : StableMarriage.Profile n)
    (horders : ∀ m, Function.curry x m ∈ IIDRanking.rankEvent (p.manRank m))
    (hcompare : ∀ w m old, p.womanRank w m < p.womanRank w old ↔
      female (w, m) < female (w, old))
    (hx : CouponMoments.completes (tape (activeProtocol Finset.univ) female x)) :
    (RawBridge.trace (Raw.transcript (activeProtocol Finset.univ) (Function.curry x) female
      (CouponMoments.time (tape (activeProtocol Finset.univ) female x)))).length =
      CouponMoments.time (tape (activeProtocol Finset.univ) female x) := by
  apply trace_length_of_no_pause
  intro k hk hpause
  have hterm := (activeProtocol_none_iff_terminal Finset.univ _).mp hpause
  have hcover := (terminal_iff_tape_covers female x p horders hcompare k).mp hterm
  have hle := (CouponMoments.time_le_iff hx k).mpr hcover
  omega

/-- The actual coupon clock decomposes as exact PR proposals plus discarded repeats. -/
theorem coupon_time_eq_proposals_add_repeats {n : ℕ} [NeZero n]
    (female : Arrival.Edge n → ℝ) (x : (Fin n × ℕ) → Fin n)
    (p : StableMarriage.Profile n)
    (horders : ∀ m, Function.curry x m ∈ IIDRanking.rankEvent (p.manRank m))
    (hcompare : ∀ w m old, p.womanRank w m < p.womanRank w old ↔
      female (w, m) < female (w, old))
    (hx : CouponMoments.completes (tape (activeProtocol Finset.univ) female x)) :
    CouponMoments.time (tape (activeProtocol Finset.univ) female x) =
      StableMarriage.numProposals p + RawSemantics.repeatCount
        (RawBridge.trace (Raw.transcript (activeProtocol Finset.univ) (Function.curry x) female
          (CouponMoments.time (tape (activeProtocol Finset.univ) female x)))) := by
  let T := CouponMoments.time (tape (activeProtocol Finset.univ) female x)
  have hb := RawBridge.transcript_admissible_replay (activeProtocol Finset.univ)
    (Function.curry x) female p Finset.univ (RawBridge.supports_univ _) horders hcompare T
  have hcover := CouponMoments.covers_time hx
  have hall : ∀ w, ∃ m, (w, m) ∈ RawBridge.trace
      (Raw.transcript (activeProtocol Finset.univ) (Function.curry x) female T) := by
    intro w
    exact (hit_iff_tape_prefix female x p horders hcompare T w).mpr (hcover w)
  exact (coupon_time_trace_length female x p horders hcompare hx).symm.trans
    (RawSemantics.length_eq_pr_numProposals_add_repeats_of_all_hit p hb.1 hall)

set_option maxHeartbeats 800000 in
/-- The source tape is measurable on the original mixed raw source space. -/
theorem measurable_sourceTape {n : ℕ} [NeZero n] (C : Raw.Protocol n) (hs : PauseStable C) :
    Measurable (sourceTape C) := by
  have hmap : Measurable (fun z :
      (Fin n → ℕ → Fin n) × (Fin n → Fin n → ℝ) ↦
        (RawBridge.sourceFemale z, Function.uncurry z.1)) := by
    apply Measurable.prodMk
    · apply Measurable.of_eval
      intro q
      exact (measurable_pi_apply q.2).comp ((measurable_pi_apply q.1).comp measurable_snd)
    · apply Measurable.of_eval
      intro q
      exact (measurable_pi_apply q.2).comp ((measurable_pi_apply q.1).comp measurable_fst)
  exact (measurable_tape C hs).comp hmap

/-- Every woman is reached by the actual global iid tape almost surely. -/
theorem ae_sourceTape_completes {n : ℕ} [NeZero n] (C : Raw.Protocol n) (hs : PauseStable C)
    (a : Fin n → ℝ≥0) (Q : Fin n → Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hQ : ∀ m w, 0 < Q m w) :
    ∀ᵐ z ∂rawInputLaw (fun _ ↦ a) Q, CouponMoments.completes (sourceTape C z) := by
  have hp : MeasurePreserving (sourceTape C) (rawInputLaw (fun _ ↦ a) Q)
      (FirstFresh.iidStream (RandomRanking.ofWeights a)) :=
    ⟨measurable_sourceTape C hs, sourceTape_law C hs a Q hQ⟩
  exact hp.quasiMeasurePreserving.ae
    (CouponMoments.ae_completes _ (CouponMoments.ofWeights_mass_pos a ha))

/-- The full actual raw DA completion clock, expressed through its checked global tape. -/
noncomputable def rawClock {n : ℕ} [NeZero n]
    (z : (Fin n → ℕ → Fin n) × (Fin n → Fin n → ℝ)) : ℕ :=
  CouponMoments.time (sourceTape (activeProtocol Finset.univ) z)

/-- The actual raw completion clock has exactly the weighted iid coupon-time distribution. -/
theorem rawClock_law {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) :
    Measure.map rawClock (rawInputLaw (fun _ ↦ a) Q) =
      Measure.map CouponMoments.time (FirstFresh.iidStream (RandomRanking.ofWeights a)) := by
  rw [show rawClock = CouponMoments.time ∘ sourceTape (activeProtocol Finset.univ) from rfl,
    ← Measure.map_map CouponMoments.measurable_time
      (measurable_sourceTape _ (activeProtocol_pauseStable Finset.univ)),
    sourceTape_law _ (activeProtocol_pauseStable Finset.univ) a Q hQ]

/-- Almost surely, raw coupon time equals the exact PR's proposal count plus actual repeats. -/
theorem ae_rawClock_decomposition {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (ha : ∀ w, 0 < a w) (hQ : ∀ m w, 0 < Q m w) :
    ∀ᵐ z ∂rawInputLaw (fun _ ↦ a) Q,
      rawClock z = StableMarriage.numProposals (RawBridge.sourceProfile z) +
        RawSemantics.repeatCount (RawBridge.trace
          (RawBridge.history (activeProtocol Finset.univ) z (rawClock z))) := by
  filter_upwards [RawBridge.ae_source_orders (fun _ ↦ a) Q (fun _ ↦ ha),
    RawBridge.ae_source_female_injective (fun _ ↦ a) Q hQ,
    ae_sourceTape_completes (activeProtocol Finset.univ)
      (activeProtocol_pauseStable Finset.univ) a Q ha hQ] with z horders hcompare hcomplete
  exact coupon_time_eq_proposals_add_repeats (RawBridge.sourceFemale z)
    (Function.uncurry z.1) (RawBridge.sourceProfile z) horders
    (fun w m old ↦ exponentialRank_lt_iff (z.2 w) (hcompare w) m old) hcomplete

/-- The actual global tape preserves the iid coupon probability measure. -/
theorem sourceTape_measurePreserving {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) :
    MeasurePreserving (sourceTape (activeProtocol Finset.univ)) (rawInputLaw (fun _ ↦ a) Q)
      (FirstFresh.iidStream (RandomRanking.ofWeights a)) :=
  ⟨measurable_sourceTape _ (activeProtocol_pauseStable Finset.univ),
    sourceTape_law _ (activeProtocol_pauseStable Finset.univ) a Q hQ⟩

/-- The actual raw completion time has a finite second moment. -/
theorem rawClock_memLp {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (ha : ∀ w, 0 < a w) (hQ : ∀ m w, 0 < Q m w) :
    MemLp (fun z ↦ (rawClock z : ℝ)) 2 (rawInputLaw (fun _ ↦ a) Q) :=
  (CouponMoments.memLp_time_two _ (CouponMoments.ofWeights_mass_pos a ha)).comp_measurePreserving
    (sourceTape_measurePreserving a Q hQ)

/-- Every real coupon-time statistic transports to the actual completion clock. -/
theorem rawClock_integral_eq {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (hQ : ∀ m w, 0 < Q m w) (f : ℕ → ℝ) :
    (∫ z, f (rawClock z) ∂rawInputLaw (fun _ ↦ a) Q) =
      ∫ x, f (CouponMoments.time x) ∂FirstFresh.iidStream (RandomRanking.ofWeights a) := by
  have hms : Measurable (rawClock (n := n)) := CouponMoments.measurable_time.comp
    (measurable_sourceTape _ (activeProtocol_pauseStable Finset.univ))
  have hf : Measurable f := measurable_of_countable f
  rw [← integral_map hms.aemeasurable hf.aestronglyMeasurable, rawClock_law a Q hQ,
    integral_map CouponMoments.measurable_time.aemeasurable hf.aestronglyMeasurable]

/-- Uniform source mean bounds now hold for the actual raw DA clock. -/
theorem rawClock_mean_bounds {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (ha : ∀ w, 1 ≤ a w) (hQ : ∀ m w, 0 < Q m w)
    (k : ℕ) (hk : k ≤ (CouponMoments.minimumCoupons a).card) :
    CouponMoments.totalWeight a * (harmonic k : ℝ) ≤
        (∫ z, (rawClock z : ℝ) ∂rawInputLaw (fun _ ↦ a) Q) ∧
      (∫ z, (rawClock z : ℝ) ∂rawInputLaw (fun _ ↦ a) Q) ≤
        CouponMoments.totalWeight a * (harmonic n : ℝ) := by
  rw [rawClock_integral_eq a Q hQ]
  exact ⟨CouponMoments.harmonic_le_mean_time a
    (fun w ↦ lt_of_lt_of_le (by norm_num) (ha w)) k hk,
    by simpa only [Fintype.card_fin] using CouponMoments.mean_time_le_harmonic a ha⟩

/-- The actual raw completion clock inherits the checked coupon second-moment bound. -/
theorem rawClock_secondMoment_le {n : ℕ} [NeZero n] (a : Fin n → ℝ≥0)
    (Q : Fin n → Fin n → ℝ≥0) (ha : ∀ w, 1 ≤ a w) (hQ : ∀ m w, 0 < Q m w) :
    (∫ z, (rawClock z : ℝ) ^ 2 ∂rawInputLaw (fun _ ↦ a) Q) ≤
      (CouponMoments.totalWeight a * (harmonic n : ℝ)) ^ 2 +
        2 * CouponMoments.totalWeight a ^ 2 := by
  rw [rawClock_integral_eq a Q hQ (fun k ↦ (k : ℝ) ^ 2)]
  simpa only [Fintype.card_fin] using CouponMoments.secondMoment_time_le a ha

end Ashlagi.GlobalDraws
