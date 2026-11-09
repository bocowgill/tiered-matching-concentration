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

public import TieredMatching.ArrivalMeasurable
public import TieredMatching.ArrivalLaw

/-! # The concrete deferred-acceptance arrival policy has the exact PR probability law -/

@[expose] public section

namespace TieredMatching.Arrival

open MeasureTheory
open scoped NNReal ENNReal

/-- The concrete DA policy satisfies every structural premise of the allocation-law theorem. -/
theorem concrete_policy_valid {n J : ℕ} [NeZero n] (manTier : Fin n → Fin J)
    (β : Fin J → ℝ≥0) :
    ArrivalPolicyValid (fun m _ ↦ β (manTier m)) (fun r ↦ pick r manTier) where
  fresh r t x := pick_fresh r manTier x t
  score_eq r t x := congrArg β (congrArg Prod.snd
    (pick_block r manTier (allocationHistory (pick r manTier) x t)))
  measurable_fiber r t chosen := measurableSet_pick_history_fiber r manTier t chosen

/-- After the actual DA policy runs for `n²` observations, its completed raw preference profile
pushes forward to exactly the original PR market PMF. There is no assumed model-law equality. -/
theorem concrete_arrival_market_law {n I J : ℕ} [NeZero n]
    (womanTier : Fin n → Fin I) (manTier : Fin n → Fin J)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j) :
    Measure.map (arrivalProfile (fun r ↦ pick r manTier) (n * n))
      (arrivalInputLaw (fun _ w ↦ α (womanTier w)) (fun m _ ↦ β (manTier m))) =
      (Arxiv.«2009.05124».market womanTier manTier α β).toMeasure :=
  exponential_arrival_market_law womanTier manTier α β hα hβ
    (fun r ↦ pick r manTier) (concrete_policy_valid manTier β) (n * n)

/-- Every independent flat exponential source row is injective almost surely. -/
theorem ae_injective_flat_rows {n : ℕ} (Q : Fin n → Fin n → ℝ≥0)
    (hQ : ∀ m w, 0 < Q m w) :
    ∀ᵐ x ∂(Measure.pi fun q : Edge n ↦ ProbabilityTheory.expMeasure (Q q.2 q.1 : ℝ)),
      ∀ w, Function.Injective (fun m ↦ x (w, m)) := by
  have (m w : Fin n) : IsProbabilityMeasure (ProbabilityTheory.expMeasure (Q m w : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by exact_mod_cast hQ m w)
  have hrow (w : Fin n) :
      ∀ᵐ x ∂(Measure.pi fun w ↦ Measure.pi fun m ↦
        ProbabilityTheory.expMeasure (Q m w : ℝ)), Function.Injective (x w) :=
    (Measure.tendsto_eval_ae_ae (μ := fun w : Fin n ↦ Measure.pi fun m ↦
      ProbabilityTheory.expMeasure (Q m w : ℝ)) (i := w)).eventually
      (ae_injective_exponentials (fun m ↦ Q m w) (fun m ↦ hQ m w))
  have hall : ∀ᵐ x ∂(Measure.pi fun w ↦ Measure.pi fun m ↦
      ProbabilityTheory.expMeasure (Q m w : ℝ)), ∀ w, Function.Injective (x w) :=
    Filter.eventually_all.mpr hrow
  exact (measurePreserving_curry_pi (fun w m ↦
    ProbabilityTheory.expMeasure (Q m w : ℝ))).quasiMeasurePreserving.ae hall

/-- The men's independent raw inputs do not change the almost-sure source-row property. -/
theorem ae_injective_input_women {n : ℕ} (P Q : Fin n → Fin n → ℝ≥0)
    (hQ : ∀ m w, 0 < Q m w) :
    ∀ᵐ z ∂(arrivalInputLaw P Q),
      ∀ w, Function.Injective (fun m ↦ z.2 (w, m)) :=
  Measure.quasiMeasurePreserving_snd.ae (ae_injective_flat_rows Q hQ)

/-- The allocated priorities also have no within-row ties almost surely at every fixed time. -/
theorem ae_injective_allocated_rows {n J : ℕ} [NeZero n]
    (P : Fin n → Fin n → ℝ≥0) (manTier : Fin n → Fin J)
    (β : Fin J → ℝ≥0) (hβ : ∀ j, 0 < β j) (t : ℕ) :
    ∀ᵐ z ∂(arrivalInputLaw P (fun m _ ↦ β (manTier m))),
      ∀ w, Function.Injective ((arrivalMatrices (fun r ↦ pick r manTier) t z).2 w) := by
  filter_upwards [ae_injective_input_women P (fun m _ ↦ β (manTier m))
    (fun m _ ↦ hβ (manTier m))] with z hz
  let R := arrivalMenRanks z.1
  let h := allocationHistory (pick R manTier) z.2 t
  have hπ : PreservesBlocks manTier (allocationReindex (pick R manTier) h) := by
    rw [← replay_reindex R manTier h]
    exact replay_preservesBlocks R manTier h
  exact row_injective_reindex manTier _ hπ z.2 hz

/-- The actual raw replay has exactly the PR terminal state almost surely, so its proposal
counters and held partners can be transported using the concrete profile law. -/
theorem ae_allocation_terminal_state {n J : ℕ} [NeZero n]
    (P : Fin n → Fin n → ℝ≥0) (manTier : Fin n → Fin J)
    (β : Fin J → ℝ≥0) (hβ : ∀ j, 0 < β j) :
    ∀ᵐ z ∂(arrivalInputLaw P (fun m _ ↦ β (manTier m))),
      (replay (arrivalMenRanks z.1) manTier
        (allocationHistory (pick (arrivalMenRanks z.1) manTier) z.2 (n * n))).1.state =
      StableMarriage.deferredAcceptance
        (arrivalProfile (fun r ↦ pick r manTier) (n * n) z) := by
  filter_upwards [ae_injective_input_women P (fun m _ ↦ β (manTier m))
    (fun m _ ↦ hβ (manTier m))] with z hz
  exact allocation_terminal_state (arrivalMenRanks z.1) manTier z.2 hz

/-- The actual arrival construction for every market size uses the unique empty profile at zero. -/
noncomputable def concreteArrivalProfile {n J : ℕ} (manTier : Fin n → Fin J) :
    ((Fin n → Fin n → ℝ) × (ArrivalCoordinates n → ℝ)) → StableMarriage.Profile n :=
  if hn : n = 0 then fun _ ↦ default
  else arrivalProfile (fun r ↦ @pick n J ⟨hn⟩ r manTier) (n * n)

/-- The exact concrete pushforward law includes the empty-market boundary case. -/
theorem concreteArrivalProfile_market_law {n I J : ℕ}
    (womanTier : Fin n → Fin I) (manTier : Fin n → Fin J)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j) :
    Measure.map (concreteArrivalProfile manTier)
      (arrivalInputLaw (fun _ w ↦ α (womanTier w)) (fun m _ ↦ β (manTier m))) =
      (Arxiv.«2009.05124».market womanTier manTier α β).toMeasure := by
  classical
  by_cases hn : n = 0
  · subst n
    have (w : Fin 0) : IsProbabilityMeasure
        (ProbabilityTheory.expMeasure (α (womanTier w) : ℝ)) :=
      ProbabilityTheory.isProbabilityMeasure_expMeasure (by exact_mod_cast hα (womanTier w))
    have (m : Fin 0) : IsProbabilityMeasure
        (ProbabilityTheory.expMeasure (β (manTier m) : ℝ)) :=
      ProbabilityTheory.isProbabilityMeasure_expMeasure (by exact_mod_cast hβ (manTier m))
    have : IsProbabilityMeasure
        (arrivalInputLaw (fun _ w ↦ α (womanTier w)) (fun m _ ↦ β (manTier m))) :=
      inferInstanceAs (IsProbabilityMeasure ((Measure.pi fun m : Fin 0 ↦ Measure.pi fun w ↦
        ProbabilityTheory.expMeasure (α (womanTier w) : ℝ)).prod
        (Measure.pi fun q : Edge 0 ↦ ProbabilityTheory.expMeasure (β (manTier q.2) : ℝ))))
    have hs : Subsingleton (StableMarriage.Profile 0) := by
      constructor
      intro p q
      cases p
      cases q
      congr <;> exact Subsingleton.elim _ _
    have hpoint (p : StableMarriage.Profile 0) : ({p} : Set (StableMarriage.Profile 0)) =
        Set.univ := by
      ext q
      simp only [Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact hs.elim q p
    rw [concreteArrivalProfile, dite_eq_left rfl]
    apply Measure.ext_of_singleton
    intro p
    rw [Measure.map_apply measurable_const (MeasurableSet.singleton p), hpoint]
    simp
  · have : NeZero n := ⟨hn⟩
    simpa only [concreteArrivalProfile, dite_eq_right hn] using
      concrete_arrival_market_law womanTier manTier α β hα hβ

end TieredMatching.Arrival
