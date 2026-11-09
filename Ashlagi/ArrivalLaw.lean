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

public import Ashlagi.AdaptiveAllocation
public import Ashlagi.ProfileLaw

/-! # Exact profile laws for history-based exponential arrival allocations -/

@[expose] public section

namespace Ashlagi

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Select an allocation policy from the first input, which the allocation leaves unchanged. -/
def indexedAllocation {M R ι α : Type*} [DecidableEq ι]
    (selector : M → R) (pick : R → List (ι × α) → ι × ι) (t : ℕ)
    (z : M × (ι → α)) : M × (ι → α) :=
  (z.1, adaptiveAllocation (pick (selector z.1)) z.2 t)

/-- A finite policy selected from the unchanged first input preserves the complete joint law. -/
theorem measurePreserving_indexedAllocation {M R ι α : Type*}
    [MeasurableSpace M] [Fintype R] [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μM : Measure M) [SFinite μM] (μ : ι → Measure α) [∀ i, SigmaFinite (μ i)]
    (selector : M → R) (hselector : ∀ r, MeasurableSet {x | selector x = r})
    (pick : R → List (ι × α) → ι × ι)
    (hfresh : ∀ r t, ∀ x : ι → α,
      (pick r (allocationHistory (pick r) x t)).1 =
          (pick r (allocationHistory (pick r) x t)).2 ∨
      ((pick r (allocationHistory (pick r) x t)).1 ∉
          (allocationHistory (pick r) x t).map Prod.fst ∧
        (pick r (allocationHistory (pick r) x t)).2 ∉
          (allocationHistory (pick r) x t).map Prod.fst))
    (hrate : ∀ r t, ∀ x : ι → α,
      μ (pick r (allocationHistory (pick r) x t)).1 =
        μ (pick r (allocationHistory (pick r) x t)).2)
    (hmeas : ∀ r t pair,
      MeasurableSet {x : ι → α | pick r (allocationHistory (pick r) x t) = pair})
    (t : ℕ) :
    MeasurePreserving (indexedAllocation selector pick t)
      (μM.prod (Measure.pi μ)) (μM.prod (Measure.pi μ)) := by
  let choose (z : M × (ι → α)) := selector z.1
  let T (r : R) : M × (ι → α) → M × (ι → α) := Prod.map id (fun x ↦ adaptiveAllocation (pick r) x t)
  have hc (r : R) : MeasurableSet {z : M × (ι → α) | choose z = r} :=
    measurable_fst (hselector r)
  have hT (r : R) : MeasurePreserving (T r)
      (μM.prod (Measure.pi μ)) (μM.prod (Measure.pi μ)) :=
    (MeasurePreserving.id μM).prod
      (measurePreserving_adaptiveAllocation μ (pick r) (hfresh r) (hrate r) (hmeas r) t)
  have hi (r : R) : T r ⁻¹' {z | choose z = r} = {z | choose z = r} := by
    ext z
    rfl
  have h := measurePreserving_selectedTransform (μM.prod (Measure.pi μ)) choose T hc hT hi
  have heq : selectedTransform choose T = indexedAllocation selector pick t := by
    funext z
    rfl
  rw [heq] at h
  exact h

/-- Currying a finite array turns its product law into the iterated product law. -/
theorem measurePreserving_curry_pi {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace α] (μ : ι → κ → Measure α) [∀ i j, IsProbabilityMeasure (μ i j)] :
    MeasurePreserving (fun x : ι × κ → α ↦ Function.curry x)
      (Measure.pi fun p : ι × κ ↦ μ p.1 p.2)
      (Measure.pi fun i ↦ Measure.pi fun j ↦ μ i j) := by
  refine ⟨by fun_prop, ?_⟩
  have h := Measure.infinitePi_map_curry μ
  simp only [Measure.infinitePi_eq_pi] at h
  exact h

/-- Complete men's rankings, drawn once before the arrival policy runs. -/
abbrev ArrivalRanks (n : ℕ) := Fin n → Equiv.Perm (Fin n)

/-- Source and target coordinates are both oriented as woman then man. -/
abbrev ArrivalCoordinates (n : ℕ) := Fin n × Fin n

/-- A policy reads revealed women's source priorities and may depend on men's full rankings. -/
abbrev ArrivalPicker (n : ℕ) := ArrivalRanks n →
  List (ArrivalCoordinates n × ℝ) → ArrivalCoordinates n × ArrivalCoordinates n

/-- The men's rankings induced by their raw exponential rows. -/
noncomputable def arrivalMenRanks {n : ℕ} (x : Fin n → Fin n → ℝ) : ArrivalRanks n :=
  fun m ↦ exponentialRank (x m)

/-- Every fixed men's ranking tuple has a measurable raw-matrix fiber. -/
theorem measurableSet_arrivalMenRanks_fiber {n : ℕ} (r : ArrivalRanks n) :
    MeasurableSet {x : Fin n → Fin n → ℝ | arrivalMenRanks x = r} := by
  have heq : {x : Fin n → Fin n → ℝ | arrivalMenRanks x = r} =
      Set.univ.pi (fun m ↦ {x | exponentialRank x = r m}) := by
    ext x
    simp [arrivalMenRanks, funext_iff]
  rw [heq]
  exact MeasurableSet.univ_pi fun m ↦ measurableSet_exponentialRank_fiber (r m)

/-- The original independent raw inputs: men's nested rows and women's flat source slots. -/
noncomputable def arrivalInputLaw {n : ℕ} (P Q : Fin n → Fin n → ℝ≥0) :
    Measure ((Fin n → Fin n → ℝ) × (ArrivalCoordinates n → ℝ)) :=
  (Measure.pi fun m ↦ Measure.pi fun w ↦ ProbabilityTheory.expMeasure (P m w : ℝ)).prod
    (Measure.pi fun q : ArrivalCoordinates n ↦ ProbabilityTheory.expMeasure (Q q.2 q.1 : ℝ))

/-- Allocate the women's source priorities, then curry them into the row orientation of the PR. -/
noncomputable def arrivalMatrices {n : ℕ} (pick : ArrivalPicker n) (t : ℕ)
    (z : (Fin n → Fin n → ℝ) × (ArrivalCoordinates n → ℝ)) :
    (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) :=
  let allocated := indexedAllocation arrivalMenRanks pick t z
  (allocated.1, Function.curry allocated.2)

/-- The complete profile obtained by ranking the allocated raw matrices. -/
noncomputable def arrivalProfile {n : ℕ} (pick : ArrivalPicker n) (t : ℕ) :
    ((Fin n → Fin n → ℝ) × (ArrivalCoordinates n → ℝ)) → StableMarriage.Profile n :=
  rankProfile exponentialRank ∘ arrivalMatrices pick t

/-- Structural properties of an arrival allocation. These contain no assumption about its law. -/
structure ArrivalPolicyValid {n : ℕ} (Q : Fin n → Fin n → ℝ≥0) (pick : ArrivalPicker n) :
    Prop where
  fresh : ∀ r t, ∀ x : ArrivalCoordinates n → ℝ,
    (pick r (allocationHistory (pick r) x t)).1 =
        (pick r (allocationHistory (pick r) x t)).2 ∨
    ((pick r (allocationHistory (pick r) x t)).1 ∉
        (allocationHistory (pick r) x t).map Prod.fst ∧
      (pick r (allocationHistory (pick r) x t)).2 ∉
        (allocationHistory (pick r) x t).map Prod.fst)
  score_eq : ∀ r t, ∀ x : ArrivalCoordinates n → ℝ,
    Q (pick r (allocationHistory (pick r) x t)).1.2
        (pick r (allocationHistory (pick r) x t)).1.1 =
      Q (pick r (allocationHistory (pick r) x t)).2.2
        (pick r (allocationHistory (pick r) x t)).2.1
  measurable_fiber : ∀ r t pair,
    MeasurableSet {x : ArrivalCoordinates n → ℝ |
      pick r (allocationHistory (pick r) x t) = pair}

/-- The allocated raw matrices have exactly the independent exponential matrix law. -/
theorem measurePreserving_arrivalMatrices {n : ℕ} (P Q : Fin n → Fin n → ℝ≥0)
    (hP : ∀ m w, 0 < P m w) (hQ : ∀ m w, 0 < Q m w)
    (pick : ArrivalPicker n) (hvalid : ArrivalPolicyValid Q pick) (t : ℕ) :
    MeasurePreserving (arrivalMatrices pick t) (arrivalInputLaw P Q)
      (exponentialMatrixLaw P Q) := by
  have (m w : Fin n) : IsProbabilityMeasure (ProbabilityTheory.expMeasure (P m w : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by exact_mod_cast hP m w)
  have (m w : Fin n) : IsProbabilityMeasure (ProbabilityTheory.expMeasure (Q m w : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by exact_mod_cast hQ m w)
  let μM := Measure.pi fun m ↦ Measure.pi fun w ↦ ProbabilityTheory.expMeasure (P m w : ℝ)
  let μW := fun q : ArrivalCoordinates n ↦ ProbabilityTheory.expMeasure (Q q.2 q.1 : ℝ)
  have hrate (r : ArrivalRanks n) (s : ℕ) (x : ArrivalCoordinates n → ℝ) :
      μW (pick r (allocationHistory (pick r) x s)).1 =
        μW (pick r (allocationHistory (pick r) x s)).2 :=
    congrArg (fun a : ℝ≥0 ↦ ProbabilityTheory.expMeasure (a : ℝ)) (hvalid.score_eq r s x)
  have halloc : MeasurePreserving (indexedAllocation arrivalMenRanks pick t)
      (arrivalInputLaw P Q) (arrivalInputLaw P Q) :=
    measurePreserving_indexedAllocation μM μW arrivalMenRanks
      measurableSet_arrivalMenRanks_fiber pick hvalid.fresh hrate hvalid.measurable_fiber t
  have hcurry : MeasurePreserving
      (Prod.map (id : (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ))
        (fun x : ArrivalCoordinates n → ℝ ↦ Function.curry x))
      (arrivalInputLaw P Q) (exponentialMatrixLaw P Q) :=
    (MeasurePreserving.id μM).prod
      (measurePreserving_curry_pi (fun w m ↦ ProbabilityTheory.expMeasure (Q m w : ℝ)))
  have heq : arrivalMatrices pick t =
      (Prod.map (id : (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ))
        (fun x : ArrivalCoordinates n → ℝ ↦ Function.curry x)) ∘
          indexedAllocation arrivalMenRanks pick t := by
    funext z
    rfl
  rw [heq]
  exact hcurry.comp halloc

/-- A structurally valid exponential-arrival allocator pushes forward to the PR's exact
profile PMF. Neither a model-law equality nor independence of terminal counts is assumed. -/
theorem exponential_arrival_profile_law {n : ℕ} (P Q : Fin n → Fin n → ℝ≥0)
    (hP : ∀ m w, 0 < P m w) (hQ : ∀ m w, 0 < Q m w)
    (pick : ArrivalPicker n) (hvalid : ArrivalPolicyValid Q pick) (t : ℕ) :
    Measure.map (arrivalProfile pick t) (arrivalInputLaw P Q) =
      (RandomRanking.profile P Q).toMeasure := by
  have hraw := measurePreserving_arrivalMatrices P Q hP hQ pick hvalid t
  calc
    Measure.map (arrivalProfile pick t) (arrivalInputLaw P Q) =
        Measure.map (rankProfile exponentialRank)
          (Measure.map (arrivalMatrices pick t) (arrivalInputLaw P Q)) :=
      (Measure.map_map (measurable_rankProfile exponentialRank
        measurableSet_exponentialRank_fiber) hraw.measurable).symm
    _ = _ := by rw [hraw.map_eq, exponential_profile_law P Q hP hQ]

/-- The full arrival construction has exactly the tiered-market law in the original PR. -/
theorem exponential_arrival_market_law {n I J : ℕ} (womanTier : Fin n → Fin I)
    (manTier : Fin n → Fin J) (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (pick : ArrivalPicker n) (hvalid : ArrivalPolicyValid (fun m _ ↦ β (manTier m)) pick)
    (t : ℕ) :
    Measure.map (arrivalProfile pick t)
      (arrivalInputLaw (fun _ w ↦ α (womanTier w)) (fun m _ ↦ β (manTier m))) =
      (Arxiv.«2009.05124».market womanTier manTier α β).toMeasure :=
  exponential_arrival_profile_law _ _ (fun _ w ↦ hα (womanTier w))
    (fun m _ ↦ hβ (manTier m)) pick hvalid t

end Ashlagi
