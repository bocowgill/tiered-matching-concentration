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

public import Ashlagi.RankingLaw
public import Ashlagi.ExponentialOrder
public import Ashlagi.SourcePremise
public import Mathlib

/-! # Exact profile law from independent ranking rows -/

@[expose] public section

namespace Ashlagi

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Rank each row of the independent men's and women's raw priority matrices. -/
def rankProfile {n : ℕ} (rank : (Fin n → ℝ) → Equiv.Perm (Fin n))
    (x : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ)) : StableMarriage.Profile n :=
  ⟨fun m ↦ rank (x.1 m), fun w ↦ rank (x.2 w)⟩

/-- A profile fiber is the Cartesian product of its row-ranking fibers. -/
theorem rankProfile_preimage_singleton {n : ℕ}
    (rank : (Fin n → ℝ) → Equiv.Perm (Fin n)) (p : StableMarriage.Profile n) :
    rankProfile rank ⁻¹' {p} =
      (Set.univ.pi fun m ↦ {x | rank x = p.manRank m}) ×ˢ
        (Set.univ.pi fun w ↦ {x | rank x = p.womanRank w}) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod,
    Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq]
  constructor
  · intro h
    constructor
    · intro m
      exact congrFun (congrArg StableMarriage.Profile.manRank h) m
    · intro w
      exact congrFun (congrArg StableMarriage.Profile.womanRank h) w
  · rintro ⟨hM, hW⟩
    cases p
    unfold rankProfile
    congr 1 <;> funext i
    · exact hM i
    · exact hW i

/-- Measurable row-ranking fibers suffice for a measurable profile map. -/
theorem measurable_rankProfile {n : ℕ}
    (rank : (Fin n → ℝ) → Equiv.Perm (Fin n))
    (hrank : ∀ r, MeasurableSet {x | rank x = r}) : Measurable (rankProfile rank) := by
  apply measurable_to_countable'
  intro p
  rw [rankProfile_preimage_singleton]
  exact (MeasurableSet.univ_pi fun m ↦ hrank (p.manRank m)).prod
    (MeasurableSet.univ_pi fun w ↦ hrank (p.womanRank w))

/-- Independent rows with the exact successive-draw masses give the PR's exact profile PMF. -/
theorem profile_law_of_row_laws {n : ℕ}
    (rank : (Fin n → ℝ) → Equiv.Perm (Fin n))
    (hrank : ∀ r, MeasurableSet {x | rank x = r})
    (P Q : Fin n → Fin n → ℝ≥0) (hP : ∀ m w, 0 < P m w) (hQ : ∀ m w, 0 < Q m w)
    (μM μW : Fin n → Measure (Fin n → ℝ))
    [∀ m, SigmaFinite (μM m)] [∀ w, SigmaFinite (μW w)]
    (hM : ∀ m r, μM m {x | rank x = r} =
      (RandomRanking.likelihood (P m) r : ℝ≥0∞))
    (hW : ∀ w r, μW w {x | rank x = r} =
      (RandomRanking.likelihood (fun m ↦ Q m w) r : ℝ≥0∞)) :
    Measure.map (rankProfile rank) ((Measure.pi μM).prod (Measure.pi μW)) =
      (RandomRanking.profile P Q).toMeasure := by
  apply Measure.ext_of_singleton
  intro p
  rw [Measure.map_apply (measurable_rankProfile rank hrank) (by trivial),
    rankProfile_preimage_singleton, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi,
    PMF.toMeasure_apply_singleton _ p (by trivial), profile_apply_eq_product P Q hP hQ p]
  simp_rw [hM, hW]
  simp only [ENNReal.coe_mul, ENNReal.ofNNReal_finsetProd]

/-- Independent raw exponential matrices for the two sides of a market. -/
noncomputable def exponentialMatrixLaw {n : ℕ} (P Q : Fin n → Fin n → ℝ≥0) :
    Measure ((Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ)) :=
  (Measure.pi fun m ↦ Measure.pi fun w ↦ ProbabilityTheory.expMeasure (P m w : ℝ)).prod
    (Measure.pi fun w ↦ Measure.pi fun m ↦ ProbabilityTheory.expMeasure (Q m w : ℝ))

/-- Sorting independent exponential rows pushes forward to the exact PR profile PMF. -/
theorem exponential_profile_law {n : ℕ} (P Q : Fin n → Fin n → ℝ≥0)
    (hP : ∀ m w, 0 < P m w) (hQ : ∀ m w, 0 < Q m w) :
    Measure.map (rankProfile exponentialRank) (exponentialMatrixLaw P Q) =
      (RandomRanking.profile P Q).toMeasure := by
  have (m w : Fin n) : IsProbabilityMeasure (ProbabilityTheory.expMeasure (P m w : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by exact_mod_cast hP m w)
  have (m w : Fin n) : IsProbabilityMeasure (ProbabilityTheory.expMeasure (Q m w : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by exact_mod_cast hQ m w)
  exact profile_law_of_row_laws exponentialRank measurableSet_exponentialRank_fiber P Q hP hQ
    (fun m ↦ Measure.pi fun w ↦ ProbabilityTheory.expMeasure (P m w : ℝ))
    (fun w ↦ Measure.pi fun m ↦ ProbabilityTheory.expMeasure (Q m w : ℝ))
    (fun m r ↦ exponentialRank_singleton (P m) (hP m) r)
    (fun w r ↦ exponentialRank_singleton (fun m ↦ Q m w) (fun m ↦ hQ m w) r)

/-- The exponential representation uses exactly the PR's tiered-market probability law. -/
theorem exponential_market_law {n I J : ℕ} (womanTier : Fin n → Fin I)
    (manTier : Fin n → Fin J) (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j) :
    Measure.map (rankProfile exponentialRank)
      (exponentialMatrixLaw (fun _ w ↦ α (womanTier w)) (fun m _ ↦ β (manTier m))) =
      (Arxiv.«2009.05124».market womanTier manTier α β).toMeasure :=
  exponential_profile_law _ _ (fun _ w ↦ hα (womanTier w)) (fun m _ ↦ hβ (manTier m))

end Ashlagi
