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

public import TieredMatching.IIDRanking
public import TieredMatching.ProfileLaw

/-! # The exact market law from iid proposal streams and independent women's priorities -/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace TieredMatching

/-- Form a preference profile from independent row sources of possibly different types. -/
def mixedRankProfile {n : ℕ} {M W : Type*}
    (rankM : M → Equiv.Perm (Fin n)) (rankW : W → Equiv.Perm (Fin n))
    (x : (Fin n → M) × (Fin n → W)) : StableMarriage.Profile n :=
  ⟨fun m ↦ rankM (x.1 m), fun w ↦ rankW (x.2 w)⟩

/-- A mixed-source profile fiber is exactly the product of its row fibers. -/
theorem mixedRankProfile_fiber {n : ℕ} {M W : Type*}
    (rankM : M → Equiv.Perm (Fin n)) (rankW : W → Equiv.Perm (Fin n))
    (p : StableMarriage.Profile n) :
    mixedRankProfile rankM rankW ⁻¹' {p} =
      (Set.univ.pi fun m ↦ {x | rankM x = p.manRank m}) ×ˢ
        (Set.univ.pi fun w ↦ {x | rankW x = p.womanRank w}) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod,
    Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq]
  constructor
  · intro h
    exact ⟨fun m ↦ congrFun (congrArg StableMarriage.Profile.manRank h) m,
      fun w ↦ congrFun (congrArg StableMarriage.Profile.womanRank h) w⟩
  · rintro ⟨hM, hW⟩
    cases p
    unfold mixedRankProfile
    congr 1 <;> funext i
    · exact hM i
    · exact hW i

/-- Measurability of each row fiber gives a measurable mixed-source profile. -/
theorem measurable_mixedRankProfile {n : ℕ} {M W : Type*}
    [MeasurableSpace M] [MeasurableSpace W]
    (rankM : M → Equiv.Perm (Fin n)) (rankW : W → Equiv.Perm (Fin n))
    (hM : ∀ r, MeasurableSet {x | rankM x = r})
    (hW : ∀ r, MeasurableSet {x | rankW x = r}) :
    Measurable (mixedRankProfile rankM rankW) := by
  apply measurable_to_countable'
  intro p
  rw [mixedRankProfile_fiber]
  exact (MeasurableSet.univ_pi fun m ↦ hM (p.manRank m)).prod
    (MeasurableSet.univ_pi fun w ↦ hW (p.womanRank w))

/-- Exact row masses and row independence determine the exact PR profile law. -/
theorem mixed_profile_law_of_row_laws {n : ℕ} {M W : Type*}
    [MeasurableSpace M] [MeasurableSpace W]
    (rankM : M → Equiv.Perm (Fin n)) (rankW : W → Equiv.Perm (Fin n))
    (hmM : ∀ r, MeasurableSet {x | rankM x = r})
    (hmW : ∀ r, MeasurableSet {x | rankW x = r})
    (P Q : Fin n → Fin n → ℝ≥0) (hP : ∀ m w, 0 < P m w) (hQ : ∀ m w, 0 < Q m w)
    (μM : Fin n → Measure M) (μW : Fin n → Measure W)
    [∀ m, SigmaFinite (μM m)] [∀ w, SigmaFinite (μW w)]
    (hM : ∀ m r, μM m {x | rankM x = r} =
      (RandomRanking.likelihood (P m) r : ℝ≥0∞))
    (hW : ∀ w r, μW w {x | rankW x = r} =
      (RandomRanking.likelihood (fun m ↦ Q m w) r : ℝ≥0∞)) :
    Measure.map (mixedRankProfile rankM rankW) ((Measure.pi μM).prod (Measure.pi μW)) =
      (RandomRanking.profile P Q).toMeasure := by
  apply Measure.ext_of_singleton
  intro p
  rw [Measure.map_apply (measurable_mixedRankProfile rankM rankW hmM hmW) (by trivial),
    mixedRankProfile_fiber, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi,
    PMF.toMeasure_apply_singleton _ p (by trivial), profile_apply_eq_product P Q hP hQ p]
  simp_rw [hM, hW]
  simp only [ENNReal.coe_mul, ENNReal.ofNNReal_finsetProd]

/-- Independent iid male proposal streams and independent women's exponential rows. -/
noncomputable def rawInputLaw {n : ℕ} [NeZero n] (P Q : Fin n → Fin n → ℝ≥0) :
    Measure ((Fin n → ℕ → Fin n) × (Fin n → Fin n → ℝ)) :=
  (Measure.pi fun m ↦ FirstFresh.iidStream (RandomRanking.ofWeights (P m))).prod
    (Measure.pi fun w ↦ Measure.pi fun m ↦ ProbabilityTheory.expMeasure (Q m w : ℝ))

/-- Turning each male stream into first-occurrence ranks gives exactly the PR profile law. -/
theorem iid_raw_profile_law {n : ℕ} [NeZero n] (P Q : Fin n → Fin n → ℝ≥0)
    (hP : ∀ m w, 0 < P m w) (hQ : ∀ m w, 0 < Q m w) :
    Measure.map (mixedRankProfile IIDRanking.iidRank exponentialRank) (rawInputLaw P Q) =
      (RandomRanking.profile P Q).toMeasure := by
  have (m : Fin n) : IsProbabilityMeasure
      (FirstFresh.iidStream (RandomRanking.ofWeights (P m))) := by
    unfold FirstFresh.iidStream
    infer_instance
  have (m w : Fin n) : IsProbabilityMeasure (ProbabilityTheory.expMeasure (Q m w : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by exact_mod_cast hQ m w)
  exact mixed_profile_law_of_row_laws IIDRanking.iidRank exponentialRank
    IIDRanking.measurableSet_iidRank_fiber measurableSet_exponentialRank_fiber P Q hP hQ
    (fun m ↦ FirstFresh.iidStream (RandomRanking.ofWeights (P m)))
    (fun w ↦ Measure.pi fun m ↦ ProbabilityTheory.expMeasure (Q m w : ℝ))
    (fun m r ↦ IIDRanking.iidRank_singleton (P m) (hP m) r)
    (fun w r ↦ exponentialRank_singleton (fun m ↦ Q m w) (fun m ↦ hQ m w) r)

/-- The raw-stream construction has the exact PR tiered-market probability law. -/
theorem iid_raw_market_law {n I J : ℕ} [NeZero n]
    (womanTier : Fin n → Fin I) (manTier : Fin n → Fin J)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j) :
    Measure.map (mixedRankProfile IIDRanking.iidRank exponentialRank)
      (rawInputLaw (fun _ w ↦ α (womanTier w)) (fun m _ ↦ β (manTier m))) =
      (Arxiv.«2009.05124».market womanTier manTier α β).toMeasure :=
  iid_raw_profile_law _ _ (fun _ w ↦ hα (womanTier w)) (fun m _ ↦ hβ (manTier m))

/-- Every man's actual iid stream has the same distinct initial orders as his PR-law rank. -/
theorem ae_raw_input_prefixes {n : ℕ} [NeZero n] (P Q : Fin n → Fin n → ℝ≥0)
    (hP : ∀ m w, 0 < P m w) :
    ∀ᵐ z ∂rawInputLaw P Q, ∀ m k, k ≤ n →
      (IIDRanking.discoveryList ∅ k (z.1 m)).IsPrefix
        (List.ofFn (IIDRanking.iidRank (z.1 m)).symm) := by
  have hrow (m : Fin n) :
      ∀ᵐ x ∂(Measure.pi fun m ↦ FirstFresh.iidStream (RandomRanking.ofWeights (P m))),
        ∀ k ≤ n, (IIDRanking.discoveryList ∅ k (x m)).IsPrefix
          (List.ofFn (IIDRanking.iidRank (x m)).symm) :=
    (Measure.tendsto_eval_ae_ae (μ := fun m ↦
      FirstFresh.iidStream (RandomRanking.ofWeights (P m))) (i := m)).eventually
        (IIDRanking.ae_discoveryList_prefix_iidRank (P m) (hP m))
  exact Measure.quasiMeasurePreserving_fst.ae (Filter.eventually_all.mpr hrow)

/-- Every woman occurs in each man's actual iid stream almost surely. -/
theorem ae_raw_input_all_candidates {n : ℕ} [NeZero n] (P Q : Fin n → Fin n → ℝ≥0)
    (hP : ∀ m w, 0 < P m w) :
    ∀ᵐ z ∂rawInputLaw P Q, ∀ m w, ∃ t, z.1 m t = w := by
  have hrow (m : Fin n) :
      ∀ᵐ x ∂(Measure.pi fun m ↦ FirstFresh.iidStream (RandomRanking.ofWeights (P m))),
        ∀ w, ∃ t, x m t = w :=
    (Measure.tendsto_eval_ae_ae (μ := fun m ↦
      FirstFresh.iidStream (RandomRanking.ofWeights (P m))) (i := m)).eventually
        (IIDRanking.ae_all_candidates_seen (P m) (hP m))
  exact Measure.quasiMeasurePreserving_fst.ae (Filter.eventually_all.mpr hrow)

end TieredMatching
