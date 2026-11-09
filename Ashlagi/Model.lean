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

public import FormalConjecturesForMathlib.Combinatorics.RandomRanking
public import Mathlib

/-! # Finite normalization facts for the exact weighted-ranking model -/

@[expose] public section

namespace Ashlagi

open StableMarriage RandomRanking
open scoped NNReal ENNReal

/-- Preference profiles are exactly independent men's and women's ranking coordinates. -/
def profileCoordinates (n : ℕ) : Profile n ≃
    ((Fin n → Equiv.Perm (Fin n)) × (Fin n → Equiv.Perm (Fin n))) where
  toFun p := (p.manRank, p.womanRank)
  invFun r := ⟨r.1, r.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The global likelihood normalizer factors into the row normalizers. -/
theorem profile_normalizer {n : ℕ} (P Q : Fin n → Fin n → ℝ≥0) :
    (∑ p : Profile n, (∏ m, likelihood (P m) (p.manRank m)) *
      ∏ w, likelihood (fun m ↦ Q m w) (p.womanRank w)) =
    (∏ m, ∑ r : Equiv.Perm (Fin n), likelihood (P m) r) *
      ∏ w, ∑ r : Equiv.Perm (Fin n), likelihood (fun m ↦ Q m w) r := by
  rw [← (profileCoordinates n).symm.sum_comp]
  simp only [profileCoordinates, Equiv.coe_fn_symm_mk]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  rw [← Fintype.prod_sum, ← Fintype.prod_sum]

/-- Every row normalizer is positive when all public scores are positive. -/
theorem likelihood_total_pos {n : ℕ} (weight : Fin n → ℝ≥0)
    (hw : ∀ x, 0 < weight x) : 0 < ∑ r : Equiv.Perm (Fin n), likelihood weight r := by
  apply Finset.sum_pos'
  · intro r _
    exact zero_le
  · exact ⟨Equiv.refl _, Finset.mem_univ _, likelihood_pos weight hw _⟩

/-- The exact PR profile PMF factors into separately normalized ranking likelihoods. -/
theorem profile_toReal_factorization {n : ℕ} (P Q : Fin n → Fin n → ℝ≥0)
    (hP : ∀ m w, 0 < P m w) (hQ : ∀ m w, 0 < Q m w) (p : Profile n) :
    (profile P Q p).toReal =
      (∏ m, (likelihood (P m) (p.manRank m) : ℝ) /
        ∑ r : Equiv.Perm (Fin n), (likelihood (P m) r : ℝ)) *
      ∏ w, (likelihood (fun m ↦ Q m w) (p.womanRank w) : ℝ) /
        ∑ r : Equiv.Perm (Fin n), (likelihood (fun m ↦ Q m w) r : ℝ) := by
  have htotal : (∑ p : Profile n, (∏ m, likelihood (P m) (p.manRank m)) *
      ∏ w, likelihood (fun m ↦ Q m w) (p.womanRank w)) ≠ 0 := by
    rw [profile_normalizer]
    exact ne_of_gt (mul_pos
      (Finset.prod_pos fun m _ ↦ likelihood_total_pos (P m) (hP m))
      (Finset.prod_pos fun w _ ↦ likelihood_total_pos (fun m ↦ Q m w) (fun m ↦ hQ m w)))
  rw [profile, ofWeights_apply _ htotal, ENNReal.toReal_div]
  simp only [ENNReal.coe_toReal]
  rw [profile_normalizer]
  simp only [NNReal.coe_mul, NNReal.coe_prod, NNReal.coe_sum]
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib, mul_div_mul_comm]

/-- Common positive rescaling leaves a ranking likelihood unchanged. -/
theorem likelihood_scale {n : ℕ} (weight : Fin n → ℝ≥0) (r : Equiv.Perm (Fin n))
    (c : ℝ≥0) (hc : c ≠ 0) : likelihood (fun x ↦ c * weight x) r = likelihood weight r := by
  unfold likelihood
  apply Finset.prod_congr rfl
  intro k _
  rw [← Finset.mul_sum]
  exact mul_div_mul_left _ _ hc

/-- The exact profile PMF is unchanged by independent common rescalings on the two sides. -/
theorem profile_scale {n : ℕ} (P Q : Fin n → Fin n → ℝ≥0) (c d : ℝ≥0)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    profile (fun m w ↦ c * P m w) (fun m w ↦ d * Q m w) = profile P Q := by
  unfold profile
  congr 1
  funext p
  simp_rw [likelihood_scale _ _ c hc, likelihood_scale _ _ d hd]

end Ashlagi
