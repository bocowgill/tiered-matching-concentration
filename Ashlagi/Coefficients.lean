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

public import Ashlagi.SourcePremise
public import Ashlagi.Rates

/-! # The published proposal coefficient and the limiting tier probability -/

@[expose] public section

open Filter
open scoped Topology NNReal ENNReal

namespace Ashlagi

/-- The reciprocal-score denominator in G.2 is strictly positive. -/
theorem reciprocal_score_sum_pos {J : ℕ} (b : Fin J → ℝ) (β : Fin J → ℝ≥0)
    (hb : ∀ j, 0 < b j) (hβ : ∀ j, 0 < β j) (j : Fin J) :
    0 < ∑ h, b h / (β h : ℝ) := by
  apply Finset.sum_pos'
  · intro h _
    exact (div_pos (hb h) (by exact_mod_cast hβ h)).le
  · exact ⟨j, Finset.mem_univ _, div_pos (hb j) (by exact_mod_cast hβ j)⟩

/-- The exact G.2 coefficient is positive under the PR's score and share hypotheses. -/
theorem proposalCoefficient_pos {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ)
    (hb : ∀ j, 0 < b j) (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (hmin : 0 < αmin) (i : Fin I) (j : Fin J) :
    0 < proposalCoefficient b α β αmin i j := by
  exact div_pos (mul_pos (div_pos (by exact_mod_cast hα i) hmin)
    (div_pos (hb j) (by exact_mod_cast hβ j)))
    (reciprocal_score_sum_pos b β hb hβ j)

/-- Weighting G.2 proposal counts by men's scores cancels the reciprocal score. -/
theorem beta_mul_proposalCoefficient {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ)
    (hβ : ∀ j, 0 < β j) (i : Fin I) (j : Fin J) :
    (β j : ℝ) * proposalCoefficient b α β αmin i j =
      (((α i : ℝ) / αmin) / ∑ h, b h / (β h : ℝ)) * b j := by
  have hbj : (β j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hβ j)
  unfold proposalCoefficient
  simp only [div_eq_mul_inv]
  calc
    (β j : ℝ) * ((α i : ℝ) * αmin⁻¹ * (b j * (β j : ℝ)⁻¹) *
      (∑ h, b h * (β h : ℝ)⁻¹)⁻¹) =
      ((α i : ℝ) * αmin⁻¹ * (∑ h, b h * (β h : ℝ)⁻¹)⁻¹) * b j *
        ((β j : ℝ) * (β j : ℝ)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hbj, mul_one]

/-- The asymptotic winning tier probability is exactly its population share. -/
theorem proposal_rate_ratio {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ)
    (hb : ∀ j, 0 < b j) (hbsum : ∑ j, b j = 1)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j) (hmin : 0 < αmin)
    (i : Fin I) (j : Fin J) :
    ((β j : ℝ) * proposalCoefficient b α β αmin i j) /
      (∑ h, (β h : ℝ) * proposalCoefficient b α β αmin i h) = b j := by
  let K := ((α i : ℝ) / αmin) / ∑ h, b h / (β h : ℝ)
  have hK : 0 < K := div_pos (div_pos (by exact_mod_cast hα i) hmin)
    (reciprocal_score_sum_pos b β hb hβ j)
  have hsum : (∑ h, (β h : ℝ) * proposalCoefficient b α β αmin i h) = K := by
    simp_rw [beta_mul_proposalCoefficient b α β αmin hβ i]
    rw [← Finset.mul_sum, hbsum, mul_one]
  rw [hsum, beta_mul_proposalCoefficient b α β αmin hβ i j]
  change K * b j / K = b j
  field_simp [ne_of_gt hK]

/-- Rounding the deterministic reference counts does not change the limiting tier share. -/
theorem reference_tier_probability_tendsto {I J : ℕ} {f : ℕ → ℝ}
    (hf : Tendsto f atTop atTop) (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ)
    (hb : ∀ j, 0 < b j) (hbsum : ∑ j, b j = 1)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j) (hmin : 0 < αmin)
    (i : Fin I) (j : Fin J) :
    Tendsto (fun n ↦ (β j : ℝ) * (⌊proposalCoefficient b α β αmin i j * f n⌋₊ : ℝ) /
      ∑ h, (β h : ℝ) * (⌊proposalCoefficient b α β αmin i h * f n⌋₊ : ℝ))
      atTop (𝓝 (b j)) := by
  have hden : (∑ h, (β h : ℝ) * proposalCoefficient b α β αmin i h) ≠ 0 := by
    apply ne_of_gt
    apply Finset.sum_pos'
    · intro h _
      exact (mul_pos (by exact_mod_cast hβ h)
        (proposalCoefficient_pos b α β αmin hb hα hβ hmin i h)).le
    · exact ⟨j, Finset.mem_univ _, mul_pos (by exact_mod_cast hβ j)
        (proposalCoefficient_pos b α β αmin hb hα hβ hmin i j)⟩
  simpa only [proposal_rate_ratio b α β αmin hb hbsum hα hβ hmin i j] using
    floor_rate_ratio_tendsto hf (fun h ↦ (β h : ℝ))
      (proposalCoefficient b α β αmin i)
      (proposalCoefficient_pos b α β αmin hb hα hβ hmin i) hden j

/-- Rounding changes the deterministic G.2 coefficient by a quantity tending to zero.
This controls the normalizing constants, not uniformity of the stochastic estimate. -/
theorem rounded_proposalCoefficient_tendsto {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ)
    (hb : ∀ j, 0 < b j) (hβ : ∀ j, 0 < β j)
    (count : ℕ → Fin J → ℕ)
    (hcount : ∀ n j, |(count n j : ℝ) - n * b j| ≤ 1) (i : Fin I) (j : Fin J) :
    Tendsto (fun n ↦ proposalCoefficient (fun h ↦ (count n h : ℝ) / n) α β αmin i j)
      atTop (𝓝 (proposalCoefficient b α β αmin i j)) := by
  unfold proposalCoefficient
  apply Tendsto.div
  · exact tendsto_const_nhds.mul
      ((rounded_share_tendsto (fun n ↦ count n j) (b j) (fun n ↦ hcount n j)).div_const _)
  · exact tendsto_finsetSum Finset.univ (fun h _ ↦
      (rounded_share_tendsto (fun n ↦ count n h) (b h) (fun n ↦ hcount n h)).div_const _)
  · exact ne_of_gt (reciprocal_score_sum_pos b β hb hβ j)

end Ashlagi
