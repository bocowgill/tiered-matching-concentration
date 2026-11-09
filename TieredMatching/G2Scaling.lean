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

public import TieredMatching.Model
public import TieredMatching.G2Rounding

/-! # Exact score normalization for the uniform G.2 interface

Separate positive score rescaling preserves both the unchanged PR profile law and its exact
proposal coefficient. This supplies a reduction to fixed normalized score bounds. It does not
prove the normalized stochastic G.2 estimate.
-/

@[expose] public section

namespace TieredMatching.G2Scaling

open scoped NNReal ENNReal

/-- Common score rescaling on each side preserves the exact original tiered market PMF. -/
theorem market_scale {n I J : ℕ} (womanTier : Fin n → Fin I) (manTier : Fin n → Fin J)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (c d : ℝ≥0) (hc : c ≠ 0) (hd : d ≠ 0) :
    Arxiv.«2009.05124».market womanTier manTier (fun i ↦ c * α i) (fun j ↦ d * β j) =
      Arxiv.«2009.05124».market womanTier manTier α β :=
  profile_scale (fun _ w ↦ α (womanTier w)) (fun m _ ↦ β (manTier m)) c d hc hd

/-- The exact fixed-woman proposal coefficient is invariant under separate positive score
rescaling. Even zero denominators are handled by the field's literal division convention. -/
theorem proposalCoefficient_scale {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ) (c d : ℝ≥0)
    (hc : c ≠ 0) (hd : d ≠ 0) (i : Fin I) (j : Fin J) :
    proposalCoefficient b (fun i ↦ c * α i) (fun j ↦ d * β j) ((c : ℝ) * αmin) i j =
      proposalCoefficient b α β αmin i j := by
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  unfold proposalCoefficient
  simp only [NNReal.coe_mul]
  rw [mul_div_mul_left _ _ hcR]
  have hrow (k : Fin J) : b k / ((d : ℝ) * (β k : ℝ)) =
      (d : ℝ)⁻¹ * (b k / (β k : ℝ)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [hrow]
  rw [← Finset.mul_sum]
  calc
    _ = ((d : ℝ)⁻¹ * ((α i : ℝ) / αmin * (b j / (β j : ℝ)))) /
        ((d : ℝ)⁻¹ * ∑ k, b k / (β k : ℝ)) := by ring
    _ = _ := mul_div_mul_left _ _ (inv_ne_zero hdR)

/-- Being the attained minimum score is invariant under a positive common rescaling. -/
theorem isMinimumScore_scale_iff {I : ℕ} (α : Fin I → ℝ≥0) (αmin : ℝ)
    (c : ℝ≥0) (hc : 0 < c) :
    IsMinimumScore (fun i ↦ c * α i) ((c : ℝ) * αmin) ↔ IsMinimumScore α αmin := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  constructor
  · rintro ⟨hlower, i, hi⟩
    refine ⟨fun k ↦ (mul_le_mul_iff_right₀ hcR).mp ?_, i, ?_⟩
    · simpa only [NNReal.coe_mul] using hlower k
    · exact mul_left_cancel₀ hcR.ne' (by simpa only [NNReal.coe_mul] using hi)
  · rintro ⟨hlower, i, hi⟩
    refine ⟨fun k ↦ ?_, i, ?_⟩
    · simpa only [NNReal.coe_mul] using mul_le_mul_of_nonneg_left (hlower k) hcR.le
    · simp only [NNReal.coe_mul, hi]

/-- The quantitative uniform fixed-woman G.2 predicate is unchanged by exact positive
rescaling, with the same constants and market-size thresholds. -/
theorem uniformG2Bound_scale_iff {I J : ℕ}
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ) (c d : ℝ≥0)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    UniformG2Bound (fun i ↦ c * α i) (fun j ↦ d * β j) ((c : ℝ) * αmin) ↔
      UniformG2Bound α β αmin := by
  unfold UniformG2Bound
  simp_rw [market_scale _ _ α β c d hc hd,
    proposalCoefficient_scale _ α β αmin c d hc hd]

/-- Fixed score-only witnesses for normalized bounded public scores. The men's lower
normalizing fence need not be attained, and this definition permits an empty men's tier type. -/
structure ScoreNormalization {I J : ℕ} (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ) where
  womanScale : ℝ≥0
  manScale : ℝ≥0
  womanScale_pos : 0 < womanScale
  manScale_pos : 0 < manScale
  A : ℝ
  B : ℝ
  one_le_A : 1 ≤ A
  one_le_B : 1 ≤ B
  scaled_minimum : (womanScale : ℝ) * αmin = 1
  minimum_one : IsMinimumScore (fun i ↦ womanScale * α i) 1
  woman_bounds : ∀ i, 1 ≤ ((womanScale * α i : ℝ≥0) : ℝ) ∧ ((womanScale * α i : ℝ≥0) : ℝ) ≤ A
  man_bounds : ∀ j, 1 ≤ ((manScale * β j : ℝ≥0) : ℝ) ∧ ((manScale * β j : ℝ≥0) : ℝ) ≤ B

/-- Every fixed positive finite score family with its exact attained women's minimum has
fixed positive normalizers and finite bounds on both sides. No population size occurs here. -/
theorem exists_scoreNormalization {I J : ℕ} (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (αmin : ℝ) (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (hmin : IsMinimumScore α αmin) : Nonempty (ScoreNormalization α β αmin) := by
  have hminpos := hmin.pos hα
  obtain ⟨ρ, hρ, hρβ⟩ := exists_share_fence (fun j ↦ (β j : ℝ)) (fun j ↦ by exact_mod_cast hβ j)
  let c : ℝ≥0 := ⟨1 / αmin, (one_div_pos.mpr hminpos).le⟩
  let d : ℝ≥0 := ⟨1 / ρ, (one_div_pos.mpr hρ).le⟩
  have hc : 0 < c := by exact_mod_cast one_div_pos.mpr hminpos
  have hd : 0 < d := by exact_mod_cast one_div_pos.mpr hρ
  have hcmin : (c : ℝ) * αmin = 1 := by
    change (1 / αmin) * αmin = 1
    field_simp
  have hdρ : (d : ℝ) * ρ = 1 := by
    change (1 / ρ) * ρ = 1
    field_simp
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hclower (i : Fin I) : 1 ≤ (c * α i : ℝ≥0) := by
    have hh := mul_le_mul_of_nonneg_left (hmin.1 i) hcR.le
    rw [hcmin] at hh
    exact_mod_cast hh
  have hdlower (j : Fin J) : 1 ≤ (d * β j : ℝ≥0) := by
    have hh := mul_le_mul_of_nonneg_left (hρβ j).le hdR.le
    rw [hdρ] at hh
    exact_mod_cast hh
  let A : ℝ := 1 + ∑ i, ((c * α i : ℝ≥0) : ℝ)
  let B : ℝ := 1 + ∑ j, ((d * β j : ℝ≥0) : ℝ)
  have hA : 1 ≤ A := by
    change 1 ≤ 1 + ∑ i, ((c * α i : ℝ≥0) : ℝ)
    have hh : 0 ≤ ∑ i, ((c * α i : ℝ≥0) : ℝ) := by positivity
    linarith
  have hB : 1 ≤ B := by
    change 1 ≤ 1 + ∑ j, ((d * β j : ℝ≥0) : ℝ)
    have hh : 0 ≤ ∑ j, ((d * β j : ℝ≥0) : ℝ) := by positivity
    linarith
  have hminone : IsMinimumScore (fun i ↦ c * α i) 1 := by
    rw [← hcmin]
    exact (isMinimumScore_scale_iff α αmin c hc).mpr hmin
  refine ⟨⟨c, d, hc, hd, A, B, hA, hB, hcmin, hminone, ?_, ?_⟩⟩
  · intro i
    refine ⟨by exact_mod_cast hclower i, ?_⟩
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun i ↦ ((c * α i : ℝ≥0) : ℝ)) (fun i _ ↦ (c * α i).coe_nonneg) (Finset.mem_univ i)
    change ((c * α i : ℝ≥0) : ℝ) ≤ 1 + ∑ k, ((c * α k : ℝ≥0) : ℝ)
    linarith
  · intro j
    refine ⟨by exact_mod_cast hdlower j, ?_⟩
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun j ↦ ((d * β j : ℝ≥0) : ℝ)) (fun j _ ↦ (d * β j).coe_nonneg) (Finset.mem_univ j)
    change ((d * β j : ℝ≥0) : ℝ) ≤ 1 + ∑ k, ((d * β k : ℝ≥0) : ℝ)
    linarith

/-- A proof of uniform G.2 for these normalized bounded scores transports to the exact
original public scores. This theorem does not supply the normalized stochastic estimate. -/
theorem ScoreNormalization.uniformG2Bound {I J : ℕ} {α : Fin I → ℝ≥0} {β : Fin J → ℝ≥0}
    {αmin : ℝ} (N : ScoreNormalization α β αmin)
    (h : UniformG2Bound (fun i ↦ N.womanScale * α i) (fun j ↦ N.manScale * β j) 1) :
    UniformG2Bound α β αmin := by
  apply (uniformG2Bound_scale_iff α β αmin N.womanScale N.manScale
    N.womanScale_pos.ne' N.manScale_pos.ne').mp
  simpa only [N.scaled_minimum] using h

/-- The original and these fixed normalized scores have precisely equivalent uniform G.2
predicates. This transports an estimate; it is not a stochastic proof of either predicate. -/
theorem ScoreNormalization.uniformG2Bound_iff {I J : ℕ} {α : Fin I → ℝ≥0} {β : Fin J → ℝ≥0}
    {αmin : ℝ} (N : ScoreNormalization α β αmin) :
    UniformG2Bound (fun i ↦ N.womanScale * α i) (fun j ↦ N.manScale * β j) 1 ↔
      UniformG2Bound α β αmin := by
  have hh := uniformG2Bound_scale_iff α β αmin N.womanScale N.manScale
    N.womanScale_pos.ne' N.manScale_pos.ne'
  simpa only [N.scaled_minimum] using hh

/-- Certified reduction to fixed normalized bounded scores, with constants chosen before
any market size or tier maps. The implication retains the exact PR law and coefficient. -/
theorem exists_normalized_reduction {I J : ℕ} (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (αmin : ℝ) (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (hmin : IsMinimumScore α αmin) :
    ∃ N : ScoreNormalization α β αmin,
      (UniformG2Bound (fun i ↦ N.womanScale * α i) (fun j ↦ N.manScale * β j) 1 ↔
        UniformG2Bound α β αmin) := by
  obtain ⟨N⟩ := exists_scoreNormalization α β αmin hα hβ hmin
  exact ⟨N, N.uniformG2Bound_iff⟩

end TieredMatching.G2Scaling
