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

public import Mathlib

/-! # Deterministic asymptotics of the proposal-count prefixes -/

@[expose] public section

open Filter
open scoped Topology

namespace TieredMatching

/-- Scaling the floor of a positive linear function does not change its asymptotic slope. -/
theorem floor_mul_div_tendsto {f : ℕ → ℝ} (hf : Tendsto f atTop atTop)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n ↦ (⌊c * f n⌋₊ : ℝ) / f n) atTop (𝓝 c) := by
  have hcf : Tendsto (fun n ↦ c * f n) atTop atTop := hf.const_mul_atTop hc
  have h := (tendsto_nat_floor_div_atTop.comp hcf).mul_const c
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [hf.eventually_gt_atTop 0] with n hn
  dsimp only [Function.comp_apply]
  field_simp [ne_of_gt hc, ne_of_gt hn]

/-- The ceiling analogue of `floor_mul_div_tendsto`. -/
theorem ceil_mul_div_tendsto {f : ℕ → ℝ} (hf : Tendsto f atTop atTop)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n ↦ (⌈c * f n⌉₊ : ℝ) / f n) atTop (𝓝 c) := by
  have hcf : Tendsto (fun n ↦ c * f n) atTop atTop := hf.const_mul_atTop hc
  have h := (tendsto_nat_ceil_div_atTop.comp hcf).mul_const c
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [hf.eventually_gt_atTop 0] with n hn
  dsimp only [Function.comp_apply]
  field_simp [ne_of_gt hc, ne_of_gt hn]

/-- Every deterministic central prefix is nonempty eventually. -/
theorem eventually_floor_mul_pos {f : ℕ → ℝ} (hf : Tendsto f atTop atTop)
    {c : ℝ} (hc : 0 < c) : ∀ᶠ n in atTop, 0 < ⌊c * f n⌋₊ := by
  filter_upwards [(hf.const_mul_atTop hc).eventually_ge_atTop 1] with n hn
  exact Nat.floor_pos.mpr hn

/-- Fixed integer prefixes have the limiting ratio of their total tier rates. -/
theorem floor_rate_ratio_tendsto {ι : Type*} [Fintype ι] {f : ℕ → ℝ}
    (hf : Tendsto f atTop atTop) (β c : ι → ℝ) (hc : ∀ j, 0 < c j)
    (hden : ∑ j, β j * c j ≠ 0) (j : ι) :
    Tendsto (fun n ↦ β j * (⌊c j * f n⌋₊ : ℝ) /
      ∑ h, β h * (⌊c h * f n⌋₊ : ℝ)) atTop (𝓝 (β j * c j / ∑ h, β h * c h)) := by
  have hnum := (floor_mul_div_tendsto hf (hc j)).const_mul (β j)
  have hsum := tendsto_finsetSum Finset.univ (fun h _ ↦
    (floor_mul_div_tendsto hf (hc h)).const_mul (β h))
  have h := hnum.div hsum hden
  apply h.congr'
  filter_upwards [hf.eventually_gt_atTop 0] with n hn
  simp only [← mul_div_assoc, ← Finset.sum_div]
  exact div_div_div_cancel_right₀ (ne_of_gt hn) _ _

/-- An error of at most one in each integer tier count gives the stipulated limiting share. -/
theorem rounded_share_tendsto (v : ℕ → ℕ) (a : ℝ)
    (h : ∀ n, |(v n : ℝ) - n * a| ≤ 1) :
    Tendsto (fun n ↦ (v n : ℝ) / n) atTop (𝓝 a) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnε : 1 < (n : ℝ) * ε := by
    apply (div_lt_iff₀ hε).mp
    exact lt_of_lt_of_le hN (Nat.cast_le.mpr hnN)
  have hb := abs_le.mp (h n)
  rw [Real.dist_eq, abs_lt]
  constructor
  · have : a - ε < (v n : ℝ) / n := (lt_div_iff₀ hnpos).mpr (by nlinarith)
    linarith
  · have : (v n : ℝ) / n < a + ε := (div_lt_iff₀ hnpos).mpr (by nlinarith)
    linarith

/-- The two-limit step: a fixed central coupling error vanishes if every positive
sandwich tolerance bounds it by a sequence tending to its exponential-shell probability. -/
theorem tendsto_zero_of_shell_bounds (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n)
    (h : ∀ η : ℝ, 0 < η → η < 1 → ∃ r : ℕ → ℝ,
      Tendsto r atTop (𝓝 (2 * η / (1 + η))) ∧ ∀ᶠ n in atTop, d n ≤ r n) :
    Tendsto d atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let η := min (ε / 4) (1 / 2 : ℝ)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hη1 : η < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨r, hr, hdr⟩ := h η hη hη1
  have hsmall : 2 * η / (1 + η) < ε := by
    have he : η ≤ ε / 4 := min_le_left _ _
    have hb : 2 * η / (1 + η) ≤ 2 * η := div_le_self (by positivity) (by linarith)
    linarith
  have hrε : ∀ᶠ n in atTop, r n < ε := hr (gt_mem_nhds hsmall)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hdr.and hrε)
  refine ⟨N, ?_⟩
  intro n hn
  simpa [Real.dist_eq, abs_of_nonneg (hd n)] using
    (lt_of_le_of_lt (hN n hn).1 (hN n hn).2)

/-- A tier with a positive limiting share is nonempty for all sufficiently large markets. -/
theorem rounded_count_eventually_pos (v : ℕ → ℕ) (a : ℝ) (ha : 0 < a)
    (h : ∀ n, |(v n : ℝ) - n * a| ≤ 1) : ∀ᶠ n in atTop, 0 < v n := by
  have hp : ∀ᶠ n in atTop, 0 < (v n : ℝ) / n :=
    (rounded_share_tendsto v a h) (lt_mem_nhds ha)
  filter_upwards [hp] with n hn
  by_contra hz
  have hzero : v n = 0 := Nat.eq_zero_of_not_pos hz
  simp [hzero] at hn

end TieredMatching
