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

public import TieredMatching.SmoothRates

/-! # Bounded changes in initial-phase acceptance rates -/

@[expose] public section

namespace TieredMatching.InitialRates

/-- Removing already used destinations and changing bounded rewards only on a visited set
changes the unnormalized weighted reward by at most that set's probability mass. -/
theorem masked_rate_difference_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (π f g : ι → ℝ) (used visited : Finset ι)
    (hπ : ∀ w, 0 ≤ π w) (hf : ∀ w, 0 ≤ f w ∧ f w ≤ 1)
    (hg : ∀ w, 0 ≤ g w ∧ g w ≤ 1) (huv : used ⊆ visited)
    (heq : ∀ w, w ∉ visited → g w = f w) :
    |(∑ w with w ∉ used, π w * g w) - ∑ w, π w * f w| ≤ ∑ w ∈ visited, π w := by
  let a (w : ι) := if w ∈ used then 0 else g w
  have hnum : (∑ w with w ∉ used, π w * g w) = ∑ w, π w * a w := by
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : w ∈ used <;> simp only [a, hw, not_true_eq_false, ite_false,
      not_false_eq_true, ite_true, mul_zero]
  rw [hnum, ← Finset.sum_sub_distrib]
  calc
    |∑ w, (π w * a w - π w * f w)| ≤
        ∑ w, |π w * a w - π w * f w| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w, if w ∈ visited then π w else 0 := by
      apply Finset.sum_le_sum
      intro w _
      by_cases hv : w ∈ visited
      · have ha : 0 ≤ a w ∧ a w ≤ 1 := by
          by_cases hu : w ∈ used
          · simp only [a, ite_eq_left hu, le_refl, zero_le_one, and_self]
          · simpa only [a, ite_eq_right hu] using hg w
        have hd : |a w - f w| ≤ 1 := abs_le.mpr ⟨by linarith [(hf w).2, ha.1],
          by linarith [(hf w).1, ha.2]⟩
        rw [ite_eq_left hv, ← mul_sub, abs_mul, abs_of_nonneg (hπ w)]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hd (hπ w)
      · have hu : w ∉ used := fun hw ↦ hv (huv hw)
        simp only [a, ite_eq_right hu, heq w hv, sub_self, abs_zero, ite_eq_right hv, le_refl]
    _ = ∑ w ∈ visited, π w := by simp

/-- Normalizing the remaining destinations preserves a uniform small-visited-set error. -/
theorem normalized_rate_difference_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (π f g : ι → ℝ) (used visited : Finset ι)
    (hπ : ∀ w, 0 ≤ π w) (hsum : ∑ w, π w = 1)
    (hf : ∀ w, 0 ≤ f w ∧ f w ≤ 1) (hg : ∀ w, 0 ≤ g w ∧ g w ≤ 1)
    (huv : used ⊆ visited) (heq : ∀ w, w ∉ visited → g w = f w)
    (hu : (∑ w ∈ used, π w) ≤ 1 / 2) :
    |(∑ w with w ∉ used, π w * g w) / (1 - ∑ w ∈ used, π w) -
        ∑ w, π w * f w| ≤ 4 * ∑ w ∈ visited, π w := by
  let u := ∑ w ∈ used, π w
  let v := ∑ w ∈ visited, π w
  let b := ∑ w, π w * f w
  let c := ∑ w with w ∉ used, π w * g w
  have hu0 : 0 ≤ u := Finset.sum_nonneg fun w _ ↦ hπ w
  have hv0 : 0 ≤ v := Finset.sum_nonneg fun w _ ↦ hπ w
  have huv' : u ≤ v := Finset.sum_le_sum_of_subset_of_nonneg huv (fun w _ _ ↦ hπ w)
  have hb0 : 0 ≤ b := Finset.sum_nonneg fun w _ ↦ mul_nonneg (hπ w) (hf w).1
  have hb1 : b ≤ 1 := by
    rw [← hsum]
    exact Finset.sum_le_sum fun w _ ↦ by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf w).2 (hπ w)
  have hd : |c - b| ≤ v := masked_rate_difference_le π f g used visited hπ hf hg huv heq
  have hden : 0 < 1 - u := by dsimp [u]; linarith
  have hid : c / (1 - u) - b = (c - b + u * b) / (1 - u) := by
    field_simp
    ring
  have hnum : |c - b + u * b| ≤ v + u := by
    have hub : |u * b| ≤ u := by
      rw [abs_of_nonneg (mul_nonneg hu0 hb0)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hb1 hu0
    exact (abs_add_le _ _).trans (add_le_add hd hub)
  have hratio : (v + u) / (1 - u) ≤ 4 * v := by
    apply (div_le_iff₀ hden).2
    have hu' : u ≤ 1 / 2 := hu
    nlinarith [mul_nonneg hv0 (show 0 ≤ 1 / 2 - u by linarith)]
  change |c / (1 - u) - b| ≤ 4 * v
  rw [hid, abs_div, abs_of_pos hden]
  exact (div_le_div_of_nonneg_right hnum hden.le).trans hratio

/-- The total mass of finitely many visited destinations is bounded by their count. -/
theorem visited_mass_le_card {ι : Type*} (π : ι → ℝ) (visited : Finset ι) (πmax : ℝ)
    (hπ : ∀ w ∈ visited, π w ≤ πmax) :
    (∑ w ∈ visited, π w) ≤ (visited.card : ℝ) * πmax := by
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    (Finset.sum_le_sum fun w hw ↦ hπ w hw)

/-- The actual without-replacement acceptance rate stays close to the fixed setup rate
while only a small mass of destinations has been visited. -/
theorem acceptance_rate_drift {ι : Type*} [Fintype ι] [DecidableEq ι]
    (π Γ₀ Γ : ι → ℝ) (used visited : Finset ι) (β : ℝ)
    (hπ : ∀ w, 0 ≤ π w) (hsum : ∑ w, π w = 1)
    (hΓ₀ : ∀ w, 0 ≤ Γ₀ w) (hΓ : ∀ w, 0 ≤ Γ w) (hβ : 0 < β)
    (huv : used ⊆ visited) (heq : ∀ w, w ∉ visited → Γ w = Γ₀ w)
    (hu : (∑ w ∈ used, π w) ≤ 1 / 2) :
    |SmoothRates.rateOn (Finset.univ.filter fun w ↦ w ∉ used) π Γ β /
        (1 - ∑ w ∈ used, π w) - SmoothRates.rate π Γ₀ β| ≤
      4 * ∑ w ∈ visited, π w := by
  have hf (γ : ι → ℝ) (hγ : ∀ w, 0 ≤ γ w) (w : ι) :
      0 ≤ β / (β + γ w) ∧ β / (β + γ w) ≤ 1 := by
    have hd : 0 < β + γ w := add_pos_of_pos_of_nonneg hβ (hγ w)
    exact ⟨div_nonneg hβ.le hd.le, (div_le_one₀ hd).2 (by linarith [hγ w])⟩
  simpa only [SmoothRates.rate, SmoothRates.rateOn] using
    normalized_rate_difference_le π (fun w ↦ β / (β + Γ₀ w))
      (fun w ↦ β / (β + Γ w)) used visited hπ hsum (hf Γ₀ hΓ₀) (hf Γ hΓ) huv
      (fun w hw ↦ by rw [heq w hw]) hu

end TieredMatching.InitialRates
