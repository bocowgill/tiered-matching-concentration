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

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Deterministic ordinal acceptance-rate bounds

These numerical inequalities apply to the acceptance probabilities supplied by an ordinal
history law. They make no assertion about conditioning on raw scores or future events.
-/

@[expose] public section

namespace TieredMatching
namespace SmoothRates

/-- The acceptance rate on a specified set of fresh destinations. -/
noncomputable def rateOn {W : Type*} (F : Finset W) (π Γ : W → ℝ) (β : ℝ) : ℝ :=
  ∑ w ∈ F, π w * (β / (β + Γ w))

/-- A popularity score at least one can only increase the acceptance probability. -/
theorem one_div_one_add_le {β γ : ℝ} (hβ : 1 ≤ β) (hγ : 0 ≤ γ) :
    1 / (1 + γ) ≤ β / (β + γ) := by
  apply (div_le_div_iff₀ (by positivity : 0 < 1 + γ) (by linarith : 0 < β + γ)).2
  nlinarith

/-- The score-one rate also upper bounds the score-normalized acceptance probability. -/
theorem popularity_div_add_le {β γ : ℝ} (hβ : 1 ≤ β) (hγ : 0 ≤ γ) :
    β / (β + γ) ≤ β / (1 + γ) := by
  exact div_le_div_of_nonneg_left (by linarith : 0 ≤ β) (by positivity)
    (by linarith : 1 + γ ≤ β + γ)

/-- A finite harmonic-mean bound for fresh destinations; no renormalization of their mass
is performed. The empty-set case is included. -/
theorem fresh_rate_lower {W : Type*} (F : Finset W) (π Γ : W → ℝ)
    {β πmin : ℝ} (hβ : 1 ≤ β) (hπmin : 0 ≤ πmin)
    (hπ : ∀ w ∈ F, πmin ≤ π w) (hΓ : ∀ w ∈ F, 0 ≤ Γ w) :
    πmin * (F.card : ℝ) ^ 2 / ((F.card : ℝ) + ∑ w ∈ F, Γ w) ≤ rateOn F π Γ β := by
  have hj := Finset.sq_sum_div_le_sum_sq_div F (fun _ ↦ (1 : ℝ))
    (g := fun w ↦ 1 + Γ w) (fun w hw ↦ by linarith [hΓ w hw])
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, one_pow,
    Finset.sum_add_distrib] at hj
  calc
    πmin * (F.card : ℝ) ^ 2 / ((F.card : ℝ) + ∑ w ∈ F, Γ w) =
        πmin * ((F.card : ℝ) ^ 2 / ((F.card : ℝ) + ∑ w ∈ F, Γ w)) := by ring
    _ ≤ πmin * ∑ w ∈ F, 1 / (1 + Γ w) := mul_le_mul_of_nonneg_left hj hπmin
    _ = ∑ w ∈ F, πmin * (1 / (1 + Γ w)) := Finset.mul_sum ..
    _ ≤ rateOn F π Γ β := by
      apply Finset.sum_le_sum
      intro w hw
      exact mul_le_mul (hπ w hw) (one_div_one_add_le hβ (hΓ w hw))
        (div_nonneg zero_le_one (by linarith [hΓ w hw])) (hπmin.trans (hπ w hw))

/-- The full rate for a finite destination population. -/
noncomputable def rate {W : Type*} [Fintype W] (π Γ : W → ℝ) (β : ℝ) : ℝ :=
  ∑ w, π w * (β / (β + Γ w))

/-- Nonnegative destination masses give a nonnegative acceptance rate. -/
theorem rate_nonneg {W : Type*} [Fintype W] (π Γ : W → ℝ)
    {β : ℝ} (hβ : 1 ≤ β) (hπ : ∀ w, 0 ≤ π w) (hΓ : ∀ w, 0 ≤ Γ w) :
    0 ≤ rate π Γ β := by
  exact Finset.sum_nonneg fun w _ ↦
    mul_nonneg (hπ w) (div_nonneg (by linarith) (by linarith [hΓ w]))

/-- The score-one rate is a lower bound for every rescaled popularity score. -/
theorem rate_one_le {W : Type*} [Fintype W] (π Γ : W → ℝ)
    {β : ℝ} (hβ : 1 ≤ β) (hπ : ∀ w, 0 ≤ π w) (hΓ : ∀ w, 0 ≤ Γ w) :
    rate π Γ 1 ≤ rate π Γ β := by
  apply Finset.sum_le_sum
  intro w _
  exact mul_le_mul_of_nonneg_left (one_div_one_add_le hβ (hΓ w)) (hπ w)

/-- Score-normalized rates are at most the score-one rate. -/
theorem rate_le_popularity_mul_one {W : Type*} [Fintype W] (π Γ : W → ℝ)
    {β : ℝ} (hβ : 1 ≤ β) (hπ : ∀ w, 0 ≤ π w) (hΓ : ∀ w, 0 ≤ Γ w) :
    rate π Γ β ≤ β * rate π Γ 1 := by
  unfold rate
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w _
  have hh := mul_le_mul_of_nonneg_left (popularity_div_add_le hβ (hΓ w)) (hπ w)
  convert hh using 1
  ring

/-- Positive total destination mass makes the score-one acceptance rate strictly positive. -/
theorem rate_one_pos {W : Type*} [Fintype W] (π Γ : W → ℝ)
    (hπ : ∀ w, 0 ≤ π w) (hΓ : ∀ w, 0 ≤ Γ w) (hmass : 0 < ∑ w, π w) :
    0 < rate π Γ 1 := by
  have hex : ∃ w, 0 < π w := by
    by_contra h
    have h0 : ∀ w, π w ≤ 0 := fun w ↦ le_of_not_gt (fun hw ↦ h ⟨w, hw⟩)
    have hs := Finset.sum_nonpos (s := Finset.univ) (fun w _ ↦ h0 w)
    linarith
  obtain ⟨w, hw⟩ := hex
  apply Finset.sum_pos'
  · intro v _
    exact mul_nonneg (hπ v) (div_nonneg zero_le_one (by linarith [hΓ v]))
  · exact ⟨w, Finset.mem_univ _, mul_pos hw (div_pos zero_lt_one (by linarith [hΓ w]))⟩

/-- On a high-weight destination the popularity scaling error has a small relative bound. -/
theorem pointwise_scaling_gap_le_high {β γ g : ℝ}
    (hβ : 1 ≤ β) (hg : 0 < g) (hγg : g ≤ γ) :
    β / (1 + γ) - β / (β + γ) ≤ (β - 1) / g * (β / (1 + γ)) := by
  have hβ0 : 0 < β := by linarith
  have hγ : 0 ≤ γ := le_trans hg.le hγg
  have hfactor : β / (1 + γ) - β / (β + γ) =
      β / (1 + γ) * ((β - 1) / (β + γ)) := by
    field_simp [show 1 + γ ≠ 0 by positivity, show β + γ ≠ 0 by positivity]
    ring
  rw [hfactor]
  have hratio := div_le_div_of_nonneg_left (sub_nonneg.mpr hβ) hg
    (show g ≤ β + γ by linarith)
  have hm := mul_le_mul_of_nonneg_left hratio
    (div_nonneg hβ0.le (by positivity : 0 ≤ 1 + γ))
  simpa only [mul_comm] using hm

/-- Without a high-weight assumption the scaling error is bounded by the score itself. -/
theorem pointwise_scaling_gap_le_score {β γ : ℝ} (hβ : 1 ≤ β) (hγ : 0 ≤ γ) :
    β / (1 + γ) - β / (β + γ) ≤ β := by
  have hβ0 : 0 ≤ β := by linarith
  have hbase : β / (1 + γ) ≤ β := by
    apply (div_le_iff₀ (by positivity : 0 < 1 + γ)).2
    nlinarith
  have hp : 0 ≤ β / (β + γ) := div_nonneg hβ0 (by linarith)
  linarith

/-- The full scaling error separates into a high-weight error and the mass of low destinations. -/
theorem scaling_gap_le {W : Type*} [Fintype W] (π Γ : W → ℝ) (low : Finset W)
    {β g : ℝ} (hβ : 1 ≤ β) (hg : 0 < g)
    (hπ : ∀ w, 0 ≤ π w) (hΓ : ∀ w, 0 ≤ Γ w)
    (hhigh : ∀ w, w ∉ low → g ≤ Γ w) :
    β * rate π Γ 1 - rate π Γ β ≤
      (β - 1) / g * (β * rate π Γ 1) + β * ∑ w ∈ low, π w := by
  classical
  have hc : 0 ≤ (β - 1) / g := div_nonneg (sub_nonneg.mpr hβ) hg.le
  have hβ0 : 0 ≤ β := by linarith
  have hpoint (w : W) : β / (1 + Γ w) - β / (β + Γ w) ≤
      (β - 1) / g * (β / (1 + Γ w)) + if w ∈ low then β else 0 := by
    by_cases hw : w ∈ low
    · rw [ite_eq_left hw]
      have hh := pointwise_scaling_gap_le_score hβ (hΓ w)
      have hn : 0 ≤ (β - 1) / g * (β / (1 + Γ w)) :=
        mul_nonneg hc (div_nonneg hβ0 (by linarith [hΓ w]))
      linarith
    · rw [ite_eq_right hw, add_zero]
      exact pointwise_scaling_gap_le_high hβ hg (hhigh w hw)
  have heq : β * rate π Γ 1 - rate π Γ β =
      ∑ w, π w * (β / (1 + Γ w) - β / (β + Γ w)) := by
    unfold rate
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro w _
    ring
  have hlow : (∑ w, π w * (if w ∈ low then β else 0)) = β * ∑ w ∈ low, π w := by
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_ite_mem_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [heq]
  calc
    _ ≤ ∑ w, π w * ((β - 1) / g * (β / (1 + Γ w)) +
        if w ∈ low then β else 0) :=
      Finset.sum_le_sum fun w _ ↦ mul_le_mul_of_nonneg_left (hpoint w) (hπ w)
    _ = (β - 1) / g * (β * rate π Γ 1) + β * ∑ w ∈ low, π w := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, hlow]
      congr 1
      unfold rate
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring

/-- A scalar reciprocal comparison that does not divide by a possibly zero rate. -/
theorem reciprocal_gap_le {β p q c ℓ : ℝ}
    (hβ : 1 ≤ β) (hp : 0 < p) (hpq : p ≤ q) (hqβ : q ≤ β * p)
    (hc : 0 ≤ c) (hℓ : 0 ≤ ℓ)
    (hgap : β * p - q ≤ c * (β * p) + β * ℓ) :
    |1 / q - 1 / (β * p)| ≤ c / p + ℓ / p ^ 2 := by
  have hβ0 : 0 < β := by linarith
  have hq0 : 0 < q := hp.trans_le hpq
  have hβp : 0 < β * p := mul_pos hβ0 hp
  have hd : 0 < β * p * q := mul_pos hβp hq0
  have hn : 0 ≤ 1 / q - 1 / (β * p) :=
    sub_nonneg.mpr (one_div_le_one_div_of_le hq0 hqβ)
  have heq : 1 / q - 1 / (β * p) = (β * p - q) / (β * p * q) := by
    field_simp
  rw [abs_of_nonneg hn, heq]
  calc
    (β * p - q) / (β * p * q) ≤ (c * (β * p) + β * ℓ) / (β * p * q) :=
      div_le_div_of_nonneg_right hgap hd.le
    _ = c / q + ℓ / (p * q) := by field_simp
    _ ≤ c / p + ℓ / p ^ 2 := by
      apply add_le_add (div_le_div_of_nonneg_left hc hp hpq)
      exact div_le_div_of_nonneg_left hℓ (sq_pos_of_pos hp) (by nlinarith)

/-- Reciprocal acceptance rates differ from exact inverse-popularity scaling by an explicit
high-weight term and low-mass term. -/
theorem reciprocal_scaling_error_le {W : Type*} [Fintype W]
    (π Γ : W → ℝ) (low : Finset W) {β g : ℝ}
    (hβ : 1 ≤ β) (hg : 0 < g) (hπ : ∀ w, 0 ≤ π w) (hΓ : ∀ w, 0 ≤ Γ w)
    (hmass : 0 < ∑ w, π w) (hhigh : ∀ w, w ∉ low → g ≤ Γ w) :
    |1 / rate π Γ β - 1 / (β * rate π Γ 1)| ≤
      (β - 1) / (g * rate π Γ 1) + (∑ w ∈ low, π w) / (rate π Γ 1) ^ 2 := by
  have hp := rate_one_pos π Γ hπ hΓ hmass
  have hlow : 0 ≤ ∑ w ∈ low, π w := Finset.sum_nonneg fun w _ ↦ hπ w
  have hraw := reciprocal_gap_le hβ hp (rate_one_le π Γ hβ hπ hΓ)
    (rate_le_popularity_mul_one π Γ hβ hπ hΓ)
    (div_nonneg (sub_nonneg.mpr hβ) hg.le) hlow
    (scaling_gap_le π Γ low hβ hg hπ hΓ hhigh)
  simpa only [div_div] using hraw

/-- A purely numerical uniform bound for the two reciprocal error terms at logarithmic scale. -/
theorem reciprocal_error_terms_le_uniform {β B g p ℓ L cg cp C : ℝ}
    (hβ : 1 ≤ β) (hβB : β ≤ B) (hL : 0 < L) (hcg : 0 < cg) (hcp : 0 < cp)
    (hg : cg * L ≤ g) (hp : cp / L ≤ p) (hℓ : 0 ≤ ℓ) (hlow : ℓ * L ^ 2 ≤ C) :
    (β - 1) / (g * p) + ℓ / p ^ 2 ≤ (B - 1) / (cg * cp) + C / cp ^ 2 := by
  have hg0 : 0 < g := (mul_pos hcg hL).trans_le hg
  have hp0 : 0 < p := (div_pos hcp hL).trans_le hp
  have hgp : cg * cp ≤ g * p := by
    have hm := mul_le_mul hg hp (div_nonneg hcp.le hL.le) hg0.le
    have heq : cg * L * (cp / L) = cg * cp := by field_simp
    rwa [heq] at hm
  have hhigh : (β - 1) / (g * p) ≤ (B - 1) / (cg * cp) := by
    calc
      _ ≤ (B - 1) / (g * p) :=
        div_le_div_of_nonneg_right (by linarith : β - 1 ≤ B - 1)
          (mul_nonneg hg0.le hp0.le)
      _ ≤ _ := div_le_div_of_nonneg_left (by linarith : 0 ≤ B - 1)
        (mul_pos hcg hcp) hgp
  have hpl : cp ≤ p * L := (div_le_iff₀ hL).mp hp
  have hsquare : cp ^ 2 ≤ p ^ 2 * L ^ 2 := by
    nlinarith [mul_self_le_mul_self hcp.le hpl]
  have hlow' : ℓ / p ^ 2 ≤ C / cp ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hp0) (sq_pos_of_pos hcp)).2
    have h₁ := mul_le_mul_of_nonneg_left hsquare hℓ
    have h₂ := mul_le_mul_of_nonneg_left hlow (sq_nonneg p)
    nlinarith
  exact add_le_add hhigh hlow'

/-- Smooth high weights, a score-one rate lower bound, and a squared-scale low-mass bound
give a uniform constant error in inverse-popularity scaling. -/
theorem reciprocal_scaling_error_le_uniform {W : Type*} [Fintype W]
    (π Γ : W → ℝ) (low : Finset W) {β B g L cg cp C : ℝ}
    (hβ : 1 ≤ β) (hβB : β ≤ B) (hL : 0 < L) (hcg : 0 < cg) (hcp : 0 < cp)
    (hπ : ∀ w, 0 ≤ π w) (hΓ : ∀ w, 0 ≤ Γ w) (hmass : 0 < ∑ w, π w)
    (hhigh : ∀ w, w ∉ low → g ≤ Γ w)
    (hg : cg * L ≤ g) (hp : cp / L ≤ rate π Γ 1)
    (hlow : (∑ w ∈ low, π w) * L ^ 2 ≤ C) :
    |1 / rate π Γ β - 1 / (β * rate π Γ 1)| ≤
      (B - 1) / (cg * cp) + C / cp ^ 2 := by
  have hg0 : 0 < g := (mul_pos hcg hL).trans_le hg
  refine (reciprocal_scaling_error_le π Γ low hβ hg0 hπ hΓ hmass hhigh).trans ?_
  exact reciprocal_error_terms_le_uniform hβ hβB hL hcg hcp hg hp
    (Finset.sum_nonneg fun w _ ↦ hπ w) hlow

/-- Smooth-state score-one rates are bounded above by the low mass and inverse high weight. -/
theorem rate_one_upper {W : Type*} [Fintype W]
    (π Γ : W → ℝ) (low : Finset W) {g : ℝ}
    (hg : 0 < g) (hπ : ∀ w, 0 ≤ π w) (hΓ : ∀ w, 0 ≤ Γ w)
    (hmass : ∑ w, π w = 1) (hhigh : ∀ w, w ∉ low → g ≤ Γ w) :
    rate π Γ 1 ≤ (∑ w ∈ low, π w) + 1 / g := by
  classical
  have hp (w : W) : 1 / (1 + Γ w) ≤ 1 / g + if w ∈ low then 1 else 0 := by
    by_cases hw : w ∈ low
    · rw [ite_eq_left hw]
      have hh : 1 / (1 + Γ w) ≤ 1 := by
        simpa only [div_one] using one_div_le_one_div_of_le zero_lt_one
          (show 1 ≤ 1 + Γ w by linarith [hΓ w])
      have hn : 0 ≤ 1 / g := by positivity
      linarith
    · rw [ite_eq_right hw, add_zero]
      exact one_div_le_one_div_of_le hg (show g ≤ 1 + Γ w by linarith [hhigh w hw])
  have hlow : (∑ w, π w * (if w ∈ low then (1 : ℝ) else 0)) = ∑ w ∈ low, π w := by
    simp_rw [mul_ite, mul_one, mul_zero]
    exact Finset.sum_ite_mem_eq _ _
  calc
    rate π Γ 1 ≤ ∑ w, π w * (1 / g + if w ∈ low then 1 else 0) :=
      Finset.sum_le_sum fun w _ ↦ mul_le_mul_of_nonneg_left (hp w) (hπ w)
    _ = (∑ w, π w) * (1 / g) + ∑ w ∈ low, π w := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, hlow, Finset.sum_mul]
    _ = (∑ w ∈ low, π w) + 1 / g := by rw [hmass]; ring

end SmoothRates
end TieredMatching
