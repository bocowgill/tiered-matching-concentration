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

public import Ashlagi.Model

/-! # Normalization of successive weighted complete rankings -/

@[expose] public section

namespace Ashlagi

open RandomRanking
open scoped NNReal ENNReal

/-- Successive-draw likelihood indexed by a permutation listing candidates in order. -/
noncomputable def orderedLikelihood {n : ℕ} (weight : Fin n → ℝ≥0)
    (order : Equiv.Perm (Fin n)) : ℝ≥0 :=
  ∏ k, weight (order k) / ∑ l with k ≤ l, weight (order l)

/-- Candidate-order and candidate-to-rank conventions give the same likelihood. -/
theorem orderedLikelihood_eq {n : ℕ} (weight : Fin n → ℝ≥0)
    (order : Equiv.Perm (Fin n)) :
    orderedLikelihood weight order = likelihood weight order.symm := by
  unfold orderedLikelihood likelihood
  apply Finset.prod_congr rfl
  intro k _
  simp only [Equiv.symm_symm]
  congr 1
  simpa only [Finset.sum_filter, Equiv.symm_apply_apply] using
    Equiv.sum_comp order (fun x ↦ if k ≤ order.symm x then weight x else 0)

/-- Removing the first candidate leaves the same successive sampling rule on the remaining set. -/
theorem orderedLikelihood_decompose {n : ℕ} (weight : Fin (n + 1) → ℝ≥0)
    (first : Fin (n + 1)) (tail : Equiv.Perm (Fin n)) :
    orderedLikelihood weight (Equiv.Perm.decomposeFin.symm (first, tail)) =
      weight first / (∑ x, weight x) *
        orderedLikelihood (fun x ↦ weight (Equiv.swap 0 first x.succ)) tail := by
  let order := Equiv.Perm.decomposeFin.symm (first, tail)
  have hden : (∑ l with (0 : Fin (n + 1)) ≤ l, weight (order l)) = ∑ x, weight x := by
    simpa using Equiv.sum_comp order weight
  unfold orderedLikelihood
  rw [Fin.prod_univ_succ]
  change weight (order 0) / (∑ l with (0 : Fin (n + 1)) ≤ l, weight (order l)) * _ = _
  rw [hden]
  dsimp only [order]
  rw [Equiv.Perm.decomposeFin_symm_apply_zero]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  rw [Equiv.Perm.decomposeFin_symm_apply_succ]
  congr 1
  simp [Finset.sum_filter, Fin.sum_univ_succ,
    Equiv.Perm.decomposeFin_symm_apply_succ]

/-- All successive weighted complete orders have total likelihood one. -/
theorem orderedLikelihood_sum_one {n : ℕ} (weight : Fin n → ℝ≥0)
    (hw : ∀ x, 0 < weight x) :
    ∑ order : Equiv.Perm (Fin n), orderedLikelihood weight order = 1 := by
  induction n with
  | zero => simp [orderedLikelihood]
  | succ n ih =>
    rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm]
    rw [Fintype.sum_prod_type]
    simp_rw [orderedLikelihood_decompose]
    simp_rw [← Finset.mul_sum]
    have htail (first : Fin (n + 1)) :
        (∑ tail : Equiv.Perm (Fin n),
          orderedLikelihood (fun x ↦ weight (Equiv.swap 0 first x.succ)) tail) = 1 :=
      ih _ (fun x ↦ hw _)
    simp_rw [htail, mul_one]
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (Finset.sum_pos (fun x _ ↦ hw x) Finset.univ_nonempty))

/-- The exact PR likelihood is already normalized: the global normalizer is unnecessary
when public scores are all strictly positive. -/
theorem likelihood_sum_one {n : ℕ} (weight : Fin n → ℝ≥0)
    (hw : ∀ x, 0 < weight x) :
    ∑ rank : Equiv.Perm (Fin n), likelihood weight rank = 1 := by
  have h := orderedLikelihood_sum_one weight hw
  simp_rw [orderedLikelihood_eq] at h
  let e : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) :=
    ⟨Equiv.symm, Equiv.symm, Equiv.symm_symm, Equiv.symm_symm⟩
  have hs := Equiv.sum_comp e (likelihood weight)
  exact hs ▸ h

/-- Normalizing the exact row likelihood leaves every mass unchanged. -/
theorem row_ofWeights_apply {n : ℕ} (weight : Fin n → ℝ≥0)
    (hw : ∀ x, 0 < weight x) (rank : Equiv.Perm (Fin n)) :
    ofWeights (likelihood weight) rank = (likelihood weight rank : ℝ≥0∞) := by
  rw [ofWeights_apply _ (by rw [likelihood_sum_one weight hw]; exact one_ne_zero)]
  simp [likelihood_sum_one weight hw]

/-- The exact PR's global profile normalizer equals one when all scores are positive. -/
theorem profile_likelihood_sum_one {n : ℕ} (P Q : Fin n → Fin n → ℝ≥0)
    (hP : ∀ m w, 0 < P m w) (hQ : ∀ m w, 0 < Q m w) :
    (∑ p : StableMarriage.Profile n, (∏ m, likelihood (P m) (p.manRank m)) *
      ∏ w, likelihood (fun m ↦ Q m w) (p.womanRank w)) = 1 := by
  rw [profile_normalizer]
  simp_rw [likelihood_sum_one _ (hP _), likelihood_sum_one _ (fun m ↦ hQ m _)]
  simp

/-- Exact PR point masses are the unnormalized product of literal successive-draw likelihoods;
the strict positivity assumptions make the normalization factor exactly one. -/
theorem profile_apply_eq_product {n : ℕ} (P Q : Fin n → Fin n → ℝ≥0)
    (hP : ∀ m w, 0 < P m w) (hQ : ∀ m w, 0 < Q m w)
    (p : StableMarriage.Profile n) :
    profile P Q p = (((∏ m, likelihood (P m) (p.manRank m)) *
      ∏ w, likelihood (fun m ↦ Q m w) (p.womanRank w) : ℝ≥0) : ℝ≥0∞) := by
  rw [profile, ofWeights_apply _ (by
    rw [profile_likelihood_sum_one P Q hP hQ]
    exact one_ne_zero)]
  rw [profile_likelihood_sum_one P Q hP hQ]
  simp

end Ashlagi
