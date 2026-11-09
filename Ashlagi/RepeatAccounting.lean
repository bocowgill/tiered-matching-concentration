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

public import Ashlagi.RawSemantics

/-!
# Exact accounting for raw and distinct destination hits

For every finite raw trace, the sum of the per-woman raw-minus-distinct counts is exactly the
number of repeated edges. This identity bounds the number of women with few distinct hits
by the number with few raw hits and the repeat count.
-/

@[expose] public section

namespace Ashlagi.RepeatAccounting

/-- The number of raw edges addressed to one woman, including repeated edges. -/
def rawHits {n : ℕ} (L : List (RawSemantics.Edge n)) (w : Fin n) : ℕ :=
  L.countP fun q ↦ q.1 = w

/-- The number of distinct edges addressed to one woman. -/
def distinctHits {n : ℕ} (L : List (RawSemantics.Edge n)) (w : Fin n) : ℕ :=
  (L.toFinset.filter fun q ↦ q.1 = w).card

/-- Distinct destination hits cannot exceed raw destination hits. -/
theorem distinctHits_le_rawHits {n : ℕ} (L : List (RawSemantics.Edge n)) (w : Fin n) :
    distinctHits L w ≤ rawHits L w := by
  simpa only [distinctHits, rawHits, List.filter_toFinset, ← List.countP_eq_length_filter] using
    (L.filter fun q ↦ q.1 = w).toFinset_card_le

/-- Raw destination counts partition the literal trace. -/
theorem sum_rawHits {n : ℕ} (L : List (RawSemantics.Edge n)) :
    ∑ w : Fin n, rawHits L w = L.length := by
  induction L with
  | nil => simp [rawHits]
  | cons e L ih =>
    simp only [rawHits, List.countP_cons, Finset.sum_add_distrib] at *
    simp [ih]

/-- Distinct destination counts partition the finite set of distinct edges. -/
theorem sum_distinctHits {n : ℕ} (L : List (RawSemantics.Edge n)) :
    ∑ w : Fin n, distinctHits L w = L.toFinset.card := by
  symm
  exact Finset.card_eq_sum_card_fiberwise (fun _ _ ↦ Finset.mem_univ _)

/-- Distinct edges to one woman correspond exactly to the men who queried her. -/
theorem distinctHits_eq_card_men {n : ℕ} (L : List (RawSemantics.Edge n)) (w : Fin n) :
    distinctHits L w = (Finset.univ.filter fun m : Fin n ↦ (w, m) ∈ L).card := by
  apply Finset.card_bij (fun q _ ↦ q.2)
  · intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hq, hw⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ← hw, Prod.mk.eta,
      List.mem_toFinset] using hq
  · intro q hq r hr hqr
    exact Prod.ext ((Finset.mem_filter.mp hq).2.trans (Finset.mem_filter.mp hr).2.symm) hqr
  · intro m hm
    refine ⟨(w, m), ?_, rfl⟩
    simpa only [Finset.mem_filter, List.mem_toFinset, true_and, Finset.mem_univ,
      and_true] using hm

/-- The per-woman losses under repeat erasure sum exactly to the number of repeated edges. -/
theorem sum_rawHits_sub_distinctHits {n : ℕ} (L : List (RawSemantics.Edge n)) :
    ∑ w : Fin n, (rawHits L w - distinctHits L w) = RawSemantics.repeatCount L := by
  rw [Finset.sum_tsub_distrib _ (fun w _ ↦ distinctHits_le_rawHits L w)]
  rw [sum_rawHits, sum_distinctHits]
  rfl

/-- Each woman with few distinct hits but many raw hits accounts for at least `c` repeats. -/
theorem mul_badDistinct_sub_badRaw_le_repeats {n : ℕ} (L : List (RawSemantics.Edge n))
    {c : ℝ} (hc : 0 < c) :
    c * (((Finset.univ.filter fun w : Fin n ↦ (distinctHits L w : ℝ) < c).card : ℝ) -
      ((Finset.univ.filter fun w : Fin n ↦ (rawHits L w : ℝ) < 2 * c).card : ℝ)) ≤
      RawSemantics.repeatCount L := by
  classical
  have hpoint (w : Fin n) :
      c * ((if (distinctHits L w : ℝ) < c then 1 else 0) -
        (if (rawHits L w : ℝ) < 2 * c then 1 else 0)) ≤
        ((rawHits L w - distinctHits L w : ℕ) : ℝ) := by
    rw [Nat.cast_sub (distinctHits_le_rawHits L w)]
    have hnonneg : (distinctHits L w : ℝ) ≤ rawHits L w :=
      Nat.cast_le.mpr (distinctHits_le_rawHits L w)
    by_cases hd : (distinctHits L w : ℝ) < c
    · by_cases hr : (rawHits L w : ℝ) < 2 * c
      · simp only [ite_eq_left hd, ite_eq_left hr]
        linarith
      · simp only [ite_eq_left hd, ite_eq_right hr]
        linarith
    · by_cases hr : (rawHits L w : ℝ) < 2 * c
      · simp only [ite_eq_right hd, ite_eq_left hr]
        linarith
      · simp only [ite_eq_right hd, ite_eq_right hr]
        linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun w _ ↦ hpoint w)
  rw [← Nat.cast_sum, sum_rawHits_sub_distinctHits, ← Finset.mul_sum,
    Finset.sum_sub_distrib] at hs
  simpa [Finset.sum_ite] using hs

/-- Few repeats bound the number of women with fewer than `c` distinct destination hits. -/
theorem badDistinct_card_le_badRaw_add_repeats_div {n : ℕ}
    (L : List (RawSemantics.Edge n)) {c : ℝ} (hc : 0 < c) :
    ((Finset.univ.filter fun w : Fin n ↦ (distinctHits L w : ℝ) < c).card : ℝ) ≤
      ((Finset.univ.filter fun w : Fin n ↦ (rawHits L w : ℝ) < 2 * c).card : ℝ) +
        RawSemantics.repeatCount L / c := by
  have h := mul_badDistinct_sub_badRaw_le_repeats L hc
  have hd := (le_div_iff₀ hc).mpr (by simpa only [mul_comm c] using h)
  linarith

end Ashlagi.RepeatAccounting
