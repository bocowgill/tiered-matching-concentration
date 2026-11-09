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

public import Ashlagi.Coefficients

/-! # Uniform finite-market estimates and rounded market sequences

The finite-market estimate in `UniformG2Bound` is an explicit hypothesis. This module proves
that its uniformity suffices for the exact fixed-coefficient `PropositionG2` predicate.
-/

@[expose] public section

open Filter
open scoped Topology NNReal ENNReal

namespace Ashlagi

/-- The exact population proportion of a tier in a finite labeled market. -/
noncomputable def tierShare {n K : ℕ} (tier : Fin n → Fin K) (k : Fin K) : ℝ :=
  (Fintype.card {x // tier x = k} : ℝ) / n

/-- Exact tier proportions sum to one in every nonempty market. -/
theorem sum_tierShare {n K : ℕ} (tier : Fin n → Fin K) (hn : 0 < n) :
    ∑ k, tierShare tier k = 1 := by
  classical
  have hc : ∑ k, Fintype.card {x // tier x = k} = n := by
    simpa only [Fintype.card_subtype, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
        (f := tier) (by simp)).symm
  simp only [tierShare, ← Finset.sum_div, ← Nat.cast_sum, hc]
  exact div_self (by exact_mod_cast hn.ne')

/-- Every finite family of positive shares has a common strictly positive lower fence. -/
theorem exists_share_fence {K : ℕ} (a : Fin K → ℝ) (ha : ∀ k, 0 < a k) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ k, ρ < a k := by
  classical
  let s := insert 1 (Finset.univ.image a)
  have hs : s.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  have hp : 0 < s.inf' hs id := by
    rw [Finset.lt_inf'_iff]
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · norm_num
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
      exact ha k
  refine ⟨s.inf' hs id / 2, by positivity, ?_⟩
  intro k
  have hle : s.inf' hs id ≤ a k :=
    Finset.inf'_le id (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨k, Finset.mem_univ _, rfl⟩))
  linarith

/-- Rounded shares enter one fixed positive fence, simultaneously in every tier. -/
theorem rounded_tierShare_eventually {K : ℕ} (a : Fin K → ℝ)
    (ha : ∀ k, 0 < a k) (tier : (n : ℕ) → Fin n → Fin K)
    (h : ∀ n k, |(Fintype.card {x // tier n x = k} : ℝ) - n * a k| ≤ 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ n in atTop, ∀ k, ρ ≤ tierShare (tier n) k := by
  obtain ⟨ρ, hρ, hρa⟩ := exists_share_fence a ha
  refine ⟨ρ, hρ, ?_⟩
  rw [eventually_all]
  intro k
  have hh : ∀ᶠ n in atTop, ρ < tierShare (tier n) k :=
    (rounded_share_tendsto (fun n ↦ Fintype.card {x // tier n x = k})
      (a k) (fun n ↦ h n k)) (lt_mem_nhds (hρa k))
  exact hh.mono fun _ hn ↦ hn.le

/-- A compact-uniform quantitative G.2 estimate for the exact PR market and proposal counter.
For each positive share fence, one constant and one threshold for each tolerance work for every
market size and every pair of labeled tier maps. No assertion of this process estimate is made.
-/
def UniformG2Bound {I J : ℕ} (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (αmin : ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ K : ℝ, 0 < K ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 2 ≤ n →
      ∀ (womanTier : Fin n → Fin I) (manTier : Fin n → Fin J),
      (∀ i, ρ ≤ tierShare womanTier i) → (∀ j, ρ ≤ tierShare manTier j) →
      (∑ i, tierShare womanTier i = 1) → (∑ j, tierShare manTier j = 1) →
      ∀ (i : Fin I) (w : Fin n), womanTier w = i → ∀ j : Fin J,
      (Arxiv.«2009.05124».market womanTier manTier α β).toMeasure
        {p | |(proposalCount manTier j p w : ℝ) -
            proposalCoefficient (tierShare manTier) α β αmin i j * Real.log n| >
          η * (proposalCoefficient (tierShare manTier) α β αmin i j * Real.log n)} ≤
        ENNReal.ofReal (K / (η ^ 2 * Real.log n))

/-- The quantitative failure bound vanishes for each fixed positive tolerance. -/
theorem g2_failure_bound_tendsto (K η : ℝ) :
    Tendsto (fun n : ℕ ↦ ENNReal.ofReal (K / (η ^ 2 * Real.log n)))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := ENNReal.tendsto_ofReal (hlog.const_div_atTop (K / η ^ 2))
  simpa only [ENNReal.ofReal_zero, div_div] using h

/-- A small relative perturbation of the central coefficient preserves a larger error band. -/
theorem g2_good_of_close {x c d L η ζ : ℝ} (hc : 0 < c) (hL : 0 ≤ L)
    (hζ : 0 < ζ) (hζη : ζ ≤ η / 4) (hζ1 : ζ ≤ 1 / 4)
    (hclose : |d - c| ≤ ζ * c) (hgood : |x - d * L| ≤ ζ * (d * L)) :
    |x - c * L| ≤ η * (c * L) := by
  have hd : d ≤ 2 * c := by
    have := (abs_le.mp hclose).2
    nlinarith
  have hb : ζ * d + ζ * c ≤ η * c := by
    nlinarith
  calc
    |x - c * L| ≤ |x - d * L| + |d * L - c * L| := abs_sub_le _ _ _
    _ ≤ ζ * (d * L) + (ζ * c) * L := by
      rw [← sub_mul, abs_mul, abs_of_nonneg hL]
      exact add_le_add hgood (mul_le_mul_of_nonneg_right hclose hL)
    _ = (ζ * d + ζ * c) * L := by ring
    _ ≤ (η * c) * L := mul_le_mul_of_nonneg_right hb hL
    _ = η * (c * L) := by ring

/-- Both rounded populations eventually lie in one fixed compact positive share simplex. -/
theorem rounded_markets_eventually_compact {I J : ℕ} (a : Fin I → ℝ) (b : Fin J → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (hw : ∀ n i, |(Fintype.card {w // womanTier n w = i} : ℝ) - n * a i| ≤ 1)
    (hm : ∀ n j, |(Fintype.card {m // manTier n m = j} : ℝ) - n * b j| ≤ 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ n in atTop,
      (∀ i, ρ ≤ tierShare (womanTier n) i) ∧
      (∀ j, ρ ≤ tierShare (manTier n) j) ∧
      (∑ i, tierShare (womanTier n) i = 1) ∧
      (∑ j, tierShare (manTier n) j = 1) := by
  obtain ⟨ρa, hρa, hwa⟩ := rounded_tierShare_eventually a ha womanTier hw
  obtain ⟨ρb, hρb, hmb⟩ := rounded_tierShare_eventually b hb manTier hm
  refine ⟨min ρa ρb, lt_min hρa hρb, ?_⟩
  filter_upwards [hwa, hmb, eventually_ge_atTop 1] with n hnw hnm hn
  exact ⟨fun i ↦ (min_le_left _ _).trans (hnw i),
    fun j ↦ (min_le_right _ _).trans (hnm j),
    sum_tierShare _ (by omega), sum_tierShare _ (by omega)⟩

/-- A genuinely uniform finite-market bound implies the source's exact fixed-coefficient G.2
statement for every pair of tier-map sequences with the PR's rounding error at most one.
The uniform process bound is an explicit hypothesis, and all scores remain arbitrary positive.
-/
theorem UniformG2Bound.propositionG2 {I J : ℕ} (a : Fin I → ℝ) (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (hmin : IsMinimumScore α αmin) (huniform : UniformG2Bound α β αmin)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (hw : ∀ n i, |(Fintype.card {w // womanTier n w = i} : ℝ) - n * a i| ≤ 1)
    (hm : ∀ n j, |(Fintype.card {m // manTier n m = j} : ℝ) - n * b j| ≤ 1)
    (i : Fin I) : PropositionG2 b α β αmin womanTier manTier i := by
  refine ⟨hmin, ?_⟩
  intro η hη δ hδ
  let ζ := min (η / 4) (1 / 4 : ℝ)
  have hζ : 0 < ζ := lt_min (by positivity) (by norm_num)
  have hζη : ζ ≤ η / 4 := min_le_left _ _
  have hζ4 : ζ ≤ 1 / 4 := min_le_right _ _
  have hζ1 : ζ ≤ 1 := by linarith
  obtain ⟨ρ, hρ, hcompact⟩ :=
    rounded_markets_eventually_compact a b ha hb womanTier manTier hw hm
  obtain ⟨K, _, hK⟩ := huniform ρ hρ
  obtain ⟨N, hN⟩ := hK ζ hζ hζ1
  have hclose : ∀ᶠ n in atTop, ∀ j : Fin J,
      |proposalCoefficient (tierShare (manTier n)) α β αmin i j -
        proposalCoefficient b α β αmin i j| ≤ ζ * proposalCoefficient b α β αmin i j := by
    rw [eventually_all]
    intro j
    have hc := proposalCoefficient_pos b α β αmin hb hα hβ (hmin.pos hα) i j
    have ht := rounded_proposalCoefficient_tendsto b α β αmin hb hβ
      (fun n j ↦ Fintype.card {m // manTier n m = j}) hm i j
    have ht' : Tendsto (fun n ↦ |proposalCoefficient (tierShare (manTier n))
        α β αmin i j - proposalCoefficient b α β αmin i j|) atTop (𝓝 0) := by
      change Tendsto (fun n ↦ |proposalCoefficient
        (fun j ↦ (Fintype.card {m // manTier n m = j} : ℝ) / n) α β αmin i j -
          proposalCoefficient b α β αmin i j|) atTop (𝓝 0)
      simpa only [sub_self, abs_zero] using
        (ht.sub (tendsto_const_nhds (x := proposalCoefficient b α β αmin i j))).abs
    have he : ∀ᶠ n in atTop,
        |proposalCoefficient (tierShare (manTier n)) α β αmin i j -
          proposalCoefficient b α β αmin i j| < ζ * proposalCoefficient b α β αmin i j :=
      ht' (gt_mem_nhds (mul_pos hζ hc))
    exact he.mono fun _ hh ↦ hh.le
  have hprob : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (K / (ζ ^ 2 * Real.log n)) ≤ δ := by
    have hh : ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (K / (ζ ^ 2 * Real.log n)) < δ :=
      g2_failure_bound_tendsto K ζ (gt_mem_nhds hδ)
    exact hh.mono fun _ hh ↦ hh.le
  filter_upwards [hcompact, hclose, hprob, eventually_ge_atTop (max N 2)] with
      n hncompact hnclose hnprob hn
  intro w hwti j
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn2.trans' (by norm_num))
  have hbound := hN n ((le_max_left _ _).trans hn) hn2 (womanTier n) (manTier n)
    hncompact.1 hncompact.2.1 hncompact.2.2.1 hncompact.2.2.2 i w hwti j
  apply le_trans (MeasureTheory.measure_mono ?_) (hbound.trans hnprob)
  intro p hp
  change |(proposalCount (manTier n) j p w : ℝ) -
    proposalCoefficient (tierShare (manTier n)) α β αmin i j * Real.log n| >
    ζ * (proposalCoefficient (tierShare (manTier n)) α β αmin i j * Real.log n)
  by_contra hbad
  have hg := g2_good_of_close
    (proposalCoefficient_pos b α β αmin hb hα hβ (hmin.pos hα) i j)
    hlog hζ hζη hζ4 (hnclose j) (le_of_not_gt hbad)
  exact (not_le_of_gt hp) hg

end Ashlagi
