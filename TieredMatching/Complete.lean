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

public import TieredMatching.G2Assembly
public import TieredMatching.FinalCoupling

/-! # The exact match-type concentration statement from PR 7841

The exponential-arrival law, uniform rounded-market Proposition G.2, and independent reference
coupling are proved in the imported modules. The original conjecture is used only for a separate
statement-type audit; its admitted proof is not a dependency of the theorem below.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace TieredMatching.Complete

/-- The match-type concentration conjecture in Formal Conjectures PR 7841, with exactly its
original hypotheses, finite tier rounding, probability law, and conclusion. -/
theorem match_type_concentration
    (I J : ℕ) (a : Fin I → ℝ) (b : Fin J → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (ha_sum : ∑ i, a i = 1) (hb_sum : ∑ j, b j = 1)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (hw : ∀ n i, |(Fintype.card {w // womanTier n w = i} : ℝ) - n * a i| ≤ 1)
    (hm : ∀ n j, |(Fintype.card {m // manTier n m = j} : ℝ) - n * b j| ≤ 1)
    (i : Fin I) (j : Fin J) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (Arxiv.«2009.05124».market (womanTier n) (manTier n) α β).toMeasure
      {p | |(Arxiv.«2009.05124».matchCount (womanTier n) (manTier n) i j p : ℝ) / n -
        a i * b j| ≤ ε}) atTop (𝓝 1) := by
  obtain ⟨i₀, _, hleast⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin I))
    (fun k ↦ (α k : ℝ)) ⟨i, Finset.mem_univ _⟩
  have hmin : IsMinimumScore α (α i₀ : ℝ) :=
    ⟨fun k ↦ hleast k (Finset.mem_univ _), i₀, rfl⟩
  exact FinalCoupling.match_type_concentration_of_propositionG2 I J a b ha hb ha_sum hb_sum
    α β hα hβ womanTier manTier hw hm i j (α i₀ : ℝ)
    (G2Assembly.proposition_g2 a b α β (α i₀ : ℝ) ha hb hα hβ hmin
      womanTier manTier hw hm i) ε hε

end TieredMatching.Complete
