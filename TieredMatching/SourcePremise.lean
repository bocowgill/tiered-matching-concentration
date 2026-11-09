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

public import FormalConjectures.Arxiv.«2009.05124».TieredRandomMatching
public import TieredMatching.DA

/-! # Exact source premise required from Proposition G.2

This module defines the premise against the unchanged PR law and counters. It does not assert it.
-/

@[expose] public section

open Filter
open scoped Topology NNReal ENNReal

namespace TieredMatching

/-- A real number is the least public score among the finitely many women's tiers. -/
def IsMinimumScore {I : ℕ} (α : Fin I → ℝ≥0) (αmin : ℝ) : Prop :=
  (∀ i, αmin ≤ (α i : ℝ)) ∧ ∃ i, αmin = (α i : ℝ)

/-- A minimum public score is positive when all tier scores are positive. -/
theorem IsMinimumScore.pos {I : ℕ} {α : Fin I → ℝ≥0} {αmin : ℝ}
    (h : IsMinimumScore α αmin) (hα : ∀ i, 0 < α i) : 0 < αmin := by
  obtain ⟨i, hi⟩ := h.2
  rw [hi]
  exact_mod_cast hα i

/-- The fixed-woman normalization in Proposition G.2, with a supplied minimum score. -/
noncomputable def proposalCoefficient {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ) (i : Fin I) (j : Fin J) : ℝ :=
  (α i : ℝ) / αmin * (b j / (β j : ℝ)) / ∑ h, b h / (β h : ℝ)

/-- The uniform fixed-woman assertion needed for every allowed rounded market sequence.
The measure and proposal counters are exactly those of PR 7841.
This is a hypothesis, not an axiom. -/
def PropositionG2 {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (i : Fin I) : Prop :=
  IsMinimumScore α αmin ∧ ∀ η : ℝ, 0 < η → ∀ δ : ℝ≥0∞, 0 < δ →
    ∀ᶠ n in atTop, ∀ w : Fin n, womanTier n w = i → ∀ j : Fin J,
      (Arxiv.«2009.05124».market (womanTier n) (manTier n) α β).toMeasure
        {p | |(proposalCount (manTier n) j p w : ℝ) -
            proposalCoefficient b α β αmin i j * Real.log n| >
          η * (proposalCoefficient b α β αmin i j * Real.log n)} ≤ δ

end TieredMatching
