/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.
-/
module

public import TieredMatching.Complete

/-! # Proved match-type concentration

The statement and model are those of Formal Conjectures PR 7841. Comparator
checks this declaration against the independent Mathlib-only Challenge.
-/

@[expose] public section

open Filter
open scoped Topology NNReal

namespace Arxiv.«2009.05124»

/-- Match-type concentration for every allowed rounded sequence of markets. -/
theorem _root_.TieredMatching.match_type_concentration
    (I J : ℕ) (a : Fin I → ℝ) (b : Fin J → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (ha_sum : ∑ i, a i = 1) (hb_sum : ∑ j, b j = 1)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (hw : ∀ n i, |(Fintype.card {w // womanTier n w = i} : ℝ) - n * a i| ≤ 1)
    (hm : ∀ n j, |(Fintype.card {m // manTier n m = j} : ℝ) - n * b j| ≤ 1)
    (i : Fin I) (j : Fin J) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (market (womanTier n) (manTier n) α β).toMeasure
      {p | |(matchCount (womanTier n) (manTier n) i j p : ℝ) / n - a i * b j| ≤ ε})
      atTop (𝓝 1) := by
  exact TieredMatching.Complete.match_type_concentration I J a b ha hb ha_sum hb_sum
    α β hα hβ womanTier manTier hw hm i j ε hε

end Arxiv.«2009.05124»
