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

public import TieredMatching.Main
public import TieredMatching.Rates

/-! # Exact match-count semantics -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

namespace TieredMatching

/-- The tier of the partner held by a woman in the exact PR state. -/
def heldTier {n J : ℕ} (manTier : Fin n → Fin J) (p : StableMarriage.Profile n)
    (w : Fin n) : Option (Fin J) :=
  ((StableMarriage.deferredAcceptance p).held w).map manTier

/-- The women of a designated tier. -/
def womenSet {n I : ℕ} (womanTier : Fin n → Fin I) (i : Fin I) : Finset (Fin n) :=
  Finset.univ.filter fun w ↦ womanTier w = i

/-- The PR's match count is exactly a category count of its held-partner tier labels. -/
theorem matchCount_eq_heldTier_count {n I J : ℕ} (womanTier : Fin n → Fin I)
    (manTier : Fin n → Fin J) (i : Fin I) (j : Fin J) (p : StableMarriage.Profile n) :
    Arxiv.«2009.05124».matchCount womanTier manTier i j p =
      ((womenSet womanTier i).filter fun w ↦ heldTier manTier p w = some j).card := by
  classical
  apply congrArg Finset.card
  ext w
  simp [womenSet, heldTier, Option.map_eq_some_iff]

/-- Normalized match counts are the actual label frequencies used by the transfer theorem. -/
theorem categoryFrequency_heldTier {n I J : ℕ} (womanTier : Fin n → Fin I)
    (manTier : Fin n → Fin J) (i : Fin I) (j : Fin J)
    {Ω : Type*} (p : Ω → StableMarriage.Profile n) (ω : Ω) :
    categoryFrequency (womenSet womanTier i) (fun w ω ↦ heldTier manTier (p ω) w)
      (some j) n ω =
      (Arxiv.«2009.05124».matchCount womanTier manTier i j (p ω) : ℝ) / n := by
  classical
  rw [matchCount_eq_heldTier_count]
  simp [categoryFrequency, Finset.sum_boole]

/-- The population of any women's tier is at most the market size. -/
theorem womenSet_card_le {n I : ℕ} (womanTier : Fin n → Fin I) (i : Fin I) :
    (womenSet womanTier i).card ≤ n := by
  simpa only [womenSet, Finset.card_univ, Fintype.card_fin] using
    Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun w ↦ womanTier w = i)

end TieredMatching
