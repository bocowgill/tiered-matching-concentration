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

public import Mathlib.Order.Filter.Extr
public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic

/-!
# Deterministic prefix sandwiches for minimum priorities

A minimum from a lower collection remains the minimum in every collection between the lower
and upper collections. Applied to tier-indexed arrival prefixes, this identifies the actual
and fixed-count winners whenever the minimum of the upper prefixes lies in the lower prefixes.

This is the deterministic step of the proof of match-type concentration in Remark H.1 of
Ashlagi et al., https://arxiv.org/abs/2009.05124v2.
-/

@[expose] public section

namespace Ashlagi

section Minimum

variable {α β : Type*} [PartialOrder β] {f : α → β}
variable {s t : Set α} {x y : α}

/-- On an injective upper collection, its minimum agrees with the minimum of any subcollection
containing that upper minimum. -/
theorem min_eq_of_mem_of_subset (hst : s ⊆ t) (hx : x ∈ s) (hy : y ∈ s)
    (hxt : IsMinOn f t x) (hys : IsMinOn f s y) (hf : Set.InjOn f t) : x = y := by
  apply hf (hst hx) (hst hy)
  exact le_antisymm (hxt (hst hy)) (hys hx)

/-- If the minimum of the upper collection belongs to the lower collection, the minima of
any two intermediate collections agree. Injectivity rules out ties in the upper collection. -/
theorem min_eq_of_sandwich {lower actual central upper : Set α} {a c u : α}
    (hla : lower ⊆ actual) (hlc : lower ⊆ central)
    (hau : actual ⊆ upper) (hcu : central ⊆ upper)
    (ha : a ∈ actual) (hc : c ∈ central) (hu : u ∈ lower)
    (ha_min : IsMinOn f actual a) (hc_min : IsMinOn f central c)
    (hu_min : IsMinOn f upper u) (hf : Set.InjOn f upper) : a = c := by
  exact (min_eq_of_mem_of_subset hau (hla hu) ha hu_min ha_min hf).symm.trans
    (min_eq_of_mem_of_subset hcu (hlc hu) hc hu_min hc_min hf)

end Minimum

section Prefix

variable {J : Type*}

/-- The first `count j` arrival positions in each tier, using zero-based arrival indices. -/
def prefixSet (count : J → ℕ) : Set (J × ℕ) := {x | x.2 < count x.1}

/-- Enlarging every tier's count enlarges its arrival collection. -/
theorem prefixSet_mono {count count' : J → ℕ} (h : ∀ j, count j ≤ count' j) :
    prefixSet count ⊆ prefixSet count' := by
  exact fun x hx ↦ lt_of_lt_of_le hx (h x.1)

/-- Countwise lower and upper bounds identify the actual winner with a fixed-count winner
when the upper-prefix winner belongs to the lower prefixes. -/
theorem prefix_min_eq {β : Type*} [PartialOrder β] {f : J × ℕ → β}
    {lower actual central upper : J → ℕ} {a c u : J × ℕ}
    (hla : ∀ j, lower j ≤ actual j) (hlc : ∀ j, lower j ≤ central j)
    (hau : ∀ j, actual j ≤ upper j) (hcu : ∀ j, central j ≤ upper j)
    (ha : a ∈ prefixSet actual) (hc : c ∈ prefixSet central) (hu : u ∈ prefixSet lower)
    (ha_min : IsMinOn f (prefixSet actual) a)
    (hc_min : IsMinOn f (prefixSet central) c)
    (hu_min : IsMinOn f (prefixSet upper) u)
    (hf : Set.InjOn f (prefixSet upper)) : a = c := by
  exact min_eq_of_sandwich (prefixSet_mono hla) (prefixSet_mono hlc)
    (prefixSet_mono hau) (prefixSet_mono hcu) ha hc hu ha_min hc_min hu_min hf

/-- A disagreement of winner tiers can occur only if a count leaves its deterministic bounds
or the upper-prefix winner lies outside the lower prefixes. This is a pathwise set inclusion. -/
theorem tier_disagreement_subset {Ω β : Type*} [PartialOrder β]
    (f : Ω → J × ℕ → β) (actual : Ω → J → ℕ) (lower central upper : J → ℕ)
    (a c u : Ω → J × ℕ)
    (hlc : ∀ j, lower j ≤ central j) (hcu : ∀ j, central j ≤ upper j)
    (ha : ∀ ω, a ω ∈ prefixSet (actual ω))
    (hc : ∀ ω, c ω ∈ prefixSet central)
    (ha_min : ∀ ω, IsMinOn (f ω) (prefixSet (actual ω)) (a ω))
    (hc_min : ∀ ω, IsMinOn (f ω) (prefixSet central) (c ω))
    (hu_min : ∀ ω, IsMinOn (f ω) (prefixSet upper) (u ω))
    (hf : ∀ ω, Set.InjOn (f ω) (prefixSet upper)) :
    {ω | (a ω).1 ≠ (c ω).1} ⊆
      {ω | ¬ ∀ j, lower j ≤ actual ω j ∧ actual ω j ≤ upper j} ∪
      {ω | u ω ∉ prefixSet lower} := by
  classical
  intro ω hne
  by_cases hgood : ∀ j, lower j ≤ actual ω j ∧ actual ω j ≤ upper j
  · by_cases hlow : u ω ∈ prefixSet lower
    · exact False.elim (hne (congrArg Prod.fst
        (prefix_min_eq (fun j ↦ (hgood j).1) hlc (fun j ↦ (hgood j).2) hcu
          (ha ω) (hc ω) hlow (ha_min ω) (hc_min ω) (hu_min ω) (hf ω))))
    · exact Or.inr hlow
  · exact Or.inl hgood

end Prefix

section Counts

variable {ι J : Type*} [DecidableEq J]

/-- Every occurrence of a tier in the first assignment is either an occurrence in the second
assignment or a position where the two assignments disagree. -/
theorem tier_count_le_add_disagreements (s : Finset ι) (a c : ι → J) (j : J) :
    (s.filter (fun x ↦ a x = j)).card ≤ (s.filter (fun x ↦ c x = j)).card +
      (s.filter (fun x ↦ a x ≠ c x)).card := by
  classical
  apply le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  exact fun x hx ↦ (em (c x = j)).elim
    (fun hcx ↦ Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hcx⟩))
    (fun hcx ↦ Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
        fun h ↦ hcx (h.symm.trans (Finset.mem_filter.mp hx).2)⟩))

/-- Changing an assignment at `D` positions changes every tier count by at most `D`. -/
theorem abs_tier_count_sub_le_disagreements (s : Finset ι) (a c : ι → J) (j : J) :
    |((s.filter (fun x ↦ a x = j)).card : ℝ) - (s.filter (fun x ↦ c x = j)).card| ≤
      (s.filter (fun x ↦ a x ≠ c x)).card := by
  apply abs_sub_le_iff.mpr
  exact ⟨sub_le_iff_le_add'.mpr (by
    simpa only [Nat.cast_add] using
      (Nat.cast_le (α := ℝ)).mpr (tier_count_le_add_disagreements s a c j)),
    sub_le_iff_le_add'.mpr (by
      simpa only [Nat.cast_add, ne_comm] using
        (Nat.cast_le (α := ℝ)).mpr (tier_count_le_add_disagreements s c a j))⟩

end Counts

end Ashlagi
