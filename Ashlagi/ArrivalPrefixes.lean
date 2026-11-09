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

public import Ashlagi.ArrivalPolicy
public import Mathlib.Data.Finset.Sort

/-! # Canonical finite source prefixes for the concrete arrival policy -/

@[expose] public section

namespace Ashlagi.Arrival

section FiniteOrder

variable {α : Type*} [LinearOrder α]

/-- A finite initial segment relative to `T`, using the original order on labels. -/
def firstPrefix (T : Finset α) (k : ℕ) : Finset α :=
  T.filter fun x ↦ (T.filter fun y ↦ y < x).card < k

/-- A relatively downward-closed finite set is determined by its cardinality. -/
theorem downset_eq_firstPrefix {D T : Finset α} (hDT : D ⊆ T)
    (hdown : ∀ x ∈ D, ∀ y ∈ T, y < x → y ∈ D) : D = firstPrefix T D.card := by
  ext x
  simp only [firstPrefix, Finset.mem_filter]
  constructor
  · intro hx
    refine ⟨hDT hx, Finset.card_lt_card ?_⟩
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨fun y hy ↦ hdown x hx y (Finset.mem_filter.mp hy).1
      (Finset.mem_filter.mp hy).2, ?_⟩
    intro heq
    have := heq.symm ▸ hx
    exact (Finset.mem_filter.mp this).2.false
  · rintro ⟨hxT, hcard⟩
    by_contra hx
    have hsub : D ⊆ T.filter fun y ↦ y < x := by
      intro y hy
      refine Finset.mem_filter.mpr ⟨hDT hy, ?_⟩
      rcases lt_trichotomy y x with hlt | heq | hgt
      · exact hlt
      · exact False.elim (hx (heq ▸ hy))
      · exact False.elim (hx (hdown y hy x hxT hgt))
    exact (not_lt_of_ge (Finset.card_le_card hsub)) hcard

/-- The predecessor count of the increasing enumeration is its enumeration index. -/
theorem predecessor_card_orderEmb (T : Finset α) (i : Fin T.card) :
    (T.filter fun y ↦ y < T.orderEmbOfFin rfl i).card = i.val := by
  classical
  let e := T.orderEmbOfFin rfl
  have himage : (Finset.univ.filter fun j : Fin T.card ↦ j < i).image e =
      T.filter fun y ↦ y < e i := by
    ext y
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨T.orderEmbOfFin_mem rfl j, e.strictMono hj⟩
    · rintro ⟨hyT, hy⟩
      let j := (T.orderIsoOfFin rfl).symm ⟨y, hyT⟩
      have hej : e j = y := by
        exact congrArg Subtype.val ((T.orderIsoOfFin rfl).apply_symm_apply ⟨y, hyT⟩)
      exact ⟨j, e.lt_iff_lt.mp (hej ▸ hy), hej⟩
  rw [← himage, Finset.card_image_of_injective _ e.injective]
  simpa only [← Fin.val_fin_lt, Nat.min_eq_right i.isLt.le] using
    Fin.card_filter_val_lt (n := T.card) (m := i.val)

/-- A canonical prefix consists exactly of the first `k` increasing enumeration entries. -/
theorem firstPrefix_eq_image (T : Finset α) (k : ℕ) :
    firstPrefix T k = (Finset.univ.filter fun i : Fin T.card ↦ i.val < k).image
      (T.orderEmbOfFin rfl) := by
  classical
  ext x
  simp only [firstPrefix, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hxT, hrank⟩
    let i := (T.orderIsoOfFin rfl).symm ⟨x, hxT⟩
    have hei : T.orderEmbOfFin rfl i = x :=
      congrArg Subtype.val ((T.orderIsoOfFin rfl).apply_symm_apply ⟨x, hxT⟩)
    refine ⟨i, ?_, hei⟩
    simpa only [← hei, predecessor_card_orderEmb] using hrank
  · rintro ⟨i, hi, rfl⟩
    exact ⟨T.orderEmbOfFin_mem rfl i, by simpa only [predecessor_card_orderEmb] using hi⟩

/-- The cardinality of a finite prefix is exactly the truncated requested length. -/
theorem card_firstPrefix (T : Finset α) (k : ℕ) :
    (firstPrefix T k).card = min k T.card := by
  classical
  rw [firstPrefix_eq_image, Finset.card_image_of_injective _ (T.orderEmbOfFin rfl).injective]
  simpa only [Nat.min_comm] using Fin.card_filter_val_lt (n := T.card) (m := k)

/-- Feasible prefix lengths have exactly the requested cardinality. -/
theorem card_firstPrefix_of_le (T : Finset α) {k : ℕ} (hk : k ≤ T.card) :
    (firstPrefix T k).card = k := by
  rw [card_firstPrefix, Nat.min_eq_left hk]

end FiniteOrder

/-- All source-man labels in a designated tier, retaining the original natural order. -/
def tierMen {n J : ℕ} (manTier : Fin n → Fin J) (j : Fin J) : Finset (Fin n) :=
  Finset.univ.filter fun m ↦ manTier m = j

/-- The canonical first `k` source slots in a man's tier, indexed by original source-man labels. -/
def tierPrefix {n J : ℕ} (manTier : Fin n → Fin J) (j : Fin J) (k : ℕ) : Finset (Fin n) :=
  firstPrefix (tierMen manTier j) k

/-- Genuine used source-man labels within one fixed woman/tier block. -/
noncomputable def usedMen {n J : ℕ} [NeZero n] (P : Fin n → Equiv.Perm (Fin n))
    (manTier : Fin n → Fin J) (h : List (Edge n × ℝ)) (w : Fin n) (j : Fin J) :
    Finset (Fin n) := by
  classical
  exact (tierMen manTier j).filter fun m ↦ (w, m) ∈ usedSources P manTier h

/-- Actual queried output-man labels within one fixed woman/tier block. -/
noncomputable def queriedMen {n J : ℕ} (P : Fin n → Equiv.Perm (Fin n))
    (manTier : Fin n → Fin J) (s : RawState n) (w : Fin n) (j : Fin J) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun m ↦ manTier m = j ∧ Queried P s (w, m)

/-- Source labels consumed by the concrete policy are an initial segment in their tier. -/
theorem usedMen_eq_tierPrefix {n J : ℕ} [NeZero n] (P : Fin n → Equiv.Perm (Fin n))
    (manTier : Fin n → Fin J) (x : Edge n → ℝ) (t : ℕ) (w : Fin n) (j : Fin J) :
    let h := allocationHistory (pick P manTier) x t
    usedMen P manTier h w j = tierPrefix manTier j (usedMen P manTier h w j).card := by
  classical
  dsimp only
  apply downset_eq_firstPrefix
  · exact Finset.filter_subset _ _
  · intro a ha m hm hma
    have hau := (Finset.mem_filter.mp ha).2
    have hat : manTier a = j := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
    have hmt : manTier m = j := (Finset.mem_filter.mp hm).2
    apply Finset.mem_filter.mpr
    refine ⟨hm, ?_⟩
    exact usedSources_downward P manTier x t (w, a) hau (w, m)
      (Prod.ext rfl (hmt.trans hat.symm)) hma

/-- Reindexing is a bijection between genuine used source slots and queried output edges
inside every fixed woman/tier block. In particular it preserves their counts. -/
theorem usedMen_card_eq_queriedMen {n J : ℕ} [NeZero n]
    (P : Fin n → Equiv.Perm (Fin n)) (manTier : Fin n → Fin J)
    (x : Edge n → ℝ) (t : ℕ) (w : Fin n) (j : Fin J) :
    let h := allocationHistory (pick P manTier) x t
    (usedMen P manTier h w j).card = (queriedMen P manTier (replay P manTier h).1 w j).card := by
  classical
  let h := allocationHistory (pick P manTier) x t
  let π := (replay P manTier h).2
  let f : Fin n → Fin n := fun m ↦ (π.symm (w, m)).2
  have hπ : PreservesBlocks manTier π := replay_preservesBlocks P manTier h
  have hrow (m : Fin n) : π.symm (w, m) = (w, f m) := by
    have hb := hπ (π.symm (w, m))
    simp only [Equiv.apply_symm_apply, block] at hb
    exact Prod.ext (congrArg Prod.fst hb).symm rfl
  have htier (m : Fin n) : manTier (f m) = manTier m := by
    have hb := hπ (π.symm (w, m))
    simp only [Equiv.apply_symm_apply, block] at hb
    exact (congrArg Prod.snd hb).symm
  apply Finset.card_bij (fun m _ ↦ f m)
  · intro m hm
    have hmt : manTier m = j := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
    have hused := (Finset.mem_filter.mp hm).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, htier m |>.trans hmt, ?_⟩
    have hq := (history_used_queried P manTier x t (π.symm (w, m))).mp
      (by
        change π (π.symm (w, m)) ∈ usedSources P manTier h
        simpa only [Equiv.apply_symm_apply] using hused)
    simpa only [hrow m] using hq
  · intro a ha b hb hab
    have heq : π.symm (w, a) = π.symm (w, b) :=
      (hrow a).trans ((congrArg (fun m ↦ (w, m)) hab).trans (hrow b).symm)
    exact congrArg Prod.snd (π.symm.injective heq)
  · intro m hm
    have hmt : manTier m = j := (Finset.mem_filter.mp hm).2.1
    have hq : Queried P (replay P manTier h).1 (w, m) := (Finset.mem_filter.mp hm).2.2
    let a := (π (w, m)).2
    have hb := hπ (w, m)
    have hprow : π (w, m) = (w, a) :=
      Prod.ext (congrArg (fun b : Fin n × Fin J ↦ b.1) hb) rfl
    have hused := (history_used_queried P manTier x t (w, m)).mpr hq
    refine ⟨a, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · exact (congrArg (fun b : Fin n × Fin J ↦ b.2) hb).trans hmt
      · change π (w, m) ∈ usedSources P manTier h at hused
        rw [hprow] at hused
        exact hused
    · change (π.symm (w, a)).2 = m
      rw [← hprow, Equiv.symm_apply_apply]

/-- At the PR's terminal time, used source counts equal its exact distinct-proposer count. -/
theorem usedMen_terminal_card {n J : ℕ} [NeZero n]
    (P : Fin n → Equiv.Perm (Fin n)) (manTier : Fin n → Fin J)
    (x : Edge n → ℝ) (hx : ∀ w, Function.Injective (fun m ↦ x (w, m)))
    (w : Fin n) (j : Fin J) :
    (usedMen P manTier (allocationHistory (pick P manTier) x (n * n)) w j).card =
      proposalCount manTier j (profile P (adaptiveAllocation (pick P manTier) x (n * n))) w := by
  classical
  rw [usedMen_card_eq_queriedMen]
  unfold queriedMen proposalCount
  apply congrArg Finset.card
  ext m
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold Queried HasProposed
  rw [allocation_terminal_state P manTier x hx]
  rfl

/-- The actual sources consumed by one woman/tier are exactly the first `proposalCount`
entries of that tier's source array in the original source-man order. -/
theorem usedMen_terminal_eq_prefix {n J : ℕ} [NeZero n]
    (P : Fin n → Equiv.Perm (Fin n)) (manTier : Fin n → Fin J)
    (x : Edge n → ℝ) (hx : ∀ w, Function.Injective (fun m ↦ x (w, m)))
    (w : Fin n) (j : Fin J) :
    usedMen P manTier (allocationHistory (pick P manTier) x (n * n)) w j =
      tierPrefix manTier j
        (proposalCount manTier j
          (profile P (adaptiveAllocation (pick P manTier) x (n * n))) w) := by
  rw [usedMen_eq_tierPrefix, usedMen_terminal_card P manTier x hx]

/-- Canonical tier prefixes have the requested cardinality, truncated by tier size. -/
theorem tierPrefix_card {n J : ℕ} (manTier : Fin n → Fin J) (j : Fin J) (k : ℕ) :
    (tierPrefix manTier j k).card = min k (tierMen manTier j).card :=
  card_firstPrefix _ _

end Ashlagi.Arrival
