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

public import Ashlagi.FirstFresh

/-! # Weighted rankings from first occurrences in IID categorical streams

The first-occurrence events are defined from the actual IID coordinates. Their laws are proved
using the first-fresh regeneration kernel, without assuming the Plackett-Luce ranking law.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace Ashlagi

namespace IIDRanking

variable {α : Type*} [DecidableEq α] [Fintype α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- The next distinct candidates after an excluded set, in their actual discovery order. -/
noncomputable def discoveryEvent (S : Finset α) : List α → Set (ℕ → α)
  | [] => Set.univ
  | q :: L => if q ∈ S then ∅ else
      ⋃ k, FirstFresh.hitAt (S : Set α) {q} k ∩
        (FirstFresh.tailAfter k) ⁻¹' discoveryEvent (insert q S) L

/-- Discovery events are measurable finite-list conditions on the IID stream. -/
theorem measurableSet_discoveryEvent (S : Finset α) (L : List α) :
    MeasurableSet (discoveryEvent S L) := by
  classical
  induction L generalizing S with
  | nil => exact MeasurableSet.univ
  | cons q L ih =>
    rw [discoveryEvent]
    split_ifs
    · exact MeasurableSet.empty
    · exact MeasurableSet.iUnion fun k ↦ (FirstFresh.measurableSet_hitAt _ _ k).inter
        ((ih _).preimage (FirstFresh.measurable_tailAfter k))

/-- Regeneration gives the exact probability recursion for the next distinct candidate. -/
theorem discoveryEvent_cons_measure (p : PMF α) (S : Finset α) (q : α) (L : List α)
    (hq : q ∉ S) :
    FirstFresh.iidStream p (discoveryEvent S (q :: L)) =
      FirstFresh.iidStream p (FirstFresh.firstValue (S : Set α) q) *
        FirstFresh.iidStream p (discoveryEvent (insert q S) L) := by
  classical
  rw [discoveryEvent, ite_eq_right hq, FirstFresh.firstValue_tail_measure p _ q hq _
    (measurableSet_discoveryEvent _ _), FirstFresh.firstValue_measure]
  simp only [Finset.mem_coe, ite_eq_right hq]

/-- Extending a prefix deletes one label from its residual embedding. -/
theorem remaining_appendNext {n d : ℕ} (p : RankingPrefix n (d + 1)) (q : Fin (d + 1))
    (r : Fin d) :
    (p.appendNext q).remaining r = p.remaining (RankingPrefix.residual q r) := by
  induction n with
  | zero => cases p
  | succ n ih =>
    cases p with
    | empty => rw [RankingPrefix.appendNext]; rfl
    | cons first tail =>
      rw [RankingPrefix.appendNext]
      change RankingPrefix.residual first ((tail.appendNext q).remaining r) = _
      rw [ih]
      rfl

/-- Listing a decomposed residual order exposes its first remaining original candidate. -/
theorem remaining_orderList {n d : ℕ} (p : RankingPrefix n (d + 1)) (q : Fin (d + 1))
    (tail : Equiv.Perm (Fin d)) :
    List.ofFn (fun r ↦ p.remaining (Equiv.Perm.decomposeFin.symm (q, tail) r)) =
      p.remaining q :: List.ofFn (fun r ↦ (p.appendNext q).remaining (tail r)) := by
  rw [List.ofFn_succ, Equiv.Perm.decomposeFin_symm_apply_zero]
  congr 1
  apply congrArg List.ofFn
  funext r
  rw [Equiv.Perm.decomposeFin_symm_apply_succ, remaining_appendNext]
  rfl

/-- First discoveries after an exposed prefix have exactly its residual ranking law. -/
theorem discoveryEvent_remaining_measure {n d : ℕ} [NeZero n] (p : RankingPrefix n d)
    (weight : Fin n → ℝ≥0) (hw : ∀ x, 0 < weight x) (order : Equiv.Perm (Fin d)) :
    FirstFresh.iidStream (RandomRanking.ofWeights weight)
      (discoveryEvent p.candidates.toFinset (List.ofFn (fun r ↦ p.remaining (order r)))) =
      (orderedLikelihood (fun r ↦ weight (p.remaining r)) order : ℝ≥0∞) := by
  induction d with
  | zero => simp [discoveryEvent, orderedLikelihood]
  | succ d ih =>
    obtain ⟨⟨q, tail⟩, rfl⟩ := Equiv.Perm.decomposeFin.symm.surjective order
    rw [remaining_orderList, discoveryEvent_cons_measure _ _ _ _ (by
      simpa using p.remaining_not_mem q), FirstFresh.firstValue_ofWeights weight hw _ _ (by
        simpa using p.remaining_not_mem q)]
    have hS : insert (p.remaining q) p.candidates.toFinset =
        (p.appendNext q).candidates.toFinset := by
      rw [RankingPrefix.candidates_appendNext]
      ext x
      simp [or_comm]
    rw [hS, ih, orderedLikelihood_decompose, ENNReal.coe_mul]
    simp only [List.mem_toFinset]
    rw [← p.sum_remaining weight]
    simp only [remaining_appendNext]
    rfl

/-- Full first-occurrence orders have the literal PR ranking likelihood. -/
theorem discovery_order_measure {n : ℕ} [NeZero n] (weight : Fin n → ℝ≥0)
    (hw : ∀ x, 0 < weight x) (order : Equiv.Perm (Fin n)) :
    FirstFresh.iidStream (RandomRanking.ofWeights weight)
      (discoveryEvent ∅ (List.ofFn order)) =
        (orderedLikelihood weight order : ℝ≥0∞) := by
  simpa only [RankingPrefix.candidates, List.toFinset_nil, RankingPrefix.remaining,
    Function.Embedding.refl_apply] using
    discoveryEvent_remaining_measure RankingPrefix.empty weight hw order

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- An exposed discovery head is fresh and occurs after only excluded draws. -/
theorem mem_discoveryEvent_cons (S : Finset α) (q : α) (L : List α) (x : ℕ → α) :
    x ∈ discoveryEvent S (q :: L) ↔ q ∉ S ∧ ∃ k,
      (∀ t < k, x t ∈ S) ∧ x k = q ∧
        FirstFresh.tailAfter k x ∈ discoveryEvent (insert q S) L := by
  classical
  by_cases hq : q ∈ S <;> simp [discoveryEvent, hq, FirstFresh.hitAt, and_assoc]

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Equal-length discovery lists are determined uniquely by the actual stream. -/
theorem discoveryEvent_unique (S : Finset α) (L M : List α) (x : ℕ → α)
    (hL : x ∈ discoveryEvent S L) (hM : x ∈ discoveryEvent S M)
    (hlen : L.length = M.length) : L = M := by
  induction L generalizing S M x with
  | nil => cases M <;> simp_all
  | cons q L ih =>
    cases M with
    | nil => simp at hlen
    | cons r M =>
      obtain ⟨hq, k, hk, hxq, htail⟩ := (mem_discoveryEvent_cons _ _ _ _).mp hL
      obtain ⟨hr, l, hl, hxr, htail'⟩ := (mem_discoveryEvent_cons _ _ _ _).mp hM
      have hkl : k = l := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · exact hq (hxq ▸ hl k h)
        · exact hr (hxr ▸ hk l h)
      subst l
      have hqr : q = r := hxq.symm.trans hxr
      rw [← hqr] at htail'
      exact congrArg₂ List.cons hqr (ih _ _ _ htail htail' (by simpa using hlen))

/-- A candidate-to-rank permutation agrees with the complete first-discovery order. -/
def rankEvent {n : ℕ} (rank : Equiv.Perm (Fin n)) : Set (ℕ → Fin n) :=
  discoveryEvent ∅ (List.ofFn rank.symm)

/-- Complete discovery ranks are uniquely determined on every stream where they exist. -/
theorem rankEvent_unique {n : ℕ} (x : ℕ → Fin n) (r s : Equiv.Perm (Fin n))
    (hr : x ∈ rankEvent r) (hs : x ∈ rankEvent s) : r = s := by
  have hlist := discoveryEvent_unique ∅ _ _ x hr hs (by simp)
  have hfun := List.ofFn_injective hlist
  have heq : r.symm = s.symm := Equiv.ext (fun q ↦ congrFun hfun q)
  simpa using congrArg Equiv.symm heq

/-- Each full discovery-rank event is measurable. -/
theorem measurableSet_rankEvent {n : ℕ} (r : Equiv.Perm (Fin n)) :
    MeasurableSet (rankEvent r) := measurableSet_discoveryEvent _ _

/-- Exact PR mass for each candidate-to-rank first-occurrence permutation. -/
theorem rankEvent_measure {n : ℕ} [NeZero n] (weight : Fin n → ℝ≥0)
    (hw : ∀ x, 0 < weight x) (rank : Equiv.Perm (Fin n)) :
    FirstFresh.iidStream (RandomRanking.ofWeights weight) (rankEvent rank) =
      (RandomRanking.likelihood weight rank : ℝ≥0∞) := by
  simpa only [rankEvent, orderedLikelihood_eq, Equiv.symm_symm] using
    discovery_order_measure weight hw rank.symm

/-- Almost all IID streams determine a complete first-occurrence ranking. -/
theorem ae_exists_rank {n : ℕ} [NeZero n] (weight : Fin n → ℝ≥0)
    (hw : ∀ x, 0 < weight x) :
    ∀ᵐ x ∂FirstFresh.iidStream (RandomRanking.ofWeights weight),
      ∃ r, x ∈ rankEvent r := by
  have hdisj : Pairwise (fun r s : Equiv.Perm (Fin n) ↦
      Disjoint (rankEvent r) (rankEvent s)) := by
    intro r s hrs
    rw [Set.disjoint_left]
    intro x hr hs
    exact hrs (rankEvent_unique x r s hr hs)
  have hm : FirstFresh.iidStream (RandomRanking.ofWeights weight) (⋃ r, rankEvent r) = 1 := by
    rw [measure_iUnion hdisj measurableSet_rankEvent, tsum_fintype]
    simp_rw [rankEvent_measure weight hw]
    rw [← ENNReal.ofNNReal_finsetSum, likelihood_sum_one weight hw, ENNReal.coe_one]
  rw [ae_iff]
  have heq : {x : ℕ → Fin n | ¬∃ r, x ∈ rankEvent r} = (⋃ r, rankEvent r)ᶜ := by
    ext x
    simp
  rw [heq, measure_compl (MeasurableSet.iUnion measurableSet_rankEvent)
    (measure_ne_top _ _), measure_univ, hm, tsub_self]

open scoped Classical in
/-- The actual first-occurrence rank, with an arbitrary default only if no full order exists. -/
noncomputable def iidRank {n : ℕ} (x : ℕ → Fin n) : Equiv.Perm (Fin n) :=
  if h : ∃ r, x ∈ rankEvent r then Classical.choose h else Equiv.refl _

/-- On a full discovery event the constructed rank is exactly its unique candidate-to-rank map. -/
theorem iidRank_eq_of_mem {n : ℕ} (x : ℕ → Fin n) (r : Equiv.Perm (Fin n))
    (hr : x ∈ rankEvent r) : iidRank x = r := by
  rw [iidRank, dite_eq_left ⟨r, hr⟩]
  exact rankEvent_unique x _ r (Classical.choose_spec
    (show ∃ s, x ∈ rankEvent s from ⟨r, hr⟩)) hr

/-- Every fiber of the total first-occurrence ranking is measurable. -/
theorem measurableSet_iidRank_fiber {n : ℕ} (r : Equiv.Perm (Fin n)) :
    MeasurableSet {x : ℕ → Fin n | iidRank x = r} := by
  classical
  have heq : {x : ℕ → Fin n | iidRank x = r} = rankEvent r ∪
      (if r = Equiv.refl _ then (⋃ s, rankEvent s)ᶜ else ∅) := by
    ext x
    change (iidRank x = r) ↔ x ∈ rankEvent r ∨
      x ∈ (if r = Equiv.refl _ then (⋃ s, rankEvent s)ᶜ else ∅)
    by_cases hx : ∃ s, x ∈ rankEvent s
    · obtain ⟨s, hs⟩ := hx
      rw [show iidRank x = s from iidRank_eq_of_mem x s hs]
      by_cases hsr : s = r
      · subst s
        simp [hs]
      · have hxr : x ∉ rankEvent r := fun hr ↦ hsr (rankEvent_unique x s r hs hr)
        simp [hxr, hsr, show ∃ s, x ∈ rankEvent s from ⟨s, hs⟩]
    · have hxall : ∀ s, x ∉ rankEvent s := fun s hs ↦ hx ⟨s, hs⟩
      have hxr : x ∉ rankEvent r := fun hr ↦ hx ⟨r, hr⟩
      simp [iidRank, hxr, hxall, eq_comm]
  rw [heq]
  apply (measurableSet_rankEvent r).union
  split_ifs
  · exact (MeasurableSet.iUnion measurableSet_rankEvent).compl
  · exact MeasurableSet.empty

/-- The first-occurrence ranking is measurable into the discrete permutation space. -/
theorem measurable_iidRank {n : ℕ} :
    @Measurable (ℕ → Fin n) (Equiv.Perm (Fin n)) inferInstance ⊤ iidRank := by
  let : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  apply measurable_to_countable
  intro x
  exact measurableSet_iidRank_fiber (iidRank x)

/-- The constructed ranking agrees with complete actual first discoveries almost surely. -/
theorem ae_rankEvent_iidRank {n : ℕ} [NeZero n] (weight : Fin n → ℝ≥0)
    (hw : ∀ x, 0 < weight x) :
    ∀ᵐ x ∂FirstFresh.iidStream (RandomRanking.ofWeights weight),
      x ∈ rankEvent (iidRank x) := by
  filter_upwards [ae_exists_rank weight hw] with x hx
  obtain ⟨r, hr⟩ := hx
  simpa only [iidRank_eq_of_mem x r hr] using hr

/-- The total first-occurrence rank has the exact PR likelihood at every singleton. -/
theorem iidRank_singleton {n : ℕ} [NeZero n] (weight : Fin n → ℝ≥0)
    (hw : ∀ x, 0 < weight x) (r : Equiv.Perm (Fin n)) :
    FirstFresh.iidStream (RandomRanking.ofWeights weight) {x | iidRank x = r} =
      (RandomRanking.likelihood weight r : ℝ≥0∞) := by
  rw [← rankEvent_measure weight hw r]
  apply measure_congr
  filter_upwards [ae_rankEvent_iidRank weight hw] with x hx
  apply propext
  constructor
  · intro hr
    simpa only [hr] using hx
  · exact iidRank_eq_of_mem x r

/-- Pushforward of IID first occurrences is exactly the unchanged normalized PR row law. -/
theorem iidRank_law {n : ℕ} [NeZero n] (weight : Fin n → ℝ≥0)
    (hw : ∀ x, 0 < weight x) :
    @Measure.map (ℕ → Fin n) (Equiv.Perm (Fin n)) inferInstance ⊤ iidRank
      (FirstFresh.iidStream (RandomRanking.ofWeights weight)) =
    @PMF.toMeasure (Equiv.Perm (Fin n)) ⊤
      (RandomRanking.ofWeights (RandomRanking.likelihood weight)) := by
  let : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  apply Measure.ext_of_singleton
  intro r
  rw [Measure.map_apply measurable_iidRank (measurableSet_singleton r),
    PMF.toMeasure_apply_singleton _ r (measurableSet_singleton r), row_ofWeights_apply weight hw]
  exact iidRank_singleton weight hw r

open scoped Classical in
/-- The concrete discovery algorithm takes each first fresh index and resumes strictly after it. -/
noncomputable def discoveryList (S : Finset α) : ℕ → (ℕ → α) → List α
  | 0, _ => []
  | k + 1, x => if h : ∃ t, x t ∉ S then
      x (Nat.find h) :: discoveryList (insert (x (Nat.find h)) S) k
        (FirstFresh.tailAfter (Nat.find h) x)
    else []

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The concrete first-fresh algorithm realizes exactly the recursive discovery event. -/
theorem discoveryEvent_iff_discoveryList (S : Finset α) (L : List α) (x : ℕ → α) :
    x ∈ discoveryEvent S L ↔ discoveryList S L.length x = L := by
  classical
  induction L generalizing S x with
  | nil => simp [discoveryEvent, discoveryList]
  | cons q L ih =>
    by_cases hex : ∃ t, x t ∉ S
    · constructor
      · intro hdisc
        obtain ⟨hq, k, hk, hxq, htail⟩ := (mem_discoveryEvent_cons _ _ _ _).mp hdisc
        have hfind : Nat.find hex = k := by
          have hle := Nat.find_min' hex (hxq ▸ hq)
          have hge : k ≤ Nat.find hex := by
            by_contra hnot
            have hkfind := hk (Nat.find hex) (by omega)
            exact Nat.find_spec hex hkfind
          omega
        simp only [List.length_cons, discoveryList, dite_eq_left hex, hfind]
        rw [hxq]
        exact congrArg (List.cons q) ((ih _ _).mp htail)
      · intro hlist
        simp only [List.length_cons, discoveryList, dite_eq_left hex] at hlist
        obtain ⟨hhead, htail⟩ := List.cons.inj hlist
        rw [hhead] at htail
        apply (mem_discoveryEvent_cons _ _ _ _).mpr
        refine ⟨hhead ▸ Nat.find_spec hex, Nat.find hex, ?_, hhead, (ih _ _).mpr htail⟩
        intro t ht
        exact not_not.mp (Nat.find_min hex ht)
    · constructor
      · intro hdisc
        obtain ⟨hq, k, _, hxq, _⟩ := (mem_discoveryEvent_cons _ _ _ _).mp hdisc
        exact False.elim (hex ⟨k, hxq ▸ hq⟩)
      · simp [discoveryList, hex]

/-- The concrete discovery algorithm is measurable as a list-valued function. -/
theorem measurable_discoveryList (S : Finset α) (k : ℕ) :
    @Measurable (ℕ → α) (List α) inferInstance ⊤ (discoveryList S k) := by
  classical
  let : MeasurableSpace (List α) := ⊤
  change Measurable (discoveryList S k)
  induction k generalizing S with
  | zero => exact measurable_const
  | succ k ih =>
    let A : Set (ℕ → α) := {x | ∃ t, x t ∉ S}
    have hA : MeasurableSet A := by
      have heq : A = ⋃ t, {x : ℕ → α | x t ∉ S} := by ext x; simp [A]
      rw [heq]
      exact MeasurableSet.iUnion fun t ↦ ((S.measurableSet).preimage
        (measurable_pi_apply t)).compl
    have hf (t : ℕ) : Measurable (fun x : ℕ → α ↦ x t ::
        discoveryList (insert (x t) S) k (FirstFresh.tailAfter t x)) := by
      have hrec : Measurable (fun y : α × (ℕ → α) ↦
          discoveryList (insert y.1 S) k y.2) :=
        measurable_from_prod_countable_right (fun q ↦ ih (insert q S))
      have hcons : Measurable (fun y : α × List α ↦ y.1 :: y.2) :=
        measurable_of_countable _
      exact hcons.comp ((measurable_pi_apply t).prodMk
        (hrec.comp ((measurable_pi_apply t).prodMk (FirstFresh.measurable_tailAfter t))))
    have hfound : Measurable (fun x : A ↦ x.val (Nat.find x.property) ::
        discoveryList (insert (x.val (Nat.find x.property)) S) k
          (FirstFresh.tailAfter (Nat.find x.property) x.val)) := by
      exact Measurable.find (p := fun t (x : A) ↦ x.val t ∉ S)
        (f := fun t (x : A) ↦ x.val t :: discoveryList (insert (x.val t) S) k
          (FirstFresh.tailAfter t x.val))
        (fun t ↦ (hf t).comp measurable_subtype_coe)
        (fun t ↦ ((S.measurableSet).preimage
          ((measurable_pi_apply t).comp measurable_subtype_coe)).compl)
        (fun x ↦ x.property)
    convert Measurable.dite hfound (measurable_const (a := ([] : List α))) hA using 1
    funext x
    dsimp only [discoveryList, A]
    split_ifs <;> simp_all

/-- The concrete full discovery list agrees almost surely with the constructed PR-law rank. -/
theorem ae_discoveryList_iidRank {n : ℕ} [NeZero n] (weight : Fin n → ℝ≥0)
    (hw : ∀ x, 0 < weight x) :
    ∀ᵐ x ∂FirstFresh.iidStream (RandomRanking.ofWeights weight),
      discoveryList ∅ n x = List.ofFn (iidRank x).symm := by
  filter_upwards [ae_rankEvent_iidRank weight hw] with x hx
  have h := (discoveryEvent_iff_discoveryList ∅ (List.ofFn (iidRank x).symm) x).mp hx
  simpa only [List.length_ofFn] using h

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Computing more distinct discoveries extends the same concrete discovery list. -/
theorem discoveryList_prefix (S : Finset α) (k l : ℕ) (hkl : k ≤ l) (x : ℕ → α) :
    (discoveryList S k x).IsPrefix (discoveryList S l x) := by
  classical
  induction k generalizing S l x with
  | zero => simp [discoveryList]
  | succ k ih =>
    cases l with
    | zero => omega
    | succ l =>
      simp only [discoveryList]
      split_ifs
      · exact List.cons_prefix_cons.mpr ⟨rfl, ih _ _ (by omega) _⟩
      · simp

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Every candidate in a discovery event actually occurs in the original unshifted stream. -/
theorem discoveryEvent_seen (S : Finset α) (L : List α) (x : ℕ → α)
    (h : x ∈ discoveryEvent S L) (q : α) (hq : q ∈ L) : ∃ t, x t = q := by
  induction L generalizing S x with
  | nil => simp at hq
  | cons r L ih =>
    obtain ⟨_, k, _, hxr, htail⟩ := (mem_discoveryEvent_cons _ _ _ _).mp h
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨k, hxr⟩
    · obtain ⟨t, ht⟩ := ih _ _ htail hq
      exact ⟨k + 1 + t, ht⟩

/-- All finite initial discoveries agree almost surely with prefixes of the same PR-law rank. -/
theorem ae_discoveryList_prefix_iidRank {n : ℕ} [NeZero n] (weight : Fin n → ℝ≥0)
    (hw : ∀ x, 0 < weight x) :
    ∀ᵐ x ∂FirstFresh.iidStream (RandomRanking.ofWeights weight), ∀ k ≤ n,
      (discoveryList ∅ k x).IsPrefix (List.ofFn (iidRank x).symm) := by
  filter_upwards [ae_discoveryList_iidRank weight hw] with x hx
  intro k hk
  rw [← hx]
  exact discoveryList_prefix ∅ k n hk x

/-- Every candidate is eventually seen in the actual IID stream, simultaneously almost surely. -/
theorem ae_all_candidates_seen {n : ℕ} [NeZero n] (weight : Fin n → ℝ≥0)
    (hw : ∀ x, 0 < weight x) :
    ∀ᵐ x ∂FirstFresh.iidStream (RandomRanking.ofWeights weight), ∀ q, ∃ t, x t = q := by
  filter_upwards [ae_rankEvent_iidRank weight hw] with x hx
  intro q
  apply discoveryEvent_seen ∅ _ x hx q
  exact List.mem_ofFn.mpr ⟨iidRank x q, (iidRank x).symm_apply_apply q⟩

end IIDRanking

end Ashlagi
