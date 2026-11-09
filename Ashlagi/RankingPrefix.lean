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

public import Ashlagi.RankingLaw

/-! # Exact weighted ranking transitions after finite exposed prefixes

A prefix records the successive residual relabelings used by `Equiv.Perm.decomposeFin`.
Its public candidate list is a list of original labels; rankings map candidates to ranks.
-/

@[expose] public section

namespace Ashlagi

open scoped NNReal ENNReal

/-- A prefix of a ranking on `n` candidates, leaving exactly `d` candidates unexposed. -/
inductive RankingPrefix : ℕ → ℕ → Type
  | empty {n : ℕ} : RankingPrefix n n
  | cons {n d : ℕ} (first : Fin (n + 1)) (tail : RankingPrefix n d) :
      RankingPrefix (n + 1) d

namespace RankingPrefix

/-- The residual labels after choosing `first`, in the convention of `decomposeFin`. -/
def residual {n : ℕ} (first : Fin (n + 1)) : Fin n ↪ Fin (n + 1) :=
  ⟨fun x ↦ Equiv.swap 0 first x.succ,
    (Equiv.swap 0 first).injective.comp (Fin.succ_injective n)⟩

/-- Unexposed candidates as original labels. -/
def remaining {n d : ℕ} : RankingPrefix n d → (Fin d ↪ Fin n)
  | .empty => Function.Embedding.refl _
  | .cons first tail => tail.remaining.trans (residual first)

/-- The exposed candidates, in preference order, as original labels. -/
def candidates {n d : ℕ} : RankingPrefix n d → List (Fin n)
  | .empty => []
  | .cons first tail => first :: tail.candidates.map (residual first)

/-- Matching a prefix is a recursive condition on candidate-order permutations. -/
def Matches {n d : ℕ} : RankingPrefix n d → Equiv.Perm (Fin n) → Prop
  | .empty, _ => True
  | .cons first tail, order =>
      (Equiv.Perm.decomposeFin order).1 = first ∧
        tail.Matches (Equiv.Perm.decomposeFin order).2

/-- The literal sum of PR likelihoods of orders extending the prefix. -/
noncomputable def mass {n d : ℕ} (p : RankingPrefix n d)
    (weight : Fin n → ℝ≥0) : ℝ≥0 := by
  classical
  exact ∑ order : Equiv.Perm (Fin n),
    if p.Matches order then orderedLikelihood weight order else 0

/-- Appending one unexposed candidate consumes exactly one residual label. -/
def appendNext {n d : ℕ} (p : RankingPrefix n (d + 1)) (q : Fin (d + 1)) :
    RankingPrefix n d := by
  cases p with
  | empty => exact .cons q .empty
  | cons first tail => exact .cons first (tail.appendNext q)
termination_by n

/-- The list interpretation of appending a residual label uses its original candidate label. -/
theorem candidates_appendNext {n d : ℕ} (p : RankingPrefix n (d + 1)) (q : Fin (d + 1)) :
    (p.appendNext q).candidates = p.candidates ++ [p.remaining q] := by
  induction n with
  | zero => cases p
  | succ n ih =>
    cases p with
    | empty => rw [appendNext]; rfl
    | cons first tail =>
      rw [appendNext]
      simp only [candidates, ih, List.map_append, List.map_cons, List.map_nil,
        List.cons_append, remaining, Function.Embedding.trans_apply]

/-- Empty-prefix mass is exactly one, including the zero-candidate market. -/
theorem mass_empty {n : ℕ} (weight : Fin n → ℝ≥0) (hw : ∀ x, 0 < weight x) :
    (empty : RankingPrefix n n).mass weight = 1 := by
  simpa [mass, Matches] using orderedLikelihood_sum_one weight hw

/-- Summing out complete residual orders gives the exact first-choice recursion. -/
theorem mass_cons {n d : ℕ} (first : Fin (n + 1)) (tail : RankingPrefix n d)
    (weight : Fin (n + 1) → ℝ≥0) :
    (cons first tail).mass weight = weight first / (∑ x, weight x) *
      tail.mass (fun x ↦ weight (residual first x)) := by
  classical
  unfold mass
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  simp only [Matches, Equiv.apply_symm_apply, orderedLikelihood_decompose]
  rw [Finset.sum_eq_single first]
  · simp only [true_and]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro order _
    by_cases h : tail.Matches order <;> simp [h, residual]
  · intro other _ hother
    simp [hother]
  · simp

/-- Every possible exposed prefix has positive mass under positive weights. -/
theorem mass_pos {n d : ℕ} (p : RankingPrefix n d) (weight : Fin n → ℝ≥0)
    (hw : ∀ x, 0 < weight x) : 0 < p.mass weight := by
  induction p with
  | empty => rw [mass_empty weight hw]; exact zero_lt_one
  | cons first tail ih =>
    rw [mass_cons]
    exact mul_pos (div_pos (hw first)
      (Finset.sum_pos (fun x _ ↦ hw x) Finset.univ_nonempty))
      (ih _ (fun x ↦ hw _))

/-- The exact next-choice kernel after an arbitrary exposed ranking prefix. -/
theorem mass_appendNext {n d : ℕ} (p : RankingPrefix n (d + 1))
    (weight : Fin n → ℝ≥0) (hw : ∀ x, 0 < weight x) (q : Fin (d + 1)) :
    (p.appendNext q).mass weight =
      weight (p.remaining q) / (∑ r, weight (p.remaining r)) * p.mass weight := by
  induction n with
  | zero => cases p
  | succ n ih =>
    cases p with
    | empty =>
      rw [appendNext, mass_cons, mass_empty _ (fun x ↦ hw _), mass_empty _ hw]
      simp [remaining]
    | cons first tail =>
      rw [appendNext, mass_cons, mass_cons, ih _ _ (fun x ↦ hw _)]
      simp only [remaining, Function.Embedding.trans_apply]
      ring

/-- Residual labels omit precisely the candidate just exposed. -/
theorem residual_range {n : ℕ} (first x : Fin (n + 1)) :
    (∃ q, residual first q = x) ↔ x ≠ first := by
  constructor
  · rintro ⟨q, rfl⟩ h
    have hh := Equiv.swap_apply_eq_iff.mp h
    simp at hh
  · intro hx
    have hz : Equiv.swap 0 first x ≠ 0 := by
      intro heq
      have hh := Equiv.swap_apply_eq_iff.mp heq
      exact hx (by simpa using hh)
    obtain hzero | ⟨q, hq⟩ := Fin.eq_zero_or_eq_succ (Equiv.swap 0 first x)
    · exact False.elim (hz hzero)
    · refine ⟨q, ?_⟩
      change Equiv.swap 0 first q.succ = x
      rw [← hq, Equiv.swap_apply_self]

/-- Every recorded prefix has the expected length. -/
theorem length_candidates_add {n d : ℕ} (p : RankingPrefix n d) :
    p.candidates.length + d = n := by
  induction p with
  | empty => simp [candidates]
  | cons first tail ih => simp only [candidates, List.length_cons, List.length_map]; omega

/-- An unexposed candidate cannot occur in the exposed list. -/
theorem remaining_not_mem {n d : ℕ} (p : RankingPrefix n d) (q : Fin d) :
    p.remaining q ∉ p.candidates := by
  induction p with
  | empty => simp [candidates]
  | cons first tail ih =>
    simp only [remaining, Function.Embedding.trans_apply, candidates, List.mem_cons,
      List.mem_map, not_or]
    constructor
    · exact (residual_range first _).mp ⟨_, rfl⟩
    · rintro ⟨a, ha, heq⟩
      exact ih q ((residual first).injective heq ▸ ha)

/-- The original labels of every exposed prefix are distinct. -/
theorem nodup_candidates {n d : ℕ} (p : RankingPrefix n d) : p.candidates.Nodup := by
  induction p with
  | empty => simp [candidates]
  | cons first tail ih =>
    change (first :: tail.candidates.map (residual first)).Nodup
    apply List.nodup_cons.mpr
    constructor
    · rw [List.mem_map]
      rintro ⟨a, _, ha⟩
      exact ((residual_range first _).mp ⟨a, rfl⟩) ha
    · exact ih.map (residual first).injective

/-- Every unseen original candidate has a unique residual label. -/
theorem remaining_range {n d : ℕ} (p : RankingPrefix n d) (x : Fin n) :
    (∃ q, p.remaining q = x) ↔ x ∉ p.candidates := by
  constructor
  · rintro ⟨q, rfl⟩
    exact p.remaining_not_mem q
  · induction p with
    | empty => intro _; exact ⟨x, rfl⟩
    | cons first tail ih =>
      intro hx
      have hxfirst : x ≠ first := by
        intro heq
        exact hx (by simp [candidates, heq])
      obtain ⟨y, rfl⟩ := (residual_range first x).mpr hxfirst
      have hy : y ∉ tail.candidates := by
        intro hmem
        exact hx (by simp [candidates, hmem])
      obtain ⟨q, hq⟩ := ih y hy
      exact ⟨q, congrArg (residual first) hq⟩

/-- The decomposition lists the first candidate and then the relabeled residual order. -/
theorem orderList_decompose {n : ℕ} (first : Fin (n + 1))
    (tail : Equiv.Perm (Fin n)) :
    List.ofFn (Equiv.Perm.decomposeFin.symm (first, tail)) =
      first :: (List.ofFn tail).map (residual first) := by
  rw [List.ofFn_succ, Equiv.Perm.decomposeFin_symm_apply_zero, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext x
  exact Equiv.Perm.decomposeFin_symm_apply_succ tail first x

/-- The recursive prefix event is exactly the usual prefix of the candidate-order list. -/
theorem matches_iff_prefix {n d : ℕ} (p : RankingPrefix n d)
    (order : Equiv.Perm (Fin n)) :
    p.Matches order ↔ p.candidates.IsPrefix (List.ofFn order) := by
  induction p with
  | empty => simp [Matches, candidates]
  | cons first tail ih =>
    obtain ⟨⟨a, t⟩, rfl⟩ := Equiv.Perm.decomposeFin.symm.surjective order
    rw [orderList_decompose]
    simp only [Matches, Equiv.apply_symm_apply, candidates, List.cons_prefix_cons]
    constructor
    · rintro ⟨rfl, ht⟩
      exact ⟨rfl, (ih t).mp ht |>.map _⟩
    · rintro ⟨rfl, ht⟩
      exact ⟨rfl, (ih t).mpr ((List.prefix_map_iff_of_injective
        (residual first).injective).mp ht)⟩

/-- Every distinct finite list of admissible length has a prefix representation. -/
theorem exists_candidates_eq {n : ℕ} (L : List (Fin n)) (hL : L.Nodup)
    (hlen : L.length ≤ n) : ∃ d, ∃ p : RankingPrefix n d, p.candidates = L := by
  induction L using List.reverseRecOn with
  | nil => exact ⟨n, empty, rfl⟩
  | append_singleton L x ih =>
    have hh : x ∉ L ∧ L.Nodup := by
      simpa only [List.singleton_append, List.nodup_cons] using
        (List.nodup_append_comm.mp hL)
    have hprior : L.length ≤ n := by
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    obtain ⟨d, p, hp⟩ := ih hh.2 hprior
    have hd : 0 < d := by
      have := p.length_candidates_add
      simp only [List.length_append, List.length_singleton] at hlen
      rw [hp] at this
      omega
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
    obtain ⟨q, hq⟩ := (p.remaining_range x).mpr (hp ▸ hh.1)
    exact ⟨d, p.appendNext q, by rw [candidates_appendNext, hp, hq]⟩

/-- Summing weights over residual labels is exactly summing over unseen original candidates. -/
theorem sum_remaining {n d : ℕ} (p : RankingPrefix n d) (weight : Fin n → ℝ≥0) :
    (∑ q, weight (p.remaining q)) = ∑ x with x ∉ p.candidates, weight x := by
  classical
  apply Finset.sum_bij (fun q _ ↦ p.remaining q)
  · intro q _
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using p.remaining_not_mem q
  · intro a _ b _ hab
    exact p.remaining.injective hab
  · intro x hx
    obtain ⟨q, hq⟩ := (p.remaining_range x).mpr (Finset.mem_filter.mp hx).2
    exact ⟨q, Finset.mem_univ _, hq⟩
  · simp

end RankingPrefix

/-- Total literal PR likelihood of candidate-to-rank permutations starting with a given list.
The inverse permutation lists candidates in preference order.
-/
noncomputable def prefixLikelihood {n : ℕ} (weight : Fin n → ℝ≥0)
    (L : List (Fin n)) : ℝ≥0 := by
  classical
  exact ∑ rank : Equiv.Perm (Fin n),
    if L.IsPrefix (List.ofFn rank.symm) then RandomRanking.likelihood weight rank else 0

/-- The recursive prefix mass equals the PR likelihood sum in candidate-to-rank orientation. -/
theorem RankingPrefix.mass_eq_prefixLikelihood {n d : ℕ} (p : RankingPrefix n d)
    (weight : Fin n → ℝ≥0) : p.mass weight = prefixLikelihood weight p.candidates := by
  classical
  let inv : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) :=
    ⟨Equiv.symm, Equiv.symm, Equiv.symm_symm, Equiv.symm_symm⟩
  unfold RankingPrefix.mass prefixLikelihood
  rw [← Equiv.sum_comp inv]
  apply Finset.sum_congr rfl
  intro order _
  simp only [inv, Equiv.coe_fn_mk, Equiv.symm_symm, orderedLikelihood_eq,
    RankingPrefix.matches_iff_prefix]

/-- Exact weighted next-destination law after any distinct exposed candidate list. -/
theorem prefixLikelihood_append {n : ℕ} (weight : Fin n → ℝ≥0)
    (hw : ∀ x, 0 < weight x) (L : List (Fin n)) (hL : L.Nodup)
    (hlen : L.length < n) (q : Fin n) (hq : q ∉ L) :
    prefixLikelihood weight (L ++ [q]) =
      weight q / (∑ x with x ∉ L, weight x) * prefixLikelihood weight L := by
  obtain ⟨d, p, hp⟩ := RankingPrefix.exists_candidates_eq L hL hlen.le
  have hd : 0 < d := by
    have := p.length_candidates_add
    rw [hp] at this
    omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  obtain ⟨r, hr⟩ := (p.remaining_range q).mpr (hp ▸ hq)
  have h := p.mass_appendNext weight hw r
  rw [RankingPrefix.mass_eq_prefixLikelihood, RankingPrefix.mass_eq_prefixLikelihood,
    RankingPrefix.candidates_appendNext, p.sum_remaining, hp, hr] at h
  exact h

/-- The empty-prefix likelihood is one for every market size, including zero. -/
theorem prefixLikelihood_nil {n : ℕ} (weight : Fin n → ℝ≥0) (hw : ∀ x, 0 < weight x) :
    prefixLikelihood weight [] = 1 := by
  simpa only [RankingPrefix.candidates] using (RankingPrefix.mass_eq_prefixLikelihood
    (RankingPrefix.empty : RankingPrefix n n)
    weight).symm.trans (RankingPrefix.mass_empty weight hw)

/-- Every admissible distinct prefix has strictly positive PR mass. -/
theorem prefixLikelihood_pos {n : ℕ} (weight : Fin n → ℝ≥0) (hw : ∀ x, 0 < weight x)
    (L : List (Fin n)) (hL : L.Nodup) (hlen : L.length ≤ n) :
    0 < prefixLikelihood weight L := by
  obtain ⟨d, p, hp⟩ := RankingPrefix.exists_candidates_eq L hL hlen
  rw [← hp, ← p.mass_eq_prefixLikelihood]
  exact p.mass_pos weight hw

/-- Dividing the extended-prefix mass by the positive prefix mass gives the exact next law. -/
theorem prefixLikelihood_next_conditional {n : ℕ} (weight : Fin n → ℝ≥0)
    (hw : ∀ x, 0 < weight x) (L : List (Fin n)) (hL : L.Nodup)
    (hlen : L.length < n) (q : Fin n) (hq : q ∉ L) :
    prefixLikelihood weight (L ++ [q]) / prefixLikelihood weight L =
      weight q / (∑ x with x ∉ L, weight x) := by
  rw [prefixLikelihood_append weight hw L hL hlen q hq]
  exact mul_div_cancel_right₀ _ (ne_of_gt (prefixLikelihood_pos weight hw L hL hlen.le))

/-- Probability of a specified exposed preference list under the exact PR row distribution. -/
noncomputable def prefixProbability {n : ℕ} (weight : Fin n → ℝ≥0)
    (L : List (Fin n)) : ℝ≥0∞ :=
  letI : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  (RandomRanking.ofWeights (RandomRanking.likelihood weight)).toMeasure
    {rank | L.IsPrefix (List.ofFn rank.symm)}

/-- The PR row normalizer leaves the literal prefix-likelihood sum unchanged. -/
theorem prefixProbability_eq_likelihood {n : ℕ} (weight : Fin n → ℝ≥0)
    (hw : ∀ x, 0 < weight x) (L : List (Fin n)) :
    prefixProbability weight L = (prefixLikelihood weight L : ℝ≥0∞) := by
  classical
  rw [prefixProbability, @PMF.toMeasure_apply _ ⊤ _ _ (by trivial), tsum_fintype]
  unfold prefixLikelihood
  rw [ENNReal.ofNNReal_finsetSum]
  apply Finset.sum_congr rfl
  intro rank _
  by_cases h : L.IsPrefix (List.ofFn rank.symm)
  · simp [h, row_ofWeights_apply weight hw]
  · simp [h]

/-- The exact PR row measure obeys the weighted residual next-destination transition. -/
theorem prefixProbability_append {n : ℕ} (weight : Fin n → ℝ≥0)
    (hw : ∀ x, 0 < weight x) (L : List (Fin n)) (hL : L.Nodup)
    (hlen : L.length < n) (q : Fin n) (hq : q ∉ L) :
    prefixProbability weight (L ++ [q]) =
      (weight q / (∑ x with x ∉ L, weight x) : ℝ≥0) * prefixProbability weight L := by
  rw [prefixProbability_eq_likelihood weight hw, prefixProbability_eq_likelihood weight hw,
    prefixLikelihood_append weight hw L hL hlen q hq, ENNReal.coe_mul]

/-- Conditioning on any admissible prefix is legitimate: its exact PR probability is positive. -/
theorem prefixProbability_pos {n : ℕ} (weight : Fin n → ℝ≥0) (hw : ∀ x, 0 < weight x)
    (L : List (Fin n)) (hL : L.Nodup) (hlen : L.length ≤ n) :
    0 < prefixProbability weight L := by
  rw [prefixProbability_eq_likelihood weight hw]
  exact_mod_cast prefixLikelihood_pos weight hw L hL hlen

/-- The probability ratio for the nested prefix events is exactly the residual weighted law. -/
theorem prefixProbability_next_conditional {n : ℕ} (weight : Fin n → ℝ≥0)
    (hw : ∀ x, 0 < weight x) (L : List (Fin n)) (hL : L.Nodup)
    (hlen : L.length < n) (q : Fin n) (hq : q ∉ L) :
    prefixProbability weight (L ++ [q]) / prefixProbability weight L =
      (weight q / (∑ x with x ∉ L, weight x) : ℝ≥0) := by
  rw [prefixProbability_eq_likelihood weight hw, prefixProbability_eq_likelihood weight hw,
    ← ENNReal.coe_div (ne_of_gt (prefixLikelihood_pos weight hw L hL hlen.le)),
    prefixLikelihood_next_conditional weight hw L hL hlen q hq]

/-- A full distinct prefix leaves no possible next candidate. -/
theorem mem_of_full_prefix {n : ℕ} (L : List (Fin n)) (hL : L.Nodup)
    (hlen : L.length = n) (q : Fin n) : q ∈ L := by
  obtain ⟨d, p, hp⟩ := RankingPrefix.exists_candidates_eq L hL hlen.le
  have hd : d = 0 := by
    have := p.length_candidates_add
    rw [hp, hlen] at this
    omega
  by_contra hq
  obtain ⟨r, _⟩ := (p.remaining_range q).mpr (hp ▸ hq)
  subst d
  exact Fin.elim0 r

end Ashlagi
