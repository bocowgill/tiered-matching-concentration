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

public import FormalConjecturesForMathlib.Combinatorics.StableMarriage.DeferredAcceptance
public import Mathlib.Tactic

/-! # Proposal-count semantics for the exact deferred-acceptance implementation -/

@[expose] public section

namespace TieredMatching

open StableMarriage

/-- The state after `t` proposal attempts, using the PR's exact transition. -/
def run {n : ℕ} (p : Profile n) (t : ℕ) : ProposalState n :=
  (proposalStep p)^[t] ⟨fun _ ↦ 0, fun _ ↦ none⟩

/-- A pair has been queried precisely when its rank is below the man's counter. -/
def HasProposed {n : ℕ} (p : Profile n) (s : ProposalState n) (m w : Fin n) : Prop :=
  (p.manRank m w).val < s.next m

instance {n : ℕ} (p : Profile n) (s : ProposalState n) (m w : Fin n) :
    Decidable (HasProposed p s m w) := inferInstanceAs (Decidable ((p.manRank m w).val < s.next m))

/-- Distinct tier-`j` proposers received by a woman in the terminal PR state. -/
noncomputable def proposalCount {n J : ℕ} (manTier : Fin n → Fin J) (j : Fin J)
    (p : Profile n) (w : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter fun m ↦ manTier m = j ∧
    HasProposed p (deferredAcceptance p) m w).card

/-- One step preserves the upper bound of every proposal counter. -/
theorem step_next_le {n : ℕ} (p : Profile n) (s : ProposalState n)
    (hs : ∀ m, s.next m ≤ n) (m : Fin n) : (proposalStep p s).next m ≤ n := by
  unfold proposalStep
  split
  · exact hs m
  · split
    · simp only [Function.update_apply]
      split_ifs with hm
      · subst m
        omega
      · exact hs m
    · exact hs m

/-- Counters never decrease. -/
theorem step_next_mono {n : ℕ} (p : Profile n) (s : ProposalState n) (m : Fin n) :
    s.next m ≤ (proposalStep p s).next m := by
  unfold proposalStep
  split
  · exact le_rfl
  · split
    · simp only [Function.update_apply]
      split_ifs with hm
      · subst m
        omega
      · exact le_rfl
    · exact le_rfl

/-- No man makes more than `n` proposals during the exact iteration. -/
theorem run_next_le {n : ℕ} (p : Profile n) (t : ℕ) (m : Fin n) :
    (run p t).next m ≤ n := by
  induction t generalizing m with
  | zero => exact Nat.zero_le n
  | succ t ih =>
    rw [run, Function.iterate_succ_apply']
    exact step_next_le p (run p t) ih m

/-- At terminal time, the counter still counts a prefix of a strict list. -/
theorem terminal_next_le {n : ℕ} (p : Profile n) (m : Fin n) :
    (deferredAcceptance p).next m ≤ n := run_next_le p (n * n) m

/-- A proposal count cannot exceed the number of men in that tier. -/
theorem proposalCount_le_tier {n J : ℕ} (manTier : Fin n → Fin J) (j : Fin J)
    (p : Profile n) (w : Fin n) :
    proposalCount manTier j p w ≤ (Finset.univ.filter fun m ↦ manTier m = j).card := by
  classical
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
  exact hm.1

/-- The strict-list counter never counts a woman twice. -/
theorem proposed_prefix_card {n : ℕ} (p : Profile n) (m : Fin n) :
    (Finset.univ.filter fun w ↦ HasProposed p (deferredAcceptance p) m w).card =
      (deferredAcceptance p).next m := by
  classical
  let s := (deferredAcceptance p).next m
  have hs : s ≤ n := terminal_next_le p m
  have hmap : (Finset.univ.filter fun w ↦ HasProposed p (deferredAcceptance p) m w).image
      (p.manRank m) = Finset.univ.filter fun k : Fin n ↦ k.val < s := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hk
      exact ⟨(p.manRank m).symm k, by simpa [HasProposed] using hk, by simp⟩
  rw [← Finset.card_image_of_injective _ (p.manRank m).injective, hmap]
  rw [Fin.card_filter_val_lt, Nat.min_eq_right hs]

/-- The number of distinct proposals already made in a state. -/
def potential {n : ℕ} (s : ProposalState n) : ℕ := ∑ m, s.next m

/-- Each genuine transition strictly increases the total proposal count. -/
theorem step_eq_or_potential_lt {n : ℕ} (p : Profile n) (s : ProposalState n) :
    proposalStep p s = s ∨ potential s < potential (proposalStep p s) := by
  unfold proposalStep
  split
  · exact Or.inl rfl
  · split
    · right
      rename_i m hfind hlt
      change ∑ x, s.next x < ∑ x, Function.update s.next m (s.next m + 1) x
      apply Finset.sum_lt_sum
      · intro x _
        simp only [Function.update_apply]
        split_ifs with hx
        · subst x
          omega
        · exact le_rfl
      · exact ⟨m, Finset.mem_univ _, by simp⟩
    · exact Or.inl rfl

/-- The total proposal count never exceeds `n²`. -/
theorem run_potential_le {n : ℕ} (p : Profile n) (t : ℕ) :
    potential (run p t) ≤ n * n := by
  calc
    potential (run p t) ≤ ∑ _m : Fin n, n :=
      Finset.sum_le_sum fun m _ ↦ run_next_le p t m
    _ = n * n := by simp

/-- Before the process becomes fixed, it has made at least one proposal per elapsed step. -/
theorem time_le_potential_or_fixed {n : ℕ} (p : Profile n) (t : ℕ) :
    t ≤ potential (run p t) ∨ proposalStep p (run p t) = run p t := by
  induction t with
  | zero => exact Or.inl (Nat.zero_le _)
  | succ t ih =>
    rw [run, Function.iterate_succ_apply']
    change t + 1 ≤ potential (proposalStep p (run p t)) ∨
      proposalStep p (proposalStep p (run p t)) = proposalStep p (run p t)
    rcases ih with htime | hfixed
    · rcases step_eq_or_potential_lt p (run p t) with hfixed | hlt
      · exact Or.inr (congrArg (proposalStep p) hfixed)
      · exact Or.inl (by omega)
    · exact Or.inr (congrArg (proposalStep p) hfixed)

/-- The PR's `n²`-step terminal state is a genuine fixed point of deferred acceptance. -/
theorem terminal_fixed {n : ℕ} (p : Profile n) :
    proposalStep p (deferredAcceptance p) = deferredAcceptance p := by
  rcases time_le_potential_or_fixed p (n * n) with htime | hfixed
  · rcases step_eq_or_potential_lt p (run p (n * n)) with hfixed | hlt
    · exact hfixed
    · have hbound := run_potential_le p (n * n + 1)
      rw [run, Function.iterate_succ_apply'] at hbound
      change potential (proposalStep p (run p (n * n))) ≤ n * n at hbound
      omega
  · exact hfixed

/-- Incrementing one counter adds exactly its next woman to the proposed-pair set. -/
theorem hasProposed_update_iff {n : ℕ} (p : Profile n) (s : ProposalState n) (m : Fin n)
    (hn : s.next m < n) (held : Fin n → Option (Fin n)) (m' w' : Fin n) :
    HasProposed p ⟨Function.update s.next m (s.next m + 1), held⟩ m' w' ↔
      HasProposed p s m' w' ∨
        m' = m ∧ w' = (p.manRank m).symm ⟨s.next m, hn⟩ := by
  by_cases hm : m' = m
  · subst m'
    simp only [HasProposed, Function.update_self, true_and]
    rw [Equiv.eq_symm_apply, Fin.ext_iff]
    exact Nat.lt_succ_iff_lt_or_eq
  · simp [HasProposed, hm]

/-- The next candidate in a strict list has not been queried along this edge before. -/
theorem next_not_hasProposed {n : ℕ} (p : Profile n) (s : ProposalState n) (m : Fin n)
    (hn : s.next m < n) :
    ¬ HasProposed p s m ((p.manRank m).symm ⟨s.next m, hn⟩) := by
  simp [HasProposed]

/-- Every held man has proposed, and every proposed pair is weakly worse for the woman than
the man she currently holds. The latter clause also guarantees that she holds a man. -/
def BestHolds {n : ℕ} (p : Profile n) (s : ProposalState n) : Prop :=
  ∀ w, (∀ m, s.held w = some m → HasProposed p s m w) ∧
    (∀ m, HasProposed p s m w →
      ∃ k, s.held w = some k ∧ p.womanRank w k ≤ p.womanRank w m)

/-- A new proposal preserves the best-proposal invariant when the selected new holder is
one of the previous proposers or the new proposer and dominates both alternatives. -/
theorem bestHolds_update {n : ℕ} (p : Profile n) (s : ProposalState n) (hs : BestHolds p s)
    (m : Fin n) (hn : s.next m < n) (k : Fin n)
    (hk : HasProposed p s k ((p.manRank m).symm ⟨s.next m, hn⟩) ∨ k = m)
    (hkm : p.womanRank ((p.manRank m).symm ⟨s.next m, hn⟩) k ≤
      p.womanRank ((p.manRank m).symm ⟨s.next m, hn⟩) m)
    (hkold : ∀ old, s.held ((p.manRank m).symm ⟨s.next m, hn⟩) = some old →
      p.womanRank ((p.manRank m).symm ⟨s.next m, hn⟩) k ≤
        p.womanRank ((p.manRank m).symm ⟨s.next m, hn⟩) old) :
    BestHolds p ⟨Function.update s.next m (s.next m + 1),
      Function.update s.held ((p.manRank m).symm ⟨s.next m, hn⟩) (some k)⟩ := by
  intro w
  constructor
  · intro m' hheld
    by_cases hw : w = (p.manRank m).symm ⟨s.next m, hn⟩
    · subst w
      have hm' : k = m' := by simpa using hheld
      subst m'
      apply (hasProposed_update_iff p s m hn _ k _).mpr
      exact hk.elim Or.inl (fun h ↦ Or.inr ⟨h, rfl⟩)
    · have hold : s.held w = some m' := by simpa [Function.update_apply, hw] using hheld
      exact (hasProposed_update_iff p s m hn _ m' w).mpr (Or.inl ((hs w).1 m' hold))
  · intro m' hproposed
    rcases (hasProposed_update_iff p s m hn _ m' w).mp hproposed with hold | ⟨rfl, hw⟩
    · rcases (hs w).2 m' hold with ⟨old, hheld, hdom⟩
      by_cases hw : w = (p.manRank m).symm ⟨s.next m, hn⟩
      · subst w
        exact ⟨k, by simp, le_trans (hkold old hheld) hdom⟩
      · exact ⟨old, by simpa [Function.update_apply, hw] using hheld, hdom⟩
    · subst w
      exact ⟨k, by simp, hkm⟩

/-- The exact PR transition preserves the best-proposal invariant. -/
theorem step_bestHolds {n : ℕ} (p : Profile n) (s : ProposalState n)
    (hs : BestHolds p s) : BestHolds p (proposalStep p s) := by
  unfold proposalStep
  split
  · exact hs
  · split
    · rename_i m hfind hn
      dsimp only
      cases hheld : s.held ((p.manRank m).symm ⟨s.next m, hn⟩) with
      | none =>
        change BestHolds p ⟨Function.update s.next m (s.next m + 1),
          Function.update s.held ((p.manRank m).symm ⟨s.next m, hn⟩) (some m)⟩
        apply bestHolds_update p s hs m hn m (Or.inr rfl) le_rfl
        intro old hold
        simp [hheld] at hold
      | some old =>
        simp only [decide_eq_true_eq]
        split_ifs with hlt
        · apply bestHolds_update p s hs m hn m (Or.inr rfl) le_rfl
          intro old' hold'
          have heq : old' = old := Option.some.inj (hold'.symm.trans hheld)
          subst old'
          exact le_of_lt hlt
        · have hbest := bestHolds_update p s hs m hn old
            (Or.inl ((hs _).1 old hheld)) (le_of_not_gt hlt)
            (fun old' hold' ↦ le_of_eq (congrArg (p.womanRank _) (Option.some.inj
              (hheld.symm.trans hold'))))
          simpa only [← hheld, Function.update_eq_self] using hbest
    · exact hs

/-- The best-proposal invariant holds throughout the actual run. -/
theorem run_bestHolds {n : ℕ} (p : Profile n) (t : ℕ) : BestHolds p (run p t) := by
  induction t with
  | zero => simp [run, BestHolds, HasProposed]
  | succ t ih =>
    rw [run, Function.iterate_succ_apply']
    exact step_bestHolds p (run p t) ih

/-- Every woman holds her favorite among all men who have proposed to her. -/
theorem terminal_bestHolds {n : ℕ} (p : Profile n) :
    BestHolds p (deferredAcceptance p) := run_bestHolds p (n * n)

/-- A fixed state has no unmatched man with an untried candidate. -/
theorem fixed_no_eligible {n : ℕ} (p : Profile n) (s : ProposalState n)
    (hs : proposalStep p s = s) (m : Fin n) (hn : s.next m < n) :
    ∃ w, s.held w = some m := by
  have hnone : (List.finRange n).find?
      (fun k ↦ s.next k < n ∧ ∀ w, s.held w ≠ some k) = none := by
    cases hfind : (List.finRange n).find?
        (fun k ↦ s.next k < n ∧ ∀ w, s.held w ≠ some k) with
    | none => rfl
    | some k =>
      have hkbool := List.find?_some hfind
      have hk : s.next k < n ∧ ∀ w, s.held w ≠ some k := by simpa using hkbool
      have hnext := congrArg (fun state ↦ state.next k) hs
      unfold proposalStep at hnext
      simp only [hfind, ↓reduceDIte, hk.1, Function.update_self] at hnext
      omega
  have hnot := List.find?_eq_none.mp hnone m (by simp)
  by_contra hfree
  apply hnot
  exact decide_eq_true (And.intro hn (fun w hw ↦ hfree ⟨w, hw⟩))

/-- Every woman is matched in the exact terminal iteration, including all positive market
sizes. At size zero the quantifier has empty domain. -/
theorem terminal_has_holder {n : ℕ} (p : Profile n) (w : Fin n) :
    ∃ m, (deferredAcceptance p).held w = some m := by
  classical
  let s := deferredAcceptance p
  by_cases hex : ∃ m, s.next m = n
  · obtain ⟨m, hm⟩ := hex
    have hprop : HasProposed p s m w := by
      change (p.manRank m w).val < s.next m
      rw [hm]
      exact (p.manRank m w).isLt
    obtain ⟨k, hk, _⟩ := (terminal_bestHolds p w).2 m hprop
    exact ⟨k, hk⟩
  · have hmatch : ∀ m, ∃ v, s.held v = some m := by
      intro m
      apply fixed_no_eligible p s (terminal_fixed p) m
      have hle := terminal_next_le p m
      have hne : s.next m ≠ n := fun hm ↦ hex ⟨m, hm⟩
      change s.next m ≤ n at hle
      omega
    choose f hf using hmatch
    have hinj : Function.Injective f := by
      intro a b hab
      exact Option.some.inj ((hf a).symm.trans ((congrArg s.held hab).trans (hf b)))
    obtain ⟨m, hm⟩ := Finite.surjective_of_injective hinj w
    exact ⟨m, hm ▸ hf m⟩

/-- No man is simultaneously held by two different women. -/
def HeldInjective {n : ℕ} (s : ProposalState n) : Prop :=
  ∀ w w' m, s.held w = some m → s.held w' = some m → w = w'

/-- Assigning a previously free man to one woman preserves uniqueness of held men. -/
theorem heldInjective_update {n : ℕ} (s : ProposalState n) (hs : HeldInjective s)
    (w m : Fin n) (hfree : ∀ v, s.held v ≠ some m) (next : Fin n → ℕ) :
    HeldInjective ⟨next, Function.update s.held w (some m)⟩ := by
  intro u v k hu hv
  by_cases huw : u = w
  · subst u
    have hmk : m = k := by simpa using hu
    subst k
    by_cases hvw : v = w
    · exact hvw.symm
    · exact False.elim (hfree v (by simpa [Function.update_apply, hvw] using hv))
  · by_cases hvw : v = w
    · subst v
      have hmk : m = k := by simpa using hv
      subst k
      exact False.elim (hfree u (by simpa [Function.update_apply, huw] using hu))
    · exact hs u v k (by simpa [Function.update_apply, huw] using hu)
        (by simpa [Function.update_apply, hvw] using hv)

/-- The exact transition never causes a man to be held by two women. -/
theorem step_heldInjective {n : ℕ} (p : Profile n) (s : ProposalState n)
    (hs : HeldInjective s) : HeldInjective (proposalStep p s) := by
  unfold proposalStep
  split
  · exact hs
  · split
    · rename_i m hfind hn
      have hkbool := List.find?_some hfind
      have hk : s.next m < n ∧ ∀ w, s.held w ≠ some m := by simpa using hkbool
      dsimp only
      split_ifs
      · exact heldInjective_update s hs _ m hk.2 _
      · exact hs
    · exact hs

/-- No run state simultaneously holds a man at two different women. -/
theorem run_heldInjective {n : ℕ} (p : Profile n) (t : ℕ) :
    HeldInjective (run p t) := by
  induction t with
  | zero => simp [run, HeldInjective]
  | succ t ih =>
    rw [run, Function.iterate_succ_apply']
    exact step_heldInjective p (run p t) ih

/-- The terminal holding relation is injective on the men it holds. -/
theorem terminal_heldInjective {n : ℕ} (p : Profile n) :
    HeldInjective (deferredAcceptance p) := run_heldInjective p (n * n)

/-- The terminal state is exactly the holding relation of a complete matching, with the
matching oriented from men to women as in the PR's shared model. -/
theorem terminal_complete_matching {n : ℕ} (p : Profile n) :
    ∃ μ : Matching n, ∀ w, (deferredAcceptance p).held w = some (μ.symm w) := by
  classical
  choose f hf using terminal_has_holder p
  have hinj : Function.Injective f := by
    intro w v h
    exact terminal_heldInjective p w v (f w) (hf w) (by simpa [h] using hf v)
  exact ⟨(Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩).symm, hf⟩

/-- A held terminal man belongs to the proposer set and minimizes the woman's rank on it. -/
theorem terminal_held_isMinOn {n : ℕ} (p : Profile n) (w m : Fin n)
    (hheld : (deferredAcceptance p).held w = some m) :
    HasProposed p (deferredAcceptance p) m w ∧
      IsMinOn (p.womanRank w) {k | HasProposed p (deferredAcceptance p) k w} m := by
  refine ⟨(terminal_bestHolds p w).1 m hheld, ?_⟩
  intro k hk
  obtain ⟨old, hold, hdom⟩ := (terminal_bestHolds p w).2 k hk
  have heq : m = old := Option.some.inj (hheld.symm.trans hold)
  change p.womanRank w m ≤ p.womanRank w k
  simpa only [heq] using hdom

end TieredMatching
