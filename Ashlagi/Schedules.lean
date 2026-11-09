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

public import Ashlagi.DA

/-! # Schedule independence for deferred acceptance with a fixed active entrant set

The chosen-man transition uses the exact preference comparisons and counter update of
`StableMarriage.proposalStep`. Reachable terminal proposal relations are the least relations
closed under initial proposals and rejection followed by the next proposal.
-/

@[expose] public section

namespace Ashlagi.Schedules

open StableMarriage

/-- A man may propose exactly when active, free, and not at the end of his strict list. -/
def Eligible {n : ℕ} (A : Finset (Fin n)) (s : ProposalState n) (m : Fin n) : Prop :=
  m ∈ A ∧ s.next m < n ∧ ∀ w, s.held w ≠ some m

/-- One genuine proposal by a specified man, with the PR's exact acceptance comparison. -/
def propose {n : ℕ} (p : Profile n) (s : ProposalState n) (m : Fin n)
    (hn : s.next m < n) : ProposalState n :=
  let w := (p.manRank m).symm ⟨s.next m, hn⟩
  let accept := match s.held w with
    | none => true
    | some old => decide (p.womanRank w m < p.womanRank w old)
  ⟨Function.update s.next m (s.next m + 1),
    if accept then Function.update s.held w (some m) else s.held⟩

/-- A finite admissible DA execution; the scheduler may choose any eligible active man. -/
inductive Reachable {n : ℕ} (p : Profile n) (A : Finset (Fin n)) : ProposalState n → Prop
  | initial : Reachable p A ⟨fun _ ↦ 0, fun _ ↦ none⟩
  | step {s : ProposalState n} (hs : Reachable p A s) (m : Fin n)
      (hm : Eligible A s m) : Reachable p A (propose p s m hm.2.1)

/-- Termination means no active, free man has an untried candidate. -/
def Terminal {n : ℕ} (A : Finset (Fin n)) (s : ProposalState n) : Prop :=
  ∀ m, ¬ Eligible A s m

/-- A held man's counter ends immediately after the woman who currently holds him. -/
def LatestHolds {n : ℕ} (p : Profile n) (s : ProposalState n) : Prop :=
  ∀ w m, s.held w = some m → s.next m = (p.manRank m w).val + 1

/-- The concrete invariants of every admissible finite execution. -/
structure Valid {n : ℕ} (p : Profile n) (A : Finset (Fin n)) (s : ProposalState n) : Prop where
  next_le : ∀ m, s.next m ≤ n
  best : BestHolds p s
  latest : LatestHolds p s
  held_injective : HeldInjective s
  inactive : ∀ m, m ∉ A → s.next m = 0

/-- A genuine chosen-man proposal preserves best holdings. -/
theorem propose_bestHolds {n : ℕ} (p : Profile n) (s : ProposalState n)
    (hs : BestHolds p s) (m : Fin n) (hn : s.next m < n) :
    BestHolds p (propose p s m hn) := by
  unfold propose
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

/-- A genuine proposal preserves the latest-held-counter invariant. -/
theorem propose_latestHolds {n : ℕ} (p : Profile n) (s : ProposalState n)
    (hs : LatestHolds p s) (m : Fin n) (hn : s.next m < n)
    (hfree : ∀ w, s.held w ≠ some m) : LatestHolds p (propose p s m hn) := by
  classical
  let w := (p.manRank m).symm ⟨s.next m, hn⟩
  unfold propose
  dsimp only
  split_ifs with ha
  · intro v k hheld
    change Function.update s.held w (some m) v = some k at hheld
    by_cases hv : v = w
    · subst v
      have hk : m = k := by simpa [w] using hheld
      subst k
      simp [w]
    · have hold : s.held v = some k := by
        simpa only [Function.update_of_ne hv] using hheld
      have hkm : k ≠ m := fun heq ↦ hfree v (heq ▸ hold)
      simpa only [Function.update_of_ne hkm] using hs v k hold
  · intro v k hheld
    have hkm : k ≠ m := fun heq ↦ hfree v (heq ▸ hheld)
    simpa only [Function.update_of_ne hkm] using hs v k hheld

/-- The full invariant is preserved by every genuine eligible proposal. -/
theorem propose_valid {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    (s : ProposalState n) (hs : Valid p A s) (m : Fin n) (hm : Eligible A s m) :
    Valid p A (propose p s m hm.2.1) := by
  classical
  constructor
  · intro k
    change Function.update s.next m (s.next m + 1) k ≤ n
    by_cases hk : k = m
    · subst k
      simp only [Function.update_self]
      exact hm.2.1
    · simpa only [Function.update_of_ne hk] using hs.next_le k
  · exact propose_bestHolds p s hs.best m hm.2.1
  · exact propose_latestHolds p s hs.latest m hm.2.1 hm.2.2
  · unfold propose
    dsimp only
    split_ifs
    · exact heldInjective_update s hs.held_injective _ m hm.2.2 _
    · exact hs.held_injective
  · intro k hk
    have hkm : k ≠ m := fun h ↦ hk (h ▸ hm.1)
    change Function.update s.next m (s.next m + 1) k = 0
    simpa only [Function.update_of_ne hkm] using hs.inactive k hk

/-- Every reachable state has bounded counters, best holdings, unique holders and active support. -/
theorem reachable_valid {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {s : ProposalState n} (hs : Reachable p A s) : Valid p A s := by
  induction hs with
  | initial =>
    constructor
    · intro m
      exact Nat.zero_le _
    · simp [BestHolds, HasProposed]
    · simp [LatestHolds]
    · simp [HeldInjective]
    · simp
  | step hs m hm ih => exact propose_valid p A _ ih m hm

/-- Every proposal in an admissible run was made by an active man. -/
theorem proposed_active {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {s : ProposalState n} (hs : Reachable p A s) {m w : Fin n}
    (hprop : HasProposed p s m w) : m ∈ A := by
  by_contra hm
  have hz := (reachable_valid p A hs).inactive m hm
  simp [HasProposed, hz] at hprop

/-- Every active entrant is held at termination, even when some other men are inactive. -/
theorem terminal_active_held {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {s : ProposalState n} (hs : Reachable p A s) (ht : Terminal A s)
    (m : Fin n) (hm : m ∈ A) : ∃ w, s.held w = some m := by
  classical
  have hv := reachable_valid p A hs
  by_cases hn : s.next m < n
  · by_contra hnone
    exact ht m ⟨hm, hn, fun w hw ↦ hnone ⟨w, hw⟩⟩
  · have heq : s.next m = n := Nat.le_antisymm (hv.next_le m) (Nat.le_of_not_gt hn)
    have hall (w : Fin n) : ∃ k, s.held w = some k := by
      have hp : HasProposed p s m w := by
        simp only [HasProposed, heq]
        exact (p.manRank m w).isLt
      obtain ⟨k, hk, _⟩ := (hv.best w).2 m hp
      exact ⟨k, hk⟩
    choose f hf using hall
    have hinj : Function.Injective f := by
      intro u v huv
      exact hv.held_injective u v (f u) (hf u) (by simpa [huv] using hf v)
    obtain ⟨w, hw⟩ := Finite.surjective_of_injective hinj m
    exact ⟨w, hw ▸ hf w⟩

/-- A relation is rejection-closed when it contains active men's first proposals and their
successive proposals whenever a strictly better proposer reaches the previous woman. -/
structure RejectionClosed {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    (S : Fin n → Fin n → Prop) : Prop where
  first : ∀ m, m ∈ A → ∀ w, (p.manRank m w).val = 0 → S m w
  next : ∀ m, m ∈ A → ∀ w v k, S m w → S k w →
    p.womanRank w k < p.womanRank w m →
    (p.manRank m v).val = (p.manRank m w).val + 1 → S m v

/-- Hard kernel: every admissible execution's proposal relation lies in every rejection-closed
relation. The induction uses actual free-man eligibility and best holdings, not terminality. -/
theorem reachable_proposals_subset_closed {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    (S : Fin n → Fin n → Prop) (hS : RejectionClosed p A S)
    {s : ProposalState n} (hs : Reachable p A s) :
    ∀ m w, HasProposed p s m w → S m w := by
  classical
  induction hs with
  | initial => simp [HasProposed]
  | @step s hs m hm ih =>
    intro k v hp
    rcases (hasProposed_update_iff p s m hm.2.1
      (propose p s m hm.2.1).held k v).mp hp with hold | ⟨hkm, hv⟩
    · exact ih k v hold
    · subst k
      subst v
      by_cases hz : s.next m = 0
      · exact hS.first m hm.1 _ (by simp [hz])
      · let w := (p.manRank m).symm ⟨s.next m - 1, by have hn := hm.2.1; omega⟩
        have hw : HasProposed p s m w := by
          simp only [HasProposed, w, Equiv.apply_symm_apply]
          omega
        have hv := reachable_valid p A hs
        obtain ⟨old, hheld, hdom⟩ := (hv.best w).2 m hw
        have hne : old ≠ m := fun heq ↦ hm.2.2 w (heq ▸ hheld)
        have hlt : p.womanRank w old < p.womanRank w m := by
          apply lt_of_le_of_ne hdom
          intro heq
          exact hne ((p.womanRank w).injective heq)
        exact hS.next m hm.1 w _ old (ih m w hw)
          (ih old w ((hv.best w).1 old hheld)) hlt (by simp [w]; omega)

/-- A terminal execution's queried relation is itself rejection-closed. -/
theorem terminal_proposals_closed {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {s : ProposalState n} (hs : Reachable p A s) (ht : Terminal A s) :
    RejectionClosed p A (HasProposed p s) := by
  have hv := reachable_valid p A hs
  constructor
  · intro m hm w hw
    obtain ⟨v, hheld⟩ := terminal_active_held p A hs ht m hm
    have hlast := hv.latest v m hheld
    change (p.manRank m w).val < s.next m
    omega
  · intro m hm w v k hmw hkw hbetter hsucc
    by_contra hnot
    have hnext : s.next m = (p.manRank m w).val + 1 := by
      unfold HasProposed at hmw hnot
      omega
    obtain ⟨u, hheld⟩ := terminal_active_held p A hs ht m hm
    have hlast := hv.latest u m hheld
    have hrank : p.manRank m u = p.manRank m w := Fin.ext (by omega)
    have huw : u = w := (p.manRank m).injective hrank
    subst u
    obtain ⟨old, hold, hdom⟩ := (hv.best w).2 k hkw
    have heq : old = m := Option.some.inj (hold.symm.trans hheld)
    subst old
    exact (not_lt_of_ge hdom) hbetter

/-- Any two terminal admissible schedules have exactly the same proposal relation, for any
fixed active entrant subset (in particular, leave-one-out and leave-two-out markets). -/
theorem terminal_proposals_iff {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {s t : ProposalState n} (hs : Reachable p A s) (ht : Reachable p A t)
    (hsT : Terminal A s) (htT : Terminal A t) (m w : Fin n) :
    HasProposed p s m w ↔ HasProposed p t m w :=
  ⟨reachable_proposals_subset_closed p A _ (terminal_proposals_closed p A ht htT) hs m w,
    reachable_proposals_subset_closed p A _ (terminal_proposals_closed p A hs hsT) ht m w⟩

/-- The total number of genuinely made proposals never exceeds n² in any schedule. -/
theorem reachable_potential_le {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {s : ProposalState n} (hs : Reachable p A s) : potential s ≤ n * n := by
  calc
    potential s ≤ ∑ _m : Fin n, n :=
      Finset.sum_le_sum fun m _ ↦ (reachable_valid p A hs).next_le m
    _ = n * n := by simp

/-- Every genuine chosen-man update strictly increases the proposal potential. -/
theorem propose_potential_lt {n : ℕ} (p : Profile n) (s : ProposalState n)
    (m : Fin n) (hn : s.next m < n) : potential s < potential (propose p s m hn) := by
  classical
  change ∑ x, s.next x < ∑ x, Function.update s.next m (s.next m + 1) x
  apply Finset.sum_lt_sum
  · intro x _
    simp only [Function.update_apply]
    split_ifs with hx
    · subst x
      omega
    · exact le_rfl
  · exact ⟨m, Finset.mem_univ _, by simp⟩

/-- Every active-entrant market has a terminal admissible execution. Continuing genuine
eligible proposals must terminate because the proposal potential is bounded. -/
theorem exists_terminal {n : ℕ} (p : Profile n) (A : Finset (Fin n)) :
    ∃ s, Reachable p A s ∧ Terminal A s := by
  classical
  have aux : ∀ k, ∀ s : ProposalState n, Reachable p A s →
      n * n - potential s = k → ∃ t, Reachable p A t ∧ Terminal A t := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro s hs hk
      by_cases ht : Terminal A s
      · exact ⟨s, hs, ht⟩
      · have hex : ∃ m, Eligible A s m := by simpa only [Terminal, not_forall, not_not] using ht
        obtain ⟨m, hm⟩ := hex
        let t := propose p s m hm.2.1
        have hr : Reachable p A t := Reachable.step hs m hm
        have hb := reachable_potential_le p A hr
        have hi := propose_potential_lt p s m hm.2.1
        have hsmall : n * n - potential t < k := by
          change potential s < potential t at hi
          omega
        exact ih _ hsmall t hr rfl
  exact aux _ _ Reachable.initial rfl

/-- Bounded prefix counters are determined by the complete queried-edge relation. -/
theorem next_eq_of_proposals_iff {n : ℕ} (p : Profile n) (s t : ProposalState n)
    (hs : ∀ m, s.next m ≤ n) (ht : ∀ m, t.next m ≤ n)
    (heq : ∀ m w, HasProposed p s m w ↔ HasProposed p t m w) : s.next = t.next := by
  funext m
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · let w := (p.manRank m).symm ⟨s.next m, by have hb := ht m; omega⟩
    have hp : HasProposed p t m w := by simpa only [HasProposed, w,
      Equiv.apply_symm_apply] using hlt
    have hbad := (heq m w).mpr hp
    simp [HasProposed, w] at hbad
  · let w := (p.manRank m).symm ⟨t.next m, by have hb := hs m; omega⟩
    have hp : HasProposed p s m w := by simpa only [HasProposed, w,
      Equiv.apply_symm_apply] using hgt
    have hbad := (heq m w).mp hp
    simp [HasProposed, w] at hbad

/-- Best holdings are determined by the queried relation for strict preferences. -/
theorem held_eq_of_proposals_iff {n : ℕ} (p : Profile n) (s t : ProposalState n)
    (hs : BestHolds p s) (ht : BestHolds p t)
    (heq : ∀ m w, HasProposed p s m w ↔ HasProposed p t m w) : s.held = t.held := by
  funext w
  cases hsw : s.held w with
  | none =>
    cases htw : t.held w with
    | none => rfl
    | some m =>
      obtain ⟨k, hk, _⟩ := (hs w).2 m ((heq m w).mpr ((ht w).1 m htw))
      simp [hsw] at hk
  | some m =>
    obtain ⟨k, hk, hkm⟩ := (ht w).2 m ((heq m w).mp ((hs w).1 m hsw))
    obtain ⟨old, hold, hom⟩ := (hs w).2 k ((heq k w).mpr ((ht w).1 k hk))
    have holdm : old = m := Option.some.inj (hold.symm.trans hsw)
    subst old
    have hmk : m = k := (p.womanRank w).injective (le_antisymm hom hkm)
    simpa [hmk] using hk.symm

/-- Full terminal states, including proposal counters and tentative partners, are independent
of the eligible free-man schedule for each fixed active entrant subset. -/
theorem terminal_state_eq {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {s t : ProposalState n} (hs : Reachable p A s) (ht : Reachable p A t)
    (hsT : Terminal A s) (htT : Terminal A t) : s = t := by
  have heq := terminal_proposals_iff p A hs ht hsT htT
  have hn := next_eq_of_proposals_iff p s t (reachable_valid p A hs).next_le
    (reachable_valid p A ht).next_le heq
  have hh := held_eq_of_proposals_iff p s t (reachable_valid p A hs).best
    (reachable_valid p A ht).best heq
  cases s
  cases t
  cases hn
  cases hh
  rfl

/-- One PR first-free-man transition is either padding or an admissible all-entrant proposal. -/
theorem proposalStep_reachable {n : ℕ} (p : Profile n) {s : ProposalState n}
    (hs : Reachable p Finset.univ s) : Reachable p Finset.univ (proposalStep p s) := by
  classical
  cases hfind : (List.finRange n).find?
      (fun m ↦ s.next m < n ∧ ∀ w, s.held w ≠ some m) with
  | none => simpa only [proposalStep, hfind] using hs
  | some m =>
    have hm : s.next m < n ∧ ∀ w, s.held w ≠ some m := by
      simpa using List.find?_some hfind
    have heq : proposalStep p s = propose p s m hm.1 := by
      simp only [proposalStep, hfind, dite_eq_left hm.1, propose]
      rfl
    rw [heq]
    exact Reachable.step hs m ⟨Finset.mem_univ m, hm⟩

/-- Every prefix of the PR's exact fixed first-free schedule is admissible. -/
theorem pr_run_reachable {n : ℕ} (p : Profile n) (t : ℕ) :
    Reachable p Finset.univ (run p t) := by
  induction t with
  | zero => exact Reachable.initial
  | succ t ih =>
    rw [run, Function.iterate_succ_apply']
    exact proposalStep_reachable p ih

/-- The exact PR terminal state is a reachable terminal all-entrant execution. -/
theorem pr_terminal {n : ℕ} (p : Profile n) :
    Reachable p Finset.univ (deferredAcceptance p) ∧
      Terminal Finset.univ (deferredAcceptance p) := by
  refine ⟨pr_run_reachable p (n * n), ?_⟩
  intro m hm
  obtain ⟨w, hw⟩ := fixed_no_eligible p _ (terminal_fixed p) m hm.2.1
  exact hm.2.2 w hw

/-- Any terminal eligible-man schedule with all entrants has exactly the PR's queried pairs. -/
theorem terminal_proposals_iff_pr {n : ℕ} (p : Profile n) {s : ProposalState n}
    (hs : Reachable p Finset.univ s) (ht : Terminal Finset.univ s) (m w : Fin n) :
    HasProposed p s m w ↔ HasProposed p (deferredAcceptance p) m w :=
  terminal_proposals_iff p Finset.univ hs (pr_terminal p).1 ht (pr_terminal p).2 m w

/-- Any terminal eligible-man schedule with all entrants has the exact PR terminal state. -/
theorem terminal_state_eq_pr {n : ℕ} (p : Profile n) {s : ProposalState n}
    (hs : Reachable p Finset.univ s) (ht : Terminal Finset.univ s) :
    s = deferredAcceptance p :=
  terminal_state_eq p Finset.univ hs (pr_terminal p).1 ht (pr_terminal p).2

/-- An inactive man is never held in an admissible execution. -/
theorem held_active {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {s : ProposalState n} (hs : Reachable p A s) {w m : Fin n}
    (hh : s.held w = some m) : m ∈ A :=
  proposed_active p A hs ((reachable_valid p A hs).best w |>.1 m hh)

/-- Terminal holdings cover exactly the active entrants; `Valid.held_injective` gives uniqueness. -/
theorem terminal_held_iff_active {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {s : ProposalState n} (hs : Reachable p A s) (ht : Terminal A s) (m : Fin n) :
    (∃ w, s.held w = some m) ↔ m ∈ A := by
  constructor
  · rintro ⟨w, hw⟩
    exact held_active p A hs hw
  · exact terminal_active_held p A hs ht m

/-- An execution remains admissible when previously inactive additional entrants are admitted. -/
theorem reachable_mono_active {n : ℕ} (p : Profile n) {A B : Finset (Fin n)}
    (hAB : A ⊆ B) {s : ProposalState n} (hs : Reachable p A s) : Reachable p B s := by
  induction hs with
  | initial => exact Reachable.initial
  | step hs m hm ih => exact Reachable.step ih m ⟨hAB hm.1, hm.2⟩

/-- Every proposal from a smaller entrant set occurs in any terminal run of a larger entrant
set. This follows from rejection closure, without coupling or a probabilistic assumption. -/
theorem reachable_proposals_subset_larger_terminal {n : ℕ} (p : Profile n)
    {A B : Finset (Fin n)} (hAB : A ⊆ B) {s t : ProposalState n}
    (hs : Reachable p A s) (ht : Reachable p B t) (htT : Terminal B t)
    (m w : Fin n) : HasProposed p s m w → HasProposed p t m w :=
  reachable_proposals_subset_closed p B _ (terminal_proposals_closed p B ht htT)
    (reachable_mono_active p hAB hs) m w

/-- There is exactly one reachable terminal state for every fixed entrant subset. -/
theorem existsUnique_terminal {n : ℕ} (p : Profile n) (A : Finset (Fin n)) :
    ∃! s, Reachable p A s ∧ Terminal A s := by
  obtain ⟨s, hs, ht⟩ := exists_terminal p A
  refine ⟨s, ⟨hs, ht⟩, ?_⟩
  intro t hterm
  exact terminal_state_eq p A hterm.1 hs hterm.2 ht

/-- Deferred acceptance with only the specified active entrants. Uniqueness makes this
independent of the chosen witness and of every admissible terminating schedule. -/
noncomputable def activeDeferredAcceptance {n : ℕ} (p : Profile n) (A : Finset (Fin n)) :
    ProposalState n := Classical.choose (exists_terminal p A)

/-- The partial-entrant terminal state has a genuine admissible terminating execution. -/
theorem activeDeferredAcceptance_spec {n : ℕ} (p : Profile n) (A : Finset (Fin n)) :
    Reachable p A (activeDeferredAcceptance p A) ∧
      Terminal A (activeDeferredAcceptance p A) :=
  Classical.choose_spec (exists_terminal p A)

/-- Every admissible terminating schedule realizes the partial-entrant DA state. -/
theorem terminal_state_eq_active {n : ℕ} (p : Profile n) (A : Finset (Fin n))
    {s : ProposalState n} (hs : Reachable p A s) (ht : Terminal A s) :
    s = activeDeferredAcceptance p A :=
  terminal_state_eq p A hs (activeDeferredAcceptance_spec p A).1 ht
    (activeDeferredAcceptance_spec p A).2

/-- Activating every man specializes partial-entrant DA to the exact PR implementation. -/
theorem activeDeferredAcceptance_univ {n : ℕ} (p : Profile n) :
    activeDeferredAcceptance p Finset.univ = deferredAcceptance p :=
  terminal_state_eq_pr p (activeDeferredAcceptance_spec p Finset.univ).1
    (activeDeferredAcceptance_spec p Finset.univ).2

/-- Removing entrants can only remove proposed edges. This includes arbitrary leave-one and
leave-two entrant subsets and compares exact prefix-counter semantics. -/
theorem active_proposals_mono {n : ℕ} (p : Profile n) {A B : Finset (Fin n)}
    (hAB : A ⊆ B) (m w : Fin n) :
    HasProposed p (activeDeferredAcceptance p A) m w →
      HasProposed p (activeDeferredAcceptance p B) m w :=
  reachable_proposals_subset_larger_terminal p hAB (activeDeferredAcceptance_spec p A).1
    (activeDeferredAcceptance_spec p B).1 (activeDeferredAcceptance_spec p B).2 m w

end Ashlagi.Schedules
