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
public import Mathlib

/-! # Measurability of the concrete DA arrival policy -/

@[expose] public section

namespace Ashlagi.Arrival

open MeasureTheory

local instance {n : ℕ} : MeasurableSpace (StableMarriage.ProposalState n) := ⊤
local instance {n : ℕ} : MeasurableSpace (Equiv.Perm (Edge n)) := ⊤
local instance {n : ℕ} : MeasurableSpace (List (Edge n)) := ⊤

local instance {n : ℕ} : Countable (StableMarriage.ProposalState n) := by
  apply Function.Injective.countable
    (f := fun s : StableMarriage.ProposalState n ↦ (s.next, s.held))
  intro s t h
  cases s
  cases t
  cases h
  rfl

/-- A measurable countable-valued choice may select among measurable functions. -/
theorem measurable_choose_apply {Ω K Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Countable K] (choose : Ω → K) (f : K → Ω → Y)
    (hc : ∀ k, MeasurableSet {x | choose x = k}) (hf : ∀ k, Measurable (f k)) :
    Measurable (fun x ↦ f (choose x) x) := by
  intro s hs
  have heq : (fun x ↦ f (choose x) x) ⁻¹' s =
      ⋃ k, {x | choose x = k} ∩ (f k ⁻¹' s) := by
    ext x
    simp
  rw [heq]
  exact MeasurableSet.iUnion fun k ↦ (hc k).inter (hf k hs)

/-- The finite state after one raw update is a measurable function of the incoming value
and the previously held scores, for each fixed control state. -/
theorem measurable_advance_state_fixed {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Fin n → Equiv.Perm (Fin n)) (s : StableMarriage.ProposalState n)
    (scores : Ω → Fin n → ℝ) (v : Ω → ℝ)
    (hs : ∀ w, Measurable (fun x ↦ scores x w)) (hv : Measurable v) :
    Measurable (fun x ↦ (advance P ⟨s, scores x⟩ (v x)).state) := by
  classical
  cases he : nextEdge P s with
  | none => simpa only [advance, he] using
      (measurable_const : Measurable (fun _ : Ω ↦ s))
  | some q =>
    rcases q with ⟨w, m⟩
    cases hh : s.held w with
    | none => simpa only [advance, he, hh, ite_true] using
        (measurable_const : Measurable (fun _ : Ω ↦
          (⟨Function.update s.next m (s.next m + 1),
            Function.update s.held w (some m)⟩ : StableMarriage.ProposalState n)))
    | some old =>
      have heq : (fun x ↦ (advance P ⟨s, scores x⟩ (v x)).state) =
          (fun x ↦ if v x < scores x w then
            (⟨Function.update s.next m (s.next m + 1),
              Function.update s.held w (some m)⟩ : StableMarriage.ProposalState n)
            else ⟨Function.update s.next m (s.next m + 1), s.held⟩) := by
        funext x
        simp only [advance, he, hh, decide_eq_true_eq]
        split_ifs <;> rfl
      rw [heq]
      exact measurable_const.ite (measurableSet_lt hv (hs w)) measurable_const

/-- A single held-score update is measurable for fixed control state. -/
theorem measurable_advance_score_fixed {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Fin n → Equiv.Perm (Fin n)) (s : StableMarriage.ProposalState n)
    (scores : Ω → Fin n → ℝ) (v : Ω → ℝ)
    (hs : ∀ w, Measurable (fun x ↦ scores x w)) (hv : Measurable v) (w' : Fin n) :
    Measurable (fun x ↦ (advance P ⟨s, scores x⟩ (v x)).score w') := by
  classical
  have hu (w : Fin n) : Measurable (fun x ↦ Function.update (scores x) w (v x) w') := by
    by_cases hw : w' = w
    · simpa [Function.update_apply, hw] using hv
    · simpa [Function.update_apply, hw] using hs w'
  cases he : nextEdge P s with
  | none => simpa only [advance, he] using hs w'
  | some q =>
    rcases q with ⟨w, m⟩
    cases hh : s.held w with
    | none => simpa only [advance, he, hh, ite_true] using hu w
    | some old =>
      have heq : (fun x ↦ (advance P ⟨s, scores x⟩ (v x)).score w') =
          (fun x ↦ if v x < scores x w then Function.update (scores x) w (v x) w'
            else scores x w') := by
        funext x
        simp only [advance, he, hh, decide_eq_true_eq]
        split_ifs <;> rfl
      rw [heq]
      exact (hu w).ite (measurableSet_lt hv (hs w)) (hs w')

/-- The countable controls and each real held score in a generated replay are measurable. -/
theorem measurable_replay_history {n J : ℕ} [NeZero n]
    (P : Fin n → Equiv.Perm (Fin n)) (manTier : Fin n → Fin J) (t : ℕ) :
    Measurable (fun x : Edge n → ℝ ↦
      (replay P manTier (allocationHistory (pick P manTier) x t)).1.state) ∧
    Measurable (fun x : Edge n → ℝ ↦
      (replay P manTier (allocationHistory (pick P manTier) x t)).2) ∧
    Measurable (fun x : Edge n → ℝ ↦
      (allocationHistory (pick P manTier) x t).map Prod.fst) ∧
    ∀ w, Measurable (fun x : Edge n → ℝ ↦
      (replay P manTier (allocationHistory (pick P manTier) x t)).1.score w) := by
  classical
  induction t with
  | zero =>
    exact ⟨measurable_const, measurable_const, measurable_const, fun _ ↦ measurable_const⟩
  | succ t ih =>
    let history (x : Edge n → ℝ) := allocationHistory (pick P manTier) x t
    let old (x : Edge n → ℝ) := replay P manTier (history x)
    let scores (x : Edge n → ℝ) := (old x).1.score
    let Control := StableMarriage.ProposalState n × Equiv.Perm (Edge n) × List (Edge n)
    let control (x : Edge n → ℝ) : Control :=
      ((old x).1.state, (old x).2, (history x).map Prod.fst)
    let pair (k : Control) := pairForState P manTier ⟨k.1, fun _ ↦ 0⟩ k.2.1 k.2.2
    have hcontrol (k : Control) : MeasurableSet {x : Edge n → ℝ | control x = k} := by
      rcases k with ⟨s, π, keys⟩
      have hs : MeasurableSet {x : Edge n → ℝ | (old x).1.state = s} := by
        exact ih.1 (measurableSet_singleton s)
      have hr : MeasurableSet {x : Edge n → ℝ | (old x).2 = π} := by
        exact ih.2.1 (measurableSet_singleton π)
      have hk : MeasurableSet {x : Edge n → ℝ | (history x).map Prod.fst = keys} := by
        exact ih.2.2.1 (measurableSet_singleton keys)
      have heq : {x : Edge n → ℝ | control x = (s, π, keys)} =
          {x | (old x).1.state = s} ∩
            ({x | (old x).2 = π} ∩ {x | (history x).map Prod.fst = keys}) := by
        ext x
        constructor
        · intro h
          exact ⟨congrArg (fun k : Control ↦ k.1) h,
            congrArg (fun k : Control ↦ k.2.1) h, congrArg (fun k : Control ↦ k.2.2) h⟩
        · rintro ⟨hs, hr, hk⟩
          exact Prod.ext hs (Prod.ext hr hk)
      rw [heq]
      exact hs.inter (hr.inter hk)
    let value (x : Edge n → ℝ) := x (pair (control x)).1
    have hv : Measurable value :=
      measurable_choose_apply control (fun k x ↦ x (pair k).1) hcontrol
        (fun k ↦ measurable_pi_apply _)
    have hscore (w : Fin n) : Measurable (fun x : Edge n → ℝ ↦ scores x w) := ih.2.2.2 w
    constructor
    · have hm := measurable_choose_apply control
        (fun k x ↦ (advance P ⟨k.1, scores x⟩ (value x)).state) hcontrol
        (fun k ↦ measurable_advance_state_fixed P k.1 scores value hscore hv)
      convert hm using 1
      funext x
      rfl
    constructor
    · have hm := measurable_choose_apply control
        (fun k (_ : Edge n → ℝ) ↦ k.2.1.trans (Equiv.swap (pair k).1 (pair k).2))
        hcontrol (fun _ ↦ measurable_const)
      convert hm using 1
      funext x
      rfl
    constructor
    · have hm := measurable_choose_apply control
        (fun k (_ : Edge n → ℝ) ↦ (pair k).1 :: k.2.2) hcontrol (fun _ ↦ measurable_const)
      convert hm using 1
      funext x
      rfl
    intro w
    have hm := measurable_choose_apply control
      (fun k x ↦ (advance P ⟨k.1, scores x⟩ (value x)).score w) hcontrol
      (fun k ↦ measurable_advance_score_fixed P k.1 scores value hscore hv w)
    convert hm using 1
    funext x
    rfl

/-- Every pair-choice fiber of the generated concrete DA history is measurable. -/
theorem measurableSet_pick_history_fiber {n J : ℕ} [NeZero n]
    (P : Fin n → Equiv.Perm (Fin n)) (manTier : Fin n → Fin J) (t : ℕ)
    (chosen : Edge n × Edge n) :
    MeasurableSet {x : Edge n → ℝ |
      pick P manTier (allocationHistory (pick P manTier) x t) = chosen} := by
  classical
  let : MeasurableSpace (Edge n × Edge n) := ⊤
  have ih := measurable_replay_history P manTier t
  let history (x : Edge n → ℝ) := allocationHistory (pick P manTier) x t
  let old (x : Edge n → ℝ) := replay P manTier (history x)
  let Control := StableMarriage.ProposalState n × Equiv.Perm (Edge n) × List (Edge n)
  let control (x : Edge n → ℝ) : Control :=
    ((old x).1.state, (old x).2, (history x).map Prod.fst)
  have hc : Measurable control := ih.1.prodMk (ih.2.1.prodMk ih.2.2.1)
  have hcontrol (k : Control) : MeasurableSet {x : Edge n → ℝ | control x = k} :=
    hc (measurableSet_singleton k)
  have hpick : Measurable (fun x : Edge n → ℝ ↦
      pick P manTier (allocationHistory (pick P manTier) x t)) := by
    have hm := measurable_choose_apply control
      (fun k (_ : Edge n → ℝ) ↦ pairForState P manTier ⟨k.1, fun _ ↦ 0⟩ k.2.1 k.2.2)
      hcontrol (fun _ ↦ measurable_const)
    convert hm using 1
    funext x
    rfl
  exact hpick (measurableSet_singleton chosen)

end Ashlagi.Arrival
