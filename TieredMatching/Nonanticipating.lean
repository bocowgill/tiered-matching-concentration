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

public import Mathlib

/-! # Invariance of adaptive query histories under changes to unqueried coordinates -/

@[expose] public section

namespace TieredMatching

/-- A deterministic querying rule observes only the coordinates already stored in its history. -/
def queryHistory {ι α : Type*} (next : List (ι × α) → ι) (x : ι → α) :
    ℕ → List (ι × α)
  | 0 => []
  | t + 1 =>
    let h := queryHistory next x t
    let q := next h
    (q, x q) :: h

/-- Agreement on the coordinates queried in one run makes another run's history identical. -/
theorem queryHistory_eq_of_agree {ι α : Type*} (next : List (ι × α) → ι)
    (x y : ι → α) (t : ℕ)
    (hagree : ∀ q, q ∈ (queryHistory next x t).map Prod.fst → y q = x q) :
    queryHistory next y t = queryHistory next x t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hprefix : ∀ q, q ∈ (queryHistory next x t).map Prod.fst → y q = x q := by
      intro q hq
      exact hagree q (by simp only [queryHistory, List.map_cons, List.mem_cons]; exact Or.inr hq)
    have heq := ih hprefix
    have hnew : y (next (queryHistory next x t)) = x (next (queryHistory next x t)) :=
      hagree _ (by simp [queryHistory])
    simp only [queryHistory, heq, hnew]

/-- Swapping two still unqueried coordinates leaves the complete observed history unchanged. -/
theorem queryHistory_swap_eq {ι α : Type*} [DecidableEq ι]
    (next : List (ι × α) → ι) (x : ι → α) (t : ℕ) (a b : ι)
    (ha : a ∉ (queryHistory next x t).map Prod.fst)
    (hb : b ∉ (queryHistory next x t).map Prod.fst) :
    queryHistory next (x ∘ Equiv.swap a b) t = queryHistory next x t := by
  apply queryHistory_eq_of_agree
  intro q hq
  have hqa : q ≠ a := fun h ↦ ha (h ▸ hq)
  have hqb : q ≠ b := fun h ↦ hb (h ▸ hq)
  simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hqa hqb]

/-- The next query is unchanged by a swap outside the previously observed coordinates. -/
theorem next_query_swap_eq {ι α : Type*} [DecidableEq ι]
    (next : List (ι × α) → ι) (x : ι → α) (t : ℕ) (a b : ι)
    (ha : a ∉ (queryHistory next x t).map Prod.fst)
    (hb : b ∉ (queryHistory next x t).map Prod.fst) :
    next (queryHistory next (x ∘ Equiv.swap a b) t) = next (queryHistory next x t) :=
  congrArg next (queryHistory_swap_eq next x t a b ha hb)

/-- A pair chosen solely from revealed history is unchanged by swapping its two fresh entries. -/
theorem pickedPair_selected_swap_eq {ι α : Type*} [DecidableEq ι]
    (next : List (ι × α) → ι) (pick : List (ι × α) → ι × ι) (t : ℕ)
    (hfresh : ∀ x : ι → α,
      (pick (queryHistory next x t)).1 ∉ (queryHistory next x t).map Prod.fst ∧
      (pick (queryHistory next x t)).2 ∉ (queryHistory next x t).map Prod.fst)
    (x : ι → α) :
    pick (queryHistory next
      (x ∘ Equiv.swap (pick (queryHistory next x t)).1 (pick (queryHistory next x t)).2) t) =
        pick (queryHistory next x t) :=
  congrArg pick (queryHistory_swap_eq next x t _ _ (hfresh x).1 (hfresh x).2)

/-- Involutive transformations turn selected-branch invariance into invariance of every fiber. -/
theorem choice_eq_iff_of_selected_invariant {K Ω : Type*}
    (choose : Ω → K) (T : K → Ω → Ω) (hinvol : ∀ k, Function.Involutive (T k))
    (hselected : ∀ x, choose (T (choose x) x) = choose x) (k : K) (x : Ω) :
    choose (T k x) = k ↔ choose x = k := by
  constructor
  · intro h
    simpa only [h, hinvol k x] using hselected (T k x)
  · intro h
    simpa only [h] using hselected x

/-- Swapping coordinates is an involution on arrays. -/
theorem swap_coordinates_involutive {ι α : Type*} [DecidableEq ι] (a b : ι) :
    Function.Involutive (fun x : ι → α ↦ x ∘ Equiv.swap a b) := by
  intro x
  funext q
  simp only [Function.comp_apply, Equiv.swap_apply_self]

/-- Every fixed swap preserves the fiber where that pair is selected from a fresh history. -/
theorem pickedPair_swap_fiber_iff {ι α : Type*} [DecidableEq ι]
    (next : List (ι × α) → ι) (pick : List (ι × α) → ι × ι) (t : ℕ)
    (hfresh : ∀ x : ι → α,
      (pick (queryHistory next x t)).1 ∉ (queryHistory next x t).map Prod.fst ∧
      (pick (queryHistory next x t)).2 ∉ (queryHistory next x t).map Prod.fst)
    (a b : ι) (x : ι → α) :
    pick (queryHistory next (x ∘ Equiv.swap a b) t) = (a, b) ↔
      pick (queryHistory next x t) = (a, b) := by
  exact choice_eq_iff_of_selected_invariant
    (fun y ↦ pick (queryHistory next y t))
    (fun pair y ↦ y ∘ Equiv.swap pair.1 pair.2)
    (fun pair ↦ swap_coordinates_involutive pair.1 pair.2)
    (pickedPair_selected_swap_eq next pick t hfresh) (a, b) x

/-- The selected transformation may be the identity after the revealing procedure terminates. -/
theorem pickedPair_selected_swap_eq_of_eq_or_fresh {ι α : Type*} [DecidableEq ι]
    (next : List (ι × α) → ι) (pick : List (ι × α) → ι × ι) (t : ℕ)
    (hfresh : ∀ x : ι → α,
      (pick (queryHistory next x t)).1 = (pick (queryHistory next x t)).2 ∨
      ((pick (queryHistory next x t)).1 ∉ (queryHistory next x t).map Prod.fst ∧
        (pick (queryHistory next x t)).2 ∉ (queryHistory next x t).map Prod.fst))
    (x : ι → α) :
    pick (queryHistory next
      (x ∘ Equiv.swap (pick (queryHistory next x t)).1 (pick (queryHistory next x t)).2) t) =
        pick (queryHistory next x t) := by
  rcases hfresh x with heq | ⟨ha, hb⟩
  · simp [heq]
  · exact congrArg pick (queryHistory_swap_eq next x t _ _ ha hb)

/-- Fresh-history pair selection preserves every fixed swap fiber, allowing identity padding. -/
theorem pickedPair_swap_fiber_iff_of_eq_or_fresh {ι α : Type*} [DecidableEq ι]
    (next : List (ι × α) → ι) (pick : List (ι × α) → ι × ι) (t : ℕ)
    (hfresh : ∀ x : ι → α,
      (pick (queryHistory next x t)).1 = (pick (queryHistory next x t)).2 ∨
      ((pick (queryHistory next x t)).1 ∉ (queryHistory next x t).map Prod.fst ∧
        (pick (queryHistory next x t)).2 ∉ (queryHistory next x t).map Prod.fst))
    (a b : ι) (x : ι → α) :
    pick (queryHistory next (x ∘ Equiv.swap a b) t) = (a, b) ↔
      pick (queryHistory next x t) = (a, b) := by
  exact choice_eq_iff_of_selected_invariant
    (fun y ↦ pick (queryHistory next y t))
    (fun pair y ↦ y ∘ Equiv.swap pair.1 pair.2)
    (fun pair ↦ swap_coordinates_involutive pair.1 pair.2)
    (pickedPair_selected_swap_eq_of_eq_or_fresh next pick t hfresh) (a, b) x

/-- Set form of the fixed-pair fiber invariance used by selected measure-preserving swaps. -/
theorem pickedPair_swap_preimage_fiber {ι α : Type*} [DecidableEq ι]
    (next : List (ι × α) → ι) (pick : List (ι × α) → ι × ι) (t : ℕ)
    (hfresh : ∀ x : ι → α,
      (pick (queryHistory next x t)).1 = (pick (queryHistory next x t)).2 ∨
      ((pick (queryHistory next x t)).1 ∉ (queryHistory next x t).map Prod.fst ∧
        (pick (queryHistory next x t)).2 ∉ (queryHistory next x t).map Prod.fst))
    (pair : ι × ι) :
    (fun x : ι → α ↦ x ∘ Equiv.swap pair.1 pair.2) ⁻¹'
        {x | pick (queryHistory next x t) = pair} =
      {x | pick (queryHistory next x t) = pair} := by
  ext x
  exact pickedPair_swap_fiber_iff_of_eq_or_fresh next pick t hfresh pair.1 pair.2 x

end TieredMatching
