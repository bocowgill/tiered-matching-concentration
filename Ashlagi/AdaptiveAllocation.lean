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

public import Ashlagi.AdaptiveExposure
public import Ashlagi.Nonanticipating

/-! # Full product-law preservation by nonanticipating allocation permutations -/

@[expose] public section

namespace Ashlagi

open MeasureTheory

/-- The source observation history when the first endpoint is queried at each stage. -/
def allocationHistory {ι α : Type*} (pick : List (ι × α) → ι × ι)
    (x : ι → α) (t : ℕ) : List (ι × α) :=
  queryHistory (fun h ↦ (pick h).1) x t

/-- The accumulated inverse allocation permutation: it maps output labels to source indices. -/
def allocationReindex {ι α : Type*} [DecidableEq ι] (pick : List (ι × α) → ι × ι) :
    List (ι × α) → Equiv.Perm ι
  | [] => Equiv.refl _
  | _ :: h => (allocationReindex pick h).trans (Equiv.swap (pick h).1 (pick h).2)

/-- Complete the allocation by retaining all as-yet unqueried source coordinates. -/
def adaptiveAllocation {ι α : Type*} [DecidableEq ι] (pick : List (ι × α) → ι × ι)
    (x : ι → α) (t : ℕ) : ι → α :=
  x ∘ allocationReindex pick (allocationHistory pick x t)

/-- The raw-source swap selected at the current observation history. -/
def allocationStep {ι α : Type*} [DecidableEq ι] (pick : List (ι × α) → ι × ι)
    (t : ℕ) (x : ι → α) : ι → α :=
  x ∘ Equiv.swap (pick (allocationHistory pick x t)).1
    (pick (allocationHistory pick x t)).2

/-- At time zero, no array coordinates have been allocated or permuted. -/
theorem adaptiveAllocation_zero {ι α : Type*} [DecidableEq ι]
    (pick : List (ι × α) → ι × ι) (x : ι → α) : adaptiveAllocation pick x 0 = x := by
  funext q
  rfl

/-- Fresh endpoints, or an identity swap, leave the previously observed history unchanged. -/
theorem allocationHistory_step_eq {ι α : Type*} [DecidableEq ι]
    (pick : List (ι × α) → ι × ι) (t : ℕ)
    (hfresh : ∀ x : ι → α,
      (pick (allocationHistory pick x t)).1 = (pick (allocationHistory pick x t)).2 ∨
      ((pick (allocationHistory pick x t)).1 ∉ (allocationHistory pick x t).map Prod.fst ∧
        (pick (allocationHistory pick x t)).2 ∉ (allocationHistory pick x t).map Prod.fst))
    (x : ι → α) :
    allocationHistory pick (allocationStep pick t x) t = allocationHistory pick x t := by
  rcases hfresh x with heq | ⟨ha, hb⟩
  · simp only [allocationStep, heq, Equiv.swap_self, Equiv.coe_refl, Function.comp_id]
  · exact queryHistory_swap_eq (fun h ↦ (pick h).1) x t _ _ ha hb

/-- The actual history-defined complete allocation is a composition of selected fresh swaps. -/
theorem adaptiveAllocation_succ {ι α : Type*} [DecidableEq ι]
    (pick : List (ι × α) → ι × ι) (t : ℕ)
    (hfresh : ∀ x : ι → α,
      (pick (allocationHistory pick x t)).1 = (pick (allocationHistory pick x t)).2 ∨
      ((pick (allocationHistory pick x t)).1 ∉ (allocationHistory pick x t).map Prod.fst ∧
        (pick (allocationHistory pick x t)).2 ∉ (allocationHistory pick x t).map Prod.fst))
    (x : ι → α) :
    adaptiveAllocation pick x (t + 1) = adaptiveAllocation pick (allocationStep pick t x) t := by
  funext q
  have hh := allocationHistory_step_eq pick t hfresh x
  simp only [adaptiveAllocation, hh]
  rfl

/-- The successor allocation reads from the swapped source index of the previous reindexing. -/
theorem adaptiveAllocation_succ_apply {ι α : Type*} [DecidableEq ι]
    (pick : List (ι × α) → ι × ι) (x : ι → α) (t : ℕ) (q : ι) :
    adaptiveAllocation pick x (t + 1) q =
      x (Equiv.swap (pick (allocationHistory pick x t)).1
        (pick (allocationHistory pick x t)).2
        (allocationReindex pick (allocationHistory pick x t) q)) := rfl

/-- The selected source value is placed at the output label whose previous source index
was the selected second endpoint. -/
theorem adaptiveAllocation_readback {ι α : Type*} [DecidableEq ι]
    (pick : List (ι × α) → ι × ι) (x : ι → α) (t : ℕ) :
    adaptiveAllocation pick x (t + 1)
        ((allocationReindex pick (allocationHistory pick x t)).symm
          (pick (allocationHistory pick x t)).2) =
      x (pick (allocationHistory pick x t)).1 := by
  rw [adaptiveAllocation_succ_apply, Equiv.apply_symm_apply, Equiv.swap_apply_right]

/-- A current output label whose source index is not swapped retains its allocated value. -/
theorem adaptiveAllocation_preserves_unaffected {ι α : Type*} [DecidableEq ι]
    (pick : List (ι × α) → ι × ι) (x : ι → α) (t : ℕ) (q : ι)
    (ha : allocationReindex pick (allocationHistory pick x t) q ≠
      (pick (allocationHistory pick x t)).1)
    (hb : allocationReindex pick (allocationHistory pick x t) q ≠
      (pick (allocationHistory pick x t)).2) :
    adaptiveAllocation pick x (t + 1) q = adaptiveAllocation pick x t q := by
  rw [adaptiveAllocation_succ_apply, Equiv.swap_apply_of_ne_of_ne ha hb]
  rfl

/-- A history-selected fresh swap preserves the product law when its two marginal laws agree. -/
theorem measurePreserving_allocationStep {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace α] (μ : ι → Measure α) [∀ i, SigmaFinite (μ i)]
    (pick : List (ι × α) → ι × ι) (t : ℕ)
    (hfresh : ∀ x : ι → α,
      (pick (allocationHistory pick x t)).1 = (pick (allocationHistory pick x t)).2 ∨
      ((pick (allocationHistory pick x t)).1 ∉ (allocationHistory pick x t).map Prod.fst ∧
        (pick (allocationHistory pick x t)).2 ∉ (allocationHistory pick x t).map Prod.fst))
    (hrate : ∀ x : ι → α,
      μ (pick (allocationHistory pick x t)).1 = μ (pick (allocationHistory pick x t)).2)
    (hmeas : ∀ pair : ι × ι,
      MeasurableSet {x : ι → α | pick (allocationHistory pick x t) = pair}) :
    MeasurePreserving (allocationStep pick t) (Measure.pi μ) (Measure.pi μ) := by
  classical
  let K := {pair : ι × ι // μ pair.1 = μ pair.2}
  let choose (x : ι → α) : K := ⟨pick (allocationHistory pick x t), hrate x⟩
  let T (pair : K) (x : ι → α) := x ∘ Equiv.swap pair.val.1 pair.val.2
  have hc (pair : K) : MeasurableSet {x : ι → α | choose x = pair} := by
    have heq : {x : ι → α | choose x = pair} =
        {x : ι → α | pick (allocationHistory pick x t) = pair.val} := by
      ext x
      exact Subtype.val_inj.symm
    rw [heq]
    exact hmeas pair.val
  have hT (pair : K) : MeasurePreserving (T pair) (Measure.pi μ) (Measure.pi μ) :=
    measurePreserving_swapCoordinates μ pair.val.1 pair.val.2 pair.property
  have hinv (pair : K) : T pair ⁻¹' {x | choose x = pair} = {x | choose x = pair} := by
    ext x
    change choose (T pair x) = pair ↔ choose x = pair
    have hi := pickedPair_swap_fiber_iff_of_eq_or_fresh (fun h ↦ (pick h).1) pick t hfresh
      pair.val.1 pair.val.2 x
    constructor
    · intro hx
      exact Subtype.ext (hi.mp (congrArg Subtype.val hx))
    · intro hx
      exact Subtype.ext (hi.mpr (congrArg Subtype.val hx))
  have h := measurePreserving_selectedTransform (Measure.pi μ) choose T hc hT hinv
  have heq : selectedTransform choose T = allocationStep pick t := by
    funext x
    rfl
  rw [heq] at h
  exact h

/-- Any finite complete allocation defined by the revealed history preserves the full
independent product law. No independence of a random stopping count is assumed. -/
theorem measurePreserving_adaptiveAllocation {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace α] (μ : ι → Measure α) [∀ i, SigmaFinite (μ i)]
    (pick : List (ι × α) → ι × ι)
    (hfresh : ∀ t : ℕ, ∀ x : ι → α,
      (pick (allocationHistory pick x t)).1 = (pick (allocationHistory pick x t)).2 ∨
      ((pick (allocationHistory pick x t)).1 ∉ (allocationHistory pick x t).map Prod.fst ∧
        (pick (allocationHistory pick x t)).2 ∉ (allocationHistory pick x t).map Prod.fst))
    (hrate : ∀ t : ℕ, ∀ x : ι → α,
      μ (pick (allocationHistory pick x t)).1 = μ (pick (allocationHistory pick x t)).2)
    (hmeas : ∀ t : ℕ, ∀ pair : ι × ι,
      MeasurableSet {x : ι → α | pick (allocationHistory pick x t) = pair})
    (t : ℕ) :
    MeasurePreserving (fun x ↦ adaptiveAllocation pick x t) (Measure.pi μ) (Measure.pi μ) := by
  induction t with
  | zero =>
    have heq : (fun x : ι → α ↦ adaptiveAllocation pick x 0) = id :=
      funext (adaptiveAllocation_zero pick)
    rw [heq]
    exact MeasurePreserving.id (Measure.pi μ)
  | succ t ih =>
    have hs := measurePreserving_allocationStep μ pick t (hfresh t) (hrate t) (hmeas t)
    have heq : (fun x : ι → α ↦ adaptiveAllocation pick x (t + 1)) =
        (fun x ↦ adaptiveAllocation pick (allocationStep pick t x) t) :=
      funext (adaptiveAllocation_succ pick t (hfresh t))
    rw [heq]
    exact ih.comp hs

end Ashlagi
