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

public import Ashlagi.StoppedHazards

/-! # Finite adaptive competing-destination hazards

A finite history-dependent tree succeeds when it exhausts its empty destinations or stops.
The only local assumption compares the empty-hit and protected-target-hit masses. No iid
sampling or independent eventual-survival marks are required. Compiling a DA execution into
this tree is a separate obligation.
-/

@[expose] public section

namespace Ashlagi.CompetingHazards

open scoped ENNReal
open Ashlagi.StoppedHazards

/-- The three possible destination classes at a continuation step. -/
inductive Destination where
  | empty
  | neutral
  | target
  deriving DecidableEq

/-- Total probability of one destination class. -/
noncomputable def mass {n : ℕ} (law : PMF (Fin n))
    (kind : Fin n → Destination) (d : Destination) : ℝ :=
  branchMass law (fun i ↦ decide (kind i = d))

/-- The safe-completion potential with `k` empty destinations remaining. -/
noncomputable def potential (A : ℝ) (k : ℕ) : ℝ := ((A + 1)⁻¹) ^ k

/-- Stopping, pausing, or reaching a cap counts as safe success. A step is possible only
with a positive empty count. Target branches fail immediately; their child is unused. -/
inductive Tree (A : ℝ) : ℕ → Type
  | stop (k : ℕ) : Tree A k
  | step {k n : ℕ} (law : PMF (Fin n)) (kind : Fin n → Destination)
      (hazard : mass law kind .target ≤ A * mass law kind .empty)
      (child : (i : Fin n) → Tree A (if kind i = .empty then k else k + 1)) :
      Tree A (k + 1)

/-- The actual success/failure law, using each node's own transition PMF. -/
noncomputable def outcomeLaw {A : ℝ} : {k : ℕ} → Tree A k → PMF Bool
  | _, .stop _ => PMF.pure true
  | _, .step law kind _ child => law.bind fun i ↦
      if kind i = .target then PMF.pure false else outcomeLaw (child i)

/-- The potential is positive for nonnegative `A`. -/
theorem potential_pos {A : ℝ} (hA : 0 ≤ A) (k : ℕ) : 0 < potential A k := by
  exact pow_pos (inv_pos.mpr (by linarith)) _

/-- The potential never exceeds one. -/
theorem potential_le_one {A : ℝ} (hA : 0 ≤ A) (k : ℕ) : potential A k ≤ 1 := by
  apply pow_le_one₀ (inv_nonneg.mpr (by linarith))
  exact (inv_le_one₀ (by linarith : 0 < A + 1)).mpr (by linarith)

/-- Empty-hit potential gain is exactly `A` times the next potential. -/
theorem potential_difference {A : ℝ} (hA : 0 ≤ A) (k : ℕ) :
    potential A k - potential A (k + 1) = A * potential A (k + 1) := by
  have hne : A + 1 ≠ 0 := by linarith
  unfold potential
  rw [pow_succ]
  field_simp
  ring

/-- The local branch reward is zero on failure and the child's potential otherwise. -/
noncomputable def reward (A : ℝ) (k : ℕ) : Destination → ℝ
  | .empty => potential A k
  | .neutral => potential A (k + 1)
  | .target => 0

/-- Exact one-step potential accounting under an arbitrary finite transition law. -/
theorem weighted_reward {n : ℕ} (law : PMF (Fin n))
    (kind : Fin n → Destination) (A : ℝ) (k : ℕ) :
    (∑ i, (law i).toReal * reward A k (kind i)) =
      potential A (k + 1) + (potential A k - potential A (k + 1)) * mass law kind .empty -
        potential A (k + 1) * mass law kind .target := by
  have ht (i : Fin n) : (law i).toReal * reward A k (kind i) =
      potential A (k + 1) * (law i).toReal +
      (potential A k - potential A (k + 1)) *
        (if kind i = .empty then (law i).toReal else 0) -
      potential A (k + 1) * (if kind i = .target then (law i).toReal else 0) := by
    cases kind i <;> simp [reward] <;> ring
  simp_rw [ht]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_real_mass]
  simp [mass, branchMass]

/-- The local hazard inequality makes the potential subharmonic. -/
theorem potential_le_weighted_reward {A : ℝ} (hA : 0 ≤ A) {n : ℕ}
    (law : PMF (Fin n)) (kind : Fin n → Destination) (k : ℕ)
    (hazard : mass law kind .target ≤ A * mass law kind .empty) :
    potential A (k + 1) ≤ ∑ i, (law i).toReal * reward A k (kind i) := by
  rw [weighted_reward, potential_difference hA]
  have h := mul_le_mul_of_nonneg_left hazard (potential_pos hA (k + 1)).le
  nlinarith

/-- Testing a Boolean law with its success indicator gives its success mass. -/
theorem expectation_success (law : PMF Bool) :
    expectation law (fun b ↦ if b then 1 else 0) = law true := by
  simp [expectation, tsum_fintype]

/-- Finite backward induction gives the actual success-probability bound. -/
theorem ofReal_potential_le_success {A : ℝ} (hA : 0 ≤ A) {k : ℕ} (tree : Tree A k) :
    ENNReal.ofReal (potential A k) ≤ outcomeLaw tree true := by
  induction tree with
  | stop k =>
    simpa [outcomeLaw] using ENNReal.ofReal_le_ofReal (potential_le_one hA k)
  | @step k n law kind hazard child ih =>
    rw [← expectation_success, outcomeLaw, expectation_bind]
    calc
      _ ≤ ENNReal.ofReal (∑ i, (law i).toReal * reward A k (kind i)) :=
        ENNReal.ofReal_le_ofReal (potential_le_weighted_reward hA law kind k hazard)
      _ = expectation law (fun i ↦ ENNReal.ofReal (reward A k (kind i))) := by
        symm
        apply expectation_ofReal
        intro i
        cases kind i <;> simp [reward, (potential_pos hA k).le,
          (potential_pos hA (k + 1)).le]
      _ ≤ _ := by
        apply expectation_mono
        intro i
        by_cases ht : kind i = .target
        · simp [ht, reward, expectation_pure]
        · rw [ite_eq_right ht, expectation_success]
          have hr : reward A k (kind i) =
              potential A (if kind i = .empty then k else k + 1) := by
            cases he : kind i <;> simp_all [reward]
          rw [hr]
          exact ih i

/-- Real-valued success probability is at least `(A+1)⁻ᵏ`. -/
theorem potential_le_success {A : ℝ} (hA : 0 ≤ A) {k : ℕ} (tree : Tree A k) :
    potential A k ≤ (outcomeLaw tree true).toReal := by
  have h := ENNReal.toReal_mono ((outcomeLaw tree).apply_ne_top true)
    (ofReal_potential_le_success hA tree)
  simpa only [ENNReal.toReal_ofReal (potential_pos hA k).le] using h

/-- With at most two empty destinations the uniform regeneration probability is
at least `(A+1)⁻²`. This also covers completion at zero and all safe finite caps. -/
theorem two_empty_le_success {A : ℝ} (hA : 0 ≤ A) {k : ℕ} (hk : k ≤ 2)
    (tree : Tree A k) : potential A 2 ≤ (outcomeLaw tree true).toReal := by
  apply le_trans _ (potential_le_success hA tree)
  exact pow_le_pow_of_le_one (inv_nonneg.mpr (by linarith))
    ((inv_le_one₀ (by linarith : 0 < A + 1)).mpr (by linarith)) hk

/-- The same bound controls return-to-free failure probability when this tree is used
as a held episode. There is no independence assumption on the eventual outcome. -/
theorem failure_le_one_sub_potential {A : ℝ} (hA : 0 ≤ A) {k : ℕ}
    (tree : Tree A k) :
    (outcomeLaw tree false).toReal ≤ 1 - potential A k := by
  have hsum : outcomeLaw tree false + outcomeLaw tree true = 1 := by
    simpa [tsum_fintype, add_comm] using (outcomeLaw tree).tsum_coe
  have hr : (outcomeLaw tree false).toReal + (outcomeLaw tree true).toReal = 1 := by
    rw [← ENNReal.toReal_add ((outcomeLaw tree).apply_ne_top false)
      ((outcomeLaw tree).apply_ne_top true), hsum]
    rfl
  have h := potential_le_success hA tree
  linarith

end Ashlagi.CompetingHazards
