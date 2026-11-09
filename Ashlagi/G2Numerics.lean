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

public import Ashlagi.TotalMoments

/-! # Scalar error budget for the uniform G.2 assembly

Every coefficient here is fixed independently of the tolerance. These are deterministic
inequalities; no probability estimate or G.2 conclusion is a premise hidden in a definition.
-/

@[expose] public section

namespace Ashlagi.G2Numerics

/-- A positive unit-scale logarithm is bounded by its cube. -/
theorem self_le_cube {L : ℝ} (hL : 1 ≤ L) : L ≤ L ^ 3 := by
  have hh : 1 ≤ L ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ L)
  nlinarith

/-- The tolerance and logarithm budget is smaller than the fourth population power. -/
theorem tolerance_log_le_fourth {n L η : ℝ} (hn : 0 < n) (hL : 1 ≤ L)
    (hLn : L ^ 3 ≤ n) (hη : 0 < η) (hη1 : η ≤ 1) : η ^ 2 * L ≤ n ^ 4 := by
  have hηsq : η ^ 2 ≤ 1 := by nlinarith
  have hLcube := self_le_cube hL
  have hn1 : 1 ≤ n := by linarith
  have hn2 : n ≤ n ^ 2 := by nlinarith
  have hn4 : n ^ 2 ≤ n ^ 4 := by nlinarith [sq_nonneg (n ^ 2 - 1)]
  have hh := mul_le_mul_of_nonneg_right hηsq (by linarith : 0 ≤ L)
  nlinarith

/-- A fourth-power clock failure fits into the common uniform error budget. -/
theorem clock_error_le {n L η : ℝ} (hn : 0 < n) (hL : 1 ≤ L) (hLn : L ^ 3 ≤ n)
    (hη : 0 < η) (hη1 : η ≤ 1) : 1 / n ^ 4 ≤ 1 / (η ^ 2 * L) := by
  apply one_div_le_one_div_of_le (by positivity : 0 < η ^ 2 * L)
  exact tolerance_log_le_fourth hn hL hLn hη hη1

/-- Cubic-log repeat noise divided by a relative threshold is controlled by one fixed
coefficient over eta squared log n. The tolerance restriction supplies the spare eta. -/
theorem repeat_error_le {n L η cActual cmin M noise : ℝ}
    (hn : 0 < n) (hL : 1 ≤ L) (hLn : L ^ 3 ≤ n) (hη : 0 < η) (hη1 : η ≤ 1)
    (hcmin : 0 < cmin) (hcenter : cmin * L ≤ cActual) (hM : 0 ≤ M)
    (hnoise : noise ≤ M * L ^ 3 / n) :
    noise / (η * cActual / 3) ≤ (3 * M / cmin) / (η ^ 2 * L) := by
  have hLpos : 0 < L := by linarith
  have hActual : 0 < cActual := lt_of_lt_of_le (mul_pos hcmin hLpos) hcenter
  have hnum : 0 ≤ M * L ^ 3 / n := by positivity
  have hden : 0 < η * cActual / 3 := by positivity
  have hdenmin : 0 < η * (cmin * L) / 3 := by positivity
  have hsmall : M * L ^ 3 / n ≤ M := by
    apply (div_le_iff₀ hn).mpr
    nlinarith [mul_le_mul_of_nonneg_left hLn hM]
  calc
    _ ≤ (M * L ^ 3 / n) / (η * cActual / 3) :=
      div_le_div_of_nonneg_right hnoise hden.le
    _ ≤ (M * L ^ 3 / n) / (η * (cmin * L) / 3) :=
      div_le_div_of_nonneg_left hnum hdenmin (by nlinarith)
    _ ≤ M / (η * (cmin * L) / 3) := div_le_div_of_nonneg_right hsmall hdenmin.le
    _ = (3 * M / cmin) / (η * L) := by field_simp
    _ ≤ (3 * M / cmin) / (η ^ 2 * L) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right hη1 (mul_pos hη hLpos).le]

/-- The literal martingale variance term has the requested fixed coefficient once the
clock horizon is O(n log n) and a single woman's hit probability is O(1/n). -/
theorem martingale_error_le {n L η cActual cmin H q K A : ℝ}
    (hn : 0 < n) (hL : 1 ≤ L) (hη : 0 < η) (hcmin : 0 < cmin)
    (hcenter : cmin * L ≤ cActual) (hH0 : 0 ≤ H) (hH : H ≤ K * n * L)
    (hq : q ≤ A / n) (hK : 0 < K) (hA : 0 ≤ A) :
    H * q / (η * cActual / 3) ^ 2 ≤ (9 * K * A / cmin ^ 2) / (η ^ 2 * L) := by
  have hLpos : 0 < L := by linarith
  have hActual : 0 < cActual := lt_of_lt_of_le (mul_pos hcmin hLpos) hcenter
  have hnum : H * q ≤ K * A * L := by
    calc
      _ ≤ H * (A / n) := mul_le_mul_of_nonneg_left hq hH0
      _ ≤ (K * n * L) * (A / n) := mul_le_mul_of_nonneg_right hH (div_nonneg hA hn.le)
      _ = _ := by field_simp
  have hdenmin : 0 < (η * (cmin * L) / 3) ^ 2 := by positivity
  have hden : (η * (cmin * L) / 3) ^ 2 ≤ (η * cActual / 3) ^ 2 := by
    have hh : η * (cmin * L) / 3 ≤ η * cActual / 3 := by nlinarith
    exact pow_le_pow_left₀ (by positivity) hh 2
  calc
    _ ≤ (K * A * L) / (η * cActual / 3) ^ 2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ ≤ (K * A * L) / (η * (cmin * L) / 3) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) hdenmin hden
    _ = _ := by field_simp; ring

/-- Replacing eta by eta/3 in the tier tail costs exactly the fixed factor nine. -/
theorem tier_error_eq (C η L : ℝ) : C / ((η / 3) ^ 2 * L) = (9 * C) / (η ^ 2 * L) := by
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The complete tolerance-independent coefficient for the four actual error sources. -/
noncomputable def errorConstant (A K C M cmin : ℝ) : ℝ :=
  1 + 9 * K * A / cmin ^ 2 + 9 * C + 3 * M / cmin

/-- The combined coefficient is positive under the fixed nonnegative source constants. -/
theorem errorConstant_pos {A K C M cmin : ℝ} (hA : 1 ≤ A) (hK : 0 < K)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hcmin : 0 < cmin) : 0 < errorConstant A K C M cmin := by
  unfold errorConstant
  positivity

/-- The four deterministic error expressions share a single fixed coefficient. -/
theorem error_budget {n L η cActual cmin M noise H q K A C : ℝ}
    (hn : 0 < n) (hL : 1 ≤ L) (hLn : L ^ 3 ≤ n) (hη : 0 < η) (hη1 : η ≤ 1)
    (hcmin : 0 < cmin) (hcenter : cmin * L ≤ cActual) (hM : 0 ≤ M)
    (hnoise : noise ≤ M * L ^ 3 / n) (hH0 : 0 ≤ H) (hH : H ≤ K * n * L)
    (hq : q ≤ A / n) (hK : 0 < K) (hA : 0 ≤ A) :
    1 / n ^ 4 + H * q / (η * cActual / 3) ^ 2 + C / ((η / 3) ^ 2 * L) +
      noise / (η * cActual / 3) ≤ errorConstant A K C M cmin / (η ^ 2 * L) := by
  have h0 := clock_error_le hn hL hLn hη hη1
  have h1 := martingale_error_le hn hL hη hcmin hcenter hH0 hH hq hK hA
  have h2 := tier_error_eq C η L
  have h3 := repeat_error_le hn hL hLn hη hη1 hcmin hcenter hM hnoise
  have he : errorConstant A K C M cmin / (η ^ 2 * L) =
      1 / (η ^ 2 * L) + (9 * K * A / cmin ^ 2) / (η ^ 2 * L) +
        (9 * C) / (η ^ 2 * L) + (3 * M / cmin) / (η ^ 2 * L) := by
    unfold errorConstant
    ring
  rw [he]
  linarith

/-- The exact original clock ceiling is bounded by a fixed n log n coefficient. -/
theorem clockCap_le {n : ℕ} (hn : 1 ≤ n) {A : ℝ} (hA : 1 ≤ A)
    (hlog : 1 ≤ Real.log n) :
    (TotalMoments.clockCap A n : ℝ) ≤ (5 * A + 1) * n * Real.log n := by
  exact Continuation.globalCap_le hn (by linarith : 0 ≤ 5 * A) hlog

end Ashlagi.G2Numerics
