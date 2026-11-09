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

public import Ashlagi.Continuation
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Uniform numerical scales for actual continuation bounds

Fixed normalized score constants give an ordinary continuation mean of order log n and a
polynomial tail at a logarithm-squared threshold. Ceilings and the quarter-list floor are explicit.
-/

@[expose] public section

namespace Ashlagi.ContinuationAsymptotics

open Filter
open scoped Topology

/-- The exact genuine global cap used by the actual continuation setting. -/
noncomputable def globalCap (K : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (K * n * Real.log n)

/-- The actual designated quarter-prefix cap, including its integer floor. -/
def individualCap (n : ℕ) : ℕ := n / 4

/-- The integer proposal threshold on the source's squared-logarithm scale. -/
noncomputable def threshold (D : ℝ) (n : ℕ) : ℕ := Nat.ceil (D * (Real.log n) ^ 2)

/-- The numerical mean endpoint before simplifying its explicit cap errors. -/
noncomputable def meanBound (A c q K : ℝ) (n : ℕ) : ℝ :=
  2 / ((c / Real.log n) * q) + n *
    (2 * Real.exp (-(globalCap K n : ℝ) / (A * n)) +
      2 * Real.exp (-((c / Real.log n) * q / 2) * individualCap n))

/-- The numerical tail endpoint below the designated quarter-prefix cap. -/
noncomputable def tailBound (A c q K : ℝ) (n k : ℕ) : ℝ :=
  2 * Real.exp (-((c / Real.log n) * q / 2) * k) +
    2 * Real.exp (-(globalCap K n : ℝ) / (A * n))

/-- A fixed positive multiple of n eventually dominates the square of log n. -/
theorem eventually_log_sq_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (Real.log n) ^ 2 ≤ ε * n := by
  have hr := (isLittleO_log_rpow_rpow_atTop (s := 1) 2 zero_lt_one).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  filter_upwards [hr.def hε] with n hn
  simpa only [Function.comp_apply, Real.rpow_two, Real.rpow_one, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (Real.log (n : ℝ))),
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using hn

/-- Log n is eventually at least one. -/
theorem eventually_one_le_log : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1

/-- The quarter-prefix floor is at least n/8 once n is at least eight. -/
theorem eighth_le_individualCap {n : ℕ} (hn : 8 ≤ n) :
    (n : ℝ) / 8 ≤ (individualCap n : ℝ) := by
  have hrem : n < 4 * (n / 4 + 1) := by omega
  have hquot : 2 ≤ n / 4 := by omega
  have hr : (n : ℝ) < 4 * ((n / 4 : ℕ) + 1 : ℝ) := by exact_mod_cast hrem
  have hq : (2 : ℝ) ≤ (n / 4 : ℕ) := by exact_mod_cast hquot
  dsimp only [individualCap]
  nlinarith

/-- Every fixed positive squared-logarithm threshold eventually lies below the quarter cap. -/
theorem eventually_threshold_lt_individualCap {D : ℝ} (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop, threshold D n < individualCap n := by
  filter_upwards [eventually_log_sq_le (by positivity : 0 < 1 / (32 * D)),
    eventually_ge_atTop 32] with n hlog hn
  have hn8 : 8 ≤ n := by omega
  have hc := Nat.ceil_lt_add_one (mul_nonneg hD.le (sq_nonneg (Real.log n)))
  have hf := eighth_le_individualCap hn8
  have hn' : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog' : D * (Real.log n) ^ 2 ≤ (n : ℝ) / 32 := by
    have hm := mul_le_mul_of_nonneg_left hlog hD.le
    calc
      _ ≤ D * (1 / (32 * D) * n) := hm
      _ = (n : ℝ) / 32 := by field_simp
  change Nat.ceil (D * (Real.log n) ^ 2) < individualCap n
  exact_mod_cast (show (Nat.ceil (D * (Real.log n) ^ 2) : ℝ) <
    (individualCap n : ℝ) by nlinarith)

/-- The ceiling in the genuine global cap can only improve the exponential error bound. -/
theorem global_exp_le {A K r : ℝ} (hA : 0 < A) {n : ℕ} (hn : 0 < n)
    (hlog : 0 ≤ Real.log n) (hK : A * r ≤ K) :
    Real.exp (-(globalCap K n : ℝ) / (A * n)) ≤ Real.exp (-r * Real.log n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ (mul_pos hA hn')).mpr
  have hceil := Nat.le_ceil (K * n * Real.log n)
  have hmul := mul_le_mul_of_nonneg_right hK
    (mul_nonneg hn'.le hlog)
  dsimp only [globalCap]
  nlinarith

/-- The ceiling threshold gives the desired polynomial-scale designated tail exponent. -/
theorem threshold_exp_le {c q D r : ℝ} (hc : 0 < c) (hq : 0 < q)
    {n : ℕ} (hlog : 0 < Real.log n) (hD : 2 * r ≤ c * q * D) :
    Real.exp (-((c / Real.log n) * q / 2) * threshold D n) ≤
      Real.exp (-r * Real.log n) := by
  have hr : (c / Real.log n) * q / 2 = (c * q) / (2 * Real.log n) := by ring
  apply Real.exp_le_exp.mpr
  rw [hr]
  have hceil := Nat.le_ceil (D * (Real.log n) ^ 2)
  have hm := mul_le_mul_of_nonneg_left hceil (mul_pos hc hq).le
  have hd := mul_le_mul_of_nonneg_right hD (sq_nonneg (Real.log n))
  have he : r * Real.log n ≤ (c * q) / (2 * Real.log n) * threshold D n := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log n)).mpr
    dsimp only [threshold]
    nlinarith
  linarith

/-- Exponentials on logarithmic arguments are literal inverse polynomial powers. -/
theorem exp_neg_log_eq_rpow {n : ℕ} (hn : 0 < n) (r : ℝ) :
    Real.exp (-r * Real.log n) = (n : ℝ) ^ (-r) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hn']
  congr 1
  ring

/-- The integral exponent form avoids any rounding ambiguity in mean-error estimates. -/
theorem exp_neg_nat_log {n : ℕ} (hn : 0 < n) (r : ℕ) :
    Real.exp (-(r : ℝ) * Real.log n) = 1 / (n : ℝ) ^ r := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hn', one_div]

/-- A quarter-prefix cap has exponentially small probability on every fixed polynomial scale. -/
theorem eventually_individual_exp_le {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-((c / Real.log n) * q / 2) * individualCap n) ≤
        Real.exp (-3 * Real.log n) := by
  filter_upwards [eventually_log_sq_le (by positivity : 0 < c * q / 48),
    eventually_one_le_log, eventually_ge_atTop 8] with n hsq hlog hn
  have hf := eighth_le_individualCap hn
  have hl : 0 < Real.log n := by linarith
  have hr : (c / Real.log n) * q / 2 = c * q / (2 * Real.log n) := by ring
  have hp : c * q / (2 * Real.log n) * ((n : ℝ) / 8) ≤
      c * q / (2 * Real.log n) * individualCap n :=
    mul_le_mul_of_nonneg_left hf (by positivity)
  have he : 3 * Real.log n ≤ c * q / (2 * Real.log n) * individualCap n := by
    have hlow : 3 * Real.log n ≤ c * q / (2 * Real.log n) * ((n : ℝ) / 8) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log n)).mpr
      nlinarith
    exact hlow.trans hp
  apply Real.exp_le_exp.mpr
  rw [hr]
  linarith

/-- Both actual cap errors, multiplied by n, are eventually at most one. -/
theorem eventually_mean_errors_le_one {A c q K : ℝ} (hA : 0 < A)
    (hc : 0 < c) (hq : 0 < q) (hK : 3 * A ≤ K) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * (2 * Real.exp (-(globalCap K n : ℝ) / (A * n)) +
        2 * Real.exp (-((c / Real.log n) * q / 2) * individualCap n)) ≤ 1 := by
  filter_upwards [eventually_individual_exp_le hc hq, eventually_one_le_log,
    eventually_ge_atTop 2] with n hind hlog hn
  have hn0 : 0 < n := by omega
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hg := global_exp_le hA hn0 (by linarith : 0 ≤ Real.log n)
    (by linarith : A * 3 ≤ K)
  have hpoly := exp_neg_nat_log hn0 3
  norm_num only [Nat.cast_ofNat] at hpoly
  rw [hpoly] at hg hind
  have he := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hg (by norm_num : (0 : ℝ) ≤ 2))
      (mul_le_mul_of_nonneg_left hind (by norm_num : (0 : ℝ) ≤ 2)))
        (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  apply he.trans
  have hp : (0 : ℝ) < n := by linarith
  field_simp
  nlinarith [sq_nonneg ((n : ℝ) - 2)]

/-- The numerical ordinary-count endpoint is eventually bounded by a fixed multiple of log n. -/
theorem eventually_meanBound_le_log {A c q K : ℝ} (hA : 0 < A)
    (hc : 0 < c) (hq : 0 < q) (hK : 3 * A ≤ K) :
    ∀ᶠ n : ℕ in atTop, meanBound A c q K n ≤ (2 / (c * q) + 1) * Real.log n := by
  filter_upwards [eventually_mean_errors_le_one hA hc hq hK, eventually_one_le_log]
    with n herr hlog
  have heq : 2 / ((c / Real.log n) * q) = (2 / (c * q)) * Real.log n := by
    field_simp
  unfold meanBound
  rw [heq]
  nlinarith

/-- Fixed logarithm-squared thresholds have the actual endpoint's polynomial tail, uniformly
for every sufficiently large market size; the threshold remains below the exact floor cap. -/
theorem eventually_tailBound_le_rpow {A c q K D r : ℝ} (hA : 0 < A)
    (hc : 0 < c) (hq : 0 < q) (hDpos : 0 < D)
    (hK : A * r ≤ K) (hD : 2 * r ≤ c * q * D) :
    ∀ᶠ n : ℕ in atTop,
      threshold D n < individualCap n ∧
        tailBound A c q K n (threshold D n) ≤ 4 * (n : ℝ) ^ (-r) := by
  filter_upwards [eventually_threshold_lt_individualCap hDpos, eventually_one_le_log,
    eventually_ge_atTop 1] with n hcap hlog hn
  have hn0 : 0 < n := by omega
  have hg := global_exp_le hA hn0 (by linarith : 0 ≤ Real.log n) hK
  have ht := threshold_exp_le hc hq (by linarith : 0 < Real.log n) hD
  rw [exp_neg_log_eq_rpow hn0 r] at hg ht
  refine ⟨hcap, ?_⟩
  unfold tailBound
  linarith

/-- The fixed numerator of the source's acceptance rate c/log n. -/
noncomputable def acceptanceConstant (A B C K : ℝ) : ℝ :=
  1 / (4 * A * (1 + B * (C + K + 1)))

/-- Public normalized parameters make the acceptance numerator strictly positive. -/
theorem acceptanceConstant_pos {A B C K : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hK : 0 ≤ K) : 0 < acceptanceConstant A B C K := by
  unfold acceptanceConstant
  positivity

/-- The actual setting's acceptance rate is exactly c/log n for fixed normalized parameters. -/
theorem setting_acceptanceRate_eq {n : ℕ} (S : Continuation.Setting n) {A B C K : ℝ}
    (hA : S.A = A) (hB : S.B = B) (hC : S.C = C) (hK : S.K = K)
    (hL : S.L = Real.log n) :
    S.acceptanceRate = acceptanceConstant A B C K / Real.log n := by
  simp only [Continuation.Setting.acceptanceRate, acceptanceConstant, hA, hB, hC, hK, hL,
    div_eq_mul_inv, mul_inv_rev]
  ring

/-- The exact actual mean endpoint has the numerical form used by the asymptotic estimates. -/
theorem setting_mean_le_meanBound {n : ℕ} (S : Continuation.Setting n) {A B C K : ℝ}
    (hA : S.A = A) (hB : S.B = B) (hC : S.C = C) (hK : S.K = K)
    (hL : S.L = Real.log n) :
    VisitBounds.expectation (Continuation.lawAt S.a S.b S.protocol S.setup)
      (fun p ↦ (S.ordinaryCount p : ℝ)) ≤
        meanBound A (acceptanceConstant A B C K) (CompetingHazards.potential A 2) K n := by
  have hs := S.ordinary_mean_le
  rw [setting_acceptanceRate_eq S hA hB hC hK hL] at hs
  simpa only [meanBound, globalCap, individualCap, Continuation.Setting.caps,
    Continuation.Setting.survivalRate, hA, hK, hL] using hs

/-- Below the explicit floor cap, the actual conditional tail has the numerical endpoint. -/
theorem setting_tail_le_tailBound {n : ℕ} (S : Continuation.Setting n) {A B C K : ℝ}
    (hA : S.A = A) (hB : S.B = B) (hC : S.C = C) (hK : S.K = K)
    (hL : S.L = Real.log n) (k : ℕ) (hk : k < individualCap n) :
    (FiniteConditioning.eventMass (Continuation.lawAt S.a S.b S.protocol S.setup)
      {p | k ≤ S.ordinaryCount p}).toReal ≤
        tailBound A (acceptanceConstant A B C K) (CompetingHazards.potential A 2) K n k := by
  have hs := S.ordinary_tail_le k hk
  rw [setting_acceptanceRate_eq S hA hB hC hK hL] at hs
  simpa only [tailBound, globalCap, Continuation.Setting.caps,
    Continuation.Setting.survivalRate, hA, hK, hL] using hs

/-- Uniform actual ordinary-continuation bounds over every admissible nonnull setup history.
All constants are fixed before n varies. The probability law conditions only on that setup. -/
theorem eventually_uniform_actual_bounds {A B C K D r : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hK : A * (r + 3) ≤ K)
    (hD : 2 * (r + 2) /
      (acceptanceConstant A B C K * CompetingHazards.potential A 2) ≤ D) :
    ∀ᶠ n : ℕ in atTop, ∀ S : Continuation.Setting n,
      S.A = A → S.B = B → S.C = C → S.K = K → S.L = Real.log n →
      VisitBounds.expectation (Continuation.lawAt S.a S.b S.setupProtocol S.setup)
        (fun p ↦ (S.ordinaryCount p : ℝ)) ≤
          (2 / (acceptanceConstant A B C K * CompetingHazards.potential A 2) + 1) *
            Real.log n ∧
      (FiniteConditioning.eventMass (Continuation.lawAt S.a S.b S.setupProtocol S.setup)
        {p | threshold D n ≤ S.ordinaryCount p}).toReal ≤ 4 * (n : ℝ) ^ (-r) := by
  have hApos : 0 < A := by linarith
  have hBnonneg : 0 ≤ B := by linarith
  have hKthree : 3 * A ≤ K := by nlinarith
  have hKnonneg : 0 ≤ K := by linarith
  have hc := acceptanceConstant_pos hApos hBnonneg hC hKnonneg
  have hq := CompetingHazards.potential_pos hApos.le 2
  have hcq := mul_pos hc hq
  have hDpos : 0 < D := lt_of_lt_of_le (div_pos (by linarith) hcq) hD
  have hDmul : 2 * r ≤ acceptanceConstant A B C K *
      CompetingHazards.potential A 2 * D := by
    have hh := (div_le_iff₀ hcq).mp hD
    nlinarith
  filter_upwards [eventually_meanBound_le_log hApos hc hq hKthree,
    eventually_tailBound_le_rpow hApos hc hq hDpos (by nlinarith : A * r ≤ K) hDmul]
    with n hmean htail S hSA hSB hSC hSK hSL
  rw [← S.setup_law_eq]
  constructor
  · exact (setting_mean_le_meanBound S hSA hSB hSC hSK hSL).trans hmean
  · exact (setting_tail_le_tailBound S hSA hSB hSC hSK hSL (threshold D n) htail.1).trans
      htail.2

/-- A fixed global coefficient paying any prescribed polynomial error exponent. -/
noncomputable def globalCoefficient (A r : ℝ) : ℝ := A * (r + 3)

/-- An explicit fixed squared-logarithm tail coefficient for the normalized setting. -/
noncomputable def tailCoefficient (A B C r : ℝ) : ℝ :=
  2 * (r + 2) / (acceptanceConstant A B C (globalCoefficient A r) *
    CompetingHazards.potential A 2)

/-- An explicit fixed coefficient of the ordinary continuation's logarithmic mean. -/
noncomputable def meanCoefficient (A B C r : ℝ) : ℝ :=
  2 / (acceptanceConstant A B C (globalCoefficient A r) *
    CompetingHazards.potential A 2) + 1

/-- All canonical asymptotic coefficients are positive under normalized public bounds. -/
theorem coefficients_pos {A B C r : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hC : 0 ≤ C) (hr : 0 ≤ r) :
    0 < globalCoefficient A r ∧ 0 < tailCoefficient A B C r ∧
      0 < meanCoefficient A B C r := by
  have hApos : 0 < A := by linarith
  have hK : 0 < globalCoefficient A r := mul_pos hApos (by linarith)
  have hc := acceptanceConstant_pos hApos (by linarith : 0 ≤ B) hC hK.le
  have hq := CompetingHazards.potential_pos hApos.le 2
  refine ⟨hK, ?_, ?_⟩
  · exact div_pos (by linarith) (mul_pos hc hq)
  · unfold meanCoefficient
    positivity

/-- For each fixed polynomial exponent, explicit normalized constants give a uniform actual
O(log n) mean and O(n⁻ʳ) tail beyond a ceil(D log² n) threshold. The global cap is
ceil(K n log n), and the designated cap is exactly floor(n/4). -/
theorem eventually_uniform_canonical_bounds {A B C r : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C) (hr : 0 ≤ r) :
    ∀ᶠ n : ℕ in atTop, ∀ S : Continuation.Setting n,
      S.A = A → S.B = B → S.C = C → S.K = globalCoefficient A r →
      S.L = Real.log n →
      VisitBounds.expectation (Continuation.lawAt S.a S.b S.setupProtocol S.setup)
        (fun p ↦ (S.ordinaryCount p : ℝ)) ≤ meanCoefficient A B C r * Real.log n ∧
      (FiniteConditioning.eventMass (Continuation.lawAt S.a S.b S.setupProtocol S.setup)
        {p | threshold (tailCoefficient A B C r) n ≤ S.ordinaryCount p}).toReal ≤
          4 * (n : ℝ) ^ (-r) :=
  eventually_uniform_actual_bounds hA hB hC hr le_rfl le_rfl

end Ashlagi.ContinuationAsymptotics
