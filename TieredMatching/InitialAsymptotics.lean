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

public import TieredMatching.InitialPhase
public import TieredMatching.ContinuationAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Uniform actual initial-phase estimates from deterministic smooth setup states

The inputs are pointwise smooth-setup properties and the original nonnull setup-prefix event.
The initial means and covariance come from the actual finite PR phase estimates, without a
geometric reference coupling or assumed stochastic moment statement.
-/

@[expose] public section

namespace TieredMatching.InitialAsymptotics

open StableMarriage MeasureTheory TieredMatching.Ordinal Protocols FiniteConditioning Filter
open scoped ENNReal NNReal Topology

/-- A completed setup with fixed normalized score bounds and deterministic smoothness data. -/
structure Setting (n : ℕ) (A B C ζ κ : ℝ) where
  a : Fin n → ℝ≥0
  b : Fin n → ℝ≥0
  u : Fin n
  v : Fin n
  distinct : u ≠ v
  setup : List (Entry n)
  nonnull : eventMass (Continuation.market a b) (InitialPhase.setupEvent u v setup) ≠ 0
  a_lower : ∀ w, 1 ≤ (a w : ℝ)
  a_upper : ∀ w, (a w : ℝ) ≤ A
  b_lower : ∀ m, 1 ≤ (b m : ℝ)
  b_upper : ∀ m, (b m : ℝ) ≤ B
  total : (potential (recordState setup) : ℝ) ≤ C * n * Real.log n
  low : Finset (Fin n)
  low_card : (low.card : ℝ) ≤ (n : ℝ) ^ (1 - κ)
  high : ∀ w, w ∉ low → ζ * Real.log n ≤ VisitBounds.gamma b setup w

/-- A fixed uniform lower-rate numerator obtained from the harmonic bound. -/
noncomputable def lowerConstant (A B C : ℝ) : ℝ := 1 / (A * (1 + B * C))

/-- The deterministic logarithm-squared cap coefficient; it pays a tenth-power tail. -/
noncomputable def capCoefficient (A B C : ℝ) : ℝ := 20 / lowerConstant A B C

/-- The actual integer initial-phase cap, with its ceiling retained. -/
noncomputable def cap (A B C : ℝ) (n : ℕ) : ℕ :=
  ContinuationAsymptotics.threshold (capCoefficient A B C) n

/-- Positivity and unit upper bound for the uniform lower-rate numerator. -/
theorem lowerConstant_bounds {A B C : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C) :
    0 < lowerConstant A B C ∧ lowerConstant A B C ≤ 1 := by
  have hBC : 0 ≤ B * C := mul_nonneg (by linarith) hC
  have hden : 1 ≤ A * (1 + B * C) := by nlinarith
  exact ⟨by unfold lowerConstant; positivity,
    by simpa only [lowerConstant, one_div_one] using one_div_le_one_div_of_le zero_lt_one hden⟩

/-- A normalized public mass is at least the reciprocal of A times population size. -/
theorem normalized_lower {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ≥0) {A : ℝ}
    (_hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (w : Fin n) : 1 / (A * n) ≤ InitialDrift.normalized a w := by
  have hsum := InitialDrift.total_pos hn a ha1
  have hsumA : (∑ v, (a v : ℝ)) ≤ A * n := by
    calc
      _ ≤ ∑ _v : Fin n, A := Finset.sum_le_sum fun v _ ↦ haA v
      _ = _ := by simp [mul_comm]
  exact (one_div_le_one_div_of_le hsum hsumA).trans
    (div_le_div_of_nonneg_right (ha1 w) hsum.le)

/-- The harmonic expression has a fixed logarithmic lower bound under the genuine count cap. -/
theorem numerical_rate_lower {A B C N L G : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hN : 0 < N) (hL : 1 ≤ L) (hG : 0 ≤ G) (hcap : G ≤ B * C * N * L) :
    lowerConstant A B C / L ≤ (1 / (A * N)) * N ^ 2 / (N + G) := by
  have hA0 : 0 < A := by linarith
  have hL0 : 0 < L := by linarith
  have hBC : 0 ≤ B * C := mul_nonneg (by linarith) hC
  have hBC1 : 0 < 1 + B * C := by linarith
  have hmax : N + G ≤ N * (1 + B * C) * L := by
    nlinarith [mul_nonneg hN.le (sub_nonneg.mpr hL)]
  calc
    lowerConstant A B C / L =
        (1 / (A * N)) * N ^ 2 / (N * (1 + B * C) * L) := by
      unfold lowerConstant
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hmax

/-- Every fixed setup baseline, including score one, is at least cp/log n. -/
theorem rate_lower {n : ℕ} {A B C ζ κ : ℝ} (S : Setting n A B C ζ κ)
    (hn : 0 < n) (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hlog : 1 ≤ Real.log n) {β : ℝ} (hβ : 1 ≤ β) :
    lowerConstant A B C / Real.log n ≤
      SmoothRates.rate (InitialDrift.normalized S.a) (VisitBounds.gamma S.b S.setup) β := by
  have hΓ (w : Fin n) : 0 ≤ VisitBounds.gamma S.b S.setup w :=
    Finset.sum_nonneg fun m _ ↦ (S.b m.val).coe_nonneg
  have hsum : (∑ w, VisitBounds.gamma S.b S.setup w) ≤ B * C * n * Real.log n := by
    have hg := Continuation.sum_gamma_le S.b S.setup (by linarith : 0 ≤ B) S.b_upper
    have hm := mul_le_mul_of_nonneg_left S.total (by linarith : 0 ≤ B)
    exact hg.trans (by nlinarith [hm])
  have hr := SmoothRates.fresh_rate_lower (Finset.univ : Finset (Fin n))
    (InitialDrift.normalized S.a) (VisitBounds.gamma S.b S.setup) hβ
    (by positivity : 0 ≤ 1 / (A * n))
    (fun w _ ↦ normalized_lower hn S.a hA S.a_lower S.a_upper w) (fun w _ ↦ hΓ w)
  simp only [Finset.card_univ, Fintype.card_fin] at hr
  exact (numerical_rate_lower hA hB hC (by exact_mod_cast hn) hlog
    (Finset.sum_nonneg fun w _ ↦ hΓ w) hsum).trans hr


/-- The low public mass is bounded by the deterministic sublinear exceptional-set size. -/
theorem low_mass_le {n : ℕ} {A B C ζ κ : ℝ} (S : Setting n A B C ζ κ)
    (hn : 0 < n) (hA : 0 ≤ A) :
    (∑ w ∈ S.low, InitialDrift.normalized S.a w) ≤ A / (n : ℝ) ^ κ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hh := InitialRates.visited_mass_le_card (InitialDrift.normalized S.a) S.low
    (A / n) (fun w _ ↦ InitialDrift.normalized_upper hn S.a hA S.a_lower S.a_upper w)
  have hm := mul_le_mul_of_nonneg_right S.low_card (div_nonneg hA hn'.le)
  refine hh.trans (hm.trans_eq ?_)
  rw [Real.rpow_sub hn', Real.rpow_one]
  field_simp

/-- Powers of log are uniformly dominated by any positive population power. -/
theorem eventually_log_power_le {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, (Real.log n) ^ k ≤ ε * (n : ℝ) ^ κ := by
  have hr := (isLittleO_log_rpow_rpow_atTop (s := κ) (k : ℝ) hκ).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  filter_upwards [hr.def hε, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  simpa only [Function.comp_apply, Real.rpow_natCast, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hl k), abs_of_nonneg (Real.rpow_nonneg hn' κ)] using hn

/-- The exceptional public mass times log squared eventually has a uniform unit bound. -/
theorem eventually_low_mass {A B C ζ κ : ℝ} (hA : 1 ≤ A) (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop, ∀ S : Setting n A B C ζ κ,
      (∑ w ∈ S.low, InitialDrift.normalized S.a w) * (Real.log n) ^ 2 ≤ 1 := by
  have hA0 : 0 < A := by linarith
  filter_upwards [eventually_log_power_le (one_div_pos.mpr hA0) hκ 2,
    eventually_ge_atTop (1 : ℕ)] with n hn hn1 S
  have hn0 : 0 < n := by omega
  have hpow : 0 < (n : ℝ) ^ κ := Real.rpow_pos_of_pos (by exact_mod_cast hn0) κ
  have hh := mul_le_mul_of_nonneg_right (low_mass_le S hn0 hA0.le)
    (sq_nonneg (Real.log n))
  refine hh.trans ?_
  apply (le_of_mul_le_mul_right · hpow)
  have hm := mul_le_mul_of_nonneg_left hn hA0.le
  calc
    (A / (n : ℝ) ^ κ * (Real.log n) ^ 2) * (n : ℝ) ^ κ =
        A * (Real.log n) ^ 2 := by field_simp
    _ ≤ 1 * (n : ℝ) ^ κ := by
      simpa only [← mul_assoc, mul_one_div_cancel hA0.ne', one_mul] using hm

/-- Smoothness bounds every score-bounded baseline by a constant over log population. -/
theorem rate_upper {n : ℕ} {A B C ζ κ : ℝ} (S : Setting n A B C ζ κ)
    (hn : 0 < n) (hζ : 0 < ζ) (_hB : 1 ≤ B) (hlog : 1 ≤ Real.log n)
    (hlow : (∑ w ∈ S.low, InitialDrift.normalized S.a w) * (Real.log n) ^ 2 ≤ 1)
    {β : ℝ} (hβ : 1 ≤ β) (hβB : β ≤ B) :
    SmoothRates.rate (InitialDrift.normalized S.a) (VisitBounds.gamma S.b S.setup) β ≤
      B * (1 + 1 / ζ) / Real.log n := by
  have hL : 0 < Real.log n := by linarith
  have hΓ (w : Fin n) : 0 ≤ VisitBounds.gamma S.b S.setup w :=
    Finset.sum_nonneg fun m _ ↦ (S.b m.val).coe_nonneg
  have hπ := InitialDrift.normalized_nonneg S.a
  have hr := SmoothRates.rate_one_upper (InitialDrift.normalized S.a)
    (VisitBounds.gamma S.b S.setup) S.low (mul_pos hζ hL) hπ hΓ
    (InitialDrift.normalized_sum hn S.a S.a_lower) S.high
  have hell0 : 0 ≤ ∑ w ∈ S.low, InitialDrift.normalized S.a w :=
    Finset.sum_nonneg fun w _ ↦ hπ w
  have hell : (∑ w ∈ S.low, InitialDrift.normalized S.a w) ≤ 1 / Real.log n := by
    apply (le_div_iff₀ hL).mpr
    nlinarith [mul_nonneg hell0 (mul_nonneg hL.le (sub_nonneg.mpr hlog))]
  have hone : SmoothRates.rate (InitialDrift.normalized S.a)
      (VisitBounds.gamma S.b S.setup) 1 ≤ (1 + 1 / ζ) / Real.log n := by
    calc
      _ ≤ 1 / Real.log n + 1 / (ζ * Real.log n) := hr.trans (add_le_add hell le_rfl)
      _ = _ := by field_simp
  have hp := SmoothRates.rate_le_popularity_mul_one (InitialDrift.normalized S.a)
    (VisitBounds.gamma S.b S.setup) hβ hπ hΓ
  calc
    _ ≤ β * ((1 + 1 / ζ) / Real.log n) :=
      hp.trans (mul_le_mul_of_nonneg_left hone (by linarith))
    _ ≤ B * ((1 + 1 / ζ) / Real.log n) :=
      mul_le_mul_of_nonneg_right hβB (by positivity)
    _ = _ := by ring


/-- The exact ceiling cap is bounded above by a fixed log-squared coefficient. -/
theorem cap_upper {A B C : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C)
    {n : ℕ} (hlog : 1 ≤ Real.log n) :
    (cap A B C n : ℝ) ≤ (capCoefficient A B C + 1) * (Real.log n) ^ 2 := by
  have hcp := (lowerConstant_bounds hA hB hC).1
  have hD : 0 ≤ capCoefficient A B C := by unfold capCoefficient; positivity
  have hc := Nat.ceil_lt_add_one (mul_nonneg hD (sq_nonneg (Real.log n)))
  change (Nat.ceil (capCoefficient A B C * (Real.log n) ^ 2) : ℝ) ≤ _
  nlinarith [sq_nonneg (Real.log n - 1)]

/-- The genuine integer cap makes the worst permitted survival tail polynomially small. -/
theorem tail_bound {A B C : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C)
    {n : ℕ} (hn : 0 < n) (hlog : 0 < Real.log n) {p d : ℝ}
    (hp : lowerConstant A B C / Real.log n ≤ p)
    (hd : d ≤ lowerConstant A B C / (2 * Real.log n)) (hpd : p + d ≤ 1)
    (hd0 : 0 ≤ d) :
    (1 - p + d) ^ cap A B C n ≤ 1 / (n : ℝ) ^ 10 := by
  have hcp := (lowerConstant_bounds hA hB hC).1
  have hbase : 0 ≤ 1 - p + d := by linarith
  have hbase' : 1 - p + d ≤ Real.exp (-(lowerConstant A B C / Real.log n) / 2) := by
    have he := Real.add_one_le_exp (-(lowerConstant A B C / Real.log n) / 2)
    have heq : lowerConstant A B C / (2 * Real.log n) =
        (lowerConstant A B C / Real.log n) / 2 := by ring
    rw [heq] at hd
    linarith
  have ht := ContinuationAsymptotics.threshold_exp_le hcp (by norm_num : (0 : ℝ) < 1)
    hlog (show 2 * (10 : ℝ) ≤ lowerConstant A B C * 1 * capCoefficient A B C by
      unfold capCoefficient; field_simp; norm_num)
  calc
    _ ≤ (Real.exp (-(lowerConstant A B C / Real.log n) / 2)) ^ cap A B C n :=
      pow_le_pow_left₀ hbase hbase' _
    _ = Real.exp (-((lowerConstant A B C / Real.log n) * 1 / 2) * cap A B C n) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (-(10 : ℝ) * Real.log n) := ht
    _ = _ := ContinuationAsymptotics.exp_neg_nat_log hn 10

/-- A uniform deterministic coefficient for the actual mean-error envelope. -/
noncomputable def errorCoefficient (A B C : ℝ) : ℝ :=
  32 * A * (capCoefficient A B C + 1) / (lowerConstant A B C) ^ 2 +
    1 + 2 / lowerConstant A B C

/-- The exact finite-count error is bounded uniformly over all permitted baselines. -/
theorem error_bound {A B C : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C)
    {n : ℕ} (hn : 1 ≤ n) (hlog : 1 ≤ Real.log n) (hLn : Real.log n ≤ n)
    {p d : ℝ} (hp : lowerConstant A B C / Real.log n ≤ p)
    (hd : 0 ≤ d) (hdp : d ≤ lowerConstant A B C / (2 * Real.log n))
    (hdcap : d ≤ 8 * A * (capCoefficient A B C + 1) * (Real.log n) ^ 2 / n)
    (ht : (1 - p + d) ^ cap A B C n ≤ 1 / (n : ℝ) ^ 10) :
    InitialPhase.error n (cap A B C n) p d ≤
      errorCoefficient A B C * (Real.log n) ^ 4 / n := by
  have hcp := (lowerConstant_bounds hA hB hC).1
  have hN : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 < Real.log n := by linarith
  have hgap : lowerConstant A B C / (2 * Real.log n) ≤ p - d := by
    calc
      _ = lowerConstant A B C / Real.log n -
          lowerConstant A B C / (2 * Real.log n) := by ring
      _ ≤ p - d := sub_le_sub hp hdp
  have hgap0 : 0 < p - d := (by positivity : 0 < lowerConstant A B C /
    (2 * Real.log n)).trans_le hgap
  have hinv : 1 / (p - d) ≤ 2 * Real.log n / lowerConstant A B C := by
    calc
      _ ≤ 1 / (lowerConstant A B C / (2 * Real.log n)) :=
        one_div_le_one_div_of_le (by positivity) hgap
      _ = _ := by field_simp
  have hsq : (lowerConstant A B C / (2 * Real.log n)) ^ 2 ≤ (p - d) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hgap 2
  have hfirst : d / (p - d) ^ 2 ≤
      (32 * A * (capCoefficient A B C + 1) / lowerConstant A B C ^ 2) *
        (Real.log n) ^ 4 / n := by
    calc
      _ ≤ (8 * A * (capCoefficient A B C + 1) * (Real.log n) ^ 2 / n) /
          (lowerConstant A B C / (2 * Real.log n)) ^ 2 :=
        div_le_div₀ (hd.trans hdcap) hdcap (by positivity) hsq
      _ = _ := by field_simp; ring
  have hsecond : ((n : ℝ) + 1 / (p - d)) * (1 - p + d) ^ cap A B C n ≤
      (1 + 2 / lowerConstant A B C) * (Real.log n) ^ 4 / n := by
    have hinv' : 1 / (p - d) ≤ 2 * n / lowerConstant A B C :=
      hinv.trans (div_le_div_of_nonneg_right (by linarith :
        2 * Real.log n ≤ 2 * n) hcp.le)
    have hh := mul_le_mul ht (show (n : ℝ) + 1 / (p - d) ≤
        (1 + 2 / lowerConstant A B C) * n by
          calc
            _ ≤ (n : ℝ) + 2 * n / lowerConstant A B C := add_le_add le_rfl hinv'
            _ = _ := by ring) (by positivity)
      (by positivity : 0 ≤ (1 : ℝ) / (n : ℝ) ^ 10)
    have hpow : (n : ℝ) ≤ (n : ℝ) ^ 10 := by
      exact le_self_pow₀ hN1 (by norm_num)
    have hL4 : 1 ≤ (Real.log n) ^ 4 := one_le_pow₀ hlog
    have hratio : (n : ℝ) / (n : ℝ) ^ 10 ≤ (Real.log n) ^ 4 / n := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 10) hN).mpr
      have hpow' : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 10 := by
        exact pow_le_pow_right₀ hN1 (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_right hL4 (pow_nonneg hN.le 10)]
    calc
      _ ≤ ((1 + 2 / lowerConstant A B C) * n) * (1 / (n : ℝ) ^ 10) := by
        simpa only [mul_comm] using hh
      _ = (1 + 2 / lowerConstant A B C) * ((n : ℝ) / (n : ℝ) ^ 10) := by ring
      _ ≤ (1 + 2 / lowerConstant A B C) * ((Real.log n) ^ 4 / n) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  unfold InitialPhase.error
  calc
    _ ≤ _ := add_le_add hfirst hsecond
    _ = _ := by unfold errorCoefficient; ring


/-- A convenient fixed multiplier for reciprocal-rate upper bounds. -/
noncomputable def meanCoefficient (A B C : ℝ) : ℝ := 1 + 1 / lowerConstant A B C

/-- Uniform finite numerical conditions, retaining the actual integer cap and drift. -/
structure Numeric (n : ℕ) (A B C : ℝ) where
  population : 2 ≤ n
  log_lower : 1 ≤ Real.log n
  log_upper : Real.log n ≤ n
  drift_half : InitialPhase.delta n (cap A B C n) A ≤
    lowerConstant A B C / (2 * Real.log n)
  used_small : 2 * A * cap A B C n / n ≤ 1 / 2
  inverse_bound : Real.log n / lowerConstant A B C ≤ n
  error_small : ∀ p : ℝ, lowerConstant A B C / Real.log n ≤ p → p ≤ 1 / 2 →
    InitialPhase.error n (cap A B C n) p (InitialPhase.delta n (cap A B C n) A) ≤
      1 / (8 * meanCoefficient A B C * Real.log n)

/-- The finite numerical conditions hold eventually with constants independent of setup. -/
theorem eventually_numeric {A B C : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, Numeric n A B C := by
  have hcp := (lowerConstant_bounds hA hB hC).1
  have hcp1 := (lowerConstant_bounds hA hB hC).2
  have hA0 : 0 < A := by linarith
  have hD : 0 < capCoefficient A B C := by unfold capCoefficient; positivity
  have hK : 0 < errorCoefficient A B C := by unfold errorCoefficient; positivity
  have hQ : 0 < meanCoefficient A B C := by unfold meanCoefficient; positivity
  have hQ1 : 1 ≤ meanCoefficient A B C := by
    unfold meanCoefficient
    linarith [one_div_pos.mpr hcp]
  have hε : 0 < lowerConstant A B C / (16 * A * (capCoefficient A B C + 1)) := by
    positivity
  have hε' : 0 < 1 / (8 * meanCoefficient A B C * errorCoefficient A B C) := by
    positivity
  filter_upwards [eventually_log_power_le hε zero_lt_one 3,
    eventually_log_power_le hε' zero_lt_one 5,
    eventually_log_power_le hcp zero_lt_one 1,
    ContinuationAsymptotics.eventually_one_le_log, eventually_ge_atTop (2 : ℕ)]
    with n hdr herr hinv hlog hn
  simp only [Real.rpow_one, pow_one] at hdr herr hinv
  have hn0 : 0 < n := by omega
  have hN : (0 : ℝ) < n := by exact_mod_cast hn0
  have hL : 0 < Real.log n := by linarith
  have hLn : Real.log n ≤ n := (Real.log_le_sub_one_of_pos hN).trans (by linarith)
  have hdu : InitialPhase.delta n (cap A B C n) A ≤
      8 * A * (capCoefficient A B C + 1) * (Real.log n) ^ 2 / n := by
    unfold InitialPhase.delta
    have hm := mul_le_mul_of_nonneg_left (cap_upper hA hB hC hlog)
      (show 0 ≤ 8 * A by positivity)
    exact div_le_div_of_nonneg_right (by nlinarith [hm]) hN.le
  have hd : InitialPhase.delta n (cap A B C n) A ≤
      lowerConstant A B C / (2 * Real.log n) := by
    refine hdu.trans ?_
    apply (div_le_div_iff₀ hN (by positivity : 0 < 2 * Real.log n)).mpr
    have hm := mul_le_mul_of_nonneg_left hdr
      (show 0 ≤ 16 * A * (capCoefficient A B C + 1) by positivity)
    have he : (16 * A * (capCoefficient A B C + 1)) *
        (lowerConstant A B C / (16 * A * (capCoefficient A B C + 1)) * n) =
        lowerConstant A B C * n := by field_simp
    rw [he] at hm
    nlinarith
  have hd0 : 0 ≤ InitialPhase.delta n (cap A B C n) A := by
    unfold InitialPhase.delta
    positivity
  have hdhalf : InitialPhase.delta n (cap A B C n) A ≤ 1 / 2 := by
    refine hd.trans ?_
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.log n)).mpr
    linarith
  refine ⟨hn, hlog, hLn, hd, ?_, ?_, ?_⟩
  · have he : 2 * A * cap A B C n / n =
        InitialPhase.delta n (cap A B C n) A / 4 := by unfold InitialPhase.delta; ring
    rw [he]
    linarith
  · exact (div_le_iff₀ hcp).mpr (by nlinarith [hinv])
  · intro p hp hp1
    have hpd : p + InitialPhase.delta n (cap A B C n) A ≤ 1 := by linarith
    have ht := tail_bound hA hB hC hn0 hL hp hd hpd hd0
    refine (error_bound hA hB hC (by omega) hlog hLn hp hd0 hd hdu ht).trans ?_
    apply (div_le_div_iff₀ hN (by positivity :
      0 < 8 * meanCoefficient A B C * Real.log n)).mpr
    have hm := mul_le_mul_of_nonneg_left herr
      (show 0 ≤ 8 * meanCoefficient A B C * errorCoefficient A B C by positivity)
    have he : (8 * meanCoefficient A B C * errorCoefficient A B C) *
        (1 / (8 * meanCoefficient A B C * errorCoefficient A B C) * n) = n := by
      field_simp
    rw [he] at hm
    nlinarith

/-- Baselines for all bounded scores are eventually at most one half, uniformly over setup. -/
theorem eventually_rate_upper {A B C ζ κ : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hζ : 0 < ζ) (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop, ∀ S : Setting n A B C ζ κ, ∀ β : ℝ,
      1 ≤ β → β ≤ B →
      SmoothRates.rate (InitialDrift.normalized S.a)
        (VisitBounds.gamma S.b S.setup) β ≤ 1 / 2 := by
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (2 * B * (1 + 1 / ζ)))
  filter_upwards [eventually_low_mass hA hκ,
    ContinuationAsymptotics.eventually_one_le_log, eventually_ge_atTop (1 : ℕ), hlog]
    with n hlow hL hn hb S β hβ hβB
  refine (rate_upper S (by omega) hζ hB hL (hlow S) hβ hβB).trans ?_
  apply (div_le_iff₀ (by linarith : 0 < Real.log n)).mpr
  dsimp only [Function.comp_apply] at hb
  linarith


/-- The original market law conditioned on the literal completed setup prefix. -/
noncomputable def law {n : ℕ} {A B C ζ κ : ℝ} (S : Setting n A B C ζ κ) : PMF (Profile n) :=
  InitialPhase.setupLaw (Continuation.market S.a S.b) S.u S.v S.setup

/-- The actual first initial proposal count mean. -/
noncomputable def firstMean {n : ℕ} {A B C ζ κ : ℝ} (S : Setting n A B C ζ κ) : ℝ :=
  HazardMoments.mean (law S) (fun p ↦ InitialPhase.A1 p S.u S.v)

/-- The actual second initial proposal count mean. -/
noncomputable def secondMean {n : ℕ} {A B C ζ κ : ℝ} (S : Setting n A B C ζ κ) : ℝ :=
  HazardMoments.mean (law S) (fun p ↦ InitialPhase.A2 p S.u S.v)

/-- The actual conditional covariance of the two initial proposal counts. -/
noncomputable def covariance {n : ℕ} {A B C ζ κ : ℝ} (S : Setting n A B C ζ κ) : ℝ :=
  ProbabilityTheory.covariance (fun p ↦ (InitialPhase.A1 p S.u S.v : ℝ))
    (fun p ↦ (InitialPhase.A2 p S.u S.v : ℝ)) (law S).toMeasure

/-- The score-one baseline supplies the common inverse-popularity scale. -/
noncomputable def commonScale {n : ℕ} {A B C ζ κ : ℝ} (S : Setting n A B C ζ κ) : ℝ :=
  1 / SmoothRates.rate (InitialDrift.normalized S.a) (VisitBounds.gamma S.b S.setup) 1

/-- The fixed additive inverse-popularity error, including the actual finite-phase error. -/
noncomputable def scalingConstant (A B C ζ : ℝ) : ℝ :=
  1 + (B - 1) / (ζ * lowerConstant A B C) + 1 / lowerConstant A B C ^ 2

/-- Reciprocal baselines are bounded by the same logarithmic scale. -/
theorem inverse_rate_upper {n : ℕ} {A B C ζ κ : ℝ} (S : Setting n A B C ζ κ)
    (hn : 0 < n) (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hlog : 1 ≤ Real.log n) {β : ℝ} (hβ : 1 ≤ β) :
    1 / SmoothRates.rate (InitialDrift.normalized S.a) (VisitBounds.gamma S.b S.setup) β ≤
      Real.log n / lowerConstant A B C := by
  have hcp := (lowerConstant_bounds hA hB hC).1
  calc
    _ ≤ 1 / (lowerConstant A B C / Real.log n) :=
      one_div_le_one_div_of_le (by positivity) (rate_lower S hn hA hB hC hlog hβ)
    _ = _ := by field_simp

/-- Inverse-popularity scaling of the deterministic setup baseline, uniformly in the man. -/
theorem reciprocal_scaling {n : ℕ} {A B C ζ κ : ℝ} (S : Setting n A B C ζ κ)
    (hn : 0 < n) (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C) (hζ : 0 < ζ)
    (hlog : 1 ≤ Real.log n)
    (hlow : (∑ w ∈ S.low, InitialDrift.normalized S.a w) * (Real.log n) ^ 2 ≤ 1)
    (m : Fin n) :
    |1 / InitialPhase.baseline S.a S.b S.setup m - commonScale S / (S.b m : ℝ)| ≤
      scalingConstant A B C ζ - 1 := by
  have hcp := (lowerConstant_bounds hA hB hC).1
  have hL : 0 < Real.log n := by linarith
  have hΓ (w : Fin n) : 0 ≤ VisitBounds.gamma S.b S.setup w :=
    Finset.sum_nonneg fun k _ ↦ (S.b k.val).coe_nonneg
  have hmass : 0 < ∑ w, InitialDrift.normalized S.a w := by
    rw [InitialDrift.normalized_sum hn S.a S.a_lower]
    norm_num
  have hr := SmoothRates.reciprocal_scaling_error_le_uniform (InitialDrift.normalized S.a)
    (VisitBounds.gamma S.b S.setup) S.low (S.b_lower m) (S.b_upper m) hL hζ hcp
    (InitialDrift.normalized_nonneg S.a) hΓ hmass S.high le_rfl
    (rate_lower S hn hA hB hC hlog (by norm_num : (1 : ℝ) ≤ 1)) hlow
  have he : commonScale S / (S.b m : ℝ) =
      1 / ((S.b m : ℝ) * SmoothRates.rate (InitialDrift.normalized S.a)
        (VisitBounds.gamma S.b S.setup) 1) := by unfold commonScale; ring
  rw [he]
  convert hr using 1
  · rfl
  · unfold scalingConstant
    ring

/-- Polynomial error terms used by the actual finite-phase estimates are uniformly small. -/
theorem polynomial_payments {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) * (1 / (n : ℝ) ^ 10) ≤ 1 / 2 ∧
      2 * (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ 10) ≤ 1 / 2 := by
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have h8 : (256 : ℝ) ≤ (n : ℝ) ^ 8 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 8
    norm_num at hh
    exact hh
  have hpow : (n : ℝ) ^ 10 = (n : ℝ) ^ 8 * (n : ℝ) ^ 2 := by ring
  constructor
  · rw [mul_one_div]
    apply (div_le_iff₀ (pow_pos hN0 10)).mpr
    rw [hpow]
    nlinarith [mul_nonneg (sub_nonneg.mpr h8) (sq_nonneg (n : ℝ)),
      mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith) hN0.le]
  · rw [mul_one_div]
    apply (div_le_iff₀ (pow_pos hN0 10)).mpr
    rw [hpow]
    nlinarith [mul_nonneg (sub_nonneg.mpr h8) (sq_nonneg (n : ℝ))]


/-- The actual initial moments, expressed using the deterministic setup baselines. -/
structure MomentPacket {n : ℕ} {A B C ζ κ : ℝ} (S : Setting n A B C ζ κ) : Prop where
  first_error : |firstMean S - 1 / InitialPhase.baseline S.a S.b S.setup S.u| ≤ 1
  second_error : |secondMean S - 1 / InitialPhase.baseline S.a S.b S.setup S.v| ≤ 1
  first_upper : firstMean S ≤ meanCoefficient A B C * Real.log n
  second_upper : secondMean S ≤ meanCoefficient A B C * Real.log n
  covariance_lower : -1 ≤ covariance S

/-- The finite actual count estimates imply the moment packet under uniform numeric bounds. -/
theorem momentPacket {n : ℕ} {A B C ζ κ : ℝ} (S : Setting n A B C ζ κ)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C) (H : Numeric n A B C)
    (hpu : InitialPhase.baseline S.a S.b S.setup S.u ≤ 1 / 2)
    (hpv : InitialPhase.baseline S.a S.b S.setup S.v ≤ 1 / 2) : MomentPacket S := by
  let pu := InitialPhase.baseline S.a S.b S.setup S.u
  let pv := InitialPhase.baseline S.a S.b S.setup S.v
  let d := InitialPhase.delta n (cap A B C n) A
  let Eu := InitialPhase.error n (cap A B C n) pu d
  let Ev := InitialPhase.error n (cap A B C n) pv d
  have hn : 0 < n := by have := H.population; omega
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log n := by have := H.log_lower; linarith
  have hcp := (lowerConstant_bounds hA hB hC).1
  have hQ : 0 < meanCoefficient A B C := by unfold meanCoefficient; positivity
  have hQ1 : 1 ≤ meanCoefficient A B C := by
    unfold meanCoefficient
    linarith [one_div_pos.mpr hcp]
  have hd0 : 0 ≤ d := by dsimp [d, InitialPhase.delta]; positivity
  have hpu0 : lowerConstant A B C / Real.log n ≤ pu :=
    rate_lower S hn hA hB hC H.log_lower (S.b_lower S.u)
  have hpv0 : lowerConstant A B C / Real.log n ≤ pv :=
    rate_lower S hn hA hB hC H.log_lower (S.b_lower S.v)
  have hdpu : d < pu := by
    have hh := H.drift_half
    have hp0 : 0 < lowerConstant A B C / Real.log n := by positivity
    have heq : lowerConstant A B C / (2 * Real.log n) =
        (lowerConstant A B C / Real.log n) / 2 := by ring
    rw [heq] at hh
    dsimp [d]
    linarith [hpu0, hh]
  have hdpv : d < pv := by
    have hh := H.drift_half
    have hp0 : 0 < lowerConstant A B C / Real.log n := by positivity
    have heq : lowerConstant A B C / (2 * Real.log n) =
        (lowerConstant A B C / Real.log n) / 2 := by ring
    rw [heq] at hh
    dsimp [d]
    linarith [hpv0, hh]
  have hdhalf : d ≤ 1 / 2 := by
    refine H.drift_half.trans ?_
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.log n)).mpr
    nlinarith [H.log_lower, (lowerConstant_bounds hA hB hC).2]
  have hpud : pu + d ≤ 1 := by linarith
  have hpvd : pv + d ≤ 1 := by linarith
  have hEu0 : 0 ≤ Eu := InitialPhase.error_nonneg _ _ hd0 hdpu hpud
  have hEv0 : 0 ≤ Ev := InitialPhase.error_nonneg _ _ hd0 hdpv hpvd
  have hEu : Eu ≤ 1 / (8 * meanCoefficient A B C * Real.log n) :=
    H.error_small pu hpu0 hpu
  have hEv : Ev ≤ 1 / (8 * meanCoefficient A B C * Real.log n) :=
    H.error_small pv hpv0 hpv
  have hEL : 1 / (8 * meanCoefficient A B C * Real.log n) ≤ 1 / 8 := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * meanCoefficient A B C * Real.log n)).mpr
    nlinarith [mul_le_mul hQ1 H.log_lower (by norm_num : (0 : ℝ) ≤ 1) hQ.le]
  have htail := tail_bound hA hB hC hn hL hpu0 H.drift_half hpud hd0
  have hb (m : Fin n) : 0 < S.b m := by
    exact_mod_cast (show 0 < (S.b m : ℝ) by linarith [S.b_lower m])
  have hiu : 1 / pu ≤ Real.log n / lowerConstant A B C :=
    inverse_rate_upper S hn hA hB hC H.log_lower (S.b_lower S.u)
  have hiv : 1 / pv ≤ Real.log n / lowerConstant A B C :=
    inverse_rate_upper S hn hA hB hC H.log_lower (S.b_lower S.v)
  have hvn : 1 / pv ≤ n := hiv.trans H.inverse_bound
  have hfirst := InitialPhase.first_mean_error hn S.a S.b (by linarith : 0 ≤ A)
    S.a_lower S.a_upper hb S.u S.v S.distinct S.setup S.nonnull
    (cap A B C n) H.used_small hdpu hpud
  change |firstMean S - 1 / pu| ≤ Eu at hfirst
  have hsecond := InitialPhase.second_mean_error_geometric_tail hn S.a S.b
    (by linarith : 0 ≤ A) S.a_lower S.a_upper hb S.u S.v S.distinct S.setup S.nonnull
    (cap A B C n) H.used_small hpud hdpv hpvd hvn
  change |secondMean S - 1 / pv| ≤ Ev + (n : ℝ) * (1 - pu + d) ^ cap A B C n at hsecond
  have hpay := polynomial_payments H.population
  have hbad : (n : ℝ) * (1 - pu + d) ^ cap A B C n ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left htail hN.le).trans hpay.1
  have hfirst1 : |firstMean S - 1 / pu| ≤ 1 := by linarith
  have hsecond1 : |secondMean S - 1 / pv| ≤ 1 := by linarith
  have hscale : Real.log n / lowerConstant A B C + 1 ≤
      meanCoefficient A B C * Real.log n := by
    have heq : meanCoefficient A B C * Real.log n =
        Real.log n / lowerConstant A B C + Real.log n := by
      unfold meanCoefficient
      ring
    rw [heq]
    linarith [H.log_lower]
  have hcov := InitialPhase.initial_covariance_lower_geometric_tail hn S.a S.b
    (by linarith : 0 ≤ A) S.a_lower S.a_upper hb S.u S.v S.distinct S.setup S.nonnull
    (cap A B C n) H.used_small hdpu hpud hdpv hpvd hvn
  change -2 * (1 / pu + Eu) * Ev -
    2 * (n : ℝ) ^ 2 * (1 - pu + d) ^ cap A B C n ≤ covariance S at hcov
  have hM : 1 / pu + Eu ≤ meanCoefficient A B C * Real.log n := by linarith
  have hproduct : (1 / pu + Eu) * Ev ≤ 1 / 8 := by
    have hmul := mul_le_mul_of_nonneg_right hM hEv0
    have hbound := (le_div_iff₀ (by positivity :
      0 < 8 * meanCoefficient A B C * Real.log n)).mp hEv
    nlinarith
  have htailpay : 2 * (n : ℝ) ^ 2 * (1 - pu + d) ^ cap A B C n ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left htail (by positivity)).trans hpay.2
  refine ⟨hfirst1, hsecond1, ?_, ?_, ?_⟩
  · have hm : firstMean S ≤ 1 / pu + 1 := by linarith [(abs_le.mp hfirst1).2]
    exact (hm.trans (add_le_add hiu le_rfl)).trans hscale
  · have hm : secondMean S ≤ 1 / pv + 1 := by linarith [(abs_le.mp hsecond1).2]
    exact (hm.trans (add_le_add hiv le_rfl)).trans hscale
  · linarith


/-- Uniform original-law initial estimates with one common inverse-popularity scale. -/
structure Packet {n : ℕ} {A B C ζ κ : ℝ} (S : Setting n A B C ζ κ) : Prop
    extends MomentPacket S where
  scale_positive : 0 < commonScale S
  scale_lower : Real.log n / (B * (1 + 1 / ζ)) ≤ commonScale S
  scale_upper : commonScale S ≤ Real.log n / lowerConstant A B C
  first_scaling : |firstMean S - commonScale S / (S.b S.u : ℝ)| ≤ scalingConstant A B C ζ
  second_scaling : |secondMean S - commonScale S / (S.b S.v : ℝ)| ≤ scalingConstant A B C ζ

/-- Fixed deterministic good-setup bounds give actual initial moment and scaling estimates,
eventually uniformly over all scores, distinct last men, and nonnull setup prefixes. -/
theorem eventually_packet {A B C ζ κ : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hC : 0 ≤ C) (hζ : 0 < ζ) (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop, ∀ S : Setting n A B C ζ κ, Packet S := by
  filter_upwards [eventually_numeric hA hB hC, eventually_rate_upper hA hB hζ hκ,
    eventually_low_mass hA hκ] with n H hr hl S
  have hn : 0 < n := by have := H.population; omega
  have hL : 0 < Real.log n := by have := H.log_lower; linarith
  have hcp := (lowerConstant_bounds hA hB hC).1
  have hM := momentPacket S hA hB hC H (hr S _ (S.b_lower S.u) (S.b_upper S.u))
    (hr S _ (S.b_lower S.v) (S.b_upper S.v))
  have hp0 : 0 < SmoothRates.rate (InitialDrift.normalized S.a)
      (VisitBounds.gamma S.b S.setup) 1 :=
    (by positivity : 0 < lowerConstant A B C / Real.log n).trans_le
      (rate_lower S hn hA hB hC H.log_lower (by norm_num : (1 : ℝ) ≤ 1))
  have hscale0 : 0 < commonScale S := one_div_pos.mpr hp0
  have hscaleupper : commonScale S ≤ Real.log n / lowerConstant A B C :=
    inverse_rate_upper S hn hA hB hC H.log_lower (by norm_num : (1 : ℝ) ≤ 1)
  have hscalelower : Real.log n / (B * (1 + 1 / ζ)) ≤ commonScale S := by
    have hbpos : 0 < B := by linarith
    have hup := rate_upper S hn hζ hB H.log_lower (hl S)
      (by norm_num : (1 : ℝ) ≤ 1) hB
    calc
      _ = 1 / (B * (1 + 1 / ζ) / Real.log n) := by field_simp
      _ ≤ _ := one_div_le_one_div_of_le hp0 hup
  refine ⟨hM, hscale0, hscalelower, hscaleupper, ?_, ?_⟩
  · calc
      _ ≤ |firstMean S - 1 / InitialPhase.baseline S.a S.b S.setup S.u| +
          |1 / InitialPhase.baseline S.a S.b S.setup S.u - commonScale S / (S.b S.u : ℝ)| :=
        abs_sub_le _ _ _
      _ ≤ 1 + (scalingConstant A B C ζ - 1) :=
        add_le_add hM.first_error (reciprocal_scaling S hn hA hB hC hζ H.log_lower (hl S) S.u)
      _ = _ := by ring
  · calc
      _ ≤ |secondMean S - 1 / InitialPhase.baseline S.a S.b S.setup S.v| +
          |1 / InitialPhase.baseline S.a S.b S.setup S.v - commonScale S / (S.b S.v : ℝ)| :=
        abs_sub_le _ _ _
      _ ≤ 1 + (scalingConstant A B C ζ - 1) :=
        add_le_add hM.second_error (reciprocal_scaling S hn hA hB hC hζ H.log_lower (hl S) S.v)
      _ = _ := by ring

end TieredMatching.InitialAsymptotics
