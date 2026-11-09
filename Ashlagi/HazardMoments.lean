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

public import Ashlagi.G2Deconditioning

/-! # Moments from local stopped survival hazards

The variable has its actual finite probability law. Tail-sum identities and truncated geometric
brackets are derived before bounding its mean; no geometric-reference coupling is assumed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Ashlagi.HazardMoments

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Actual real survival probability of a bounded stopping count. -/
noncomputable def survival (μ : PMF Ω) (A : Ω → ℕ) (t : ℕ) : ℝ :=
  μ.toMeasure.real {ω | t < A ω}

/-- The actual expectation of the stopping count. -/
noncomputable def mean (μ : PMF Ω) (A : Ω → ℕ) : ℝ := ∫ ω, (A ω : ℝ) ∂μ.toMeasure

/-- An integer equals the number of its strictly smaller nonnegative integers. -/
theorem nat_eq_sum_tail_indicators (a N : ℕ) (ha : a ≤ N) :
    (a : ℝ) = ∑ t ∈ Finset.range N, if t < a then (1 : ℝ) else 0 := by
  classical
  have hset : (Finset.range N).filter (fun t ↦ t < a) = Finset.range a := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hset]
  simp

/-- The exact finite tail-sum identity for the genuine bounded stopping variable. -/
theorem mean_eq_sum_survival (μ : PMF Ω) (A : Ω → ℕ) (N : ℕ) (hA : ∀ ω, A ω ≤ N) :
    mean μ A = ∑ t ∈ Finset.range N, survival μ A t := by
  classical
  have heq : (fun ω ↦ (A ω : ℝ)) = fun ω ↦
      ∑ t ∈ Finset.range N, ({ω | t < A ω} : Set Ω).indicator (fun _ ↦ (1 : ℝ)) ω := by
    funext ω
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using
      nat_eq_sum_tail_indicators (A ω) N (hA ω)
  unfold mean
  rw [heq, integral_finsetSum _ (fun t _ ↦
    (G2Deconditioning.memLp_finite μ.toMeasure _).integrable one_le_two)]
  apply Finset.sum_congr rfl
  intro t _
  rw [integral_indicator_const 1 (Set.toFinite _).measurableSet]
  simp only [smul_eq_mul, mul_one, survival]

/-- Clipping the actual count at a deterministic cap gives exactly the truncated tail sum. -/
theorem clipped_mean_eq_sum (μ : PMF Ω) (A : Ω → ℕ) (h : ℕ) :
    mean μ (fun ω ↦ min (A ω) h) = ∑ t ∈ Finset.range h, survival μ A t := by
  rw [mean_eq_sum_survival μ _ h (fun ω ↦ min_le_right _ _)]
  apply Finset.sum_congr rfl
  intro t ht
  apply congrArg (fun s ↦ μ.toMeasure.real s)
  ext ω
  simp only [Set.mem_ofPred_eq]
  have := Finset.mem_range.mp ht
  omega

/-- Truncating before a hazard cap loses at most the global finite bound times its tail mass. -/
theorem mean_truncation_bounds (μ : PMF Ω) (A : Ω → ℕ) (N h : ℕ)
    (hA : ∀ ω, A ω ≤ N) :
    (∑ t ∈ Finset.range h, survival μ A t) ≤ mean μ A ∧
      mean μ A ≤ (∑ t ∈ Finset.range h, survival μ A t) + (N : ℝ) * survival μ A h := by
  classical
  have hi (f : Ω → ℝ) : Integrable f μ.toMeasure :=
    (G2Deconditioning.memLp_finite μ.toMeasure f).integrable one_le_two
  have hlo : mean μ (fun ω ↦ min (A ω) h) ≤ mean μ A := by
    apply integral_mono (hi _) (hi _)
    intro ω
    change ((min (A ω) h : ℕ) : ℝ) ≤ (A ω : ℝ)
    exact_mod_cast min_le_left (A ω) h
  have hup : mean μ A ≤ mean μ (fun ω ↦ min (A ω) h) +
      (N : ℝ) * survival μ A h := by
    have hp (ω : Ω) : (A ω : ℝ) ≤ (min (A ω) h : ℕ) +
        ({ω | h < A ω} : Set Ω).indicator (fun _ ↦ (N : ℝ)) ω := by
      by_cases hh : h < A ω
      · have hmem : ω ∈ ({ω | h < A ω} : Set Ω) := hh
        rw [Set.indicator_of_mem hmem, min_eq_right hh.le]
        have hc : (A ω : ℝ) ≤ N := by exact_mod_cast hA ω
        have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
        linarith
      · have hmem : ω ∉ ({ω | h < A ω} : Set Ω) := hh
        rw [Set.indicator_of_notMem hmem, min_eq_left (le_of_not_gt hh), add_zero]
    have he := integral_mono (hi _) (hi _) hp
    rw [integral_add (hi _) (hi _), integral_indicator_const (N : ℝ)
      (Set.toFinite _).measurableSet] at he
    simpa only [smul_eq_mul, mul_comm, mean, survival] using he
  rw [clipped_mean_eq_sum] at hlo hup
  exact ⟨hlo, hup⟩

omit [Fintype Ω] [MeasurableSingletonClass Ω] in
/-- Positive stopping counts survive time zero with probability one. -/
theorem survival_zero (μ : PMF Ω) (A : Ω → ℕ) (hA : ∀ ω, 1 ≤ A ω) :
    survival μ A 0 = 1 := by
  unfold survival
  have heq : {ω | 0 < A ω} = (Set.univ : Set Ω) :=
    Set.eq_univ_of_forall fun ω ↦ hA ω
  rw [heq]
  exact probReal_univ

omit [Fintype Ω] [MeasurableSingletonClass Ω] in
/-- Survival probabilities are nonnegative. -/
theorem survival_nonneg (μ : PMF Ω) (A : Ω → ℕ) (t : ℕ) : 0 ≤ survival μ A t :=
  measureReal_nonneg

omit [Fintype Ω] [MeasurableSingletonClass Ω] in
/-- Local genuine survival hazards imply geometric survival brackets up to the cap. -/
theorem survival_geometric_bounds (μ : PMF Ω) (A : Ω → ℕ) (h : ℕ) (p δ : ℝ)
    (hA : ∀ ω, 1 ≤ A ω) (hδ : 0 ≤ δ) (hpδ : p + δ ≤ 1)
    (hazard : ∀ t < h, (1 - p - δ) * survival μ A t ≤ survival μ A (t + 1) ∧
      survival μ A (t + 1) ≤ (1 - p + δ) * survival μ A t)
    (t : ℕ) (ht : t ≤ h) :
    (1 - p - δ) ^ t ≤ survival μ A t ∧ survival μ A t ≤ (1 - p + δ) ^ t := by
  have ha : 0 ≤ 1 - p - δ := by linarith
  have hb : 0 ≤ 1 - p + δ := by linarith
  induction t with
  | zero => simp [survival_zero μ A hA]
  | succ t ih =>
    obtain ⟨hlo, hup⟩ := ih (by omega)
    have hz := hazard t (by omega)
    constructor
    · calc
        (1 - p - δ) ^ (t + 1) = (1 - p - δ) * (1 - p - δ) ^ t := pow_succ' _ _
        _ ≤ (1 - p - δ) * survival μ A t := mul_le_mul_of_nonneg_left hlo ha
        _ ≤ survival μ A (t + 1) := hz.1
    · calc
        survival μ A (t + 1) ≤ (1 - p + δ) * survival μ A t := hz.2
        _ ≤ (1 - p + δ) * (1 - p + δ) ^ t := mul_le_mul_of_nonneg_left hup hb
        _ = (1 - p + δ) ^ (t + 1) := (pow_succ' _ _).symm

/-- Finite geometric sums in the positive-hazard parameterization. -/
theorem sum_geometric_survival (u : ℝ) (hu : 0 < u) (h : ℕ) :
    (∑ t ∈ Finset.range h, (1 - u) ^ t) = (1 - (1 - u) ^ h) / u := by
  apply (eq_div_iff hu.ne').mpr
  simpa only [sub_sub_cancel] using geom_sum_mul_neg (1 - u) h

/-- Exact survival recursion and boundedness give a truncated geometric expectation interval. -/
theorem mean_geometric_interval (μ : PMF Ω) (A : Ω → ℕ) (N h : ℕ) (p δ : ℝ)
    (hA1 : ∀ ω, 1 ≤ A ω) (hAN : ∀ ω, A ω ≤ N)
    (hδ : 0 ≤ δ) (hδp : δ < p) (hpδ : p + δ ≤ 1)
    (hazard : ∀ t < h, (1 - p - δ) * survival μ A t ≤ survival μ A (t + 1) ∧
      survival μ A (t + 1) ≤ (1 - p + δ) * survival μ A t) :
    (1 - (1 - p - δ) ^ h) / (p + δ) ≤ mean μ A ∧
      mean μ A ≤ 1 / (p - δ) + (N : ℝ) * (1 - p + δ) ^ h := by
  have hminus : 0 < p - δ := sub_pos.mpr hδp
  have hplus : 0 < p + δ := by linarith
  have hb : 0 ≤ 1 - p + δ := by linarith
  have hbracket (t : ℕ) (ht : t ≤ h) :=
    survival_geometric_bounds μ A h p δ hA1 hδ hpδ hazard t ht
  have hslo : (∑ t ∈ Finset.range h, (1 - p - δ) ^ t) ≤
      ∑ t ∈ Finset.range h, survival μ A t :=
    Finset.sum_le_sum fun t ht ↦ (hbracket t (Finset.mem_range.mp ht).le).1
  have hsup : (∑ t ∈ Finset.range h, survival μ A t) ≤
      ∑ t ∈ Finset.range h, (1 - p + δ) ^ t :=
    Finset.sum_le_sum fun t ht ↦ (hbracket t (Finset.mem_range.mp ht).le).2
  have hbaseA : 1 - (p + δ) = 1 - p - δ := by ring
  have hbaseB : 1 - (p - δ) = 1 - p + δ := by ring
  have hgeomA := sum_geometric_survival (p + δ) hplus h
  have hgeomB := sum_geometric_survival (p - δ) hminus h
  rw [hbaseA] at hgeomA
  rw [hbaseB] at hgeomB
  rw [hgeomA] at hslo
  rw [hgeomB] at hsup
  have hsum : (∑ t ∈ Finset.range h, survival μ A t) ≤ 1 / (p - δ) :=
    hsup.trans (div_le_div_of_nonneg_right (by linarith [pow_nonneg hb h]) hminus.le)
  have htrunc := mean_truncation_bounds μ A N h hAN
  exact ⟨hslo.trans htrunc.1, htrunc.2.trans (add_le_add hsum
    (mul_le_mul_of_nonneg_left (hbracket h le_rfl).2 (Nat.cast_nonneg N)))⟩

/-- A local stopped hazard controls the actual mean, paying explicitly for the uncontrolled tail. -/
theorem abs_mean_sub_inv_le (μ : PMF Ω) (A : Ω → ℕ) (N h : ℕ) (p δ : ℝ)
    (hA1 : ∀ ω, 1 ≤ A ω) (hAN : ∀ ω, A ω ≤ N)
    (hδ : 0 ≤ δ) (hδp : δ < p) (hpδ : p + δ ≤ 1)
    (hazard : ∀ t < h, (1 - p - δ) * survival μ A t ≤ survival μ A (t + 1) ∧
      survival μ A (t + 1) ≤ (1 - p + δ) * survival μ A t) :
    |mean μ A - 1 / p| ≤ δ / (p - δ) ^ 2 +
      ((N : ℝ) + 1 / (p - δ)) * (1 - p + δ) ^ h := by
  have hp : 0 < p := lt_of_le_of_lt hδ hδp
  have hminus : 0 < p - δ := sub_pos.mpr hδp
  have hplus : 0 < p + δ := by linarith
  have ha : 0 ≤ 1 - p - δ := by linarith
  have hb : 0 ≤ 1 - p + δ := by linarith
  have hab : 1 - p - δ ≤ 1 - p + δ := by linarith
  have hint := mean_geometric_interval μ A N h p δ hA1 hAN hδ hδp hpδ hazard
  have hrecipMinus : 1 / (p - δ) - 1 / p ≤ δ / (p - δ) ^ 2 := by
    have heq : 1 / (p - δ) - 1 / p = δ / (p * (p - δ)) := by
      field_simp
      ring
    rw [heq]
    apply div_le_div_of_nonneg_left hδ (sq_pos_of_pos hminus)
    nlinarith
  have hrecipPlus : 1 / p - 1 / (p + δ) ≤ δ / (p - δ) ^ 2 := by
    have heq : 1 / p - 1 / (p + δ) = δ / (p * (p + δ)) := by
      field_simp
      ring
    rw [heq]
    apply div_le_div_of_nonneg_left hδ (sq_pos_of_pos hminus)
    nlinarith
  have hcut : (1 - p - δ) ^ h / (p + δ) ≤
      (1 - p + δ) ^ h / (p - δ) := by
    have hi : 1 / (p + δ) ≤ 1 / (p - δ) :=
      one_div_le_one_div_of_le hminus (by linarith)
    have hm := mul_le_mul (pow_le_pow_left₀ ha hab h) hi
      (by positivity : 0 ≤ 1 / (p + δ)) (pow_nonneg hb h)
    simpa only [div_eq_mul_inv, one_mul] using hm
  rw [abs_le]
  constructor
  · have hlo : 1 / (p + δ) - (1 - p - δ) ^ h / (p + δ) ≤ mean μ A := by
      simpa only [sub_div] using hint.1
    have hN : 0 ≤ (N : ℝ) * (1 - p + δ) ^ h := mul_nonneg (Nat.cast_nonneg N)
      (pow_nonneg hb h)
    have hcut' : (1 - p - δ) ^ h / (p + δ) ≤
        1 / (p - δ) * (1 - p + δ) ^ h := by
      convert hcut using 1; ring
    nlinarith [hcut']
  · have htail : 0 ≤ 1 / (p - δ) * (1 - p + δ) ^ h := by positivity
    nlinarith [hint.2]

/-- A history-measurable first count and a close good-state mean control covariance. -/
theorem covariance_lower_of_close_on_good (μ : PMF Ω) (X Y : Ω → ℝ) (good : Set Ω)
    (N M ε c : ℝ) (hN : 0 ≤ N) (hε : 0 ≤ ε)
    (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ N) (hY : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ N)
    (hc : 0 ≤ c ∧ c ≤ N) (hXM : (∫ ω, X ω ∂μ.toMeasure) ≤ M)
    (hclose : ∀ ω ∈ good, |Y ω - c| ≤ ε) :
    -2 * M * ε - 2 * N ^ 2 * μ.toMeasure.real goodᶜ ≤ covariance X Y μ.toMeasure := by
  classical
  let bad := goodᶜ
  have hi (f : Ω → ℝ) : Integrable f μ.toMeasure :=
    (G2Deconditioning.memLp_finite μ.toMeasure f).integrable one_le_two
  have hprod_point (ω : Ω) : -ε * X ω - bad.indicator (fun _ ↦ N ^ 2) ω ≤
      X ω * (Y ω - c) := by
    by_cases hg : ω ∈ good
    · have hb : ω ∉ bad := by simpa only [bad, Set.mem_compl_iff, not_not] using hg
      rw [Set.indicator_of_notMem hb, sub_zero]
      have hh := mul_le_mul_of_nonneg_left (abs_le.mp (hclose ω hg)).1 (hX ω).1
      nlinarith
    · have hb : ω ∈ bad := hg
      rw [Set.indicator_of_mem hb]
      have hxy := mul_nonneg (hX ω).1 (hY ω).1
      have hxc := mul_le_mul (hX ω).2 hc.2 hc.1 hN
      have he := mul_nonneg hε (hX ω).1
      nlinarith
  have hprod := integral_mono (hi _) (hi _) hprod_point
  rw [integral_sub (hi _) (hi _), integral_const_mul, integral_indicator_const (N ^ 2)
    (Set.toFinite bad).measurableSet] at hprod
  simp only [smul_eq_mul, mul_comm (μ.toMeasure.real bad) (N ^ 2)] at hprod
  have herror_point (ω : Ω) : Y ω - c ≤ ε + bad.indicator (fun _ ↦ N) ω := by
    by_cases hg : ω ∈ good
    · have hb : ω ∉ bad := by simpa only [bad, Set.mem_compl_iff, not_not] using hg
      rw [Set.indicator_of_notMem hb, add_zero]
      exact (abs_le.mp (hclose ω hg)).2
    · have hb : ω ∈ bad := hg
      rw [Set.indicator_of_mem hb]
      linarith [(hY ω).2, hc.1]
  have herror := integral_mono (hi _) (hi _) herror_point
  rw [integral_add (hi _) (hi _), integral_const, integral_indicator_const N
    (Set.toFinite bad).measurableSet] at herror
  simp only [probReal_univ, smul_eq_mul, mul_comm (μ.toMeasure.real bad) N] at herror
  have hmean := G2Deconditioning.integral_bounds_of_nonnegative_bounded μ.toMeasure X (hi X) hX
  have hmul := mul_le_mul_of_nonneg_left herror hmean.1
  have heps := mul_le_mul_of_nonneg_left hXM hε
  have hbad : (∫ ω, X ω ∂μ.toMeasure) * N * μ.toMeasure.real bad ≤
      N ^ 2 * μ.toMeasure.real bad := by
    have hh := mul_le_mul_of_nonneg_right hmean.2 hN
    have hh' := mul_le_mul_of_nonneg_right hh (measureReal_nonneg : 0 ≤ μ.toMeasure.real bad)
    nlinarith
  rw [← covariance_sub_const_right (hi Y) c,
    covariance_eq_sub (G2Deconditioning.memLp_finite μ.toMeasure X)
      (G2Deconditioning.memLp_finite μ.toMeasure (fun ω ↦ Y ω - c))]
  simp only [Pi.mul_apply]
  change -2 * M * ε - 2 * N ^ 2 * μ.toMeasure.real bad ≤ _
  nlinarith

/-- The actual joint finite law of a revealed stopping history and its conditional future. -/
noncomputable def historyFuture {H : Type*} (ν : PMF H) (law : H → PMF Ω) : PMF (H × Ω) :=
  ν.bind fun h ↦ (law h).map (Prod.mk h)

/-- Exact tower identity for the actual finite history/future joint distribution. -/
theorem integral_historyFuture {H : Type*} [Fintype H] [MeasurableSpace H]
    [MeasurableSingletonClass H] (ν : PMF H) (law : H → PMF Ω) (f : H × Ω → ℝ) :
    (∫ z, f z ∂(historyFuture ν law).toMeasure) =
      ∫ h, (∫ ω, f (h, ω) ∂(law h).toMeasure) ∂ν.toMeasure := by
  rw [historyFuture, G2Deconditioning.integral_bind]
  congr 1
  funext h
  have hmk : Measurable (Prod.mk h : Ω → H × Ω) := measurable_const.prodMk measurable_id
  rw [← PMF.toMeasure_map (Prod.mk h) (law h) hmk]
  exact integral_map hmk.aemeasurable (measurable_of_finite f).aestronglyMeasurable

/-- A history-measurable count has covariance with a future count equal to covariance with its
conditional mean, under the exact finite joint distribution.
-/
theorem covariance_historyFuture {H : Type*} [Fintype H] [MeasurableSpace H]
    [MeasurableSingletonClass H] (ν : PMF H) (law : H → PMF Ω)
    (A1 : H → ℝ) (A2 : H → Ω → ℝ) :
    covariance (fun z : H × Ω ↦ A1 z.1) (fun z ↦ A2 z.1 z.2)
      (historyFuture ν law).toMeasure =
      covariance A1 (fun h ↦ ∫ ω, A2 h ω ∂(law h).toMeasure) ν.toMeasure := by
  rw [covariance_eq_sub (G2Deconditioning.memLp_finite (historyFuture ν law).toMeasure _)
    (G2Deconditioning.memLp_finite (historyFuture ν law).toMeasure _),
    covariance_eq_sub (G2Deconditioning.memLp_finite ν.toMeasure _)
      (G2Deconditioning.memLp_finite ν.toMeasure _)]
  simp only [Pi.mul_apply]
  rw [integral_historyFuture, integral_historyFuture, integral_historyFuture]
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul]

/-- The initial-count covariance estimate conditions only on the revealed stopping history.
The bad-history term is charged twice and no future count or future good event is conditioned on.
-/
theorem initial_covariance_lower {H : Type*} [Fintype H] [MeasurableSpace H]
    [MeasurableSingletonClass H] (ν : PMF H) (law : H → PMF Ω)
    (A1 : H → ℝ) (A2 : H → Ω → ℝ) (N M ε c cap : ℝ)
    (hN : 0 ≤ N) (hε : 0 ≤ ε) (hA1 : ∀ h, 0 ≤ A1 h ∧ A1 h ≤ N)
    (hA2 : ∀ h ω, 0 ≤ A2 h ω ∧ A2 h ω ≤ N) (hc : 0 ≤ c ∧ c ≤ N)
    (hmean : (∫ h, A1 h ∂ν.toMeasure) ≤ M)
    (hclose : ∀ h, A1 h ≤ cap → |(∫ ω, A2 h ω ∂(law h).toMeasure) - c| ≤ ε) :
    -2 * M * ε - 2 * N ^ 2 * ν.toMeasure.real {h | cap < A1 h} ≤
      covariance (fun z : H × Ω ↦ A1 z.1) (fun z ↦ A2 z.1 z.2)
        (historyFuture ν law).toMeasure := by
  rw [covariance_historyFuture]
  have hh := covariance_lower_of_close_on_good ν A1
    (fun h ↦ ∫ ω, A2 h ω ∂(law h).toMeasure) {h | A1 h ≤ cap}
    N M ε c hN hε hA1 (fun h ↦
      G2Deconditioning.integral_bounds_of_nonnegative_bounded (law h).toMeasure (A2 h)
        ((G2Deconditioning.memLp_finite (law h).toMeasure _).integrable one_le_two) (hA2 h))
    hc hmean hclose
  have heq : ({h | A1 h ≤ cap} : Set H)ᶜ = {h | cap < A1 h} := by
    ext h
    simp
  rw [heq] at hh
  exact hh

end Ashlagi.HazardMoments
