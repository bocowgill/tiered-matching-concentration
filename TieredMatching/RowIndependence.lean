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

public import TieredMatching.ArrivalLaw
public import TieredMatching.Transfer
public import Mathlib.Probability.Independence.Basic

/-! # Independent deterministic reference categories from separate female source rows

Measurable functions of distinct independent source rows have independent category indicators.
The mean and variance of their normalized frequencies follow from the actual product law,
including after regrouping the flat female edge array used by the arrival construction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TieredMatching.RowIndependence

/-- Categories read only the specified original source row. -/
def rowCategory {Ω ι α κ : Type*} (R : Ω → ι → α) (f : ι → α → κ)
    (w : ι) (z : Ω) : κ := f w (R z w)

/-- Independence pulls back along a genuinely measure-preserving source map. -/
theorem indepFun_comp_of_measurePreserving {Ω Ω' α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} {ν : Measure Ω'} {T : Ω → Ω'} (hT : MeasurePreserving T μ ν)
    {f : Ω' → α} {g : Ω' → β} (hf : Measurable f) (hg : Measurable g)
    (hind : IndepFun f g ν) : IndepFun (f ∘ T) (g ∘ T) μ := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t hs ht
  change μ (T ⁻¹' (f ⁻¹' s ∩ g ⁻¹' t)) =
    μ (T ⁻¹' (f ⁻¹' s)) * μ (T ⁻¹' (g ⁻¹' t))
  rw [hT.measure_preimage ((hs.preimage hf).inter (ht.preimage hg)).nullMeasurableSet,
    hT.measure_preimage (hs.preimage hf).nullMeasurableSet,
    hT.measure_preimage (ht.preimage hg).nullMeasurableSet]
  exact hind.measure_inter_preimage_eq_mul s t hs ht

section Rows

variable {Ω ι α κ : Type*} [MeasurableSpace Ω] [Fintype ι] [MeasurableSpace α]
  [MeasurableSpace κ] (μ : Measure Ω) (μW : ι → Measure α)
  [∀ w, IsProbabilityMeasure (μW w)] (R : Ω → ι → α)
  (hR : MeasurePreserving R μ (Measure.pi μW))
  (f : ι → α → κ) (hf : ∀ w, Measurable (f w))

include hR hf

omit [∀ w, IsProbabilityMeasure (μW w)] in
/-- Row-based reference categories are measurable on the actual source space. -/
theorem measurable_rowCategory (w : ι) : Measurable (rowCategory R f w) :=
  (hf w).comp ((measurable_pi_apply w).comp hR.measurable)

omit [∀ w, IsProbabilityMeasure (μW w)] in
/-- Singleton category events are measurable without any measurable-equality assumption. -/
theorem measurableSet_rowCategory_eq [MeasurableSingletonClass κ] (w : ι) (j : κ) :
    MeasurableSet {z | rowCategory R f w z = j} :=
  (measurableSet_singleton j).preimage (measurable_rowCategory μ μW R hR f hf w)

/-- Each reference category has exactly its own source-row marginal law. -/
theorem rowCategory_measure (w : ι) (E : Set κ) (hE : MeasurableSet E) :
    μ {z | rowCategory R f w z ∈ E} = μW w {x | f w x ∈ E} := by
  have h := (measurePreserving_eval μW w).comp hR
  change μ ((fun z ↦ R z w) ⁻¹' (f w ⁻¹' E)) = μW w (f w ⁻¹' E)
  exact h.measure_preimage (hE.preimage (hf w)).nullMeasurableSet

/-- Independence is derived from distinct coordinate rows, without an independence premise. -/
theorem indepFun_rowCategory (w v : ι) (hwv : w ≠ v) :
    IndepFun (rowCategory R f w) (rowCategory R f v) μ := by
  have hi := (iIndepFun_pi (μ := μW) (X := f) (fun w ↦ (hf w).aemeasurable)).indepFun hwv
  exact indepFun_comp_of_measurePreserving hR
    ((hf w).comp (measurable_pi_apply w)) ((hf v).comp (measurable_pi_apply v)) hi

/-- Category indicator independence is inherited by measurable functions of separate rows. -/
theorem indepFun_row_indicator [MeasurableSingletonClass κ] [DecidableEq κ]
    (w v : ι) (hwv : w ≠ v) (j : κ) :
    IndepFun (fun z ↦ if rowCategory R f w z = j then (1 : ℝ) else 0)
      (fun z ↦ if rowCategory R f v z = j then (1 : ℝ) else 0) μ := by
  have hm : Measurable (fun k : κ ↦ if k = j then (1 : ℝ) else 0) :=
    measurable_const.ite (measurableSet_singleton j) measurable_const
  exact (indepFun_rowCategory μ μW R hR f hf w v hwv).comp hm hm

/-- The exact real probability of one row category is unchanged by the outer source context. -/
theorem rowCategory_probability [MeasurableSingletonClass κ] (w : ι) (j : κ) :
    μ.real {z | rowCategory R f w z = j} = (μW w).real {x | f w x = j} := by
  exact congrArg ENNReal.toReal (rowCategory_measure μ μW R hR f hf w {j}
    (measurableSet_singleton j))

variable [IsProbabilityMeasure μ] [MeasurableSingletonClass κ] [DecidableEq κ]

omit [∀ w, IsProbabilityMeasure (μW w)] in
/-- The source-derived reference frequency is square integrable at every real normalization. -/
theorem memLp_frequency (s : Finset ι) (j : κ) (N : ℝ) :
    MemLp (categoryFrequency s (rowCategory R f) j N) 2 μ :=
  memLp_categoryFrequency μ s _ j N (fun w _ ↦
    measurableSet_rowCategory_eq μ μW R hR f hf w j)

/-- Exact reference mean, allowing distinct category probabilities on different rows. -/
theorem integral_frequency (s : Finset ι) (j : κ) (N : ℝ) :
    (∫ z, categoryFrequency s (rowCategory R f) j N z ∂μ) =
      (∑ w ∈ s, (μW w).real {x | f w x = j}) / N := by
  rw [integral_categoryFrequency μ s _ j N (fun w _ ↦
    measurableSet_rowCategory_eq μ μW R hR f hf w j)]
  congr 1
  exact Finset.sum_congr rfl (fun w _ ↦ rowCategory_probability μ μW R hR f hf w j)

/-- The exact cardinality form of the independent-reference variance bound. -/
theorem variance_frequency_le_card (s : Finset ι) (j : κ) (N : ℝ) :
    variance (categoryFrequency s (rowCategory R f) j N) μ ≤ (s.card : ℝ) / (4 * N^2) := by
  apply variance_normalized_sum_le μ s
    (fun w z ↦ if rowCategory R f w z = j then (1 : ℝ) else 0)
    (fun w _ ↦ memLp_category_indicator μ _ j
      (measurableSet_rowCategory_eq μ μW R hR f hf w j) 2)
  · intro w hw z
    split_ifs <;> norm_num
  · intro w hw v hv hwv
    exact indepFun_row_indicator μ μW R hR f hf w v hwv j

/-- Reference variance is at most one over four times any positive dominating population size. -/
theorem variance_frequency_le (s : Finset ι) (j : κ) {N : ℝ}
    (hN : 0 < N) (hcard : (s.card : ℝ) ≤ N) :
    variance (categoryFrequency s (rowCategory R f) j N) μ ≤ 1 / (4 * N) := by
  apply variance_categoryFrequency_le μ s _ j
    (fun w _ ↦ measurableSet_rowCategory_eq μ μW R hR f hf w j)
    _ hN hcard
  intro w hw v hv hwv
  exact indepFun_row_indicator μ μW R hR f hf w v hwv j

end Rows

/-- The outer male context leaves the original female rows unchanged. -/
def contextCategory {M ι α κ : Type*} (f : ι → α → κ) :
    ι → M × (ι → α) → κ := rowCategory Prod.snd f

/-- Context-independent row categories are measurable pointwise in the original source variables. -/
theorem measurable_contextCategory {M ι α κ : Type*}
    [MeasurableSpace M] [MeasurableSpace α] [MeasurableSpace κ]
    (f : ι → α → κ) (hf : ∀ w, Measurable (f w)) (w : ι) :
    Measurable (contextCategory f w : M × (ι → α) → κ) :=
  (hf w).comp ((measurable_pi_apply w).comp measurable_snd)

section Context

variable {M ι α κ : Type*} [MeasurableSpace M] [Fintype ι] [MeasurableSpace α]
  [MeasurableSpace κ] (μM : Measure M) [IsProbabilityMeasure μM]
  (μW : ι → Measure α) [∀ w, IsProbabilityMeasure (μW w)]
  (f : ι → α → κ) (hf : ∀ w, Measurable (f w))

include hf

/-- The original product law gives each context-independent category its exact row marginal. -/
theorem contextCategory_measure (w : ι) (E : Set κ) (hE : MeasurableSet E) :
    (μM.prod (Measure.pi μW)) {z | contextCategory f w z ∈ E} =
      μW w {x | f w x ∈ E} :=
  rowCategory_measure _ μW Prod.snd measurePreserving_snd f hf w E hE

/-- Pairwise category independence follows from the original source rows. -/
theorem indepFun_contextCategory (w v : ι) (hwv : w ≠ v) :
    IndepFun (contextCategory f w) (contextCategory f v) (μM.prod (Measure.pi μW)) :=
  indepFun_rowCategory _ μW Prod.snd measurePreserving_snd f hf w v hwv

/-- The product source itself supplies the pairwise independent reference indicators. -/
theorem indepFun_context_indicator [MeasurableSingletonClass κ] [DecidableEq κ]
    (w v : ι) (hwv : w ≠ v) (j : κ) :
    IndepFun (fun z ↦ if contextCategory f w z = j then (1 : ℝ) else 0)
      (fun z ↦ if contextCategory f v z = j then (1 : ℝ) else 0)
      (μM.prod (Measure.pi μW)) :=
  indepFun_row_indicator _ μW Prod.snd measurePreserving_snd f hf w v hwv j

/-- Full finite-reference moment package under the original male-context/female-row product law. -/
theorem context_frequency_moments [MeasurableSingletonClass κ] [DecidableEq κ]
    (s : Finset ι) (j : κ) (N : ℝ) :
    MemLp (categoryFrequency s (contextCategory f) j N) 2 (μM.prod (Measure.pi μW)) ∧
    (∫ z, categoryFrequency s (contextCategory f) j N z ∂μM.prod (Measure.pi μW)) =
      (∑ w ∈ s, (μW w).real {x | f w x = j}) / N ∧
    variance (categoryFrequency s (contextCategory f) j N) (μM.prod (Measure.pi μW)) ≤
      (s.card : ℝ) / (4 * N^2) :=
  ⟨memLp_frequency _ μW Prod.snd measurePreserving_snd f hf s j N,
    integral_frequency _ μW Prod.snd measurePreserving_snd f hf s j N,
    variance_frequency_le_card _ μW Prod.snd measurePreserving_snd f hf s j N⟩

/-- The standard inverse-population reference variance bound in the original row product source. -/
theorem context_frequency_variance_le [MeasurableSingletonClass κ] [DecidableEq κ]
    (s : Finset ι) (j : κ) {N : ℝ} (hN : 0 < N) (hcard : (s.card : ℝ) ≤ N) :
    variance (categoryFrequency s (contextCategory f) j N) (μM.prod (Measure.pi μW)) ≤
      1 / (4 * N) :=
  variance_frequency_le _ μW Prod.snd measurePreserving_snd f hf s j hN hcard

end Context

/-- Regroup the original flat female edge coordinates by woman, retaining no male context. -/
def flatRows {M ι τ α : Type*} (z : M × (ι × τ → α)) : ι → τ → α :=
  Function.curry z.2

/-- A deterministic reference category evaluated on a woman's original flat source row. -/
def flatCategory {M ι τ α κ : Type*} (f : ι → (τ → α) → κ) :
    ι → M × (ι × τ → α) → κ := rowCategory flatRows f

/-- Reference row labels are measurable already in the original flat source coordinates. -/
theorem measurable_flatCategory {M ι τ α κ : Type*}
    [MeasurableSpace M] [MeasurableSpace α] [MeasurableSpace κ]
    (f : ι → (τ → α) → κ) (hf : ∀ w, Measurable (f w)) (w : ι) :
    Measurable (flatCategory f w : M × (ι × τ → α) → κ) :=
  (hf w).comp (Measurable.of_eval (fun m ↦
    (measurable_pi_apply (w, m)).comp measurable_snd))

section Flat

variable {M ι τ α κ : Type*} [MeasurableSpace M] [Fintype ι] [Fintype τ]
  [MeasurableSpace α] [MeasurableSpace κ] (μM : Measure M) [IsProbabilityMeasure μM]
  (μE : ι → τ → Measure α) [∀ w m, IsProbabilityMeasure (μE w m)]

/-- The actual flat female source law is exactly the product of its regrouped female rows. -/
theorem measurePreserving_flatRows :
    MeasurePreserving (flatRows : M × (ι × τ → α) → ι → τ → α)
      (μM.prod (Measure.pi fun q : ι × τ ↦ μE q.1 q.2))
      (Measure.pi fun w ↦ Measure.pi fun m ↦ μE w m) :=
  (measurePreserving_curry_pi μE).comp measurePreserving_snd

variable (f : ι → (τ → α) → κ) (hf : ∀ w, Measurable (f w))

include hf

/-- Exact marginal for a deterministic female-row category under the original flat edge law. -/
theorem flatCategory_measure (w : ι) (E : Set κ) (hE : MeasurableSet E) :
    (μM.prod (Measure.pi fun q : ι × τ ↦ μE q.1 q.2))
      {z | flatCategory f w z ∈ E} =
      (Measure.pi fun m ↦ μE w m) {x | f w x ∈ E} :=
  rowCategory_measure _ _ flatRows (measurePreserving_flatRows μM μE) f hf w E hE

/-- Regrouping proves category independence directly under the actual flat edge source. -/
theorem indepFun_flatCategory (w v : ι) (hwv : w ≠ v) :
    IndepFun (flatCategory f w) (flatCategory f v)
      (μM.prod (Measure.pi fun q : ι × τ ↦ μE q.1 q.2)) :=
  indepFun_rowCategory _ _ flatRows (measurePreserving_flatRows μM μE) f hf w v hwv

/-- Category indicators of distinct women are independent under the original flat source. -/
theorem indepFun_flat_indicator [MeasurableSingletonClass κ] [DecidableEq κ]
    (w v : ι) (hwv : w ≠ v) (j : κ) :
    IndepFun (fun z ↦ if flatCategory f w z = j then (1 : ℝ) else 0)
      (fun z ↦ if flatCategory f v z = j then (1 : ℝ) else 0)
      (μM.prod (Measure.pi fun q : ι × τ ↦ μE q.1 q.2)) :=
  indepFun_row_indicator _ _ flatRows (measurePreserving_flatRows μM μE) f hf w v hwv j

/-- Exact reference moments from the original flat female edge source, with arbitrary context. -/
theorem flat_frequency_moments [MeasurableSingletonClass κ] [DecidableEq κ]
    (s : Finset ι) (j : κ) (N : ℝ) :
    MemLp (categoryFrequency s (flatCategory f) j N) 2
      (μM.prod (Measure.pi fun q : ι × τ ↦ μE q.1 q.2)) ∧
    (∫ z, categoryFrequency s (flatCategory f) j N z
      ∂μM.prod (Measure.pi fun q : ι × τ ↦ μE q.1 q.2)) =
      (∑ w ∈ s, (Measure.pi fun m ↦ μE w m).real {x | f w x = j}) / N ∧
    variance (categoryFrequency s (flatCategory f) j N)
      (μM.prod (Measure.pi fun q : ι × τ ↦ μE q.1 q.2)) ≤ (s.card : ℝ) / (4 * N^2) :=
  ⟨memLp_frequency _ _ flatRows (measurePreserving_flatRows μM μE) f hf s j N,
    integral_frequency _ _ flatRows (measurePreserving_flatRows μM μE) f hf s j N,
    variance_frequency_le_card _ _ flatRows (measurePreserving_flatRows μM μE) f hf s j N⟩

/-- The standard inverse-population bound remains valid in the original flat edge coordinates. -/
theorem flat_frequency_variance_le [MeasurableSingletonClass κ] [DecidableEq κ]
    (s : Finset ι) (j : κ) {N : ℝ} (hN : 0 < N) (hcard : (s.card : ℝ) ≤ N) :
    variance (categoryFrequency s (flatCategory f) j N)
      (μM.prod (Measure.pi fun q : ι × τ ↦ μE q.1 q.2)) ≤ 1 / (4 * N) :=
  variance_frequency_le _ _ flatRows (measurePreserving_flatRows μM μE) f hf s j hN hcard

end Flat

/-- Cardinality domination is automatic for a subset of the market's women. -/
theorem card_finset_fin_le_market {n : ℕ} (s : Finset (Fin n)) : (s.card : ℝ) ≤ n := by
  exact_mod_cast (s.card_le_univ.trans_eq (Fintype.card_fin n))

/-- Market-normalized reference variance in nested row coordinates. -/
theorem context_frequency_variance_le_market {M κ : Type*} {n : ℕ}
    [MeasurableSpace M] [MeasurableSpace κ] [MeasurableSingletonClass κ] [DecidableEq κ]
    (μM : Measure M) [IsProbabilityMeasure μM] (μW : Fin n → Measure (Fin n → ℝ))
    [∀ w, IsProbabilityMeasure (μW w)] (f : Fin n → (Fin n → ℝ) → κ)
    (hf : ∀ w, Measurable (f w)) (s : Finset (Fin n)) (j : κ) (hn : 0 < n) :
    variance (categoryFrequency s (contextCategory f) j n) (μM.prod (Measure.pi μW)) ≤
      1 / (4 * n) :=
  context_frequency_variance_le μM μW f hf s j (by exact_mod_cast hn)
    (card_finset_fin_le_market s)

/-- Market-normalized reference variance in the original flat female-edge coordinates. -/
theorem flat_frequency_variance_le_market {M κ : Type*} {n : ℕ}
    [MeasurableSpace M] [MeasurableSpace κ] [MeasurableSingletonClass κ] [DecidableEq κ]
    (μM : Measure M) [IsProbabilityMeasure μM] (μE : Fin n → Fin n → Measure ℝ)
    [∀ w m, IsProbabilityMeasure (μE w m)] (f : Fin n → (Fin n → ℝ) → κ)
    (hf : ∀ w, Measurable (f w)) (s : Finset (Fin n)) (j : κ) (hn : 0 < n) :
    variance (categoryFrequency s (flatCategory f) j n)
      (μM.prod (Measure.pi fun q : Fin n × Fin n ↦ μE q.1 q.2)) ≤ 1 / (4 * n) :=
  flat_frequency_variance_le μM μE f hf s j (by exact_mod_cast hn)
    (card_finset_fin_le_market s)

/-- Deterministic-reference moments for a flat exponential source with male rates. -/
theorem exponential_flat_frequency_moments {M κ : Type*} {n : ℕ}
    [MeasurableSpace M] [MeasurableSpace κ] [MeasurableSingletonClass κ] [DecidableEq κ]
    (μM : Measure M) [IsProbabilityMeasure μM] (β : Fin n → ℝ≥0)
    (hβ : ∀ m, 0 < β m) (f : Fin n → (Fin n → ℝ) → κ)
    (hf : ∀ w, Measurable (f w)) (s : Finset (Fin n)) (j : κ) (hn : 0 < n) :
    MemLp (categoryFrequency s (flatCategory f) j n) 2
      (μM.prod (Measure.pi fun q : Fin n × Fin n ↦ expMeasure (β q.2 : ℝ))) ∧
    (∫ z, categoryFrequency s (flatCategory f) j n z
      ∂μM.prod (Measure.pi fun q : Fin n × Fin n ↦ expMeasure (β q.2 : ℝ))) =
      (∑ w ∈ s, (Measure.pi fun m ↦ expMeasure (β m : ℝ)).real {x | f w x = j}) / n ∧
    variance (categoryFrequency s (flatCategory f) j n)
      (μM.prod (Measure.pi fun q : Fin n × Fin n ↦ expMeasure (β q.2 : ℝ))) ≤
      (s.card : ℝ) / (4 * (n : ℝ)^2) ∧
    variance (categoryFrequency s (flatCategory f) j n)
      (μM.prod (Measure.pi fun q : Fin n × Fin n ↦ expMeasure (β q.2 : ℝ))) ≤
      1 / (4 * n) := by
  have (m : Fin n) : IsProbabilityMeasure (expMeasure (β m : ℝ)) :=
    isProbabilityMeasure_expMeasure (by exact_mod_cast hβ m)
  obtain ⟨hlp, hmean, hvar⟩ :=
    flat_frequency_moments μM (fun _ m ↦ expMeasure (β m : ℝ)) f hf s j n
  exact ⟨hlp, hmean, hvar, flat_frequency_variance_le_market μM
    (fun _ m ↦ expMeasure (β m : ℝ)) f hf s j hn⟩

section Arrival

variable {n : ℕ} {κ : Type*} [MeasurableSpace κ] (P Q : Fin n → Fin n → ℝ≥0)
  (hP : ∀ m w, 0 < P m w) (hQ : ∀ m w, 0 < Q m w)
  (f : Fin n → (Fin n → ℝ) → κ) (hf : ∀ w, Measurable (f w))

include hP hQ hf

/-- The exact original arrival source gives each deterministic reference its own row law. -/
theorem arrivalCategory_measure (w : Fin n) (E : Set κ) (hE : MeasurableSet E) :
    arrivalInputLaw P Q {z | flatCategory f w z ∈ E} =
      (Measure.pi fun m ↦ expMeasure (Q m w : ℝ)) {x | f w x ∈ E} := by
  have (m w : Fin n) : IsProbabilityMeasure (expMeasure (P m w : ℝ)) :=
    isProbabilityMeasure_expMeasure (by exact_mod_cast hP m w)
  have (m w : Fin n) : IsProbabilityMeasure (expMeasure (Q m w : ℝ)) :=
    isProbabilityMeasure_expMeasure (by exact_mod_cast hQ m w)
  exact flatCategory_measure _ (fun w m ↦ expMeasure (Q m w : ℝ)) f hf w E hE

/-- The independent female source rows prove reference indicator independence in the exact law. -/
theorem indepFun_arrival_indicator [MeasurableSingletonClass κ] [DecidableEq κ]
    (w v : Fin n) (hwv : w ≠ v) (j : κ) :
    IndepFun (fun z ↦ if flatCategory f w z = j then (1 : ℝ) else 0)
      (fun z ↦ if flatCategory f v z = j then (1 : ℝ) else 0) (arrivalInputLaw P Q) := by
  have (m w : Fin n) : IsProbabilityMeasure (expMeasure (P m w : ℝ)) :=
    isProbabilityMeasure_expMeasure (by exact_mod_cast hP m w)
  have (m w : Fin n) : IsProbabilityMeasure (expMeasure (Q m w : ℝ)) :=
    isProbabilityMeasure_expMeasure (by exact_mod_cast hQ m w)
  exact indepFun_flat_indicator _ (fun w m ↦ expMeasure (Q m w : ℝ)) f hf w v hwv j

/-- Mean, square integrability, and cardinality variance in the exact PR-compatible arrival law. -/
theorem arrival_frequency_moments [MeasurableSingletonClass κ] [DecidableEq κ]
    (s : Finset (Fin n)) (j : κ) :
    MemLp (categoryFrequency s (flatCategory f) j n) 2 (arrivalInputLaw P Q) ∧
    (∫ z, categoryFrequency s (flatCategory f) j n z ∂arrivalInputLaw P Q) =
      (∑ w ∈ s, (Measure.pi fun m ↦ expMeasure (Q m w : ℝ)).real {x | f w x = j}) / n ∧
    variance (categoryFrequency s (flatCategory f) j n) (arrivalInputLaw P Q) ≤
      (s.card : ℝ) / (4 * (n : ℝ)^2) := by
  have (m w : Fin n) : IsProbabilityMeasure (expMeasure (P m w : ℝ)) :=
    isProbabilityMeasure_expMeasure (by exact_mod_cast hP m w)
  have (m w : Fin n) : IsProbabilityMeasure (expMeasure (Q m w : ℝ)) :=
    isProbabilityMeasure_expMeasure (by exact_mod_cast hQ m w)
  exact flat_frequency_moments _ (fun w m ↦ expMeasure (Q m w : ℝ)) f hf s j n

/-- The `1/(4n)` reference variance bound under the original flat exponential arrival source. -/
theorem arrival_frequency_variance_le [MeasurableSingletonClass κ] [DecidableEq κ]
    (s : Finset (Fin n)) (j : κ) (hn : 0 < n) :
    variance (categoryFrequency s (flatCategory f) j n) (arrivalInputLaw P Q) ≤
      1 / (4 * n) := by
  have (m w : Fin n) : IsProbabilityMeasure (expMeasure (P m w : ℝ)) :=
    isProbabilityMeasure_expMeasure (by exact_mod_cast hP m w)
  have (m w : Fin n) : IsProbabilityMeasure (expMeasure (Q m w : ℝ)) :=
    isProbabilityMeasure_expMeasure (by exact_mod_cast hQ m w)
  exact flat_frequency_variance_le_market _ (fun w m ↦ expMeasure (Q m w : ℝ)) f hf s j hn

end Arrival

end TieredMatching.RowIndependence
