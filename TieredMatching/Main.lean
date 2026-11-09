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

public import TieredMatching.SourcePremise
public import TieredMatching.Transfer

/-! # Exact-PR assembly under an explicit coupling hypothesis

These are conditional bridge theorems. They do not assert the source proposition or construct
an exponential-arrival coupling. The original conjecture is never used as a premise.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

namespace TieredMatching

/-- A correctly distributed model transports the exact G.2 premise to its underlying space. -/
theorem PropositionG2.pullback {I J : ℕ} (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) (αmin : ℝ)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (i : Fin I) (hG2 : PropositionG2 b α β αmin womanTier manTier i)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (ν : (n : ℕ) → Measure (Ω n)) (p : (n : ℕ) → Ω n → StableMarriage.Profile n)
    (hp : ∀ n, Measurable (p n))
    (hlaw : ∀ n, Measure.map (p n) (ν n) =
      (Arxiv.«2009.05124».market (womanTier n) (manTier n) α β).toMeasure)
    (η : ℝ) (hη : 0 < η) (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ w : Fin n, womanTier n w = i → ∀ j : Fin J,
      ν n {ω | |(proposalCount (manTier n) j (p n ω) w : ℝ) -
          proposalCoefficient b α β αmin i j * Real.log n| >
        η * (proposalCoefficient b α β αmin i j * Real.log n)} ≤ δ := by
  filter_upwards [hG2.2 η hη δ hδ] with n hn
  intro w hw j
  have h := hn w hw j
  rw [← hlaw n, Measure.map_apply (hp n) (by trivial)] at h
  exact h

/-- The exact PR conclusion follows from a correctly distributed model, concentrated reference
variables, and a vanishing expected coupling error. All remaining construction obligations
are explicit hypotheses; this is not an unconditional proof of the conjecture. -/
theorem match_type_concentration_of_integral_coupling
    {I J : ℕ} (a : Fin I → ℝ) (b : Fin J → ℝ)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (i : Fin I) (j : Fin J)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (ν : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (ν n)]
    (p : (n : ℕ) → Ω n → StableMarriage.Profile n) (hp : ∀ n, Measurable (p n))
    (hlaw : ∀ n, Measure.map (p n) (ν n) =
      (Arxiv.«2009.05124».market (womanTier n) (manTier n) α β).toMeasure)
    (Y : (n : ℕ) → Ω n → ℝ) (hY : ∀ n, MemLp (Y n) 2 (ν n))
    (hmean : Tendsto (fun n ↦ ∫ ω, Y n ω ∂ν n) atTop (𝓝 (a i * b j)))
    (hvar : Tendsto (fun n ↦ variance (Y n) (ν n)) atTop (𝓝 0))
    (hint : ∀ n, Integrable (fun ω ↦
      (Arxiv.«2009.05124».matchCount (womanTier n) (manTier n) i j (p n ω) : ℝ) / n -
        Y n ω) (ν n))
    (herr : Tendsto (fun n ↦ ∫ ω,
      |(Arxiv.«2009.05124».matchCount (womanTier n) (manTier n) i j (p n ω) : ℝ) / n -
        Y n ω| ∂ν n) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (Arxiv.«2009.05124».market (womanTier n) (manTier n) α β).toMeasure
      {p | |(Arxiv.«2009.05124».matchCount (womanTier n) (manTier n) i j p : ℝ) / n -
        a i * b j| ≤ ε}) atTop (𝓝 1) := by
  let X (n : ℕ) (ω : Ω n) : ℝ :=
    (Arxiv.«2009.05124».matchCount (womanTier n) (manTier n) i j (p n ω) : ℝ) / n
  have hreference := convergesInProbability_of_mean_variance hY hmean hvar
  have hcon : ConvergesInProbability ν X (a i * b j) :=
    hreference.of_integral_abs_sub hint herr
  have hX : ∀ n, Measurable (X n) := by
    intro n
    have hf : Measurable (fun q : StableMarriage.Profile n ↦
      (Arxiv.«2009.05124».matchCount (womanTier n) (manTier n) i j q : ℝ) / n) :=
      measurable_from_top
    exact hf.comp (hp n)
  have hgood := hcon.good_event_tendsto_one hX hε
  apply hgood.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [← hlaw n, Measure.map_apply (hp n) (by trivial)]
  rfl

end TieredMatching
