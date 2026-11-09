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
public import Ashlagi.InitialRates

/-! # Actual normalized acceptance drift in the two initial phases

The without-replacement next-acceptance probability under the exact PR profile law equals
the masked rate divided by remaining normalized mass. Its difference from the fixed setup
rate is controlled by the visited destinations' count, without stochastic drift assumptions.
-/

@[expose] public section

namespace Ashlagi.InitialDrift

open StableMarriage MeasureTheory Ashlagi.Ordinal Protocols FiniteConditioning
open scoped ENNReal NNReal

/-- Original normalized destination weights before any preference prefix is exposed. -/
noncomputable def normalized {n : ℕ} (a : Fin n → ℝ≥0) (w : Fin n) : ℝ :=
  (a w : ℝ) / ∑ v, (a v : ℝ)

/-- Total public destination weight is positive in a nonempty normalized market. -/
theorem total_pos {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ≥0)
    (ha1 : ∀ w, 1 ≤ (a w : ℝ)) : 0 < ∑ w, (a w : ℝ) := by
  have hs : (n : ℝ) ≤ ∑ w, (a w : ℝ) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin]
      using Finset.sum_le_sum (s := Finset.univ) (fun w _ ↦ ha1 w)
  exact lt_of_lt_of_le (by exact_mod_cast hn) hs

/-- Normalized masses are nonnegative. -/
theorem normalized_nonneg {n : ℕ} (a : Fin n → ℝ≥0) (w : Fin n) :
    0 ≤ normalized a w := div_nonneg (a w).coe_nonneg (Finset.sum_nonneg fun v _ ↦ (a v).coe_nonneg)

/-- Normalized masses sum to exactly one. -/
theorem normalized_sum {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ≥0)
    (ha1 : ∀ w, 1 ≤ (a w : ℝ)) : ∑ w, normalized a w = 1 := by
  simp only [normalized, div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_inv_cancel₀ (total_pos hn a ha1).ne'

/-- Each normalized mass is at most A/n under the source score bounds. -/
theorem normalized_upper {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ≥0) {A : ℝ}
    (hA : 0 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (w : Fin n) : normalized a w ≤ A / n := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : (n : ℝ) ≤ ∑ v, (a v : ℝ) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin]
      using Finset.sum_le_sum (s := Finset.univ) (fun v _ ↦ ha1 v)
  exact (div_le_div_of_nonneg_right (haA w) (total_pos hn a ha1).le).trans
    (div_le_div_of_nonneg_left hA hN hsum)

/-- The remaining raw-weight sum has exactly the remaining normalized mass. -/
theorem remaining_mass {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ≥0)
    (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (used : Finset (Fin n)) :
    1 - ∑ w ∈ used, normalized a w =
      (∑ w ∈ Finset.univ.filter (fun w ↦ w ∉ used), (a w : ℝ)) / ∑ w, (a w : ℝ) := by
  classical
  have hpart := Finset.sum_sdiff (f := fun w ↦ (a w : ℝ)) (Finset.subset_univ used)
  have hf : Finset.univ \ used = Finset.univ.filter (fun w ↦ w ∉ used) := by ext w; simp
  rw [hf] at hpart
  simp only [normalized, div_eq_mul_inv, ← Finset.sum_mul]
  have hW := (total_pos hn a ha1).ne'
  field_simp
  nlinarith

/-- Normalizing full public masses and then masking a preference prefix gives exactly the
actual fresh-destination normalization, not an approximation. -/
theorem normalized_rate_eq {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ≥0)
    (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (used : Finset (Fin n)) (Γ : Fin n → ℝ) (β : ℝ) :
    SmoothRates.rateOn (Finset.univ.filter fun w ↦ w ∉ used)
      (fun w ↦ (a w : ℝ) / ∑ v ∈ Finset.univ.filter (fun v ↦ v ∉ used), (a v : ℝ)) Γ β =
      SmoothRates.rateOn (Finset.univ.filter fun w ↦ w ∉ used) (normalized a) Γ β /
        (1 - ∑ w ∈ used, normalized a w) := by
  classical
  have hd := remaining_mass hn a ha1 used
  have hweight (w : Fin n) :
      (a w : ℝ) / (∑ v ∈ Finset.univ.filter (fun v ↦ v ∉ used), (a v : ℝ)) =
        normalized a w / (1 - ∑ v ∈ used, normalized a v) := by
    rw [hd, normalized, div_div_div_cancel_right₀ (total_pos hn a ha1).ne']
  simp only [SmoothRates.rateOn, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w hw
  have hh := hweight w
  simp only [div_eq_mul_inv] at hh
  rw [hh]
  ring

/-- The exact actual conditional acceptance probability equals the masked normalized rate. -/
theorem actual_acceptance_eq_normalized {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0)
    (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (hb : ∀ m, 0 < b m) (C : Protocol n)
    (h : List (Entry n)) (hh : eventMass (Continuation.market a b)
      (Continuation.historyEvent C h) ≠ 0) (m : Fin n) (hs : selected C h = some m) :
    (eventMass (Continuation.lawAt a b C h) (Continuation.acceptanceEvent C h m)).toReal =
      SmoothRates.rateOn (Finset.univ.filter fun w ↦ w ∉ (manOrder h m).toFinset)
        (normalized a) (Continuation.gamma b h) (b m : ℝ) /
          (1 - ∑ w ∈ (manOrder h m).toFinset, normalized a w) := by
  classical
  have ha : ∀ w, 0 < a w := fun w ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (ha1 w)
  rw [Continuation.acceptance_probability a b ha hb C h hh m hs]
  have hrate : 0 ≤ SmoothRates.rateOn (Continuation.untried h m)
      (Continuation.destinationWeight a h m) (Continuation.gamma b h) (b m : ℝ) := by
    apply Finset.sum_nonneg
    intro w hw
    exact mul_nonneg (by unfold Continuation.destinationWeight; positivity)
      (div_nonneg (b m).coe_nonneg (add_nonneg (b m).coe_nonneg (Continuation.gamma_nonneg b h w)))
  rw [ENNReal.toReal_ofReal hrate]
  have hf : Finset.univ.filter (fun w ↦ w ∉ (manOrder h m).toFinset) =
      Continuation.untried h m := by ext w; simp [Continuation.untried]
  change SmoothRates.rateOn (Continuation.untried h m)
    (fun w ↦ (a w : ℝ) / ∑ v ∈ Continuation.untried h m, (a v : ℝ))
    (Continuation.gamma b h) (b m : ℝ) = _
  simpa only [hf] using
    normalized_rate_eq hn a ha1 (manOrder h m).toFinset (Continuation.gamma b h) (b m : ℝ)

/-- The deterministic normalized fresh rate changes by at most `8*A*cap/n` when at most
`2*cap` destinations can have changed and their total mass is at most one half. -/
theorem rate_drift_le {n : ℕ} (hn : 0 < n) (π Γ₀ Γ : Fin n → ℝ)
    (used visited : Finset (Fin n)) {A β : ℝ} (hA : 0 ≤ A) (cap : ℕ)
    (hπ : ∀ w, 0 ≤ π w) (hsum : ∑ w, π w = 1) (hupper : ∀ w, π w ≤ A / n)
    (hΓ₀ : ∀ w, 0 ≤ Γ₀ w) (hΓ : ∀ w, 0 ≤ Γ w) (hβ : 0 < β)
    (huv : used ⊆ visited) (heq : ∀ w, w ∉ visited → Γ w = Γ₀ w)
    (hcard : visited.card ≤ 2 * cap) (hsmall : 2 * A * cap / n ≤ 1 / 2) :
    |SmoothRates.rateOn (Finset.univ.filter fun w ↦ w ∉ used) π Γ β /
        (1 - ∑ w ∈ used, π w) - SmoothRates.rate π Γ₀ β| ≤ 8 * A * cap / n := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hmass : (∑ w ∈ visited, π w) ≤ 2 * A * cap / n := by
    apply (InitialRates.visited_mass_le_card π visited (A / n) (fun w _ ↦ hupper w)).trans
    have hc : (visited.card : ℝ) ≤ 2 * cap := by exact_mod_cast hcard
    have hb := mul_le_mul_of_nonneg_right hc (div_nonneg hA hN.le)
    convert hb using 1
    ring
  have hu : (∑ w ∈ used, π w) ≤ 1 / 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg huv (fun w _ _ ↦ hπ w)).trans (hmass.trans hsmall)
  apply (InitialRates.acceptance_rate_drift π Γ₀ Γ used visited β hπ hsum hΓ₀ hΓ hβ
    huv heq hu).trans
  have hb := mul_le_mul_of_nonneg_left hmass (by norm_num : (0 : ℝ) ≤ 4)
  convert hb using 1
  ring

/-- Actual initial-phase acceptance drift under the original past-conditioned PR law.
Only deterministic visited-set and past-score agreements are hypotheses. -/
theorem actual_acceptance_drift {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 0 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (C : Protocol n) (h : List (Entry n))
    (hh : eventMass (Continuation.market a b) (Continuation.historyEvent C h) ≠ 0)
    (m : Fin n) (hs : selected C h = some m) (Γ₀ : Fin n → ℝ)
    (hΓ₀ : ∀ w, 0 ≤ Γ₀ w) (visited : Finset (Fin n)) (cap : ℕ)
    (huv : (manOrder h m).toFinset ⊆ visited)
    (heq : ∀ w, w ∉ visited → Continuation.gamma b h w = Γ₀ w)
    (hcard : visited.card ≤ 2 * cap) (hsmall : 2 * A * cap / n ≤ 1 / 2) :
    |(eventMass (Continuation.lawAt a b C h) (Continuation.acceptanceEvent C h m)).toReal -
        SmoothRates.rate (normalized a) Γ₀ (b m : ℝ)| ≤ 8 * A * cap / n := by
  rw [actual_acceptance_eq_normalized hn a b ha1 hb C h hh m hs]
  exact rate_drift_le hn (normalized a) Γ₀ (Continuation.gamma b h) _ visited hA cap
    (normalized_nonneg a) (normalized_sum hn a ha1) (normalized_upper hn a hA ha1 haA)
    hΓ₀ (Continuation.gamma_nonneg b h) (by exact_mod_cast hb m) huv heq hcard hsmall

/-- The actual next accepted observation of the designated man, with every fresh destination
hidden until it is revealed. -/
def observedAcceptance {n : ℕ} (C : Protocol n) (h : List (Entry n)) (m : Fin n) :
    Set (Profile n) := {p | ∃ w, Protocols.observation C p.manRank (profilePriorities p) h =
      some ((w, m), true)}

/-- Event masses agree whenever the two predicates agree on all positive-probability points. -/
theorem eventMass_congr_support {Ω : Type*} (μ : PMF Ω) (S T : Set Ω)
    (hST : ∀ ω, μ ω ≠ 0 → (ω ∈ S ↔ ω ∈ T)) : eventMass μ S = eventMass μ T := by
  classical
  unfold eventMass
  apply tsum_congr
  intro ω
  by_cases hzero : μ ω = 0
  · simp [Set.indicator_apply, hzero]
  · have he := hST ω hzero
    by_cases hs : ω ∈ S
    · simp only [Set.indicator_apply, hs, he.mp hs, ↓reduceIte]
    · have ht : ω ∉ T := fun ht ↦ hs (he.mpr ht)
      simp only [Set.indicator_apply, hs, ht, ↓reduceIte]

/-- On an actually possible fixed prefix, the accepted observation event is exactly the
fresh accepted-edge event on the support of its conditional original profile law. -/
theorem observedAcceptance_probability_eq {n : ℕ} (a b : Fin n → ℝ≥0) (C : Protocol n)
    (h : List (Entry n))
    (hh : eventMass (Continuation.market a b) (Continuation.historyEvent C h) ≠ 0)
    (m : Fin n) :
    eventMass (Continuation.lawAt a b C h) (observedAcceptance C h m) =
      eventMass (Continuation.lawAt a b C h) (Continuation.acceptanceEvent C h m) := by
  classical
  apply eventMass_congr_support
  intro p hp
  have hsupport : p ∈
      (condition (Continuation.market a b) (Continuation.historyEvent C h)).support := hp
  rw [support_condition _ _ hh] at hsupport
  have hvalid : ValidProtocol C p.manRank h :=
    ((transcript_eq_iff C p.manRank (profilePriorities p) h.length h).mp hsupport.1).2.1
  constructor
  · rintro ⟨w, hobs⟩
    obtain ⟨hnext, haccept⟩ := (observation_eq_some_iff C _ _ h (w, m) true).mp hobs
    have hfresh := nextEdge_fresh_of_valid C p.manRank h hvalid (w, m) hnext
    have hw : w ∈ Continuation.untried h m := by
      simp only [Continuation.untried, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun hw ↦ hfresh ((mem_manOrder_iff_seenEdges h w m).mp hw)
    apply Set.mem_iUnion.mpr ⟨w, ?_⟩
    exact Set.mem_iUnion.mpr ⟨hw, And.intro hnext haccept⟩
  · intro haccept
    have he : ∃ w, w ∈ Continuation.untried h m ∧ p ∈ Continuation.acceptedEdgeEvent C h w m := by
      simpa only [Continuation.acceptanceEvent, Set.mem_iUnion, exists_prop] using haccept
    obtain ⟨w, _, hnext, ha⟩ := he
    exact ⟨w, (observation_eq_some_iff C _ _ h (w, m) true).mpr ⟨hnext, ha⟩⟩

/-- The initial-phase actual accepted-observation hazard has the stated deterministic drift
bound, ready for the finite survival/count kernel. -/
theorem observed_acceptance_drift {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 0 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (C : Protocol n) (h : List (Entry n))
    (hh : eventMass (Continuation.market a b) (Continuation.historyEvent C h) ≠ 0)
    (m : Fin n) (hs : selected C h = some m) (Γ₀ : Fin n → ℝ)
    (hΓ₀ : ∀ w, 0 ≤ Γ₀ w) (visited : Finset (Fin n)) (cap : ℕ)
    (huv : (manOrder h m).toFinset ⊆ visited)
    (heq : ∀ w, w ∉ visited → Continuation.gamma b h w = Γ₀ w)
    (hcard : visited.card ≤ 2 * cap) (hsmall : 2 * A * cap / n ≤ 1 / 2) :
    |(eventMass (Continuation.lawAt a b C h) (observedAcceptance C h m)).toReal -
        SmoothRates.rate (normalized a) Γ₀ (b m : ℝ)| ≤ 8 * A * cap / n := by
  rw [observedAcceptance_probability_eq a b C h hh m]
  exact actual_acceptance_drift hn a b hA ha1 haA hb C h hh m hs Γ₀ hΓ₀ visited cap
    huv heq hcard hsmall

end Ashlagi.InitialDrift
