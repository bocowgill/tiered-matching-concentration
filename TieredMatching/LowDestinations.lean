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

public import TieredMatching.RankTail

/-! # Actual bounded-prefix low-destination probabilities

The current selected man's exposed counter is the only prefix guard. Exact original-profile
next-destination laws and the visible-history tower give a finite future union bound.
-/

@[expose] public section

namespace TieredMatching.LowDestinations

open StableMarriage TieredMatching.Ordinal Protocols ProfileHistories FiniteConditioning
open scoped ENNReal NNReal

/-- Total public destination weight. -/
noncomputable def totalWeight {n : ℕ} (a : Fin n → ℝ≥0) : ℝ := ∑ w, (a w : ℝ)

/-- Public low-set categorical mass, before any preference suffix is exposed. -/
noncomputable def lowMass {n : ℕ} (a : Fin n → ℝ≥0) (low : Finset (Fin n)) : ℝ :=
  (∑ w ∈ low, (a w : ℝ)) / totalWeight a

/-- Only the presently selected man's counter is guarded. Pauses satisfy this guard vacuously. -/
def guard {n : ℕ} (C : Protocol n) (h : List (Entry n)) (cap : ℕ) : Prop :=
  ∀ m, selected C h = some m → (recordState h).next m ≤ cap

/-- An actual next edge hits a low destination under the current visible selected-counter guard. -/
def hit {n : ℕ} (C : Protocol n) (h : List (Entry n)) (cap : ℕ)
    (low : Finset (Fin n)) (p : Profile n) : Prop :=
  guard C h cap ∧ ∃ w ∈ low, ∃ m, nextEdge C p.manRank h = some (w, m)

/-- Public scores at least one give a total destination weight at least n. -/
theorem card_le_totalWeight {n : ℕ} (a : Fin n → ℝ≥0) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) :
    (n : ℝ) ≤ totalWeight a := by
  calc
    (n : ℝ) = ∑ _w : Fin n, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun w _ ↦ ha1 w

/-- A current prefix exposing at most cap women retains at least half the original weight
whenever A*cap/n <= 1/2. The denominator estimate is about the current prefix alone. -/
theorem half_total_le_untried {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (C : Protocol n) (h : List (Entry n))
    (hh : eventMass (VisitBounds.profileLaw a b) (event C h) ≠ 0) (m : Fin n) (cap : ℕ)
    (hcap : (recordState h).next m ≤ cap) (hsmall : A * cap / n ≤ 1 / 2) :
    totalWeight a / 2 ≤ ∑ w ∈ Continuation.untried h m, (a w : ℝ) := by
  classical
  let used := (manOrder h m).toFinset
  have hcard : used.card = (recordState h).next m := by
    rw [List.toFinset_card_of_nodup (Continuation.manOrder_nodup a b C h hh m), length_manOrder]
  have hused : Finset.univ.filter (fun w ↦ w ∈ manOrder h m) = used := by
    ext w
    simp [used]
  have hpart := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun w ↦ w ∈ manOrder h m) (fun w ↦ (a w : ℝ))
  rw [hused] at hpart
  have hbound : (∑ w ∈ used, (a w : ℝ)) ≤ A * cap := by
    calc
      _ ≤ ∑ _w ∈ used, A := Finset.sum_le_sum fun w _ ↦ haA w
      _ = A * used.card := by simp [mul_comm]
      _ = A * (recordState h).next m := by rw [hcard]
      _ ≤ A * cap := mul_le_mul_of_nonneg_left (by exact_mod_cast hcap) (by linarith)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hhalf := (div_le_iff₀ hn').mp hsmall
  have htotal := card_le_totalWeight a ha1
  change (∑ w ∈ used, (a w : ℝ)) +
    (∑ w ∈ Continuation.untried h m, (a w : ℝ)) = totalWeight a at hpart
  nlinarith

/-- Each actual conditional next-edge probability is at most twice its original categorical
mass while the selected man's current prefix satisfies the public weight guard. -/
theorem destination_probability_le {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (C : Protocol n) (h : List (Entry n))
    (hh : eventMass (VisitBounds.profileLaw a b) (event C h) ≠ 0)
    (m w : Fin n) (hs : selected C h = some m) (cap : ℕ)
    (hcap : (recordState h).next m ≤ cap) (hsmall : A * cap / n ≤ 1 / 2) :
    (eventMass (lawAt (VisitBounds.profileLaw a b) C h)
      (Continuation.destinationEvent C h w m)).toReal ≤ 2 * (a w : ℝ) / totalWeight a := by
  classical
  have ha : ∀ w, 0 < a w := fun w ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (ha1 w)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have htotal : 0 < totalWeight a := lt_of_lt_of_le hn' (card_le_totalWeight a ha1)
  change (eventMass (Continuation.lawAt a b C h)
    (Continuation.destinationEvent C h w m)).toReal ≤ _
  by_cases hw : w ∈ manOrder h m
  · rw [Continuation.destination_probability_seen a b C h hh w m hw, ENNReal.toReal_zero]
    positivity
  · rw [Continuation.destination_probability_real a b ha hb C h hh w m hs (by
      simp [Continuation.untried, hw])]
    have hd := half_total_le_untried hn a b hA ha1 haA C h hh m cap hcap hsmall
    change (a w : ℝ) / (∑ v ∈ Continuation.untried h m, (a v : ℝ)) ≤ _
    calc
      _ ≤ (a w : ℝ) / (totalWeight a / 2) :=
        div_le_div_of_nonneg_left (a w).coe_nonneg (by positivity) hd
      _ = _ := by field_simp

/-- A finite low-set union is bounded by the sum of its actual destination probabilities. -/
theorem probability_biExists_le_sum {Ω : Type*} [Fintype Ω] {ι : Type*}
    (μ : PMF Ω) (F : Finset ι) (E : ι → Set Ω) :
    SurvivalKernel.probability μ {p | ∃ w ∈ F, p ∈ E w} ≤
      ∑ w ∈ F, SurvivalKernel.probability μ (E w) := by
  classical
  rw [SurvivalKernel.probability, ← VisitBounds.expectation_indicator_one]
  calc
    _ ≤ VisitBounds.expectation μ
        (fun p ↦ ∑ w ∈ F, (E w).indicator (fun _ ↦ (1 : ℝ)) p) := by
      apply VisitBounds.expectation_mono_support
      intro p _
      by_cases hp : ∃ w ∈ F, p ∈ E w
      · obtain ⟨w, hw, hpw⟩ := hp
        rw [Set.indicator_of_mem (show p ∈ {p | ∃ w ∈ F, p ∈ E w} from ⟨w, hw, hpw⟩)]
        exact le_trans (by simp [Set.indicator_of_mem hpw])
          (Finset.single_le_sum (fun v _ ↦ by
            simp only [Set.indicator_apply]; split_ifs <;> norm_num) hw)
      · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hp]
        exact Finset.sum_nonneg fun w _ ↦ by split_ifs <;> norm_num
    _ = _ := by
      rw [EmptySurvival.expectation_finset_sum]
      apply Finset.sum_congr rfl
      intro w _
      exact VisitBounds.expectation_indicator_one _ _

/-- A bounded current selected prefix hits a public low set with conditional probability at
most twice its original categorical mass, under the actual profile law. -/
theorem one_step_probability_le {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (C : Protocol n) (h : List (Entry n))
    (hh : eventMass (VisitBounds.profileLaw a b) (event C h) ≠ 0)
    (cap : ℕ) (low : Finset (Fin n)) (hsmall : A * cap / n ≤ 1 / 2) :
    SurvivalKernel.probability (lawAt (VisitBounds.profileLaw a b) C h)
      {p | hit C h cap low p} ≤ 2 * lowMass a low := by
  classical
  by_cases hg : guard C h cap
  · cases hs : selected C h with
    | none =>
      have he : {p | hit C h cap low p} = ∅ := by
        ext p
        simp [hit, nextEdge, hs]
      rw [he, SurvivalKernel.probability_empty]
      exact mul_nonneg (by norm_num) (div_nonneg (Finset.sum_nonneg fun _ _ ↦ NNReal.coe_nonneg _)
        (Finset.sum_nonneg fun _ _ ↦ NNReal.coe_nonneg _))
    | some m =>
      have he : {p | hit C h cap low p} =
          {p | ∃ w ∈ low, p ∈ Continuation.destinationEvent C h w m} := by
        ext p
        change (guard C h cap ∧ ∃ w ∈ low, ∃ k, nextEdge C p.manRank h = some (w, k)) ↔ _
        simp only [hg, true_and, Continuation.destinationEvent, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨w, hw, k, hk⟩
          have hm := nextEdge_map_man C p.manRank h
          rw [hk, Option.map_some, hs] at hm
          have hkm : k = m := Option.some.inj hm
          exact ⟨w, hw, by simpa only [hkm] using hk⟩
        · rintro ⟨w, hw, hm⟩
          exact ⟨w, hw, m, hm⟩
      rw [he]
      apply (probability_biExists_le_sum _ low _).trans
      calc
        _ ≤ ∑ w ∈ low, 2 * (a w : ℝ) / totalWeight a := by
          apply Finset.sum_le_sum
          intro w _
          exact destination_probability_le hn a b hA ha1 haA hb C h hh m w hs cap (hg m hs) hsmall
        _ = 2 * lowMass a low := by
          simp only [lowMass, Finset.sum_div, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _
          ring
  · have he : {p | hit C h cap low p} = ∅ := by ext p; simp [hit, hg]
    rw [he, SurvivalKernel.probability_empty]
    exact mul_nonneg (by norm_num) (div_nonneg (Finset.sum_nonneg fun _ _ ↦ NNReal.coe_nonneg _)
      (Finset.sum_nonneg fun _ _ ↦ NNReal.coe_nonneg _))

/-- Finite chronological detection follows the same original profile after each actual record.
Only current selected-prefix counters are tested; future stopping counts are not inputs. -/
noncomputable def hitFuel {n : ℕ} (C : Protocol n) (cap : ℕ) (low : Finset (Fin n)) :
    ℕ → List (Entry n) → Profile n → Bool
  | 0, _, _ => false
  | fuel + 1, h, p => by
      classical
      exact decide (hit C h cap low p) ||
        hitFuel C cap low fuel (nextObservation C h p :: h) p

/-- Literal conditional success probability of the finite detection recursion. -/
noncomputable def hitProbability {n : ℕ} (μ : PMF (Profile n)) (C : Protocol n)
    (cap : ℕ) (low : Finset (Fin n)) (fuel : ℕ) (h : List (Entry n)) : ℝ :=
  VisitBounds.expectation (lawAt μ C h) (fun p ↦ if hitFuel C cap low fuel h p then 1 else 0)

/-- The actual profile-history tower supplies the union recursion for guarded low destinations. -/
theorem hitProbability_succ_le {n : ℕ} (μ : PMF (Profile n)) (C : Protocol n)
    (cap : ℕ) (low : Finset (Fin n)) (fuel : ℕ) (h : List (Entry n))
    (hh : eventMass μ (event C h) ≠ 0) :
    hitProbability μ C cap low (fuel + 1) h ≤
      SurvivalKernel.probability (lawAt μ C h) {p | hit C h cap low p} +
        ∑ e, (nextLaw μ C h e).toReal * hitProbability μ C cap low fuel (e :: h) := by
  classical
  have hhit : VisitBounds.expectation (lawAt μ C h)
      (fun p ↦ if hit C h cap low p then (1 : ℝ) else 0) =
        SurvivalKernel.probability (lawAt μ C h) {p | hit C h cap low p} := by
    rw [SurvivalKernel.probability, ← VisitBounds.expectation_indicator_one]
    congr 1
  have ht := expectation_next_lawAt_congr μ C h hh
    (fun p ↦ if hitFuel C cap low fuel (nextObservation C h p :: h) p then (1 : ℝ) else 0)
    (fun e p ↦ if hitFuel C cap low fuel (e :: h) p then (1 : ℝ) else 0) (by
      intro e he p hp
      rw [child_support_next μ C h e hh he p hp])
  calc
    _ ≤ VisitBounds.expectation (lawAt μ C h) (fun p ↦
        (if hit C h cap low p then (1 : ℝ) else 0) +
          (if hitFuel C cap low fuel (nextObservation C h p :: h) p then 1 else 0)) := by
      apply VisitBounds.expectation_mono_support
      intro p _
      by_cases hh : hit C h cap low p
      · simp only [hitFuel, hh, decide_true, Bool.true_or, ↓reduceIte]
        split_ifs <;> norm_num
      · simp only [hitFuel, hh, decide_false, Bool.false_or, ↓reduceIte, zero_add, le_refl]
    _ = _ := by
      rw [Continuation.expectation_add, hhit, ht]
      rfl

/-- Finite backward induction bounds actual guarded low-destination detection by horizon times
its exact one-step categorical mass bound. Null child histories contribute zero. -/
theorem hitProbability_le {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (C : Protocol n) (h : List (Entry n))
    (hh : eventMass (VisitBounds.profileLaw a b) (event C h) ≠ 0)
    (cap : ℕ) (low : Finset (Fin n)) (hsmall : A * cap / n ≤ 1 / 2) (fuel : ℕ) :
    hitProbability (VisitBounds.profileLaw a b) C cap low fuel h ≤
      (fuel : ℝ) * (2 * lowMass a low) := by
  induction fuel generalizing h with
  | zero => simp [hitProbability, hitFuel, VisitBounds.expectation_const]
  | succ fuel ih =>
    have hs := hitProbability_succ_le (VisitBounds.profileLaw a b) C cap low fuel h hh
    have hlocal := one_step_probability_le hn a b hA ha1 haA hb C h hh cap low hsmall
    have hsum : (∑ e, (nextLaw (VisitBounds.profileLaw a b) C h e).toReal *
        hitProbability (VisitBounds.profileLaw a b) C cap low fuel (e :: h)) ≤
          (fuel : ℝ) * (2 * lowMass a low) := by
      calc
        _ ≤ ∑ e, (nextLaw (VisitBounds.profileLaw a b) C h e).toReal *
            ((fuel : ℝ) * (2 * lowMass a low)) := by
          apply Finset.sum_le_sum
          intro e _
          by_cases he : nextLaw (VisitBounds.profileLaw a b) C h e = 0
          · simp only [he, ENNReal.toReal_zero, zero_mul, le_refl]
          · exact mul_le_mul_of_nonneg_left
              (ih (e :: h) (child_nonnull _ C h e hh he)) ENNReal.toReal_nonneg
        _ = _ := by rw [← Finset.sum_mul, Continuation.sum_mass_real, one_mul]
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith

/-- The finite recursion detects exactly an actual chronological guarded hit. -/
theorem hitFuel_iff {n : ℕ} (C : Protocol n) (cap : ℕ) (low : Finset (Fin n))
    (fuel : ℕ) (h : List (Entry n)) (p : Profile n) :
    hitFuel C cap low fuel h p = true ↔
      ∃ t < fuel, hit C (EmptySurvival.advance C p t h) cap low p := by
  induction fuel generalizing h with
  | zero => simp [hitFuel]
  | succ fuel ih =>
    simp only [hitFuel, Bool.or_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro (hh | ⟨t, ht, hh⟩)
      · exact ⟨0, Nat.zero_lt_succ _, hh⟩
      · exact ⟨t + 1, by omega, hh⟩
    · rintro ⟨t, ht, hh⟩
      cases t with
      | zero => exact Or.inl hh
      | succ t => exact Or.inr ⟨t, by omega, hh⟩

/-- Guarded low-destination hits at literal future ordinary protocol times. -/
def futureEvent {n : ℕ} (C : Protocol n) (h0 : List (Entry n)) (cap : ℕ)
    (low : Finset (Fin n)) (T : ℕ) : Set (Profile n) :=
  {p | ∃ t < T, hit C (Protocols.profileTranscript C p (h0.length + t)) cap low p}

/-- On a realized setup prefix, finite detection is exactly the event at future transcript times. -/
theorem hitFuel_iff_futureEvent {n : ℕ} (C : Protocol n) (h0 : List (Entry n))
    (cap : ℕ) (low : Finset (Fin n)) (T : ℕ) (p : Profile n)
    (hp : Protocols.profileTranscript C p h0.length = h0) :
    hitFuel C cap low T h0 p = true ↔ p ∈ futureEvent C h0 cap low T := by
  simp only [hitFuel_iff, futureEvent, Set.mem_ofPred_eq,
    EmptySurvival.advance_eq_transcript C p _ h0 hp]

/-- Actual conditional finite-horizon union bound, using only each current selected counter.
No future count, stopping event, or terminal condition appears in the conditioning history. -/
theorem future_probability_le {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (C : Protocol n) (h0 : List (Entry n))
    (hh : eventMass (VisitBounds.profileLaw a b) (event C h0) ≠ 0)
    (cap : ℕ) (low : Finset (Fin n)) (hsmall : A * cap / n ≤ 1 / 2) (T : ℕ) :
    (eventMass (lawAt (VisitBounds.profileLaw a b) C h0)
      (futureEvent C h0 cap low T)).toReal ≤ (T : ℝ) * (2 * lowMass a low) := by
  have hbnd := hitProbability_le hn a b hA ha1 haA hb C h0 hh cap low hsmall T
  have he : hitProbability (VisitBounds.profileLaw a b) C cap low T h0 =
      SurvivalKernel.probability (lawAt (VisitBounds.profileLaw a b) C h0)
        {p | hitFuel C cap low T h0 p = true} := by
    rw [SurvivalKernel.probability, ← VisitBounds.expectation_indicator_one]
    unfold hitProbability
    congr 1
    funext p
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  have hevent := SurvivalKernel.probability_congr_support
    (lawAt (VisitBounds.profileLaw a b) C h0)
    {p | hitFuel C cap low T h0 p = true} (futureEvent C h0 cap low T) (by
      intro p hp
      have hs : p ∈ (condition (VisitBounds.profileLaw a b) (event C h0)).support := hp
      rw [support_condition _ _ hh] at hs
      exact hitFuel_iff_futureEvent C h0 cap low T p hs.1)
  rw [he, hevent] at hbnd
  exact hbnd

/-- The original categorical low-set mass is bounded by A times its population fraction. -/
theorem lowMass_le_card {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ≥0) {A : ℝ}
    (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (low : Finset (Fin n)) : lowMass a low ≤ A * low.card / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ht := card_le_totalWeight a ha1
  have htotal : 0 ≤ totalWeight a := (lt_of_lt_of_le hn' ht).le
  have hsum : (∑ w ∈ low, (a w : ℝ)) ≤ A * low.card := by
    calc
      _ ≤ ∑ _w ∈ low, A := Finset.sum_le_sum fun w _ ↦ haA w
      _ = _ := by simp [mul_comm]
  unfold lowMass
  exact (div_le_div_of_nonneg_right hsum htotal).trans
    (div_le_div_of_nonneg_left (mul_nonneg (by linarith) (Nat.cast_nonneg _)) hn' ht)

/-- The same actual guarded union bound has the convenient cardinality-only form. -/
theorem future_probability_le_card {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (C : Protocol n) (h0 : List (Entry n))
    (hh : eventMass (VisitBounds.profileLaw a b) (event C h0) ≠ 0)
    (cap : ℕ) (low : Finset (Fin n)) (hsmall : A * cap / n ≤ 1 / 2) (T : ℕ) :
    (eventMass (lawAt (VisitBounds.profileLaw a b) C h0)
      (futureEvent C h0 cap low T)).toReal ≤ 2 * T * A * low.card / n := by
  apply (future_probability_le hn a b hA ha1 haA hb C h0 hh cap low hsmall T).trans
  have hbnd := mul_le_mul_of_nonneg_left (lowMass_le_card hn a hA ha1 haA low)
    (show 0 ≤ 2 * (T : ℝ) by positivity)
  convert hbnd using 1 <;> ring

/-- The actual conditional probability-measure form of the finite future union bound. -/
theorem future_measure_le {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (C : Protocol n) (h0 : List (Entry n))
    (hh : eventMass (VisitBounds.profileLaw a b) (event C h0) ≠ 0)
    (cap : ℕ) (low : Finset (Fin n)) (hsmall : A * cap / n ≤ 1 / 2) (T : ℕ) :
    ((lawAt (VisitBounds.profileLaw a b) C h0).toMeasure
      (futureEvent C h0 cap low T)).toReal ≤ 2 * T * lowMass a low := by
  rw [← eventMass_eq_toMeasure _ _ (by trivial)]
  have hbnd := future_probability_le hn a b hA ha1 haA hb C h0 hh cap low hsmall T
  convert hbnd using 1
  ring

/-- The first two bounded priority phases use at most 2c steps and expose at most 2c entries
of their currently selected man. Their guarded low-destination error is at most 4c*pi(low). -/
theorem two_cap_probability_le {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (C : Protocol n) (h0 : List (Entry n))
    (hh : eventMass (VisitBounds.profileLaw a b) (event C h0) ≠ 0)
    (cap : ℕ) (low : Finset (Fin n)) (hsmall : A * (2 * cap : ℕ) / n ≤ 1 / 2) :
    (eventMass (lawAt (VisitBounds.profileLaw a b) C h0)
      (futureEvent C h0 (2 * cap) low (2 * cap))).toReal ≤ 4 * cap * lowMass a low := by
  have hbnd := future_probability_le hn a b hA ha1 haA hb C h0 hh (2 * cap) low hsmall (2 * cap)
  convert hbnd using 1
  push_cast
  ring

open ContinuationAsymptotics

/-- A rounded log² threshold is at most (D+1)log² n once log n is at least one. -/
theorem threshold_le_log_sq {D : ℝ} (hD : 0 < D) {n : ℕ} (hlog : 1 ≤ Real.log n) :
    (threshold D n : ℝ) ≤ (D + 1) * (Real.log n) ^ 2 := by
  have hc := Nat.ceil_lt_add_one (mul_nonneg hD.le (sq_nonneg (Real.log n)))
  have hs : 1 ≤ (Real.log n) ^ 2 := by nlinarith [sq_nonneg (Real.log n - 1)]
  change (Nat.ceil (D * (Real.log n) ^ 2) : ℝ) ≤ _
  nlinarith

/-- Every fixed rounded log² cap is eventually smaller than any positive linear budget. -/
theorem eventually_threshold_le_mul {D ε : ℝ} (hD : 0 < D) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, (threshold D n : ℝ) ≤ ε * n := by
  have hp : 0 < D + 1 := by linarith
  filter_upwards [eventually_one_le_log,
    eventually_log_sq_le (div_pos hε hp)] with n hlog hsq
  apply (threshold_le_log_sq hD hlog).trans
  calc
    _ ≤ (D + 1) * (ε / (D + 1) * n) := mul_le_mul_of_nonneg_left hsq hp.le
    _ = ε * n := by field_simp

/-- The square of a rounded log² cap is eventually negligible on every positive
polynomial scale. -/
theorem eventually_threshold_sq_mul_rpow_le {D κ ε : ℝ} (hD : 0 < D)
    (hκ : 0 < κ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (threshold D n : ℝ) ^ 2 * (n : ℝ) ^ (-κ) ≤ ε := by
  have hp : 0 < D + 1 := by linarith
  have ho := (isLittleO_log_rpow_rpow_atTop (s := κ) 4 hκ).comp_tendsto
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ))
      Filter.atTop Filter.atTop)
  filter_upwards [ho.def (div_pos hε (sq_pos_of_pos hp)), eventually_one_le_log,
    Filter.eventually_ge_atTop 1] with n hsmall hlog hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsmall' : (Real.log n) ^ 4 ≤ ε / (D + 1) ^ 2 * (n : ℝ) ^ κ := by
    simpa only [Function.comp_apply, Real.rpow_ofNat, Real.rpow_natCast, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ Real.log n) 4),
      abs_of_nonneg (Real.rpow_nonneg hn'.le κ)] using hsmall
  have hc := pow_le_pow_left₀ (Nat.cast_nonneg (threshold D n))
    (threshold_le_log_sq hD hlog) 2
  have hc' : (threshold D n : ℝ) ^ 2 ≤ (D + 1) ^ 2 * (Real.log n) ^ 4 := by
    nlinarith [hc]
  have hm := mul_le_mul_of_nonneg_left hsmall' (sq_nonneg (D + 1))
  have he : (D + 1) ^ 2 * (ε / (D + 1) ^ 2 * (n : ℝ) ^ κ) = ε * (n : ℝ) ^ κ := by
    field_simp
  rw [he] at hm
  have hbnd := hc'.trans hm
  rw [Real.rpow_neg hn'.le]
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hn' κ)).mpr hbnd

/-- Fixed log² caps eventually satisfy every deterministic guard used by the first two phases. -/
theorem eventually_threshold_guards {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (2 * (threshold D n : ℝ) ≤ (n : ℝ) * Real.log n) ∧
      threshold D n < n / 4 ∧ A * (2 * threshold D n : ℕ) / n ≤ 1 / 2 := by
  filter_upwards [eventually_threshold_le_mul hD (by positivity : 0 < 1 / (4 * A)),
    eventually_threshold_le_mul hD (by norm_num : (0 : ℝ) < 1 / 4),
    eventually_threshold_lt_individualCap hD, eventually_one_le_log,
    Filter.eventually_ge_atTop 1] with n hcap hquarter hfloor hlog hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  refine ⟨?_, hfloor, ?_⟩
  · have hm := mul_le_mul_of_nonneg_left hlog hn'.le
    nlinarith
  · apply (div_le_iff₀ hn').mpr
    have hm := mul_le_mul_of_nonneg_left hcap (show 0 ≤ 2 * A by positivity)
    have he : (2 * A) * (1 / (4 * A) * (n : ℝ)) = (1 / 2 : ℝ) * n := by field_simp; norm_num
    rw [he] at hm
    push_cast
    nlinarith [hm]

/-- The source's complete rank/low-destination exception expression is eventually at most one,
uniformly over all low masses with a fixed positive polynomial decay exponent. -/
theorem eventually_rest_error_le_one {A D κ : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ ℓ : ℝ, 0 ≤ ℓ → ℓ ≤ A * (n : ℝ) ^ (-κ) →
      4 * (threshold D n : ℝ) ^ 2 * ℓ +
        8 * threshold D n * (n : ℝ) ^ (-4 : ℝ) +
          16 * n * (n : ℝ) ^ (-4 : ℝ) ≤ 1 := by
  filter_upwards [eventually_threshold_sq_mul_rpow_le hD hκ
    (by positivity : 0 < 1 / (8 * A)),
    eventually_threshold_le_mul hD (by norm_num : (0 : ℝ) < 1),
    Filter.eventually_ge_atTop 4] with n hsmall hcap hn ℓ _ hℓ
  have hn0 : 0 < n := by omega
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hfirst : 4 * (threshold D n : ℝ) ^ 2 * ℓ ≤ 1 / 2 := by
    calc
      _ ≤ 4 * (threshold D n : ℝ) ^ 2 * (A * (n : ℝ) ^ (-κ)) :=
        mul_le_mul_of_nonneg_left hℓ (by positivity)
      _ = 4 * A * ((threshold D n : ℝ) ^ 2 * (n : ℝ) ^ (-κ)) := by ring
      _ ≤ 4 * A * (1 / (8 * A)) := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = 1 / 2 := by field_simp; norm_num
  have hpower : (n : ℝ) * (n : ℝ) ^ (-4 : ℝ) = 1 / (n : ℝ) ^ (3 : ℕ) := by
    calc
      _ = (n : ℝ) ^ (-3 : ℝ) := by
        have hi := RankTail.nat_mul_rpow hn0 (3 : ℝ)
        norm_num only [show (3 : ℝ) + 1 = 4 by norm_num] at hi
        exact hi
      _ = _ := by
        rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_ofNat, one_div]
  have htail : 8 * threshold D n * (n : ℝ) ^ (-4 : ℝ) +
      16 * n * (n : ℝ) ^ (-4 : ℝ) ≤ 1 / 2 := by
    have hm := mul_le_mul_of_nonneg_right hcap
      (Real.rpow_nonneg (Nat.cast_nonneg n) (-4 : ℝ))
    have hp : (0 : ℝ) < (n : ℝ) ^ (3 : ℕ) := by positivity
    have hn3 : (4 : ℝ) ^ (3 : ℕ) ≤ (n : ℝ) ^ (3 : ℕ) := by gcongr
    have hfrac : 24 / (n : ℝ) ^ (3 : ℕ) ≤ 1 / 2 := by
      apply (div_le_iff₀ hp).mpr
      norm_num at hn3
      linarith
    have hfrac' : 24 * ((n : ℝ) * (n : ℝ) ^ (-4 : ℝ)) ≤ 1 / 2 := by
      rw [hpower]
      simpa only [div_eq_mul_inv, one_div, one_mul] using hfrac
    nlinarith [hm, hfrac']
  linarith

end TieredMatching.LowDestinations
