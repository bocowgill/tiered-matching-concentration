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

public import TieredMatching.InitialAsymptotics
public import TieredMatching.SmoothSetup

/-! # Actual finite leave-two setup states

The original PR market is disintegrated over its literal finite completed setup transcript.
Good labels carry deterministic smoothness and the actual uniform initial moment packet.
-/

@[expose] public section

namespace TieredMatching.PairStates

open StableMarriage MeasureTheory FiniteConditioning TieredMatching.Ordinal Protocols Filter
open scoped ENNReal NNReal

/-- A finite label records every setup observation, including pauses, with its exact clock. -/
abbrev Label (n : ℕ) := Fin (n * n) → Entry n

/-- The literal newest-first setup history decoded from a finite label. -/
def decode {n : ℕ} (h : Label n) : List (Entry n) := List.ofFn h

/-- The actual staged setup transcript, encoded without padding aliases. -/
noncomputable def state {n : ℕ} (u v : Fin n) (p : Profile n) : Label n :=
  fun i ↦ (InitialPhase.history p u v 0).get
    ⟨i.val, by simpa only [InitialPhase.history_length, Nat.add_zero] using i.isLt⟩

/-- Decoding the actual label recovers the exact setup transcript. -/
theorem decode_state {n : ℕ} (u v : Fin n) (p : Profile n) :
    decode (state u v p) = InitialPhase.history p u v 0 := by
  apply List.ext_getElem
  · simp only [decode, List.length_ofFn, InitialPhase.history_length, Nat.add_zero]
  · intro i hi hj
    simp only [decode, List.getElem_ofFn, state, List.get_eq_getElem]

/-- Literal label equality is exactly equality with the original setup prefix event. -/
theorem state_fiber {n : ℕ} (u v : Fin n) (h : Label n) :
    {p | state u v p = h} = InitialPhase.setupEvent u v (decode h) := by
  ext p
  change state u v p = h ↔ InitialPhase.history p u v 0 = decode h
  rw [← decode_state u v p]
  exact List.ofFn_inj.symm

/-- The finite observation law of the actual completed setup. -/
noncomputable def law {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n) : PMF (Label n) :=
  μ.map (state u v)

/-- Conditional future law given only the literal complete setup label. -/
noncomputable def future {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n) (h : Label n) :
    PMF (Profile n) := InitialPhase.setupLaw μ u v (decode h)

/-- A setup label's mass is the exact original setup-prefix event mass. -/
theorem law_apply {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n) (h : Label n) :
    law μ u v h = eventMass μ (InitialPhase.setupEvent u v (decode h)) := by
  rw [← state_fiber]
  exact (eventMass_observation_fiber μ (state u v) h).symm

/-- Null labels and null conditioning events agree exactly. -/
theorem nonnull_iff {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n) (h : Label n) :
    law μ u v h ≠ 0 ↔ eventMass μ (InitialPhase.setupEvent u v (decode h)) ≠ 0 := by
  rw [law_apply]

/-- Mixing the actual conditional future laws recovers the original market, including nulls. -/
theorem bind_future {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n) :
    (law μ u v).bind (future μ u v) = μ := by
  have hf : future μ u v = fun h ↦ condition μ {p | state u v p = h} := by
    funext h
    rw [state_fiber]
    rfl
  rw [hf]
  exact bind_condition_eq μ (state u v)

/-- Mapping an actual finite law transports every event mass by literal preimage. -/
theorem eventMass_map {Ω R : Type*} (μ : PMF Ω) (f : Ω → R) (E : Set R) :
    eventMass (μ.map f) E = eventMass μ (f ⁻¹' E) := by
  simpa only [PMF.toOuterMeasure_apply, eventMass] using
    PMF.toOuterMeasure_map_apply f μ E

/-- The actual staged setup equals the completed leave-two ordinary setup transcript. -/
theorem decode_state_setup {n : ℕ} (u v : Fin n) (p : Profile n) :
    decode (state u v p) = SmoothSetup.setupHistory (ordinaryEntrants u v) p := by
  rw [decode_state]
  exact stagedProtocol_setup_transcript p u v (n * n) le_rfl

/-- The finite label's setup potential is the genuine completed active-market total. -/
theorem state_total {n : ℕ} (u v : Fin n) (p : Profile n) :
    potential (recordState (decode (state u v p))) =
      SmoothSetup.setupTotal (ordinaryEntrants u v) p := by
  rw [decode_state_setup, SmoothSetup.setupHistory_state]
  rfl

/-- Low-weight women in a finite setup label are the literal low accumulated-score set. -/
noncomputable def low {n : ℕ} (b : Fin n → ℝ≥0) (A : ℝ) (h : Label n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun w ↦ VisitBounds.gamma b (decode h) w <
    SmoothSetup.gammaCoefficient A * Real.log n

/-- Deterministic smoothness conditions on a finite setup label. -/
def Smooth {n : ℕ} (b : Fin n → ℝ≥0) (A : ℝ) (h : Label n) : Prop :=
  (potential (recordState (decode h)) : ℝ) ≤ RankTail.setupCoefficient A 3 * n * Real.log n ∧
    ((low b A h).card : ℝ) ≤ (n : ℝ) ^ (1 - SmoothSetup.setupExponent A)

/-- A good setup label is both supported by the actual market and deterministically smooth. -/
def Good {n : ℕ} (μ : PMF (Profile n)) (b : Fin n → ℝ≥0) (A : ℝ)
    (u v : Fin n) (h : Label n) : Prop := law μ u v h ≠ 0 ∧ Smooth b A h

/-- The low-set statistic of an actual label is exactly the source's actual setup statistic. -/
theorem state_low_card {n : ℕ} (b : Fin n → ℝ≥0) (A : ℝ) (u v : Fin n) (p : Profile n) :
    ((low b A (state u v p)).card : ℝ) =
      SmoothSetup.badSetupCount (ordinaryEntrants u v) b p (Real.log n / (64 * A ^ 2)) := by
  classical
  have hc : SmoothSetup.gammaCoefficient A * Real.log n = Real.log n / (64 * A ^ 2) := by
    unfold SmoothSetup.gammaCoefficient
    ring
  simp only [low, decode_state_setup, hc, SmoothSetup.badSetupCount, SmoothSetup.setupWeight]
  rfl


/-- Exact joint setup/future point mass, with no arbitrary assignment on null branches. -/
theorem law_mul_future {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n)
    (h : Label n) (p : Profile n) :
    law μ u v h * future μ u v h p = if state u v p = h then μ p else 0 := by
  classical
  have hf : future μ u v h = condition μ {p | state u v p = h} := by
    rw [state_fiber]
    rfl
  rw [hf]
  have hh := observation_mul_condition μ (state u v) h p
  split_ifs with he
  · simpa only [law, ite_eq_left he] using hh
  · simpa only [law, ite_eq_right he] using hh

/-- Positive conditional profiles have the literal setup label being conditioned on. -/
theorem future_state {n : ℕ} (μ : PMF (Profile n)) (u v : Fin n)
    (h : Label n) (hh : law μ u v h ≠ 0) (p : Profile n)
    (hp : future μ u v h p ≠ 0) : state u v p = h := by
  have hs : p ∈ (future μ u v h).support := hp
  change p ∈ (condition μ (InitialPhase.setupEvent u v (decode h))).support at hs
  rw [support_condition μ _ ((nonnull_iff μ u v h).mp hh)] at hs
  exact Set.ext_iff.mp (state_fiber u v h) p |>.mpr hs.1

/-- Null setup labels have zero total branch mass, so they do not enlarge the bad event. -/
theorem bad_mass_eq {n : ℕ} (μ : PMF (Profile n)) (b : Fin n → ℝ≥0) (A : ℝ)
    (u v : Fin n) :
    eventMass (law μ u v) {h | ¬ Good μ b A u v h} =
      eventMass μ {p | ¬ Smooth b A (state u v p)} := by
  classical
  have he : eventMass (law μ u v) {h | ¬ Good μ b A u v h} =
      eventMass (law μ u v) {h | ¬ Smooth b A h} := by
    unfold eventMass
    apply tsum_congr
    intro h
    by_cases hh : law μ u v h = 0
    · simp only [Set.indicator_apply, hh, ite_self]
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, Good, hh, ne_eq,
        not_false_eq_true, true_and]
  rw [he]
  exact eventMass_map μ (state u v) _

/-- The good-label failure probability is the actual source leave-two setup failure event. -/
theorem bad_mass_source {n : ℕ} (a b : Fin n → ℝ≥0) (A : ℝ) (u v : Fin n) :
    (eventMass (law (Continuation.market a b) u v)
        {h | ¬ Good (Continuation.market a b) b A u v h}).toReal =
      ((VisitBounds.profileLaw a b).toMeasure).real {p | ¬(
        (SmoothSetup.setupTotal (ordinaryEntrants u v) p : ℝ) ≤
          RankTail.setupCoefficient A 3 * n * Real.log n ∧
        SmoothSetup.badSetupCount (ordinaryEntrants u v) b p (Real.log n / (64 * A ^ 2)) ≤
          (n : ℝ) ^ (1 - SmoothSetup.setupExponent A))} := by
  rw [bad_mass_eq]
  simp only [Smooth, state_total, state_low_card]
  rw [eventMass_eq_toMeasure _ _ (by trivial)]
  rfl

/-- The actual finite setup distribution has the source uniform smooth-state probability. -/
theorem eventually_bad_mass {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ (a b : Fin n → ℝ≥0),
      (∀ w, 1 ≤ (a w : ℝ)) → (∀ w, (a w : ℝ) ≤ A) →
      (∀ m, 1 ≤ (b m : ℝ)) → (∀ m, (b m : ℝ) ≤ B) →
      ∀ u v : Fin n, u ≠ v →
      (eventMass (law (Continuation.market a b) u v)
        {h | ¬ Good (Continuation.market a b) b A u v h}).toReal ≤
          13 * (n : ℝ) ^ (-SmoothSetup.setupExponent A) := by
  filter_upwards [SmoothSetup.eventually_leave_two_smooth_setup hA hB]
    with n hn a b ha1 haA hb1 hbB u v huv
  rw [bad_mass_source]
  exact hn a b ha1 haA hb1 hbB u v huv

/-- Every supported smooth label gives the exact initial-phase setup setting. -/
noncomputable def setting {n : ℕ} (a b : Fin n → ℝ≥0) {A B : ℝ}
    (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb1 : ∀ m, 1 ≤ (b m : ℝ)) (hbB : ∀ m, (b m : ℝ) ≤ B)
    (u v : Fin n) (huv : u ≠ v) (h : Label n)
    (hh : Good (Continuation.market a b) b A u v h) :
    InitialAsymptotics.Setting n A B (RankTail.setupCoefficient A 3)
      (SmoothSetup.gammaCoefficient A) (SmoothSetup.setupExponent A) where
  a := a
  b := b
  u := u
  v := v
  distinct := huv
  setup := decode h
  nonnull := (nonnull_iff _ _ _ _).mp hh.1
  a_lower := ha1
  a_upper := haA
  b_lower := hb1
  b_upper := hbB
  total := hh.2.1
  low := low b A h
  low_card := hh.2.2
  high := by
    classical
    intro w hw
    have he : ¬ VisitBounds.gamma b (decode h) w <
        SmoothSetup.gammaCoefficient A * Real.log n := by
      simpa only [low, Finset.mem_filter, Finset.mem_univ, true_and] using hw
    exact le_of_not_gt he

/-- The actual good-state initial packet is uniform over the whole finite setup support. -/
theorem eventually_good_packet {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ (a b : Fin n → ℝ≥0)
      (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
      (hb1 : ∀ m, 1 ≤ (b m : ℝ)) (hbB : ∀ m, (b m : ℝ) ≤ B)
      (u v : Fin n) (huv : u ≠ v) (h : Label n)
      (hh : Good (Continuation.market a b) b A u v h),
      InitialAsymptotics.Packet (setting a b ha1 haA hb1 hbB u v huv h hh) := by
  have hconst := SmoothSetup.setup_constants hA
  have hC : 0 ≤ RankTail.setupCoefficient A 3 := by
    unfold RankTail.setupCoefficient
    linarith
  filter_upwards [InitialAsymptotics.eventually_packet hA hB hC hconst.1 hconst.2.1]
    with n hn a b ha1 haA hb1 hbB u v huv h hh
  exact hn _


/-- The initial packet's law is exactly this label's conditional original-market future. -/
theorem setting_law {n : ℕ} (a b : Fin n → ℝ≥0) {A B : ℝ}
    (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb1 : ∀ m, 1 ≤ (b m : ℝ)) (hbB : ∀ m, (b m : ℝ) ≤ B)
    (u v : Fin n) (huv : u ≠ v) (h : Label n)
    (hh : Good (Continuation.market a b) b A u v h) :
    InitialAsymptotics.law (setting a b ha1 haA hb1 hbB u v huv h hh) =
      future (Continuation.market a b) u v h := rfl

/-- A globally defined setup scale, zero on unsupported or nonsmooth labels. -/
noncomputable def globalScale {n : ℕ} (a b : Fin n → ℝ≥0) (A : ℝ)
    (u v : Fin n) (h : Label n) : ℝ := by
  classical
  exact if Good (Continuation.market a b) b A u v h then
    1 / SmoothRates.rate (InitialDrift.normalized a) (VisitBounds.gamma b (decode h)) 1 else 0

/-- On good labels the global scale is precisely the actual initial packet's common scale. -/
theorem globalScale_good {n : ℕ} (a b : Fin n → ℝ≥0) {A B : ℝ}
    (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb1 : ∀ m, 1 ≤ (b m : ℝ)) (hbB : ∀ m, (b m : ℝ) ≤ B)
    (u v : Fin n) (huv : u ≠ v) (h : Label n)
    (hh : Good (Continuation.market a b) b A u v h) :
    globalScale a b A u v h =
      InitialAsymptotics.commonScale (setting a b ha1 haA hb1 hbB u v huv h hh) := by
  simp only [globalScale, ite_eq_left hh]
  rfl

/-- The global setup scale is uniformly bounded on all labels, including null labels. -/
theorem eventually_globalScale_bound {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ (a b : Fin n → ℝ≥0)
      (_ha1 : ∀ w, 1 ≤ (a w : ℝ)) (_haA : ∀ w, (a w : ℝ) ≤ A)
      (_hb1 : ∀ m, 1 ≤ (b m : ℝ)) (_hbB : ∀ m, (b m : ℝ) ≤ B)
      (u v : Fin n) (_huv : u ≠ v) (h : Label n),
      |globalScale a b A u v h| ≤
        Real.log n / InitialAsymptotics.lowerConstant A B (RankTail.setupCoefficient A 3) := by
  classical
  have hC : 0 ≤ RankTail.setupCoefficient A 3 := by
    unfold RankTail.setupCoefficient
    linarith
  have hcp := (InitialAsymptotics.lowerConstant_bounds hA hB hC).1
  filter_upwards [eventually_good_packet hA hB,
    ContinuationAsymptotics.eventually_one_le_log] with n hn hlog a b ha1 haA hb1 hbB u v huv h
  by_cases hh : Good (Continuation.market a b) b A u v h
  · rw [globalScale_good a b ha1 haA hb1 hbB u v huv h hh]
    have H := hn a b ha1 haA hb1 hbB u v huv h hh
    rw [abs_of_pos H.scale_positive]
    exact H.scale_upper
  · simp only [globalScale, ite_eq_right hh, abs_zero]
    exact div_nonneg (by linarith) hcp.le

end TieredMatching.PairStates
