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

public import Ashlagi.PairStates
public import Ashlagi.RestAfterAcceptance
public import Ashlagi.MixtureBounds
public import Ashlagi.TierConcentration

/-! # Unconditional original-PR pair proposal moments

Actual initial counts and their actual post-acceptance remainders give the good-state full
rank moments. Literal finite setup disintegration, a retained common-mean variance, and
clipping charged to global rank tails then remove every exceptional setup state.
-/

@[expose] public section

namespace Ashlagi.GlobalPairMoments

open MeasureTheory ProbabilityTheory StableMarriage Filter FiniteConditioning
open scoped ENNReal NNReal Topology

local instance {n : ℕ} : MeasurableSpace (PairStates.Label n) := ⊤

/-- Fixed leave-two setup total coefficient. -/
noncomputable abbrev setupConstant (A : ℝ) : ℝ := RankTail.setupCoefficient A 3

/-- Fixed initial-mean coefficient. -/
noncomputable def initialCoefficient (A B : ℝ) : ℝ :=
  InitialAsymptotics.meanCoefficient A B (setupConstant A)

/-- Fixed common-scale coefficient. -/
noncomputable def scaleCoefficient (A B : ℝ) : ℝ :=
  1 / InitialAsymptotics.lowerConstant A B (setupConstant A)

/-- Fixed initial inverse-popularity error. -/
noncomputable def initialError (A B : ℝ) : ℝ :=
  InitialAsymptotics.scalingConstant A B (setupConstant A) (SmoothSetup.gammaCoefficient A)

/-- The proved uniform actual post-acceptance mean bound. -/
noncomputable def restCoefficient (A B : ℝ) : ℝ :=
  RestAfterAcceptance.restMeanConstant A B (setupConstant A) (SmoothSetup.gammaCoefficient A)

/-- Fixed error in each conditional full-rank common-scale approximation. -/
noncomputable def meanError (A B : ℝ) : ℝ := initialError A B + restCoefficient A B

/-- Good-state covariance loss from adding the nonnegative actual remainders. -/
noncomputable def conditionalCovarianceCoefficient (A B : ℝ) : ℝ :=
  1 + 2 * initialCoefficient A B * restCoefficient A B + restCoefficient A B ^ 2

/-- One real clipping threshold controls global tails and all masked conditional means. -/
noncomputable def clipCoefficient (A B : ℝ) : ℝ :=
  RankTail.rankCoefficient A B 4 + scaleCoefficient A B + meanError A B + 1

/-- Final uniform popularity-weighted pair-mean error. -/
noncomputable def meanConstant (A B : ℝ) : ℝ := 2 * B * meanError A B + 1

/-- Final uniform lower covariance coefficient. -/
noncomputable def covarianceConstant (A B : ℝ) : ℝ :=
  MixtureBounds.covarianceLogConstant (conditionalCovarianceCoefficient A B)
    (scaleCoefficient A B) (meanError A B)

/-- Fixed setup and moment constants have the signs required by every reduction. -/
theorem coefficient_signs {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    0 ≤ setupConstant A ∧ 0 < initialCoefficient A B ∧ 0 < scaleCoefficient A B ∧
      0 < initialError A B ∧ 0 < restCoefficient A B ∧ 0 < meanError A B ∧
      0 < conditionalCovarianceCoefficient A B ∧ 0 < clipCoefficient A B ∧
      0 < meanConstant A B ∧ 0 < covarianceConstant A B := by
  have hC : 0 ≤ setupConstant A := by unfold setupConstant RankTail.setupCoefficient; linarith
  have hζ := (SmoothSetup.setup_constants hA).1
  have hc := (InitialAsymptotics.lowerConstant_bounds hA hB hC).1
  have hr := RestAfterAcceptance.restMeanConstant_pos hA hB hC hζ
  have hD := RankTail.rankCoefficient_pos hA hB (by norm_num : (0 : ℝ) ≤ 4)
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hBm : 0 ≤ B - 1 := by linarith
  have hi : 0 < initialCoefficient A B := by
    unfold initialCoefficient InitialAsymptotics.meanCoefficient
    positivity
  have hl : 0 < scaleCoefficient A B := by unfold scaleCoefficient; positivity
  have hs : 0 < initialError A B := by
    unfold initialError InitialAsymptotics.scalingConstant
    positivity
  have hrest : 0 < restCoefficient A B := hr
  have he : 0 < meanError A B := by unfold meanError; positivity
  have hcov : 0 < conditionalCovarianceCoefficient A B := by
    unfold conditionalCovarianceCoefficient
    positivity
  have hclip : 0 < clipCoefficient A B := by unfold clipCoefficient; positivity
  refine ⟨hC, hi, hl, hs, hrest, he, hcov, hclip, ?_, ?_⟩
  · unfold meanConstant
    positivity
  · exact MixtureBounds.covarianceLogConstant_pos hcov.le hl.le he.le

/-- The initial setup fields instantiate the actual rest theorem without changing the law. -/
noncomputable def restSetting {n : ℕ} {A B C ζ κ : ℝ}
    (S : InitialAsymptotics.Setting n A B C ζ κ) (hn : 8 ≤ n) (hlog : 1 ≤ Real.log n)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C) (hζ : 0 < ζ) (hκ : 0 < κ) :
    RestAfterAcceptance.SmoothSetup n where
  a := S.a
  b := S.b
  u := S.u
  v := S.v
  distinct := S.distinct
  h0 := S.setup
  A := A
  B := B
  C := C
  κ := κ
  ζ := ζ
  low := S.low
  n_ge := hn
  log_ge := hlog
  A_ge := hA
  B_ge := hB
  C_nonneg := hC
  κ_pos := hκ
  ζ_pos := hζ
  a_ge := S.a_lower
  a_le := S.a_upper
  b_ge := S.b_lower
  b_le := S.b_upper
  nonnull := S.nonnull
  total := S.total
  low_card := S.low_card
  high := S.high

/-- Exact pointwise real rank decomposition for either staged entrant. -/
theorem rank_decomposition {n : ℕ} (side : RestAfterAcceptance.Side) (p : Profile n)
    (u v : Fin n) : (RankTail.rank p (RestAfterAcceptance.man side u v) : ℝ) =
      (RestAfterAcceptance.initialCount side p u v : ℝ) +
        (RestAfterAcceptance.rest side p u v : ℝ) := by
  exact_mod_cast RestAfterAcceptance.rank_eq_initial_add_rest side p u v

/-- Exact mean decomposition under any finite conditional original-profile law. -/
theorem rank_mean_decomposition {n : ℕ} (ν : PMF (Profile n))
    (side : RestAfterAcceptance.Side) (u v : Fin n) :
    (∫ p, (RankTail.rank p (RestAfterAcceptance.man side u v) : ℝ) ∂ν.toMeasure) =
      (∫ p, (RestAfterAcceptance.initialCount side p u v : ℝ) ∂ν.toMeasure) +
        ∫ p, (RestAfterAcceptance.rest side p u v : ℝ) ∂ν.toMeasure := by
  simp_rw [rank_decomposition side]
  exact integral_add ((G2Deconditioning.memLp_finite ν.toMeasure _).integrable one_le_two)
    ((G2Deconditioning.memLp_finite ν.toMeasure _).integrable one_le_two)

/-- The actual full-rank moment packet on one supported smooth setup label. -/
structure FullPacket {n : ℕ} (ν : PMF (Profile n)) (b : Fin n → ℝ≥0)
    (u v : Fin n) (Λ K C : ℝ) : Prop where
  first_mean : |(∫ p, (RankTail.rank p u : ℝ) ∂ν.toMeasure) - Λ / (b u : ℝ)| ≤ K
  second_mean : |(∫ p, (RankTail.rank p v : ℝ) ∂ν.toMeasure) - Λ / (b v : ℝ)| ≤ K
  covariance_lower : -C * Real.log n ≤ covariance
    (fun p ↦ (RankTail.rank p u : ℝ)) (fun p ↦ (RankTail.rank p v : ℝ)) ν.toMeasure

/-- Actual initial packets plus proved actual remainder means give actual full-rank packets. -/
theorem fullPacket_of_initial_rest {n : ℕ} {A B C ζ κ : ℝ}
    (S : InitialAsymptotics.Setting n A B C ζ κ) (H : InitialAsymptotics.Packet S)
    (hlog : 1 ≤ Real.log n) {Kr : ℝ} (hKr : 0 ≤ Kr)
    (hrest : ∀ side : RestAfterAcceptance.Side,
      (∫ p, (RestAfterAcceptance.rest side p S.u S.v : ℝ)
        ∂(InitialAsymptotics.law S).toMeasure) ≤ Kr) :
    FullPacket (InitialAsymptotics.law S) S.b S.u S.v (InitialAsymptotics.commonScale S)
      (InitialAsymptotics.scalingConstant A B C ζ + Kr)
      (1 + 2 * InitialAsymptotics.meanCoefficient A B C * Kr + Kr ^ 2) := by
  have hfirst := rank_mean_decomposition (InitialAsymptotics.law S) .first S.u S.v
  have hsecond := rank_mean_decomposition (InitialAsymptotics.law S) .second S.u S.v
  have hr0 (side : RestAfterAcceptance.Side) : 0 ≤ ∫ p,
      (RestAfterAcceptance.rest side p S.u S.v : ℝ) ∂(InitialAsymptotics.law S).toMeasure :=
    integral_nonneg (fun p ↦ Nat.cast_nonneg _)
  have hm0 : 0 ≤ InitialAsymptotics.meanCoefficient A B C * Real.log n := by
    have hi : 0 ≤ InitialAsymptotics.firstMean S := integral_nonneg (fun p ↦ Nat.cast_nonneg _)
    exact hi.trans H.first_upper
  refine ⟨?_, ?_, ?_⟩
  · simp only [RestAfterAcceptance.man, RestAfterAcceptance.initialCount] at hfirst
    rw [hfirst]
    have he := H.first_scaling
    change |(∫ p, (InitialPhase.A1 p S.u S.v : ℝ)
      ∂(InitialAsymptotics.law S).toMeasure) - _| ≤ _ at he
    rw [show (∫ p, (InitialPhase.A1 p S.u S.v : ℝ) ∂(InitialAsymptotics.law S).toMeasure) +
      (∫ p, (RestAfterAcceptance.rest .first p S.u S.v : ℝ) ∂(InitialAsymptotics.law S).toMeasure) -
      InitialAsymptotics.commonScale S / (S.b S.u : ℝ) =
      ((∫ p, (InitialPhase.A1 p S.u S.v : ℝ) ∂(InitialAsymptotics.law S).toMeasure) -
        InitialAsymptotics.commonScale S / (S.b S.u : ℝ)) +
      (∫ p, (RestAfterAcceptance.rest .first p S.u S.v : ℝ)
        ∂(InitialAsymptotics.law S).toMeasure) by ring]
    exact (abs_add_le _ _).trans (by rw [abs_of_nonneg (hr0 .first)]; linarith [hrest .first])
  · simp only [RestAfterAcceptance.man, RestAfterAcceptance.initialCount] at hsecond
    rw [hsecond]
    have he := H.second_scaling
    change |(∫ p, (InitialPhase.A2 p S.u S.v : ℝ)
      ∂(InitialAsymptotics.law S).toMeasure) - _| ≤ _ at he
    rw [show (∫ p, (InitialPhase.A2 p S.u S.v : ℝ) ∂(InitialAsymptotics.law S).toMeasure) +
      (∫ p, (RestAfterAcceptance.rest .second p S.u S.v : ℝ)
        ∂(InitialAsymptotics.law S).toMeasure) -
      InitialAsymptotics.commonScale S / (S.b S.v : ℝ) =
      ((∫ p, (InitialPhase.A2 p S.u S.v : ℝ) ∂(InitialAsymptotics.law S).toMeasure) -
        InitialAsymptotics.commonScale S / (S.b S.v : ℝ)) +
      (∫ p, (RestAfterAcceptance.rest .second p S.u S.v : ℝ)
        ∂(InitialAsymptotics.law S).toMeasure) by ring]
    exact (abs_add_le _ _).trans (by rw [abs_of_nonneg (hr0 .second)]; linarith [hrest .second])
  · have hc := G2Moments.covariance_add_nonnegative_lower_of_means
      (InitialAsymptotics.law S).toMeasure
      (fun p ↦ (InitialPhase.A1 p S.u S.v : ℝ))
      (fun p ↦ (RestAfterAcceptance.rest .first p S.u S.v : ℝ))
      (fun p ↦ (InitialPhase.A2 p S.u S.v : ℝ))
      (fun p ↦ (RestAfterAcceptance.rest .second p S.u S.v : ℝ))
      (G2Deconditioning.memLp_finite _ _) (G2Deconditioning.memLp_finite _ _)
      (G2Deconditioning.memLp_finite _ _) (G2Deconditioning.memLp_finite _ _)
      (fun p ↦ Nat.cast_nonneg _) (fun p ↦ Nat.cast_nonneg _)
      (fun p ↦ Nat.cast_nonneg _) (fun p ↦ Nat.cast_nonneg _) hm0 hKr
      H.first_upper H.second_upper (hrest .first) (hrest .second) H.covariance_lower
    have hx : (fun p ↦ (InitialPhase.A1 p S.u S.v : ℝ)) +
        (fun p ↦ (RestAfterAcceptance.rest .first p S.u S.v : ℝ)) =
          fun p ↦ (RankTail.rank p S.u : ℝ) := by
      funext p
      exact (rank_decomposition .first p S.u S.v).symm
    have hy : (fun p ↦ (InitialPhase.A2 p S.u S.v : ℝ)) +
        (fun p ↦ (RestAfterAcceptance.rest .second p S.u S.v : ℝ)) =
          fun p ↦ (RankTail.rank p S.v : ℝ) := by
      funext p
      exact (rank_decomposition .second p S.u S.v).symm
    rw [hx, hy] at hc
    have hn : 0 ≤ (1 + Kr ^ 2) * (Real.log n - 1) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith

/-- All supported smooth actual setup labels eventually carry the full-rank packet. -/
theorem eventually_good_fullPacket {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ (a b : Fin n → ℝ≥0)
      (_ha1 : ∀ w, 1 ≤ (a w : ℝ)) (_haA : ∀ w, (a w : ℝ) ≤ A)
      (_hb1 : ∀ m, 1 ≤ (b m : ℝ)) (_hbB : ∀ m, (b m : ℝ) ≤ B)
      (u v : Fin n) (_huv : u ≠ v) (h : PairStates.Label n)
      (_hh : PairStates.Good (Continuation.market a b) b A u v h),
      FullPacket (PairStates.future (Continuation.market a b) u v h) b u v
        (PairStates.globalScale a b A u v h) (meanError A B)
          (conditionalCovarianceCoefficient A B) := by
  obtain ⟨hC, _, _, _, hR, _, _, _, _, _⟩ := coefficient_signs hA hB
  have hz := (SmoothSetup.setup_constants hA).1
  have hk := (SmoothSetup.setup_constants hA).2.1
  filter_upwards [PairStates.eventually_good_packet hA hB,
    RestAfterAcceptance.eventually_uniform_rest_integrals hA hB hC hk hz,
    eventually_ge_atTop 8, ContinuationAsymptotics.eventually_one_le_log]
    with n hpacket hrest hn hlog a b ha1 haA hb1 hbB u v huv h hh
  let S := PairStates.setting a b ha1 haA hb1 hbB u v huv h hh
  let T := restSetting S hn hlog hA hB hC hz hk
  have hr : ∀ side : RestAfterAcceptance.Side,
      (∫ p, (RestAfterAcceptance.rest side p S.u S.v : ℝ) ∂(InitialAsymptotics.law S).toMeasure) ≤
        restCoefficient A B := by
    intro side
    exact hrest T rfl rfl rfl rfl rfl side
  rw [PairStates.globalScale_good a b ha1 haA hb1 hbB u v huv h hh]
  exact fullPacket_of_initial_rest S (hpacket a b ha1 haA hb1 hbB u v huv h hh) hlog hR.le hr

/-- A full-rank packet gives a uniform popularity-weighted pair-mean bound. -/
theorem weighted_error_of_packet {n : ℕ} (ν : PMF (Profile n)) (b : Fin n → ℝ≥0)
    (u v : Fin n) {Λ K C B : ℝ} (hK : 0 ≤ K)
    (hb1 : ∀ m, 1 ≤ (b m : ℝ)) (hbB : ∀ m, (b m : ℝ) ≤ B)
    (H : FullPacket ν b u v Λ K C) :
    |(b u : ℝ) * (∫ p, (RankTail.rank p u : ℝ) ∂ν.toMeasure) -
      (b v : ℝ) * (∫ p, (RankTail.rank p v : ℝ) ∂ν.toMeasure)| ≤ 2 * B * K := by
  have hbu : 0 < (b u : ℝ) := by linarith [hb1 u]
  have hbv : 0 < (b v : ℝ) := by linarith [hb1 v]
  have he : (b u : ℝ) * (∫ p, (RankTail.rank p u : ℝ) ∂ν.toMeasure) -
      (b v : ℝ) * (∫ p, (RankTail.rank p v : ℝ) ∂ν.toMeasure) =
      (b u : ℝ) * ((∫ p, (RankTail.rank p u : ℝ) ∂ν.toMeasure) - Λ / (b u : ℝ)) -
      (b v : ℝ) * ((∫ p, (RankTail.rank p v : ℝ) ∂ν.toMeasure) - Λ / (b v : ℝ)) := by
    field_simp
    ring
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_mul, abs_of_pos hbu, abs_of_pos hbv]
  have hu := (mul_le_mul_of_nonneg_left H.first_mean hbu.le).trans
    (mul_le_mul_of_nonneg_right (hbB u) hK)
  have hv := (mul_le_mul_of_nonneg_left H.second_mean hbv.le).trans
    (mul_le_mul_of_nonneg_right (hbB v) hK)
  nlinarith

/-- Good actual setup labels form a concrete finite subset for deconditioning. -/
noncomputable def good {n : ℕ} (a b : Fin n → ℝ≥0) (A : ℝ) (u v : Fin n) :
    Finset (PairStates.Label n) := by
  classical
  exact Finset.univ.filter (PairStates.Good (Continuation.market a b) b A u v)

/-- Finite good-label membership is exactly the proved source smoothness predicate. -/
theorem mem_good {n : ℕ} (a b : Fin n → ℝ≥0) (A : ℝ) (u v : Fin n)
    (h : PairStates.Label n) : h ∈ good a b A u v ↔
      PairStates.Good (Continuation.market a b) b A u v h := by
  classical
  simp [good]

/-- The bad-label probability is the exact finite setup failure mass. -/
theorem bad_probability_eq {n : ℕ} (a b : Fin n → ℝ≥0) (A : ℝ) (u v : Fin n) :
    (PairStates.law (Continuation.market a b) u v).toMeasure.real
      {h | h ∉ good a b A u v} =
    (eventMass (PairStates.law (Continuation.market a b) u v)
      {h | ¬PairStates.Good (Continuation.market a b) b A u v h}).toReal := by
  rw [eventMass_eq_toMeasure _ _ (by trivial)]
  congr 1
  ext h
  simp only [Set.mem_ofPred_eq, mem_good]

/-- Each actual rank lies between zero and n on every original profile. -/
theorem rank_bounds {n : ℕ} (p : Profile n) (m : Fin n) :
    0 ≤ (RankTail.rank p m : ℝ) ∧ (RankTail.rank p m : ℝ) ≤ n := by
  exact ⟨Nat.cast_nonneg _, by exact_mod_cast terminal_next_le p m⟩

/-- The chosen real clipping threshold has the actual global polynomial rank tail. -/
theorem eventually_global_rank_tails {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ (a b : Fin n → ℝ≥0),
      (∀ w, 1 ≤ (a w : ℝ)) → (∀ w, (a w : ℝ) ≤ A) →
      (∀ m, 1 ≤ (b m : ℝ)) → (∀ m, (b m : ℝ) ≤ B) → ∀ m : Fin n,
      (Continuation.market a b).toMeasure.real
        {p | clipCoefficient A B * (Real.log n) ^ 2 < (RankTail.rank p m : ℝ)} ≤
          5 * (n : ℝ) ^ (-(4 : ℝ)) := by
  obtain ⟨_, _, hL, _, _, hK, _, _, _, _⟩ := coefficient_signs hA hB
  filter_upwards [RankTail.eventually_maxRank_measure_tail hA hB (by norm_num : (0 : ℝ) ≤ 4)]
    with n htail a b ha1 haA hb1 hbB m
  have hcoef : RankTail.rankCoefficient A B 4 ≤ clipCoefficient A B := by
    dsimp only [clipCoefficient]
    linarith
  have hsub : {p : Profile n |
      clipCoefficient A B * (Real.log n) ^ 2 < (RankTail.rank p m : ℝ)} ⊆
        {p | RankTail.rankCoefficient A B 4 * (Real.log n) ^ 2 ≤ (RankTail.maxRank p : ℝ)} := by
    intro p hp
    have hr : (RankTail.rank p m : ℝ) ≤ (RankTail.maxRank p : ℝ) := by
      exact_mod_cast (Finset.le_sup (s := Finset.univ) (f := RankTail.rank p) (Finset.mem_univ m))
    exact (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)).trans (hp.le.trans hr)
  exact (measureReal_mono hsub).trans (htail a b ha1 haA hb1 hbB)

/-- Exact global weighted-mean reduction, charging bad states through clipping and global tails. -/
theorem weighted_mean_mixture_bound {n : ℕ} (a b : Fin n → ℝ≥0) {A B : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hb1 : ∀ m, 1 ≤ (b m : ℝ))
    (hbB : ∀ m, (b m : ℝ) ≤ B) (u v : Fin n)
    (hfull : ∀ h ∈ good a b A u v,
      FullPacket (PairStates.future (Continuation.market a b) u v h) b u v
        (PairStates.globalScale a b A u v h) (meanError A B)
          (conditionalCovarianceCoefficient A B)) :
    |(b u : ℝ) * (∫ p, (RankTail.rank p u : ℝ) ∂(Continuation.market a b).toMeasure) -
      (b v : ℝ) * (∫ p, (RankTail.rank p v : ℝ) ∂(Continuation.market a b).toMeasure)| ≤
      2 * B * meanError A B + 2 * B * (clipCoefficient A B * (Real.log n) ^ 2) *
        (PairStates.law (Continuation.market a b) u v).toMeasure.real {h | h ∉ good a b A u v} +
      B * n * ((Continuation.market a b).toMeasure.real
        {p | clipCoefficient A B * (Real.log n) ^ 2 < (RankTail.rank p u : ℝ)} +
      (Continuation.market a b).toMeasure.real
        {p | clipCoefficient A B * (Real.log n) ^ 2 < (RankTail.rank p v : ℝ)}) := by
  obtain ⟨_, _, _, _, _, hK, _, hD, _, _⟩ := coefficient_signs hA hB
  have hm := MixtureBounds.weighted_global_mean_difference_le
    (PairStates.law (Continuation.market a b) u v)
    (PairStates.future (Continuation.market a b) u v) (good a b A u v)
    (fun p ↦ (RankTail.rank p u : ℝ)) (fun p ↦ (RankTail.rank p v : ℝ))
    (β₁ := (b u : ℝ)) (β₂ := (b v : ℝ)) (B := B) (N := (n : ℝ))
    (cap := clipCoefficient A B * (Real.log n) ^ 2) (K := 2 * B * meanError A B)
    ⟨(b u).coe_nonneg, hbB u⟩ ⟨(b v).coe_nonneg, hbB v⟩ (Nat.cast_nonneg n)
    (mul_nonneg hD.le (sq_nonneg _)) (by positivity)
    (fun p ↦ rank_bounds p u) (fun p ↦ rank_bounds p v)
    (fun h hh ↦ weighted_error_of_packet _ b u v hK.le hb1 hbB (hfull h hh))
  rw [PairStates.bind_future] at hm
  exact hm

/-- Masked full-rank means and actual covariance lower bounds give the corrected mixture bound.
The positive variance of the common conditional scale is retained in this exact inequality. -/
theorem covariance_mixture_bound {n : ℕ} (a b : Fin n → ℝ≥0) {A B : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hlog : 1 ≤ Real.log n)
    (hb1 : ∀ m, 1 ≤ (b m : ℝ)) (u v : Fin n)
    (hfull : ∀ h ∈ good a b A u v,
      FullPacket (PairStates.future (Continuation.market a b) u v h) b u v
        (PairStates.globalScale a b A u v h) (meanError A B)
          (conditionalCovarianceCoefficient A B))
    (hscale : ∀ h, |PairStates.globalScale a b A u v h| ≤ scaleCoefficient A B * Real.log n) :
    -(conditionalCovarianceCoefficient A B) * Real.log n +
      (b u : ℝ)⁻¹ * (b v : ℝ)⁻¹ * variance (PairStates.globalScale a b A u v)
        (PairStates.law (Continuation.market a b) u v).toMeasure -
      2 * ((b u : ℝ)⁻¹ + (b v : ℝ)⁻¹) * (scaleCoefficient A B * Real.log n) * meanError A B -
      2 * meanError A B ^ 2 - 5 * (clipCoefficient A B * (Real.log n) ^ 2) ^ 2 *
        (PairStates.law (Continuation.market a b) u v).toMeasure.real {h | h ∉ good a b A u v} -
      (4 * (n : ℝ) ^ 2 + 2 * (clipCoefficient A B * (Real.log n) ^ 2) * n) *
        ((Continuation.market a b).toMeasure.real
          {p | clipCoefficient A B * (Real.log n) ^ 2 < (RankTail.rank p u : ℝ)} +
        (Continuation.market a b).toMeasure.real
          {p | clipCoefficient A B * (Real.log n) ^ 2 < (RankTail.rank p v : ℝ)}) ≤
      covariance (fun p ↦ (RankTail.rank p u : ℝ)) (fun p ↦ (RankTail.rank p v : ℝ))
        (Continuation.market a b).toMeasure := by
  classical
  obtain ⟨_, _, hL, _, _, hK, hC, hD, _, _⟩ := coefficient_signs hA hB
  let ν := PairStates.law (Continuation.market a b) u v
  let f := PairStates.future (Continuation.market a b) u v
  let g := good a b A u v
  let Λ := PairStates.globalScale a b A u v
  let X : Profile n → ℝ := fun p ↦ (RankTail.rank p u : ℝ)
  let Y : Profile n → ℝ := fun p ↦ (RankTail.rank p v : ℝ)
  let e₁ : PairStates.Label n → ℝ := fun h ↦
    (if h ∈ g then ∫ p, X p ∂(f h).toMeasure else 0) - (b u : ℝ)⁻¹ * Λ h
  let e₂ : PairStates.Label n → ℝ := fun h ↦
    (if h ∈ g then ∫ p, Y p ∂(f h).toMeasure else 0) - (b v : ℝ)⁻¹ * Λ h
  have hu : 0 < (b u : ℝ) := by linarith [hb1 u]
  have hv : 0 < (b v : ℝ) := by linarith [hb1 v]
  have hau : (b u : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hb1 u)
  have he₁ : ∀ h, |e₁ h| ≤ meanError A B := by
    intro h
    by_cases hh : h ∈ g
    · have hm := (hfull h hh).first_mean
      simpa only [e₁, ite_eq_left hh, div_eq_mul_inv, mul_comm] using hm
    · have hnot : ¬PairStates.Good (Continuation.market a b) b A u v h :=
        fun hp ↦ hh ((mem_good a b A u v h).mpr hp)
      simp only [e₁, ite_eq_right hh, Λ, PairStates.globalScale, ite_eq_right hnot, mul_zero,
        sub_self, abs_zero]
      exact hK.le
  have he₂ : ∀ h, |e₂ h| ≤ meanError A B := by
    intro h
    by_cases hh : h ∈ g
    · have hm := (hfull h hh).second_mean
      simpa only [e₂, ite_eq_left hh, div_eq_mul_inv, mul_comm] using hm
    · have hnot : ¬PairStates.Good (Continuation.market a b) b A u v h :=
        fun hp ↦ hh ((mem_good a b A u v h).mpr hp)
      simp only [e₂, ite_eq_right hh, Λ, PairStates.globalScale, ite_eq_right hnot, mul_zero,
        sub_self, abs_zero]
      exact hK.le
  have hcap : (b u : ℝ)⁻¹ * (scaleCoefficient A B * Real.log n) + meanError A B ≤
      clipCoefficient A B * (Real.log n) ^ 2 := by
    have hr := RankTail.rankCoefficient_pos hA hB (by norm_num : (0 : ℝ) ≤ 4)
    have hcoef : scaleCoefficient A B + meanError A B ≤ clipCoefficient A B := by
      dsimp only [clipCoefficient]
      linarith
    have hs1 : Real.log n ≤ (Real.log n) ^ 2 := by nlinarith
    have hs2 : 1 ≤ (Real.log n) ^ 2 := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right hau
      (mul_nonneg hL.le (by linarith : 0 ≤ Real.log n))
    have h2 := mul_le_mul_of_nonneg_left hs1 hL.le
    have h3 := mul_le_mul_of_nonneg_left hs2 hK.le
    have h4 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (Real.log n))
    nlinarith
  have hc := G2Deconditioning.covariance_bind_lower_via_clipping_good_states ν f g X Y Λ e₁ e₂
    (inv_nonneg.mpr hu.le) (inv_nonneg.mpr hv.le) (Nat.cast_nonneg n)
    (mul_nonneg hD.le (sq_nonneg _)) (mul_nonneg hL.le (by linarith : 0 ≤ Real.log n))
    hK.le (mul_nonneg hC.le (by linarith : 0 ≤ Real.log n))
    (fun p ↦ rank_bounds p u) (fun p ↦ rank_bounds p v) hscale he₁ he₂ hcap
    (fun h ↦ by dsimp only [e₁]; ring) (fun h ↦ by dsimp only [e₂]; ring)
    (fun h hh ↦ by simpa only [neg_mul] using (hfull h hh).covariance_lower)
  dsimp only [ν, f, g, X, Y, Λ] at hc
  rw [PairStates.bind_future] at hc
  simpa only [neg_mul] using hc

/-- The global weighted-mean correction vanishes using bad mass and GLOBAL rank tails. -/
theorem eventually_mean_correction_le_one (B D : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop, 26 * B * D * (Real.log n) ^ 2 * (n : ℝ) ^ (-κ) +
      10 * B * n * (n : ℝ) ^ (-(4 : ℝ)) ≤ 1 := by
  have hbad := MixtureBounds.tendsto_log_pow_mul_rpow_neg 2 hκ
  have hcross : Tendsto (fun n : ℕ ↦ (n : ℝ) * (n : ℝ) ^ (-(4 : ℝ))) atTop (𝓝 0) := by
    have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    simp only [Function.comp_apply]
    rw [show -(3 : ℝ) = 1 + (-(4 : ℝ)) by norm_num, Real.rpow_add hnpos, Real.rpow_one]
  have ht : Tendsto (fun n : ℕ ↦
      26 * B * D * (Real.log n) ^ 2 * (n : ℝ) ^ (-κ) +
        10 * B * n * (n : ℝ) ^ (-(4 : ℝ))) atTop (𝓝 0) := by
    convert (hbad.const_mul (26 * B * D)).add (hcross.const_mul (10 * B)) using 1
    · ext n
      ring
    · norm_num
  exact (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun n hn ↦ hn.le)

/-- Uniform actual original-PR pair means and covariances, with no stochastic premise.
The conditional-mean variance is retained until its nonnegativity is used by the numerical gate. -/
theorem eventually_pair_moments {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ (a b : Fin n → ℝ≥0),
      (∀ w, 1 ≤ (a w : ℝ)) → (∀ w, (a w : ℝ) ≤ A) →
      (∀ m, 1 ≤ (b m : ℝ)) → (∀ m, (b m : ℝ) ≤ B) →
      TierConcentration.ComparableMeans a b (meanConstant A B) ∧
        TierConcentration.CovarianceLower a b (covarianceConstant A B) := by
  obtain ⟨_, _, hL, _, _, hK, hC, hD, hMean, _⟩ := coefficient_signs hA hB
  have hκ := (SmoothSetup.setup_constants hA).2.1
  have hBpos : 0 < B := by linarith
  filter_upwards [eventually_good_fullPacket hA hB, PairStates.eventually_globalScale_bound hA hB,
    PairStates.eventually_bad_mass hA hB, eventually_global_rank_tails hA hB,
    eventually_mean_correction_le_one B (clipCoefficient A B) hκ,
    MixtureBounds.eventually_covariance_numeric_lower (conditionalCovarianceCoefficient A B)
      (scaleCoefficient A B) (meanError A B) (clipCoefficient A B) 13 5 hL.le hK.le hD.le
      hκ (by norm_num : (2 : ℝ) < 4), ContinuationAsymptotics.eventually_one_le_log]
    with n hfull hscale hbad htail hmeanNum hcovNum hlog a b ha1 haA hb1 hbB
  have hpair (u v : Fin n) (huv : u ≠ v) :
      |(b u : ℝ) * (∫ p, (RankTail.rank p u : ℝ) ∂(Continuation.market a b).toMeasure) -
        (b v : ℝ) * (∫ p, (RankTail.rank p v : ℝ) ∂(Continuation.market a b).toMeasure)| ≤
          meanConstant A B ∧
      -(covarianceConstant A B) * Real.log n ≤ covariance
        (fun p ↦ (RankTail.rank p u : ℝ)) (fun p ↦ (RankTail.rank p v : ℝ))
          (Continuation.market a b).toMeasure := by
    have hfull' : ∀ h ∈ good a b A u v,
        FullPacket (PairStates.future (Continuation.market a b) u v h) b u v
          (PairStates.globalScale a b A u v h) (meanError A B)
            (conditionalCovarianceCoefficient A B) := by
      intro h hh
      exact hfull a b ha1 haA hb1 hbB u v huv h ((mem_good a b A u v h).mp hh)
    have hscale' : ∀ h, |PairStates.globalScale a b A u v h| ≤
        scaleCoefficient A B * Real.log n := by
      intro h
      simpa only [scaleCoefficient, div_eq_mul_inv, mul_comm, one_mul] using
        hscale a b ha1 haA hb1 hbB u v huv h
    have hδ : (PairStates.law (Continuation.market a b) u v).toMeasure.real
        {h | h ∉ good a b A u v} ≤ 13 * (n : ℝ) ^ (-SmoothSetup.setupExponent A) := by
      rw [bad_probability_eq]
      exact hbad a b ha1 haA hb1 hbB u v huv
    have htu := htail a b ha1 haA hb1 hbB u
    have htv := htail a b ha1 haA hb1 hbB v
    constructor
    · have hm := weighted_mean_mixture_bound a b hA hB hb1 hbB u v hfull'
      have hb := mul_le_mul_of_nonneg_left hδ
        (by positivity : 0 ≤ 2 * B * (clipCoefficient A B * (Real.log n) ^ 2))
      have hs : (Continuation.market a b).toMeasure.real
          {p | clipCoefficient A B * (Real.log n) ^ 2 < (RankTail.rank p u : ℝ)} +
          (Continuation.market a b).toMeasure.real
          {p | clipCoefficient A B * (Real.log n) ^ 2 < (RankTail.rank p v : ℝ)} ≤
            10 * (n : ℝ) ^ (-(4 : ℝ)) := by linarith
      have ht := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ B * n)
      dsimp only [meanConstant]
      nlinarith
    · have hc := covariance_mixture_bound a b hA hB hlog hb1 u v hfull' hscale'
      have hu : (b u : ℝ)⁻¹ ∈ Set.Icc 0 1 :=
        ⟨inv_nonneg.mpr (b u).coe_nonneg, inv_le_one_of_one_le₀ (hb1 u)⟩
      have hv : (b v : ℝ)⁻¹ ∈ Set.Icc 0 1 :=
        ⟨inv_nonneg.mpr (b v).coe_nonneg, inv_le_one_of_one_le₀ (hb1 v)⟩
      exact hcovNum _ _ _ _ _ _ _ hu hv (variance_nonneg _ _) hδ htu htv hc
  constructor
  · intro u v
    by_cases huv : u = v
    · subst v
      simp only [sub_self, abs_zero]
      exact hMean.le
    · exact (hpair u v huv).1
  · intro u v huv
    exact (hpair u v huv).2

/-- Positive fixed coefficients precede the population quantifier in the unconditional
pair result. -/
theorem uniform_pair_moments {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ∀ (a b : Fin n → ℝ≥0),
        (∀ w, 1 ≤ (a w : ℝ)) → (∀ w, (a w : ℝ) ≤ A) →
        (∀ m, 1 ≤ (b m : ℝ)) → (∀ m, (b m : ℝ) ≤ B) →
        TierConcentration.ComparableMeans a b K ∧ TierConcentration.CovarianceLower a b C := by
  obtain ⟨_, _, _, _, _, _, _, _, hK, hC⟩ := coefficient_signs hA hB
  exact ⟨meanConstant A B, covarianceConstant A B, hK, hC, eventually_pair_moments hA hB⟩

end Ashlagi.GlobalPairMoments
