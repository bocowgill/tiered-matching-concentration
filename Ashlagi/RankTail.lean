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

public import Ashlagi.ContinuationAsymptotics
public import Ashlagi.PriorityProtocols
public import Ashlagi.SurvivalKernel

/-! # Actual PR rank tails from leave-one-man-last continuation

All setup histories and continuation laws are generated from the original profile. The good
setup bound is paid for by an unconditional genuine-proposal completion tail.
-/

@[expose] public section

namespace Ashlagi.RankTail

open StableMarriage Ashlagi.Ordinal Protocols ProfileHistories FiniteConditioning
open ContinuationAsymptotics
open scoped ENNReal NNReal

/-- A man's actual PR rank is his number of genuine proposals through the terminal match. -/
noncomputable def rank {n : ℕ} (p : Profile n) (m : Fin n) : ℕ :=
  (deferredAcceptance p).next m

/-- The total number of genuine proposals in the exact original PR execution. -/
noncomputable def total {n : ℕ} (p : Profile n) : ℕ := potential (deferredAcceptance p)

/-- One genuine proposer edge contributes one public observation, with pauses contributing none. -/
theorem profile_potential_le_time {n : ℕ} (C : Protocol n) (p : Profile n) (t : ℕ) :
    potential (recordState (Protocols.profileTranscript C p t)) ≤ t := by
  induction t with
  | zero => simp [Protocols.profileTranscript, Protocols.transcript, recordState, potential]
  | succ t ih =>
    change potential (recordState (observation C p.manRank (profilePriorities p)
      (Protocols.profileTranscript C p t) :: Protocols.profileTranscript C p t)) ≤ t + 1
    cases he : observation C p.manRank (profilePriorities p)
        (Protocols.profileTranscript C p t) with
    | none => exact ih.trans (Nat.le_succ t)
    | some e =>
      rcases e with ⟨q, accepted⟩
      rw [Continuation.potential_record]
      omega

/-- A full-entrant canonical protocol is work conserving at every actual visible history. -/
theorem full_workConserving {n : ℕ} (μ : PMF (Profile n)) :
    EmptySurvival.WorkConserving μ (activeProtocol Finset.univ) [] := by
  intro h _ hh hempty hnone
  have ht := (activeProtocol_none_iff_terminal Finset.univ h).mp hnone
  obtain ⟨w, hw⟩ := hempty
  have heq : ∀ m, (recordState h).held w ≠ some m := by simp [hw]
  have hselected : ∃ m, Schedules.Eligible Finset.univ (recordState h) m := by
    obtain ⟨p, hp⟩ := ActualCompeting.exists_profile μ (activeProtocol Finset.univ) h hh
    have hr := profileTranscript_reachable (activeProtocol Finset.univ) p Finset.univ h.length
      (uses_univ _ _)
    rw [hp] at hr
    have hv := Schedules.reachable_valid p Finset.univ hr
    by_contra hn
    have hterminal : Schedules.Terminal Finset.univ (recordState h) := by
      intro m hm
      exact hn ⟨m, hm⟩
    have hall (m : Fin n) : ∃ v, (recordState h).held v = some m :=
      Schedules.terminal_active_held p Finset.univ hr hterminal m (Finset.mem_univ m)
    choose f hf using hall
    have hinj : Function.Injective f := by
      intro a b hab
      exact Option.some.inj ((hf a).symm.trans (by simpa [hab] using hf b))
    obtain ⟨m, hm⟩ := Finite.surjective_of_injective hinj w
    exact heq m (hm ▸ hf m)
  obtain ⟨m, hm⟩ := hselected
  exact ht m hm

/-- Initial conditioning carries no information. -/
theorem lawAt_nil {n : ℕ} (μ : PMF (Profile n)) (C : Protocol n) : lawAt μ C [] = μ := by
  have he : event C [] = Set.univ := by
    ext p
    simp [event, Protocols.profileTranscript, Protocols.transcript]
  ext p
  have hi := eventMass_mul_condition μ (event C []) p
  simpa only [lawAt, he, StoppedProcess.Process.eventMass_univ, one_mul,
    Set.indicator_univ] using hi

/-- A full completion before time H would use at most H genuine proposals. -/
theorem total_gt_implies_incomplete {n : ℕ} (p : Profile n) (H : ℕ)
    (hH : H < total p) :
    ∃ w, (recordState (Protocols.profileTranscript (activeProtocol Finset.univ) p H)).held w =
      none := by
  classical
  let h := Protocols.profileTranscript (activeProtocol Finset.univ) p H
  have hp : Protocols.profileTranscript (activeProtocol Finset.univ) p h.length = h := by
    simp only [h, Protocols.profileTranscript, Protocols.transcript_length]
  by_contra hn
  have hs : selected (activeProtocol Finset.univ) h = none := by
    cases hs : selected (activeProtocol Finset.univ) h with
    | none => rfl
    | some m => exact False.elim (hn (VisitBounds.exists_empty_of_selected _ p h hp m hs))
  have ht := (activeProtocol_none_iff_terminal Finset.univ h).mp hs
  have heq := profileTranscript_terminal_eq_pr (activeProtocol Finset.univ) p H ht
  have hb := profile_potential_le_time (activeProtocol Finset.univ) p H
  rw [heq] at hb
  exact (not_lt_of_ge hb) hH

/-- The full original genuine-proposal total has an unconditional coupon-completion tail. -/
theorem total_tail {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A : ℝ}
    (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (H : ℕ) :
    (eventMass (VisitBounds.profileLaw a b) {p | H < total p}).toReal ≤
      n * Real.exp (-(H : ℝ) / (A * n)) := by
  have hh : eventMass (EmptySurvival.market a b) (event (activeProtocol Finset.univ) []) ≠ 0 := by
    have he : event (activeProtocol (n := n) Finset.univ) [] = Set.univ := by
      ext p
      simp [event, Protocols.profileTranscript, Protocols.transcript]
    rw [he, StoppedProcess.Process.eventMass_univ]
    norm_num
  have ht := EmptySurvival.incomplete_probability_le_exp hn a b hA ha1 haA hb
    (activeProtocol Finset.univ) [] (full_workConserving _) hh H n (by
      simp [VisitBounds.emptyWomen, recordState])
  rw [lawAt_nil] at ht
  change (eventMass (VisitBounds.profileLaw a b) _).toReal ≤ _ at ht
  apply le_trans _ ht
  rw [← VisitBounds.expectation_indicator_one, ← VisitBounds.expectation_indicator_one]
  apply VisitBounds.expectation_mono_support
  intro p _
  by_cases hp : H < total p
  · have he := total_gt_implies_incomplete p H hp
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, List.length_nil, Nat.zero_add,
      ite_eq_left hp, ite_eq_left he, le_refl]
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hp]
    split_ifs <;> norm_num

/-- The literal completed market with the designated man still suspended. -/
noncomputable def setup {n : ℕ} (m : Fin n) (p : Profile n) : List (Entry n) :=
  Protocols.profileTranscript (activeProtocol (Finset.univ.erase m)) p (n * n)

/-- The leave-one-man-last setup always has precisely its recorded public length. -/
theorem setup_length {n : ℕ} (m : Fin n) (p : Profile n) : (setup m p).length = n * n :=
  Protocols.transcript_length _ _ _ _

/-- The incoming man has made no proposals in the leave-one-out setup. -/
theorem setup_counter_zero {n : ℕ} (m : Fin n) (p : Profile n) :
    (recordState (setup m p)).next m = 0 :=
  (activeProtocol_support (Finset.univ.erase m) p (n * n)).1 m (by simp)

/-- The leave-one-out setup uses no more genuine proposals than the exact PR terminal run. -/
theorem setup_potential_le_total {n : ℕ} (m : Fin n) (p : Profile n) :
    potential (recordState (setup m p)) ≤ total p := by
  apply Finset.sum_le_sum
  intro k _
  apply Continuation.profile_counter_le_pr (activeProtocol (Finset.univ.erase m)) p
    (setup m p)
  simp only [setup, Protocols.profileTranscript, Protocols.transcript_length]

/-- Exactly one woman is empty at the completed leave-one-man-out setup. -/
theorem setup_empty_card {n : ℕ} (m : Fin n) (p : Profile n) :
    (VisitBounds.emptyWomen (setup m p)).card = 1 := by
  classical
  let s := recordState (setup m p)
  have hr : Schedules.Reachable p (Finset.univ.erase m) s :=
    profileTranscript_reachable _ p _ _ (activeProtocol_uses _ _)
  have ht : Schedules.Terminal (Finset.univ.erase m) s := activeProtocol_terminal _ p
  have hc := (RawSemantics.terminal_iff_occupied_card p _ hr).mp ht
  have hfilter : (Finset.univ.filter fun w ↦ ¬ s.held w = none) =
      RawSemantics.occupied s := by
    ext w
    cases hw : s.held w <;> simp [RawSemantics.occupied, hw]
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun w ↦ s.held w = none)
  rw [hfilter, hc] at hsum
  simp only [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ,
    Fintype.card_fin] at hsum
  have hn : 1 ≤ n := by have hm := m.isLt; omega
  change (Finset.univ.filter fun w ↦ s.held w = none).card = 1
  omega

/-- Each setup observation fiber is precisely its literal original-profile prefix event. -/
theorem setup_fiber_eq {n : ℕ} (m : Fin n) (h : List (Entry n)) (hl : h.length = n * n) :
    {p | setup m p = h} = event (activeProtocol (Finset.univ.erase m)) h := by
  simp only [event, setup, hl]

/-- Every nonnull leave-one-out history has zero incoming counter and exactly one empty woman. -/
theorem setup_history_spec {n : ℕ} (μ : PMF (Profile n)) (m : Fin n) (h : List (Entry n))
    (hh : eventMass μ {p | setup m p = h} ≠ 0) :
    h.length = n * n ∧ (recordState h).next m = 0 ∧
      (VisitBounds.emptyWomen h).card = 1 := by
  obtain ⟨p, hp⟩ := (condition μ {p | setup m p = h}).support_nonempty
  rw [support_condition _ _ hh] at hp
  have he : setup m p = h := hp.1
  rw [← he]
  exact ⟨setup_length m p, setup_counter_zero m p, setup_empty_card m p⟩

/-- A good actual leave-one-out history supplies every deterministic field of Continuation.Setting.
Nonnullness is used only for its genuine revealed-prefix semantics. -/
noncomputable def setting {n : ℕ} (hn : 8 ≤ n) (a b : Fin n → ℝ≥0)
    {A B C K : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hlog : 1 ≤ Real.log n) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb1 : ∀ m, 1 ≤ (b m : ℝ)) (hbB : ∀ m, (b m : ℝ) ≤ B)
    (m : Fin n) (h : List (Entry n))
    (hh : eventMass (VisitBounds.profileLaw a b) {p | setup m p = h} ≠ 0)
    (hgood : (potential (recordState h) : ℝ) ≤ C * n * Real.log n) :
    Continuation.Setting n where
  a := a
  b := b
  setupProtocol := activeProtocol (Finset.univ.erase m)
  setup := h
  man := m
  A := A
  B := B
  C := C
  K := K
  L := Real.log n
  n_ge := hn
  A_ge := hA
  B_ge := hB
  C_nonneg := hC
  K_nonneg := hK
  L_ge := hlog
  a_ge := ha1
  a_le := haA
  b_ge := hb1
  b_le := hbB
  setup_nonnull := by
    have hl := (setup_history_spec (VisitBounds.profileLaw a b) m h hh).1
    rw [setup_fiber_eq m h hl] at hh
    exact hh
  setup_total := hgood
  setup_quarter := by
    have hz := (setup_history_spec (VisitBounds.profileLaw a b) m h hh).2.1
    rw [hz, Nat.cast_zero]
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  setup_empty := (setup_history_spec (VisitBounds.profileLaw a b) m h hh).2.2.le.trans (by decide)

/-- The designated continuation count equals the man's complete actual PR rank, since he
made no setup proposals. This identity holds for every original profile. -/
theorem setting_ordinaryCount_eq_rank {n : ℕ} (hn : 8 ≤ n) (a b : Fin n → ℝ≥0)
    {A B C K : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hlog : 1 ≤ Real.log n) (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb1 : ∀ m, 1 ≤ (b m : ℝ)) (hbB : ∀ m, (b m : ℝ) ≤ B)
    (m : Fin n) (h : List (Entry n))
    (hh : eventMass (VisitBounds.profileLaw a b) {p | setup m p = h} ≠ 0)
    (hgood : (potential (recordState h) : ℝ) ≤ C * n * Real.log n) (p : Profile n) :
    (setting hn a b hA hB hC hK hlog ha1 haA hb1 hbB m h hh hgood).ordinaryCount p =
      rank p m := by
  have hz := (setup_history_spec (VisitBounds.profileLaw a b) m h hh).2.1
  simp only [Continuation.Setting.ordinaryCount, setting, rank, hz, Nat.sub_zero]

/-- The good leave-one-out setup has a uniform actual conditional rank tail. -/
theorem eventually_conditional_rank_tail {A B C s : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hC : 0 ≤ C) (hs : 0 ≤ s) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (a b : Fin n → ℝ≥0),
      (∀ w, 1 ≤ (a w : ℝ)) → (∀ w, (a w : ℝ) ≤ A) →
      (∀ m, 1 ≤ (b m : ℝ)) → (∀ m, (b m : ℝ) ≤ B) →
      ∀ (m : Fin n) (h : List (Entry n)),
        eventMass (VisitBounds.profileLaw a b) {p | setup m p = h} ≠ 0 →
        (potential (recordState h) : ℝ) ≤ C * n * Real.log n →
        (eventMass (condition (VisitBounds.profileLaw a b) {p | setup m p = h})
          {p | threshold (tailCoefficient A B C s) n ≤ rank p m}).toReal ≤
            4 * (n : ℝ) ^ (-s) := by
  have hK := (coefficients_pos hA hB hC hs).1.le
  filter_upwards [eventually_uniform_canonical_bounds hA hB hC hs, eventually_one_le_log,
    Filter.eventually_ge_atTop 8] with n hbound hlog hn a b ha1 haA hb1 hbB m h hh hgood
  let S := setting hn a b hA hB hC hK hlog ha1 haA hb1 hbB m h hh hgood
  have ht := (hbound S rfl rfl rfl rfl rfl).2
  have heq : S.ordinaryCount = fun p ↦ rank p m := by
    funext p
    exact setting_ordinaryCount_eq_rank hn a b hA hB hC hK hlog ha1 haA hb1 hbB
      m h hh hgood p
  rw [heq] at ht
  have hl := (setup_history_spec (VisitBounds.profileLaw a b) m h hh).1
  rw [setup_fiber_eq m h hl]
  exact ht

/-- These proposal counts are the actual one-based partner ranks in the final PR matching. -/
theorem rank_eq_partner_rank {n : ℕ} (p : Profile n) (w m : Fin n)
    (hh : (deferredAcceptance p).held w = some m) :
    rank p m = (p.manRank m w).val + 1 :=
  (Schedules.reachable_valid p Finset.univ (Schedules.pr_terminal p).1).latest w m hh

/-- Monotonicity of literal finite-event probabilities. -/
theorem probability_mono {Ω : Type*} [Fintype Ω] (μ : PMF Ω) {E F : Set Ω}
    (hEF : E ⊆ F) : SurvivalKernel.probability μ E ≤ SurvivalKernel.probability μ F := by
  classical
  rw [SurvivalKernel.probability, SurvivalKernel.probability,
    ← VisitBounds.expectation_indicator_one, ← VisitBounds.expectation_indicator_one]
  apply VisitBounds.expectation_mono_support
  intro p _
  by_cases hp : p ∈ E
  · simp [hp, hEF hp]
  · simp only [Set.indicator_of_notMem hp]
    simp only [Set.indicator_apply]
    split_ifs <;> norm_num

/-- Multiplying the inverse (r+1) power by the market size gives the inverse r power. -/
theorem nat_mul_rpow {n : ℕ} (hn : 0 < n) (r : ℝ) :
    (n : ℝ) * (n : ℝ) ^ (-(r + 1)) = (n : ℝ) ^ (-r) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(r + 1)) := by rw [Real.rpow_one]
    _ = (n : ℝ) ^ ((1 : ℝ) + -(r + 1)) := (Real.rpow_add hn' _ _).symm
    _ = _ := by congr 1; ring

/-- A fixed setup budget dominating a genuine full-run global cap. -/
noncomputable def setupCoefficient (A r : ℝ) : ℝ := A * (r + 2) + 1

/-- The maximum-rank cutoff depends only on fixed normalized public score bounds and r. -/
noncomputable def rankCoefficient (A B r : ℝ) : ℝ :=
  tailCoefficient A B (setupCoefficient A r) (r + 1)

/-- Bad leave-one-out setup histories have their own unconditional polynomial probability.
The exceptional setup event is controlled by the full unchanged PR proposal total. -/
theorem bad_setup_probability {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0) {A r : ℝ}
    (hA : 1 ≤ A) (hr : 0 ≤ r) (hlog : 1 ≤ Real.log n)
    (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb : ∀ m, 0 < b m) (m : Fin n) :
    SurvivalKernel.probability (VisitBounds.profileLaw a b)
      {p | ¬ (potential (recordState (setup m p)) : ℝ) ≤
        setupCoefficient A r * n * Real.log n} ≤ (n : ℝ) ^ (-(r + 1)) := by
  have hApos : 0 < A := by linarith
  have hK : 0 ≤ A * (r + 2) := mul_nonneg hApos.le (by linarith)
  have hceil := Continuation.globalCap_le (show 1 ≤ n by omega) hK hlog
  have hsub : {p | ¬ (potential (recordState (setup m p)) : ℝ) ≤
      setupCoefficient A r * n * Real.log n} ⊆ {p | globalCap (A * (r + 2)) n < total p} := by
    intro p hp
    have hs := setup_potential_le_total m p
    have hs' : (potential (recordState (setup m p)) : ℝ) ≤ total p := by exact_mod_cast hs
    have hc : (globalCap (A * (r + 2)) n : ℝ) ≤
        setupCoefficient A r * n * Real.log n := hceil
    have ht : (globalCap (A * (r + 2)) n : ℝ) < total p := by
      dsimp only [Set.mem_ofPred_eq] at hp
      linarith
    exact_mod_cast ht
  apply (probability_mono (VisitBounds.profileLaw a b) hsub).trans
  have ht := total_tail hn a b hA ha1 haA hb (globalCap (A * (r + 2)) n)
  have hg := global_exp_le hApos hn (by linarith : 0 ≤ Real.log n)
    (le_refl (A * (r + 2)))
  rw [exp_neg_log_eq_rpow hn (r + 2)] at hg
  have hpow : (n : ℝ) * (n : ℝ) ^ (-(r + 2)) = (n : ℝ) ^ (-(r + 1)) := by
    rw [show -(r + 2) = -((r + 1) + 1) by ring]
    exact nat_mul_rpow hn (r + 1)
  exact ht.trans ((mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg n)).trans_eq hpow)

/-- Uniform per-man actual PR rank tail, with the bad-setup probability already paid for. -/
theorem eventually_rank_tail {A B r : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hr : 0 ≤ r) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (a b : Fin n → ℝ≥0),
      (∀ w, 1 ≤ (a w : ℝ)) → (∀ w, (a w : ℝ) ≤ A) →
      (∀ m, 1 ≤ (b m : ℝ)) → (∀ m, (b m : ℝ) ≤ B) → ∀ m : Fin n,
      (eventMass (VisitBounds.profileLaw a b)
        {p | threshold (rankCoefficient A B r) n ≤ rank p m}).toReal ≤
          5 * (n : ℝ) ^ (-(r + 1)) := by
  have hC : 0 ≤ setupCoefficient A r := by
    unfold setupCoefficient
    nlinarith
  filter_upwards [eventually_conditional_rank_tail hA hB hC (by linarith : 0 ≤ r + 1),
    eventually_one_le_log, Filter.eventually_ge_atTop 1]
    with n hconditional hlog hn a b ha1 haA hb1 hbB m
  have hn0 : 0 < n := by omega
  have hb : ∀ m, 0 < b m := fun m ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (hb1 m)
  let E : Set (Profile n) := {p | threshold (rankCoefficient A B r) n ≤ rank p m}
  let good : Set (List (Entry n)) := {h | (potential (recordState h) : ℝ) ≤
    setupCoefficient A r * n * Real.log n}
  have hm := SurvivalKernel.probability_le_of_conditional_on_good (VisitBounds.profileLaw a b)
    (setup m) good E (4 * (n : ℝ) ^ (-(r + 1))) (by positivity) (by
      intro h hh hg
      exact hconditional a b ha1 haA hb1 hbB m h hh hg)
  have hbad := bad_setup_probability hn0 a b hA hr hlog ha1 haA hb m
  change (eventMass (VisitBounds.profileLaw a b) E).toReal ≤ _
  change SurvivalKernel.probability (VisitBounds.profileLaw a b)
    {p | setup m p ∉ good} ≤ (n : ℝ) ^ (-(r + 1)) at hbad
  exact hm.trans (by linarith)

/-- A finite union of rank exceedances costs at most the sum of their actual probabilities. -/
theorem probability_exists_le_sum {n : ℕ} (μ : PMF (Profile n)) (E : Fin n → Set (Profile n)) :
    SurvivalKernel.probability μ {p | ∃ m, p ∈ E m} ≤
      ∑ m, SurvivalKernel.probability μ (E m) := by
  classical
  rw [SurvivalKernel.probability, ← VisitBounds.expectation_indicator_one]
  calc
    _ ≤ VisitBounds.expectation μ
        (fun p ↦ ∑ m : Fin n, (E m).indicator (fun _ ↦ (1 : ℝ)) p) := by
      apply VisitBounds.expectation_mono_support
      intro p _
      by_cases hp : ∃ m, p ∈ E m
      · obtain ⟨m, hm⟩ := hp
        simp only [Set.indicator_of_mem (show p ∈ {p | ∃ m, p ∈ E m} from ⟨m, hm⟩)]
        exact le_trans (by simp [Set.indicator_of_mem hm])
          (Finset.single_le_sum (fun k _ ↦ by
            simp only [Set.indicator_apply]; split_ifs <;> norm_num) (Finset.mem_univ m))
      · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hp]
        exact Finset.sum_nonneg fun m _ ↦ by split_ifs <;> norm_num
    _ = _ := by
      rw [EmptySurvival.expectation_finset_sum]
      apply Finset.sum_congr rfl
      intro m _
      exact VisitBounds.expectation_indicator_one _ _

/-- The actual maximum PR rank has a uniform polynomial tail beyond a fixed log² n cutoff.
All setup exceptions and all n men are included; no good-history assumption remains. -/
theorem eventually_max_rank_tail {A B r : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hr : 0 ≤ r) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (a b : Fin n → ℝ≥0),
      (∀ w, 1 ≤ (a w : ℝ)) → (∀ w, (a w : ℝ) ≤ A) →
      (∀ m, 1 ≤ (b m : ℝ)) → (∀ m, (b m : ℝ) ≤ B) →
      (eventMass (VisitBounds.profileLaw a b)
        {p | ∃ m, threshold (rankCoefficient A B r) n ≤ rank p m}).toReal ≤
          5 * (n : ℝ) ^ (-r) := by
  filter_upwards [eventually_rank_tail hA hB hr, Filter.eventually_ge_atTop 1]
    with n htail hn a b ha1 haA hb1 hbB
  have hn0 : 0 < n := by omega
  have hu := probability_exists_le_sum (VisitBounds.profileLaw a b)
    (fun m ↦ {p | threshold (rankCoefficient A B r) n ≤ rank p m})
  have hs : (∑ m : Fin n, SurvivalKernel.probability (VisitBounds.profileLaw a b)
      {p | threshold (rankCoefficient A B r) n ≤ rank p m}) ≤
        ∑ _m : Fin n, 5 * (n : ℝ) ^ (-(r + 1)) := by
    apply Finset.sum_le_sum
    intro m _
    exact htail a b ha1 haA hb1 hbB m
  apply hu.trans (hs.trans _)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show (n : ℝ) * (5 * (n : ℝ) ^ (-(r + 1))) =
    5 * ((n : ℝ) * (n : ℝ) ^ (-(r + 1))) by ring, nat_mul_rpow hn0 r]

/-- The actual maximum one-based partner rank in the exact PR matching. -/
noncomputable def maxRank {n : ℕ} (p : Profile n) : ℕ := Finset.univ.sup (rank p)

/-- A positive threshold is exceeded by the maximum exactly when some man's rank exceeds it. -/
theorem le_maxRank_iff {n : ℕ} (p : Profile n) {k : ℕ} (hk : 0 < k) :
    k ≤ maxRank p ↔ ∃ m, k ≤ rank p m := by
  simp only [maxRank, Finset.le_sup_iff hk, Finset.mem_univ, true_and]

/-- The maximum-rank cutoff is a strictly positive constant fixed by public score bounds. -/
theorem rankCoefficient_pos {A B r : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hr : 0 ≤ r) :
    0 < rankCoefficient A B r := by
  have hC : 0 ≤ setupCoefficient A r := by unfold setupCoefficient; nlinarith
  exact (coefficients_pos hA hB hC (by linarith : 0 ≤ r + 1)).2.1

/-- Uniform maximum-rank tail in the actual original profile measure, with a real log² n cutoff.
The constant depends only on the fixed normalized public score bounds and requested exponent. -/
theorem eventually_maxRank_measure_tail {A B r : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hr : 0 ≤ r) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (a b : Fin n → ℝ≥0),
      (∀ w, 1 ≤ (a w : ℝ)) → (∀ w, (a w : ℝ) ≤ A) →
      (∀ m, 1 ≤ (b m : ℝ)) → (∀ m, (b m : ℝ) ≤ B) →
      ((VisitBounds.profileLaw a b).toMeasure
        {p | rankCoefficient A B r * (Real.log n) ^ 2 ≤ (maxRank p : ℝ)}).toReal ≤
          5 * (n : ℝ) ^ (-r) := by
  filter_upwards [eventually_max_rank_tail hA hB hr, eventually_one_le_log]
    with n htail hlog a b ha1 haA hb1 hbB
  have hD := rankCoefficient_pos hA hB hr
  have hk : 0 < threshold (rankCoefficient A B r) n := by
    apply Nat.ceil_pos.mpr
    exact mul_pos hD (sq_pos_of_pos (by linarith : 0 < Real.log n))
  have he : {p : Profile n | rankCoefficient A B r * (Real.log n) ^ 2 ≤ (maxRank p : ℝ)} =
      {p | ∃ m, threshold (rankCoefficient A B r) n ≤ rank p m} := by
    ext p
    change (rankCoefficient A B r * (Real.log n) ^ 2 ≤ (maxRank p : ℝ)) ↔ _
    rw [← Nat.ceil_le]
    exact le_maxRank_iff p hk
  rw [he, ← eventMass_eq_toMeasure _ _ (by trivial)]
  exact htail a b ha1 haA hb1 hbB

end Ashlagi.RankTail
