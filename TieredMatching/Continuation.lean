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

public import TieredMatching.ProtocolKernel
public import TieredMatching.ProfileHistories
public import TieredMatching.EmptySurvival
public import TieredMatching.ActualCompeting
public import TieredMatching.StoppedProcess
public import TieredMatching.SmoothRates
public import TieredMatching.CompetingHazards

/-! # Actual ordinal deferred-acceptance continuation hazards

The probability law below is the unchanged PR profile law, conditioned only on its visible
protocol history. Destination and acceptance estimates are derived from its exact kernels.
-/

@[expose] public section

namespace TieredMatching.Continuation

open StableMarriage MeasureTheory TieredMatching.Ordinal Protocols Arrival FiniteConditioning
open scoped ENNReal NNReal

/-- The exact PR market, with individual public scores instead of tier maps. -/
noncomputable def market {n : ℕ} (a b : Fin n → ℝ≥0) : PMF (Profile n) :=
  RandomRanking.profile (fun _ w ↦ a w) (fun m _ ↦ b m)

/-- The information revealed by a fixed ordinal proposer protocol history. -/
def historyEvent {n : ℕ} (C : Protocol n) (h : List (Entry n)) : Set (Profile n) :=
  {p | profileTranscript C p h.length = h}

/-- Conditional continuation law under the original finite profile market. -/
noncomputable def lawAt {n : ℕ} (a b : Fin n → ℝ≥0) (C : Protocol n)
    (h : List (Entry n)) : PMF (Profile n) := condition (market a b) (historyEvent C h)

/-- Untried women are exactly the complement of the exposed distinct preference prefix. -/
def untried {n : ℕ} (h : List (Entry n)) (m : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun w ↦ w ∉ manOrder h m

/-- The current total popularity weight already seen by one woman. -/
noncomputable def gamma {n : ℕ} (b : Fin n → ℝ≥0) (h : List (Entry n)) (w : Fin n) : ℝ :=
  ∑ k : SeenMen h w, (b k.val : ℝ)

/-- The next destination event depends on the as-yet hidden preference suffix. -/
def destinationEvent {n : ℕ} (C : Protocol n) (h : List (Entry n)) (w m : Fin n) :
    Set (Profile n) := {p | nextEdge C p.manRank h = some (w, m)}

/-- Acceptance at a particular next edge under the original PR profile. -/
def acceptedEdgeEvent {n : ℕ} (C : Protocol n) (h : List (Entry n)) (w m : Fin n) :
    Set (Profile n) := {p | nextEdge C p.manRank h = some (w, m) ∧
      Ordinal.accept (profilePriorities p) (recordState h) (w, m) = true}

/-- On every nonnull visible history, the exact next-destination probability is the fresh
woman's public weight divided by the total weight of this proposer's untried women. -/
theorem destination_probability {n : ℕ} (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (C : Protocol n) (h : List (Entry n))
    (hh : eventMass (market a b) (historyEvent C h) ≠ 0) (w m : Fin n)
    (hs : selected C h = some m) (hw : w ∈ untried h m) :
    eventMass (lawAt a b C h) (destinationEvent C h w m) =
      ((a w / ∑ v ∈ untried h m, a v : ℝ≥0) : ℝ≥0∞) := by
  apply conditional_event_of_joint_factor _ _ _ hh
  rw [eventMass_eq_toMeasure _ _ (by trivial), eventMass_eq_toMeasure _ _ (by trivial)]
  exact Protocols.profile_next_destination_measure (fun _ w ↦ a w) (fun m _ ↦ b m)
    (fun _ w ↦ ha w) (fun m _ ↦ hb m) C h w m hs (Finset.mem_filter.mp hw).2

/-- The actual accepted-edge probability is the product of the fresh-destination and exact
ordinal acceptance factors. No acceptance estimate is an input to this theorem. -/
theorem accepted_edge_probability {n : ℕ} (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (C : Protocol n) (h : List (Entry n))
    (hh : eventMass (market a b) (historyEvent C h) ≠ 0) (w m : Fin n)
    (hs : selected C h = some m) (hw : w ∈ untried h m) :
    eventMass (lawAt a b C h) (acceptedEdgeEvent C h w m) =
      ENNReal.ofReal ((b m : ℝ) / ((b m : ℝ) + gamma b h w)) *
        ((a w / ∑ v ∈ untried h m, a v : ℝ≥0) : ℝ≥0∞) := by
  apply conditional_event_of_joint_factor _ _ _ hh
  rw [eventMass_eq_toMeasure _ _ (by trivial), eventMass_eq_toMeasure _ _ (by trivial)]
  change (market a b).toMeasure {p | profileTranscript C p h.length = h ∧
    nextEdge C p.manRank h = some (w, m) ∧
    Ordinal.accept (profilePriorities p) (recordState h) (w, m) = true} = _
  dsimp only [market]
  rw [Protocols.profile_next_acceptance_measure (fun _ w ↦ a w) (fun m _ ↦ b m)
    (fun _ w ↦ ha w) (fun m _ ↦ hb m),
    Protocols.profile_next_destination_measure (fun _ w ↦ a w) (fun m _ ↦ b m)
      (fun _ w ↦ ha w) (fun m _ ↦ hb m) C h w m hs (Finset.mem_filter.mp hw).2]
  simp only [gamma, untried, historyEvent, mul_assoc]

/-- A positive history mass supplies a genuine PR realization of that history. -/
theorem exists_profile_of_nonnull {n : ℕ} (a b : Fin n → ℝ≥0) (C : Protocol n)
    (h : List (Entry n)) (hh : eventMass (market a b) (historyEvent C h) ≠ 0) :
    ∃ p : Profile n, profileTranscript C p h.length = h := by
  obtain ⟨p, hp⟩ := (lawAt a b C h).support_nonempty
  have hs : p ∈ (condition (market a b) (historyEvent C h)).support := hp
  rw [support_condition _ _ hh] at hs
  exact ⟨p, hs.1⟩

/-- Positive histories have strict, duplicate-free exposed preference prefixes. -/
theorem manOrder_nodup {n : ℕ} (a b : Fin n → ℝ≥0) (C : Protocol n)
    (h : List (Entry n)) (hh : eventMass (market a b) (historyEvent C h) ≠ 0) (m : Fin n) :
    (manOrder h m).Nodup := by
  obtain ⟨p, hp⟩ := exists_profile_of_nonnull a b C h hh
  exact (((profileTranscript_iff C p h).mp hp).2.1 m).sublist.nodup
    (List.nodup_ofFn.mpr (p.manRank m).symm.injective)

/-- The number of actual untried destinations is exactly n minus the PR proposal counter. -/
theorem card_untried {n : ℕ} (a b : Fin n → ℝ≥0) (C : Protocol n)
    (h : List (Entry n)) (hh : eventMass (market a b) (historyEvent C h) ≠ 0) (m : Fin n) :
    (untried h m).card = n - (recordState h).next m := by
  classical
  have he : untried h m = Finset.univ \ (manOrder h m).toFinset := by
    ext w
    simp only [untried, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, List.mem_toFinset]
  rw [he, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
    List.toFinset_card_of_nodup (manOrder_nodup a b C h hh m), length_manOrder]

/-- The source's initial quarter-prefix condition and an additional quarter-prefix cap leave
at least half the women untried. This is a current-state inequality, not a good-event premise. -/
theorem half_untried_of_quarter_caps {n : ℕ} (a b : Fin n → ℝ≥0) (C : Protocol n)
    (h : List (Entry n)) (hh : eventMass (market a b) (historyEvent C h) ≠ 0) (m : Fin n)
    (d0 : ℕ) (hd0 : d0 < n / 4) (hadd : (recordState h).next m - d0 ≤ n / 4) :
    n / 2 ≤ (untried h m).card := by
  rw [card_untried a b C h hh]
  omega

/-- The actual selected proposer's acceptance event, indexed by its fresh destination. -/
def acceptanceEvent {n : ℕ} (C : Protocol n) (h : List (Entry n)) (m : Fin n) :
    Set (Profile n) := ⋃ w ∈ untried h m, acceptedEdgeEvent C h w m

/-- Fresh-destination masses after the exposed without-replacement prefix. -/
noncomputable def destinationWeight {n : ℕ} (a : Fin n → ℝ≥0) (h : List (Entry n))
    (m w : Fin n) : ℝ := (a w : ℝ) / ∑ v ∈ untried h m, (a v : ℝ)

/-- The selected proposer's actual acceptance probability is the finite fresh-rate sum. -/
theorem acceptance_probability {n : ℕ} (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (C : Protocol n) (h : List (Entry n))
    (hh : eventMass (market a b) (historyEvent C h) ≠ 0) (m : Fin n)
    (hs : selected C h = some m) :
    eventMass (lawAt a b C h) (acceptanceEvent C h m) =
      ENNReal.ofReal (SmoothRates.rateOn (untried h m) (destinationWeight a h m)
        (gamma b h) (b m : ℝ)) := by
  classical
  have hd : Set.PairwiseDisjoint (untried h m : Set (Fin n))
      (fun w ↦ acceptedEdgeEvent C h w m) := by
    intro w hw v hv hne
    apply Set.disjoint_left.mpr
    intro p hpw hpv
    exact hne (congrArg Prod.fst (Option.some.inj (hpw.1.symm.trans hpv.1)))
  rw [eventMass_eq_toMeasure _ _ (by trivial), acceptanceEvent,
    measure_biUnion_finset hd (fun _ _ ↦ by trivial)]
  change (∑ w ∈ untried h m, (lawAt a b C h).toMeasure (acceptedEdgeEvent C h w m)) = _
  have hterm (w : Fin n) (hw : w ∈ untried h m) :
      (lawAt a b C h).toMeasure (acceptedEdgeEvent C h w m) =
        ENNReal.ofReal (destinationWeight a h m w *
          ((b m : ℝ) / ((b m : ℝ) + gamma b h w))) := by
    rw [← eventMass_eq_toMeasure _ _ (by trivial), accepted_edge_probability a b ha hb C h hh w m
      hs hw]
    rw [ENNReal.ofReal_mul (by unfold destinationWeight; positivity : 0 ≤ destinationWeight a h m
      w)]
    rw [mul_comm]
    congr 1
    simp only [destinationWeight, ← NNReal.coe_sum, ← NNReal.coe_div, ENNReal.ofReal_coe_nnreal]
  rw [SmoothRates.rateOn, ENNReal.ofReal_sum_of_nonneg]
  · exact Finset.sum_congr rfl hterm
  · intro w hw
    exact mul_nonneg (by unfold destinationWeight; positivity : 0 ≤ destinationWeight a h m w)
      (div_nonneg (b m).coe_nonneg (add_nonneg (b m).coe_nonneg
        (Finset.sum_nonneg (fun _ _ ↦ NNReal.coe_nonneg _))))

/-- Current seen weights are nonnegative. -/
theorem gamma_nonneg {n : ℕ} (b : Fin n → ℝ≥0) (h : List (Entry n)) (w : Fin n) :
    0 ≤ gamma b h w := Finset.sum_nonneg fun _ _ ↦ NNReal.coe_nonneg _

/-- One actual recorded proposal increments the genuine global counter by exactly one. -/
theorem potential_record {n : ℕ} (h : List (Entry n)) (q : Edge n) (a : Bool) :
    potential (recordState (some (q, a) :: h)) = potential (recordState h) + 1 := by
  classical
  have hup : (∑ k, Function.update (recordState h).next q.2
      ((recordState h).next q.2 + 1) k) = (∑ k, (recordState h).next k) + 1 := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ q.2)]
    simp only [Finset.sdiff_singleton_eq_erase]
    have hs := Finset.sum_erase_add Finset.univ (recordState h).next (Finset.mem_univ q.2)
    omega
  cases a <;> exact hup

/-- Seen labels never outnumber the genuine global proposal counter, even for a malformed
record list. Validity is not being used as an extra probabilistic assumption. -/
theorem card_seen_le_potential {n : ℕ} (h : List (Entry n)) :
    (seenEdges h).card ≤ potential (recordState h) := by
  induction h with
  | nil => simp [seenEdges, recordState, potential]
  | cons entry h ih =>
    cases entry with
    | none => exact ih
    | some entry =>
      rcases entry with ⟨q, a⟩
      rw [potential_record]
      exact (Finset.card_insert_le q (seenEdges h)).trans (Nat.add_le_add_right ih 1)

/-- Summing women's seen weights counts every distinct proposed edge exactly once. -/
theorem sum_gamma {n : ℕ} (b : Fin n → ℝ≥0) (h : List (Entry n)) :
    (∑ w, gamma b h w) = ∑ q ∈ seenEdges h, (b q.2 : ℝ) := by
  classical
  have hw (w : Fin n) : gamma b h w =
      ∑ m ∈ Finset.univ.filter (fun m ↦ (w, m) ∈ seenEdges h), (b m : ℝ) := by
    exact (Finset.sum_subtype _ (by simp) (fun m ↦ (b m : ℝ))).symm
  simp_rw [hw, Finset.sum_filter]
  rw [← Finset.sum_product Finset.univ Finset.univ
    (fun q : Edge n ↦ if q ∈ seenEdges h then (b q.2 : ℝ) else 0)]
  have hu : (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n)) = Finset.univ := by
    ext q; simp
  rw [hu, ← Finset.sum_filter]
  simp

/-- The exact current total seen weight is bounded by B times genuine proposals already
made. No future total-count event is conditioned upon. -/
theorem sum_gamma_le {n : ℕ} (b : Fin n → ℝ≥0) (h : List (Entry n))
    {B : ℝ} (hB0 : 0 ≤ B) (hb : ∀ m, (b m : ℝ) ≤ B) :
    (∑ w, gamma b h w) ≤ B * potential (recordState h) := by
  rw [sum_gamma]
  calc
    _ ≤ ∑ _ ∈ seenEdges h, B := Finset.sum_le_sum fun q _ ↦ hb q.2
    _ = B * ((seenEdges h).card : ℝ) := by simp [mul_comm]
    _ ≤ B * potential (recordState h) := mul_le_mul_of_nonneg_left
      (by exact_mod_cast card_seen_le_potential h) hB0

/-- Fresh weighted destinations retain a uniform unconditional-in-the-fresh-set mass. -/
theorem destinationWeight_lower {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ≥0)
    (h : List (Entry n)) (m : Fin n) {A : ℝ} (hA : 1 ≤ A)
    (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (w : Fin n) (hw : w ∈ untried h m) :
    1 / (A * n) ≤ destinationWeight a h m w := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < ∑ v ∈ untried h m, (a v : ℝ) := by
    apply Finset.sum_pos'
    · intro v hv
      exact (a v).coe_nonneg
    · exact ⟨w, hw, lt_of_lt_of_le zero_lt_one (ha1 w)⟩
  have hsum : (∑ v ∈ untried h m, (a v : ℝ)) ≤ A * n := by
    calc
      _ ≤ ∑ v : Fin n, (a v : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun v _ _ ↦ (a v).coe_nonneg)
      _ ≤ ∑ _ : Fin n, A := Finset.sum_le_sum fun v _ ↦ haA v
      _ = A * n := by simp [mul_comm]
  exact (div_le_div_of_nonneg_right (ha1 w) (mul_nonneg (by linarith) hn'.le)).trans
    (div_le_div_of_nonneg_left (a w).coe_nonneg hden hsum)

/-- The harmonic fresh-rate estimate at half the remaining population has logarithmic scale. -/
theorem numerical_fresh_lower {N F G A B D L : ℝ} (hN : 0 < N)
    (hF : N / 2 ≤ F) (hFN : F ≤ N) (hG : 0 ≤ G)
    (hGB : G ≤ B * D * N * L) (hA : 1 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) (hL : 1 ≤ L) :
    1 / (4 * A * (1 + B * D) * L) ≤ (1 / (A * N)) * F ^ 2 / (F + G) := by
  have hA0 : 0 < A := by linarith
  have hL0 : 0 < L := by linarith
  have hBD : 0 ≤ B * D := mul_nonneg hB hD
  have hden : 0 < F + G := by linarith
  have hmax : F + G ≤ N * (1 + B * D) * L := by
    nlinarith [mul_nonneg hN.le (sub_nonneg.mpr hL)]
  have hsq : N ^ 2 / 4 ≤ F ^ 2 := by nlinarith
  calc
    _ = (1 / (A * N)) * (N ^ 2 / 4) / (N * (1 + B * D) * L) := by
      field_simp
    _ ≤ (1 / (A * N)) * (N ^ 2 / 4) / (F + G) :=
      div_le_div_of_nonneg_left (by positivity) hden hmax
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsq (by positivity)) hden.le

/-- Before the designated quarter-prefix cap and global count cap, his actual fresh proposal
has an acceptance probability of order `1/L`, uniformly in the complete visible history. -/
theorem actual_acceptance_lower {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0)
    {A B D L : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hD : 0 ≤ D) (hL : 1 ≤ L)
    (ha1 : ∀ w, 1 ≤ (a w : ℝ)) (haA : ∀ w, (a w : ℝ) ≤ A)
    (hb1 : ∀ m, 1 ≤ (b m : ℝ)) (hbB : ∀ m, (b m : ℝ) ≤ B)
    (C : Protocol n) (h : List (Entry n))
    (hh : eventMass (market a b) (historyEvent C h) ≠ 0) (m : Fin n)
    (hs : selected C h = some m) (hroom : n ≤ 2 * (untried h m).card)
    (htotal : (potential (recordState h) : ℝ) ≤ D * n * L) :
    ENNReal.ofReal (1 / (4 * A * (1 + B * D) * L)) ≤
      eventMass (lawAt a b C h) (acceptanceEvent C h m) := by
  have ha : ∀ w, 0 < a w := fun w ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (ha1 w)
  have hb : ∀ m, 0 < b m := fun m ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (hb1 m)
  rw [acceptance_probability a b ha hb C h hh m hs]
  apply ENNReal.ofReal_le_ofReal
  have hsum : (∑ w ∈ untried h m, gamma b h w) ≤ B * D * n * L := by
    calc
      _ ≤ ∑ w, gamma b h w := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun w _ _ ↦ gamma_nonneg b h w)
      _ ≤ B * potential (recordState h) := sum_gamma_le b h (by linarith) hbB
      _ ≤ B * D * n * L := by nlinarith [mul_le_mul_of_nonneg_left htotal (by linarith : 0 ≤ B)]
  apply (numerical_fresh_lower (N := (n : ℝ)) (F := ((untried h m).card : ℝ))
    (G := ∑ w ∈ untried h m, gamma b h w) (by exact_mod_cast hn) (by
      have hr : (n : ℝ) ≤ 2 * ((untried h m).card : ℝ) := by exact_mod_cast hroom
      linarith)
    (by exact_mod_cast (show (untried h m).card ≤ n by simpa using
      (Finset.card_le_univ (s := untried h m))))
    (Finset.sum_nonneg fun w _ ↦ gamma_nonneg b h w) hsum hA (by linarith) hD hL).trans
  exact SmoothRates.fresh_rate_lower (untried h m) (destinationWeight a h m) (gamma b h)
    (hb1 m) (by positivity) (destinationWeight_lower hn a h m hA ha1 haA)
    (fun w _ ↦ gamma_nonneg b h w)

/-- A seen destination has exactly zero next-destination probability, conditionally on the
actual PR ordinal history. -/
theorem destination_probability_seen {n : ℕ} (a b : Fin n → ℝ≥0)
    (C : Protocol n) (h : List (Entry n))
    (hh : eventMass (market a b) (historyEvent C h) ≠ 0) (w m : Fin n)
    (hw : w ∈ manOrder h m) :
    eventMass (lawAt a b C h) (destinationEvent C h w m) = 0 := by
  apply conditional_event_of_joint_factor _ _ _ hh
  rw [zero_mul, eventMass_eq_toMeasure _ _ (by trivial)]
  exact Protocols.profile_next_seen_destination_measure
    (fun _ w ↦ a w) (fun m _ ↦ b m) C h w m hw

/-- The real next-destination probability is the without-replacement fresh weight. -/
theorem destination_probability_real {n : ℕ} (a b : Fin n → ℝ≥0)
    (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (C : Protocol n) (h : List (Entry n))
    (hh : eventMass (market a b) (historyEvent C h) ≠ 0) (w m : Fin n)
    (hs : selected C h = some m) (hw : w ∈ untried h m) :
    (eventMass (lawAt a b C h) (destinationEvent C h w m)).toReal =
      destinationWeight a h m w := by
  rw [destination_probability a b ha hb C h hh w m hs hw, ENNReal.coe_toReal]
  simp only [destinationWeight, NNReal.coe_div, NNReal.coe_sum]

/-- Every still-empty woman is untried by every man in a realizable PR history. -/
theorem empty_untried {n : ℕ} (a b : Fin n → ℝ≥0) (C : Protocol n)
    (h : List (Entry n)) (hh : eventMass (market a b) (historyEvent C h) ≠ 0)
    (w : Fin n) (hw : (recordState h).held w = none) (m : Fin n) : w ∈ untried h m := by
  obtain ⟨p, hp⟩ := exists_profile_of_nonnull a b C h hh
  have hrow : RowFiber h w (fun k ↦ profilePriorities p (w, k)) :=
    ((transcript_eq_iff C p.manRank (profilePriorities p) h.length h).mp hp).2.2 w
  simp only [untried, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_manOrder_iff_seenEdges]
  exact rowFiber_no_holder_no_seen h w _ hrow hw m

/-- Empty women have no seen β-weight, so their acceptance probability is exactly one. -/
theorem gamma_empty {n : ℕ} (a b : Fin n → ℝ≥0) (C : Protocol n)
    (h : List (Entry n)) (hh : eventMass (market a b) (historyEvent C h) ≠ 0)
    (w : Fin n) (hw : (recordState h).held w = none) : gamma b h w = 0 := by
  have hempty : IsEmpty (SeenMen h w) := ⟨fun k ↦ by
    have hu := empty_untried a b C h hh w hw k.val
    exact (Finset.mem_filter.mp hu).2 ((mem_manOrder_iff_seenEdges h w k.val).mpr k.property)⟩
  have : IsEmpty (SeenMen h w) := hempty
  simp only [gamma, Finset.univ_eq_empty, Finset.sum_empty]

/-- An ordinary selected proposer hits any still-empty woman with probability at least
`1/(A*n)`, under the actual past-conditioned law and with no iid assumption. -/
theorem empty_destination_lower {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ≥0)
    {A : ℝ} (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ))
    (haA : ∀ w, (a w : ℝ) ≤ A) (hb : ∀ m, 0 < b m) (C : Protocol n)
    (h : List (Entry n)) (hh : eventMass (market a b) (historyEvent C h) ≠ 0)
    (m : Fin n) (hs : selected C h = some m) (w : Fin n)
    (hw : (recordState h).held w = none) :
    1 / (A * n) ≤ (eventMass (lawAt a b C h) (destinationEvent C h w m)).toReal := by
  have ha : ∀ w, 0 < a w := fun w ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (ha1 w)
  rw [destination_probability_real a b ha hb C h hh w m hs (empty_untried a b C h hh w hw m)]
  exact destinationWeight_lower hn a h m hA ha1 haA w (empty_untried a b C h hh w hw m)

/-- The protected woman's destination hazard is at most A times any still-empty woman's
hazard. The target may already be excluded by the selected man's exposed prefix. -/
theorem target_destination_le_empty {n : ℕ} (a b : Fin n → ℝ≥0)
    {A : ℝ} (hA : 1 ≤ A) (ha1 : ∀ w, 1 ≤ (a w : ℝ))
    (haA : ∀ w, (a w : ℝ) ≤ A) (hb : ∀ m, 0 < b m) (C : Protocol n)
    (h : List (Entry n)) (hh : eventMass (market a b) (historyEvent C h) ≠ 0)
    (m : Fin n) (hs : selected C h = some m) (target empty : Fin n)
    (hempty : (recordState h).held empty = none) :
    (eventMass (lawAt a b C h) (destinationEvent C h target m)).toReal ≤
      A * (eventMass (lawAt a b C h) (destinationEvent C h empty m)).toReal := by
  classical
  have ha : ∀ w, 0 < a w := fun w ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (ha1 w)
  have hne := empty_untried a b C h hh empty hempty m
  rw [destination_probability_real a b ha hb C h hh empty m hs hne]
  by_cases ht : target ∈ manOrder h m
  · rw [destination_probability_seen a b C h hh target m ht, ENNReal.toReal_zero]
    exact mul_nonneg (by linarith) (by unfold destinationWeight; positivity)
  have htarget : target ∈ untried h m := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
  rw [destination_probability_real a b ha hb C h hh target m hs htarget]
  have hnum : (a target : ℝ) ≤ A * (a empty : ℝ) := by
    nlinarith [haA target, mul_le_mul_of_nonneg_left (ha1 empty) (by linarith : 0 ≤ A)]
  have hd : 0 ≤ ∑ v ∈ untried h m, (a v : ℝ) := Finset.sum_nonneg fun v _ ↦ (a v).coe_nonneg
  simpa only [destinationWeight, mul_div_assoc] using div_le_div_of_nonneg_right hnum hd

/-- After the setup history has been observed, use the exact PR first-free proposer rule.
Before setup this protocol follows the original arbitrary staged proposer protocol. -/
def ordinaryAfter {n : ℕ} (setup : Protocol n) (h0 : List (Entry n)) : Protocol n :=
  fun h ↦ if h0.IsSuffix h then Ordinal.scheduledMan (recordState h) else setup h

/-- Sanitizing the ordinary continuation does not change its exact PR first-free choice. -/
theorem selected_ordinaryAfter {n : ℕ} (setup : Protocol n) (h0 h : List (Entry n))
    (hs : h0.IsSuffix h) : selected (ordinaryAfter setup h0) h =
      Ordinal.scheduledMan (recordState h) := by
  cases hm : Ordinal.scheduledMan (recordState h) with
  | none => simp only [selected, ordinaryAfter, ite_eq_left hs, hm, Option.filter_none]
  | some m =>
    apply selected_eq_of_eligible _ _ m
    · simp only [ordinaryAfter, ite_eq_left hs, hm]
    · exact scheduledMan_some_spec _ _ hm

/-- The continuation's changed proposer rule does not reveal or alter the setup law. -/
theorem ordinaryAfter_setup_transcript {n : ℕ} (setup : Protocol n)
    (h0 : List (Entry n)) (p : Profile n) (t : ℕ) (ht : t ≤ h0.length) :
    profileTranscript (ordinaryAfter setup h0) p t = profileTranscript setup p t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ht' : t ≤ h0.length := by omega
    have hshort : ¬ h0.IsSuffix (profileTranscript setup p t) := by
      intro hs
      have hl := hs.length_le
      have he : (profileTranscript setup p t).length = t :=
        transcript_length setup p.manRank (profilePriorities p) t
      omega
    have hc : selected (ordinaryAfter setup h0) (profileTranscript setup p t) =
        selected setup (profileTranscript setup p t) := by
      simp only [selected, ordinaryAfter, ite_eq_right hshort]
    change observation (ordinaryAfter setup h0) p.manRank (profilePriorities p)
        (profileTranscript (ordinaryAfter setup h0) p t) ::
        profileTranscript (ordinaryAfter setup h0) p t =
      observation setup p.manRank (profilePriorities p) (profileTranscript setup p t) ::
        profileTranscript setup p t
    rw [ih ht']
    simp only [Protocols.observation, Protocols.nextEdge, hc]

/-- Conditioning on the setup history under the ordinary continuation is exactly the
original staged setup-history conditioning event under the unchanged PR market. -/
theorem ordinaryAfter_historyEvent {n : ℕ} (setup : Protocol n) (h0 : List (Entry n)) :
    historyEvent (ordinaryAfter setup h0) h0 = historyEvent setup h0 := by
  ext p
  change _ = h0 ↔ _ = h0
  rw [ordinaryAfter_setup_transcript setup h0 p h0.length le_rfl]

/-- The already revealed protocol history remains a suffix at every future visible time. -/
theorem profileTranscript_suffix {n : ℕ} (C : Protocol n) (p : Profile n) (t s : ℕ) :
    (profileTranscript C p t).IsSuffix (profileTranscript C p (t + s)) := by
  induction s with
  | zero => exact ⟨[], rfl⟩
  | succ s ih =>
    change (profileTranscript C p t).IsSuffix
      (observation C p.manRank (profilePriorities p) (profileTranscript C p (t + s)) ::
        profileTranscript C p (t + s))
    exact ih.trans ⟨[_], rfl⟩

/-- The designated quarter-prefix cap still leaves at least half the complete strict list. -/
theorem twice_card_untried_of_quarter_caps {n : ℕ} (a b : Fin n → ℝ≥0) (C : Protocol n)
    (h : List (Entry n)) (hh : eventMass (market a b) (historyEvent C h) ≠ 0) (m : Fin n)
    (d0 : ℕ) (hd0 : d0 < n / 4) (hadd : (recordState h).next m - d0 ≤ n / 4) :
    n ≤ 2 * (untried h m).card := by
  rw [card_untried a b C h hh]
  omega

/-- The ceiling used for the additional global proposal cap costs at most one `n*L` unit. -/
theorem globalCap_le {n : ℕ} (hn : 1 ≤ n) {K L : ℝ} (hK : 0 ≤ K) (hL : 1 ≤ L) :
    (Nat.ceil (K * n * L) : ℝ) ≤ (K + 1) * n * L := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hL0 : 0 ≤ L := by linarith
  have hc := (Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg hK hn0) hL0)).le
  nlinarith [mul_le_mul hn' hL (by norm_num) (by positivity : (0 : ℝ) ≤ n)]

/-- Current genuine proposal totals before the additional global ceiling cap satisfy exactly
the deterministic bound needed by `actual_acceptance_lower`. -/
theorem capped_total_bound {n : ℕ} (hn : 1 ≤ n) {C K L : ℝ}
    (hK : 0 ≤ K) (hL : 1 ≤ L) (s0 s : ProposalState n)
    (hsetup : (potential s0 : ℝ) ≤ C * n * L)
    (hcap : potential s ≤ potential s0 + Nat.ceil (K * n * L)) :
    (potential s : ℝ) ≤ (C + K + 1) * n * L := by
  have hcap' : (potential s : ℝ) ≤ (potential s0 : ℝ) + (Nat.ceil (K * n * L) : ℝ) := by
    exact_mod_cast hcap
  nlinarith [globalCap_le hn hK hL]


/-- Real finite point masses sum to one. -/
theorem sum_mass_real {Ω : Type*} [Fintype Ω] (μ : PMF Ω) : ∑ ω, (μ ω).toReal = 1 := by
  have hs : ∑ ω, μ ω = 1 := by simpa only [tsum_fintype] using μ.tsum_coe
  rw [← ENNReal.toReal_sum (fun ω _ ↦ μ.apply_ne_top ω), hs]
  rfl

/-- Constant expectations under an actual finite probability law. -/
theorem expectation_const {Ω : Type*} [Fintype Ω] (μ : PMF Ω) (c : ℝ) :
    VisitBounds.expectation μ (fun _ ↦ c) = c := by
  simp only [VisitBounds.expectation, ← Finset.sum_mul, sum_mass_real, one_mul]

/-- Finite real expectation bounds ignore zero-mass points. -/
theorem expectation_mono_support {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    (f g : Ω → ℝ) (hfg : ∀ ω, μ ω ≠ 0 → f ω ≤ g ω) :
    VisitBounds.expectation μ f ≤ VisitBounds.expectation μ g := by
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hz : μ ω = 0
  · simp only [hz, ENNReal.toReal_zero, zero_mul, le_refl]
  · exact mul_le_mul_of_nonneg_left (hfg ω hz) ENNReal.toReal_nonneg

/-- Finite real expectations agree when their observables agree on positive-mass points. -/
theorem expectation_congr_support {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    (f g : Ω → ℝ) (hfg : ∀ ω, μ ω ≠ 0 → f ω = g ω) :
    VisitBounds.expectation μ f = VisitBounds.expectation μ g := by
  apply le_antisymm
  · exact expectation_mono_support μ f g (fun ω hω ↦ (hfg ω hω).le)
  · exact expectation_mono_support μ g f (fun ω hω ↦ (hfg ω hω).symm.le)

/-- Real total expectation with branch-specific future observables follows from literal
profile-prefix disintegration and equality on each positive child-prefix support. -/
theorem expectation_next_branch {n : ℕ} (μ : PMF (Profile n)) (C : Protocol n)
    (h : List (Entry n)) (hh : eventMass μ (ProfileHistories.event C h) ≠ 0)
    (F : Entry n → Profile n → ℝ) :
    VisitBounds.expectation (ProfileHistories.lawAt μ C h)
      (fun p ↦ F (ProfileHistories.nextObservation C h p) p) =
      ∑ entry, (ProfileHistories.nextLaw μ C h entry).toReal *
        VisitBounds.expectation (ProfileHistories.lawAt μ C (entry :: h)) (F entry) := by
  rw [ProfileHistories.expectation_next_lawAt μ C h hh]
  apply Finset.sum_congr rfl
  intro entry he
  by_cases hz : ProfileHistories.nextLaw μ C h entry = 0
  · simp only [hz, ENNReal.toReal_zero, zero_mul]
  · congr 1
    apply expectation_congr_support
    intro p hp
    rw [ProfileHistories.child_support_next μ C h entry hh hz p hp]


/-- A finite point law's real expectation. -/
theorem expectation_pure {Ω : Type*} [Fintype Ω] (ω : Ω) (f : Ω → ℝ) :
    VisitBounds.expectation (PMF.pure ω) f = f ω := by
  classical
  simp [VisitBounds.expectation, PMF.pure_apply, apply_ite]

/-- Mapping an actual finite law composes the observable in its real expectation. -/
theorem expectation_map {Ω R : Type*} [Fintype Ω] [Fintype R] (μ : PMF Ω)
    (f : Ω → R) (g : R → ℝ) :
    VisitBounds.expectation (μ.map f) g = VisitBounds.expectation μ (fun ω ↦ g (f ω)) := by
  rw [PMF.map, ProfileHistories.expectation_bind]
  simp only [Function.comp_apply, expectation_pure]
  rfl

/-- Finite actual event probabilities are expectations of their 0/1 indicators. -/
theorem eventMass_real_indicator {Ω : Type*} [Fintype Ω] (μ : PMF Ω) (E : Set Ω)
    [DecidablePred (fun ω ↦ ω ∈ E)] :
    (eventMass μ E).toReal = VisitBounds.expectation μ (fun ω ↦ if ω ∈ E then 1 else 0) := by
  classical
  have hfinite (ω : Ω) : E.indicator μ ω ≠ ∞ := by
    by_cases he : ω ∈ E <;> simp only [Set.indicator_apply, he, ↓reduceIte]
    · exact μ.apply_ne_top ω
    · exact ENNReal.zero_ne_top
  rw [eventMass, tsum_fintype, ENNReal.toReal_sum (fun ω _ ↦ hfinite ω)]
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases he : ω ∈ E <;> simp only [Set.indicator_apply, he, ↓reduceIte,
    ENNReal.toReal_zero, mul_one, mul_zero]

/-- Exact finite Boolean branch accounting under an arbitrary actual observation law. -/
theorem weighted_if {R : Type*} [Fintype R] (ν : PMF R) (flag : R → Bool) (u v : ℝ) :
    (∑ e, (ν e).toReal * (if flag e then u else v)) =
      v + (u - v) * ∑ e, if flag e then (ν e).toReal else 0 := by
  have hterm (e : R) : (ν e).toReal * (if flag e then u else v) =
      v * (ν e).toReal + (u - v) * (if flag e then (ν e).toReal else 0) := by
    split_ifs <;> ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_mass_real, mul_one]

/-- The visible acceptance flag; pauses have no acceptance. -/
def acceptedFlag {n : ℕ} : Entry n → Bool
  | none => false
  | some (_, accepted) => accepted

/-- Actual conditional mass of an accepted next proposal. -/
noncomputable def acceptedMass {n : ℕ} (a b : Fin n → ℝ≥0) (C : Protocol n)
    (h : List (Entry n)) : ℝ :=
  ∑ entry, if acceptedFlag entry then (ProfileHistories.nextLaw (market a b) C h entry).toReal
    else 0

/-- The fresh accepted-edge event is included in the actual next-observation accepted flag. -/
theorem acceptance_event_le_acceptedMass {n : ℕ} (a b : Fin n → ℝ≥0) (C : Protocol n)
    (h : List (Entry n)) (m : Fin n) :
    (eventMass (lawAt a b C h) (acceptanceEvent C h m)).toReal ≤ acceptedMass a b C h := by
  classical
  have heq : acceptedMass a b C h =
      VisitBounds.expectation (lawAt a b C h)
        (fun p ↦ if acceptedFlag (ProfileHistories.nextObservation C h p) then 1 else 0) := by
    rw [← expectation_map (lawAt a b C h) (ProfileHistories.nextObservation C h)
      (fun entry ↦ if acceptedFlag entry then (1 : ℝ) else 0)]
    change acceptedMass a b C h = VisitBounds.expectation
      (ProfileHistories.nextLaw (market a b) C h) _
    apply Finset.sum_congr rfl
    intro entry he
    cases hb : acceptedFlag entry <;> simp only [hb, Bool.false_eq_true, ↓reduceIte,
      mul_zero, mul_one]
  rw [heq, eventMass_real_indicator]
  apply expectation_mono_support
  intro p hp
  by_cases he : p ∈ acceptanceEvent C h m
  · have hew : ∃ w, w ∈ untried h m ∧ p ∈ acceptedEdgeEvent C h w m := by
      simpa only [acceptanceEvent, Set.mem_iUnion, exists_prop] using he
    obtain ⟨w, hfresh, hnext, haccept⟩ := hew
    have hobs : ProfileHistories.nextObservation C h p = some ((w, m), true) := by
      simp only [ProfileHistories.nextObservation, Protocols.observation, hnext,
        Option.map_some, haccept]
    simp only [he, hobs, acceptedFlag, ↓reduceIte, le_refl]
  · simp only [he, ↓reduceIte]
    split_ifs <;> norm_num


/-- A fixed real scalar factors out of a finite actual expectation. -/
theorem expectation_const_mul {Ω : Type*} [Fintype Ω] (μ : PMF Ω) (c : ℝ) (f : Ω → ℝ) :
    VisitBounds.expectation μ (fun ω ↦ c * f ω) = c * VisitBounds.expectation μ f := by
  unfold VisitBounds.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  ring

/-- Actual finite expectations respect the affine comparison used to extract the mean. -/
theorem expectation_one_add_mul {Ω : Type*} [Fintype Ω] (μ : PMF Ω) (θ : ℝ) (f : Ω → ℝ) :
    VisitBounds.expectation μ (fun ω ↦ 1 + θ * f ω) = 1 + θ * VisitBounds.expectation μ f := by
  unfold VisitBounds.expectation
  simp only [mul_add, mul_one, Finset.sum_add_distrib, sum_mass_real]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro ω hω
  ring

/-- The actual finite count mean follows from its verified exponential moment. -/
theorem mean_le_inv_of_exponential_moment {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    (X : Ω → ℕ) {θ : ℝ} (hθ : 0 < θ)
    (hm : VisitBounds.expectation μ (fun ω ↦ Real.exp (θ * (X ω : ℝ))) ≤ 2) :
    VisitBounds.expectation μ (fun ω ↦ (X ω : ℝ)) ≤ θ⁻¹ := by
  have hb := expectation_mono_support μ (fun ω ↦ 1 + θ * (X ω : ℝ))
    (fun ω ↦ Real.exp (θ * (X ω : ℝ))) (fun ω _ ↦ by
      simpa only [add_comm] using Real.add_one_le_exp (θ * (X ω : ℝ)))
  rw [expectation_one_add_mul] at hb
  have hprod : VisitBounds.expectation μ (fun ω ↦ (X ω : ℝ)) * θ ≤ 1 := by linarith
  simpa only [one_div] using (le_div_iff₀ hθ).mpr hprod

/-- Exponential Markov applied on the actual finite original path law. -/
theorem tail_le_of_exponential_moment {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    (X : Ω → ℕ) {θ : ℝ} (hθ : 0 < θ)
    (hm : VisitBounds.expectation μ (fun ω ↦ Real.exp (θ * (X ω : ℝ))) ≤ 2)
    (threshold : ℝ) :
    (eventMass μ {ω | threshold ≤ (X ω : ℝ)}).toReal ≤
      2 * Real.exp (-θ * threshold) := by
  classical
  let E : Set Ω := {ω | threshold ≤ (X ω : ℝ)}
  have hp (ω : Ω) : Real.exp (θ * threshold) * (if ω ∈ E then 1 else 0) ≤
      Real.exp (θ * (X ω : ℝ)) := by
    by_cases he : ω ∈ E
    · simp only [he, ↓reduceIte, mul_one]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left he hθ.le)
    · simp only [he, ↓reduceIte, mul_zero]
      exact (Real.exp_pos _).le
  have hi := expectation_mono_support μ _ _ (fun ω _ ↦ hp ω)
  rw [expectation_const_mul, ← eventMass_real_indicator] at hi
  have hdiv : (eventMass μ E).toReal ≤ 2 / Real.exp (θ * threshold) := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    nlinarith
  simpa only [div_eq_mul_inv, ← Real.exp_neg, neg_mul] using hdiv


/-- Finite actual expectations distribute over addition. -/
theorem expectation_add {Ω : Type*} [Fintype Ω] (μ : PMF Ω) (f g : Ω → ℝ) :
    VisitBounds.expectation μ (fun ω ↦ f ω + g ω) =
      VisitBounds.expectation μ f + VisitBounds.expectation μ g := by
  simp only [VisitBounds.expectation, mul_add, Finset.sum_add_distrib]

/-- A bounded actual count can be uncapped by paying only its explicit global and individual
cap events. Agreement is a pathwise counter statement on supported profiles. -/
theorem mean_cap_transfer {Ω : Type*} [Fintype Ω] (μ : PMF Ω) (X Z : Ω → ℕ)
    (N M : ℕ) (G : Set Ω) (hX : ∀ ω, μ ω ≠ 0 → X ω ≤ N)
    (heq : ∀ ω, μ ω ≠ 0 → ω ∉ G → Z ω < M → X ω = Z ω) :
    VisitBounds.expectation μ (fun ω ↦ (X ω : ℝ)) ≤
      VisitBounds.expectation μ (fun ω ↦ (Z ω : ℝ)) + N *
        ((eventMass μ G).toReal + (eventMass μ {ω | M ≤ Z ω}).toReal) := by
  classical
  have hp (ω : Ω) (hω : μ ω ≠ 0) : (X ω : ℝ) ≤
      ((Z ω : ℝ) + (N : ℝ) * (if ω ∈ G then 1 else 0)) +
        (N : ℝ) * (if M ≤ Z ω then 1 else 0) := by
    have hb : (X ω : ℝ) ≤ N := by exact_mod_cast hX ω hω
    have hZ : (0 : ℝ) ≤ Z ω := Nat.cast_nonneg _
    by_cases hg : ω ∈ G
    · simp only [hg, ↓reduceIte, mul_one]
      split_ifs <;> simp only [mul_one, mul_zero] <;> linarith
    · by_cases hz : M ≤ Z ω
      · simp only [hg, hz, ↓reduceIte, mul_one, mul_zero, add_zero]
        linarith
      · have hxz := heq ω hω hg (by omega)
        simp only [hg, hz, ↓reduceIte, mul_zero, add_zero, hxz, le_refl]
  have hb := expectation_mono_support μ _ _ hp
  rw [expectation_add, expectation_add, expectation_const_mul, expectation_const_mul,
    ← eventMass_real_indicator] at hb
  have hi : VisitBounds.expectation μ (fun ω ↦ if M ≤ Z ω then (1 : ℝ) else 0) =
      (eventMass μ {ω | M ≤ Z ω}).toReal := by
    exact (@eventMass_real_indicator Ω _ μ {ω | M ≤ Z ω}
      (fun ω ↦ Nat.decLe M (Z ω))).symm
  rw [hi] at hb
  linarith

/-- Below the individual cap, only the explicit global cap error is needed in the actual
tail comparison. -/
theorem tail_cap_transfer {Ω : Type*} [Fintype Ω] (μ : PMF Ω) (X Z : Ω → ℕ)
    (M k : ℕ) (hk : k < M) (G : Set Ω)
    (heq : ∀ ω, μ ω ≠ 0 → ω ∉ G → Z ω < M → X ω = Z ω) :
    (eventMass μ {ω | k ≤ X ω}).toReal ≤
      (eventMass μ {ω | k ≤ Z ω}).toReal + (eventMass μ G).toReal := by
  classical
  rw [eventMass_real_indicator, eventMass_real_indicator, eventMass_real_indicator,
    ← expectation_add]
  apply expectation_mono_support
  intro ω hω
  by_cases hg : ω ∈ G
  · simp only [hg, ↓reduceIte]
    split_ifs <;> norm_num
  · by_cases hz : k ≤ Z ω
    · simp only [hg, hz, Set.mem_ofPred_eq, ↓reduceIte]
      split_ifs <;> norm_num
    · have hxz := heq ω hω hg (by omega)
      have hx : ¬ k ≤ X ω := by omega
      simp only [hg, hz, hx, Set.mem_ofPred_eq, ↓reduceIte, zero_add, le_refl]

/-- The designated man is currently free, read entirely from the discrete visible state. -/
def Free {n : ℕ} (h : List (Entry n)) (m : Fin n) : Prop :=
  ∀ w, (recordState h).held w ≠ some m

/-- Visible freedom is decidable from the finite record state. -/
instance decidableFree {n : ℕ} (h : List (Entry n)) (m : Fin n) : Decidable (Free h m) := by
  unfold Free
  infer_instance

/-- A different destination cannot change a woman's current holder. -/
theorem held_record_of_ne {n : ℕ} (h : List (Entry n)) (q : Edge n) (a : Bool)
    (w : Fin n) (hw : q.1 ≠ w) :
    (recordState (some (q, a) :: h)).held w = (recordState h).held w := by
  cases a with
  | false => rfl
  | true => exact Function.update_of_ne (Ne.symm hw) _ _

/-- A free man remains free while another man makes a proposal. -/
theorem free_record_of_ne {n : ℕ} (h : List (Entry n)) (q : Edge n) (a : Bool)
    (m : Fin n) (hm : Free h m) (hq : q.2 ≠ m) : Free (some (q, a) :: h) m := by
  intro w
  cases a with
  | false => exact hm w
  | true =>
    by_cases hw : w = q.1
    · subst w
      simpa only [recordState, recordStep, ↓reduceIte,
        Function.update_self, ne_eq, Option.some.injEq] using hq
    · change Function.update (recordState h).held q.1 (some q.2) w ≠ some m
      rw [Function.update_of_ne hw]
      exact hm w

/-- Explicit ordinary-count stopping caps, fixed at the visible setup history. -/
structure Caps (n : ℕ) where
  setup : List (Entry n)
  man : Fin n
  global : ℕ
  individual : ℕ

namespace Caps

/-- Stops use only revealed counters, current occupancy, or a visible protocol suspension. -/
noncomputable def stopped {n : ℕ} (S : Caps n) (C : Protocol n) (h : List (Entry n)) : Bool :=
  decide (S.global ≤ potential (recordState h) - potential (recordState S.setup) ∨
    S.individual ≤ (recordState h).next S.man - (recordState S.setup).next S.man ∨
    (VisitBounds.emptyWomen h).card = 0 ∨ selected C h = none)

/-- One designated genuine proposal is counted when the visible rule selects that man. -/
def reward {n : ℕ} (S : Caps n) (C : Protocol n) (h : List (Entry n)) : ℕ :=
  if selected C h = some S.man then 1 else 0

/-- Actual additional designated proposals before the caps, following the same original
profile at every step. A suspended protocol stops; no public-clock/raw-clock equality is used. -/
noncomputable def countFuel {n : ℕ} (S : Caps n) (C : Protocol n) :
    ℕ → List (Entry n) → Profile n → ℕ
  | 0, _, _ => 0
  | k + 1, h, p => if S.stopped C h then 0 else
      S.reward C h + countFuel S C k (ProfileHistories.nextObservation C h p :: h) p

/-- Safe means no challenge to the protected woman's destination before the cap or completion.
A hit to that destination is failure even if she would reject it, a sufficient event for safety. -/
noncomputable def safeFuel {n : ℕ} (S : Caps n) (C : Protocol n) (w : Fin n) :
    ℕ → List (Entry n) → Profile n → Bool
  | 0, _, _ => true
  | k + 1, h, p => if S.stopped C h then true else
      match ProfileHistories.nextObservation C h p with
      | none => true
      | some (q, a) => if q.1 = w then false else safeFuel S C w k (some (q, a) :: h) p

/-- Before stopping, a still-available global cap bounds current genuine proposals. -/
theorem total_le_cap {n : ℕ} (S : Caps n) (C : Protocol n) (h : List (Entry n))
    (hs : S.stopped C h = false) :
    potential (recordState h) ≤ potential (recordState S.setup) + S.global := by
  have hn : ¬ (S.global ≤ potential (recordState h) - potential (recordState S.setup) ∨
      S.individual ≤ (recordState h).next S.man - (recordState S.setup).next S.man ∨
      (VisitBounds.emptyWomen h).card = 0 ∨ selected C h = none) := by
    simpa only [stopped, decide_eq_false_iff_not] using hs
  omega

/-- Before stopping, the designated additional prefix remains below its explicit cap. -/
theorem individual_lt_cap {n : ℕ} (S : Caps n) (C : Protocol n) (h : List (Entry n))
    (hs : S.stopped C h = false) :
    (recordState h).next S.man - (recordState S.setup).next S.man < S.individual := by
  have hn : ¬ (S.global ≤ potential (recordState h) - potential (recordState S.setup) ∨
      S.individual ≤ (recordState h).next S.man - (recordState S.setup).next S.man ∨
      (VisitBounds.emptyWomen h).card = 0 ∨ selected C h = none) := by
    simpa only [stopped, decide_eq_false_iff_not] using hs
  omega

/-- A pre-cap protocol step chooses a genuine eligible proposer rather than padding. -/
theorem selected_ne_none {n : ℕ} (S : Caps n) (C : Protocol n) (h : List (Entry n))
    (hs : S.stopped C h = false) : selected C h ≠ none := by
  intro hn
  simp only [stopped, hn, or_true, decide_true, Bool.true_eq_false] at hs

/-- The actual stopped future history, generated from the same original profile. -/
noncomputable def endHistory {n : ℕ} (S : Caps n) (C : Protocol n) :
    ℕ → List (Entry n) → Profile n → List (Entry n)
  | 0, h, _ => h
  | k + 1, h, p => if S.stopped C h then h else
      endHistory S C k (ProfileHistories.nextObservation C h p :: h) p

/-- The actual number of genuine global proposals used before the caps. -/
noncomputable def stepsFuel {n : ℕ} (S : Caps n) (C : Protocol n) :
    ℕ → List (Entry n) → Profile n → ℕ
  | 0, _, _ => 0
  | k + 1, h, p => if S.stopped C h then 0 else
      1 + stepsFuel S C k (ProfileHistories.nextObservation C h p :: h) p

/-- Every pre-cap actual observation is a genuine proposal by the selected eligible man. -/
theorem nextObservation_some {n : ℕ} (S : Caps n) (C : Protocol n)
    (h : List (Entry n)) (p : Profile n) (hs : S.stopped C h = false) :
    ∃ u w a, selected C h = some u ∧
      ProfileHistories.nextObservation C h p = some ((w, u), a) := by
  cases hm : selected C h with
  | none => exact False.elim (S.selected_ne_none C h hs hm)
  | some u =>
    have hn := (selected_some_spec C h u hm).1
    let w := (p.manRank u).symm ⟨(recordState h).next u, hn⟩
    refine ⟨u, w, Ordinal.accept (profilePriorities p) (recordState h) (w, u), rfl, ?_⟩
    simp only [ProfileHistories.nextObservation, Protocols.observation, Protocols.nextEdge,
      hm, dite_eq_left hn, Option.map_some]
    rfl

/-- Stopped counting exactly matches the designated man's actual PR counter increments. -/
theorem next_endHistory {n : ℕ} (S : Caps n) (C : Protocol n) (p : Profile n)
    (k : ℕ) (h : List (Entry n)) :
    (recordState (S.endHistory C k h p)).next S.man =
      (recordState h).next S.man + S.countFuel C k h p := by
  induction k generalizing h with
  | zero => simp only [endHistory, countFuel, add_zero]
  | succ k ih =>
    by_cases hs : S.stopped C h = true
    · simp only [endHistory, countFuel, hs, ↓reduceIte, add_zero]
    have hs' := Bool.eq_false_iff.mpr hs
    obtain ⟨u, w, a, hu, he⟩ := S.nextObservation_some C h p hs'
    simp only [endHistory, countFuel, hs, Bool.false_eq_true, ↓reduceIte, he, ih]
    by_cases hm : u = S.man
    · subst u
      cases a <;> simp [recordState, recordStep, reward, hu, Nat.add_assoc]
    · cases a <;> simp [recordState, recordStep, reward, hu, hm, Ne.symm hm]

/-- The global stopped clock counts genuine proposals exactly, including the cap-reaching
proposal. Padding, repeats, and public protocol time are not being equated with this clock. -/
theorem potential_endHistory {n : ℕ} (S : Caps n) (C : Protocol n) (p : Profile n)
    (k : ℕ) (h : List (Entry n)) :
    potential (recordState (S.endHistory C k h p)) =
      potential (recordState h) + S.stepsFuel C k h p := by
  induction k generalizing h with
  | zero => simp only [endHistory, stepsFuel, add_zero]
  | succ k ih =>
    by_cases hs : S.stopped C h = true
    · simp only [endHistory, stepsFuel, hs, ↓reduceIte, add_zero]
    have hs' := Bool.eq_false_iff.mpr hs
    obtain ⟨u, w, a, _, he⟩ := S.nextObservation_some C h p hs'
    simp only [endHistory, stepsFuel, hs, Bool.false_eq_true, ↓reduceIte, he, ih,
      potential_record, Nat.add_assoc]

/-- An execution still active after the finite recursion used every available genuine step. -/
theorem stepsFuel_eq_of_end_active {n : ℕ} (S : Caps n) (C : Protocol n) (p : Profile n)
    (k : ℕ) (h : List (Entry n))
    (ha : S.stopped C (S.endHistory C k h p) = false) : S.stepsFuel C k h p = k := by
  induction k generalizing h with
  | zero => rfl
  | succ k ih =>
    by_cases hs : S.stopped C h = true
    · simp only [endHistory, hs, ↓reduceIte, Bool.true_eq_false] at ha
    simp only [endHistory, hs, Bool.false_eq_true, ↓reduceIte] at ha
    simp only [stepsFuel, hs, Bool.false_eq_true, ↓reduceIte, ih _ ha, Nat.add_comm]

/-- The finite global horizon always reaches an actual stop under the explicit caps. -/
theorem endHistory_stopped {n : ℕ} (S : Caps n) (C : Protocol n) (p : Profile n) :
    S.stopped C (S.endHistory C S.global S.setup p) = true := by
  by_contra hs
  have hs' := Bool.eq_false_iff.mpr hs
  have hsteps := S.stepsFuel_eq_of_end_active C p S.global S.setup hs'
  have hpot := S.potential_endHistory C p S.global S.setup
  have heq : potential (recordState (S.endHistory C S.global S.setup p)) -
      potential (recordState S.setup) = S.global := by omega
  simp only [stopped, heq, le_refl, true_or, decide_true, Bool.true_eq_false] at hs'


/-- The actual conditional exponential moment of stopped additional designated proposals. -/
noncomputable def moment {n : ℕ} (S : Caps n) (a b : Fin n → ℝ≥0) (C : Protocol n)
    (θ : ℝ) (k : ℕ) (h : List (Entry n)) : ℝ :=
  VisitBounds.expectation (lawAt a b C h) (fun p ↦ Real.exp (θ * (S.countFuel C k h p : ℝ)))

/-- The actual conditional probability of the protected-destination safe event. -/
noncomputable def safeProbability {n : ℕ} (S : Caps n) (a b : Fin n → ℝ≥0)
    (C : Protocol n) (w : Fin n) (k : ℕ) (h : List (Entry n)) : ℝ :=
  VisitBounds.expectation (lawAt a b C h) (fun p ↦ if S.safeFuel C w k h p then 1 else 0)

/-- Both finite-recursion base observables have expectation one. -/
theorem moment_zero {n : ℕ} (S : Caps n) (a b : Fin n → ℝ≥0) (C : Protocol n)
    (θ : ℝ) (h : List (Entry n)) : S.moment a b C θ 0 h = 1 := by
  simp only [moment, countFuel, Nat.cast_zero, mul_zero, Real.exp_zero, expectation_const]

/-- At fuel zero, the actual capped protected-destination safe event is certain. -/
theorem safeProbability_zero {n : ℕ} (S : Caps n) (a b : Fin n → ℝ≥0) (C : Protocol n)
    (w : Fin n) (h : List (Entry n)) : S.safeProbability a b C w 0 h = 1 := by
  simp only [safeProbability, safeFuel, ↓reduceIte, expectation_const]

/-- The actual exponential-moment recursion is derived from the literal profile law tower. -/
theorem moment_succ {n : ℕ} (S : Caps n) (a b : Fin n → ℝ≥0) (C : Protocol n)
    (θ : ℝ) (k : ℕ) (h : List (Entry n))
    (hh : eventMass (market a b) (historyEvent C h) ≠ 0) (hs : S.stopped C h = false) :
    S.moment a b C θ (k + 1) h = Real.exp (θ * (S.reward C h : ℝ)) *
      ∑ entry, (ProfileHistories.nextLaw (market a b) C h entry).toReal *
        S.moment a b C θ k (entry :: h) := by
  unfold moment
  simp only [countFuel, hs, Bool.false_eq_true, ↓reduceIte, Nat.cast_add, mul_add, Real.exp_add]
  change VisitBounds.expectation (lawAt a b C h)
    (fun p ↦ Real.exp (θ * (S.reward C h : ℝ)) *
      (fun e p ↦ Real.exp (θ * (S.countFuel C k (e :: h) p : ℝ)))
        (ProfileHistories.nextObservation C h p) p) = _
  simp only [VisitBounds.expectation, ← Finset.mul_sum, mul_left_comm]
  congr 1
  simpa only [VisitBounds.expectation, lawAt, historyEvent, ProfileHistories.lawAt,
    ProfileHistories.event] using
    expectation_next_branch (market a b) C h hh
      (fun entry p ↦ Real.exp (θ * (S.countFuel C k (entry :: h) p : ℝ)))

/-- Stopped actual count moments are exactly one. -/
theorem moment_stopped {n : ℕ} (S : Caps n) (a b : Fin n → ℝ≥0) (C : Protocol n)
    (θ : ℝ) (k : ℕ) (h : List (Entry n)) (hs : S.stopped C h = true) :
    S.moment a b C θ k h = 1 := by
  cases k <;> simp only [moment, countFuel, hs, ↓reduceIte, Nat.cast_zero,
    mul_zero, Real.exp_zero, expectation_const]

/-- Safe-event probability at an actual stopped history is exactly one. -/
theorem safeProbability_stopped {n : ℕ} (S : Caps n) (a b : Fin n → ℝ≥0) (C : Protocol n)
    (w : Fin n) (k : ℕ) (h : List (Entry n)) (hs : S.stopped C h = true) :
    S.safeProbability a b C w k h = 1 := by
  cases k <;> simp only [safeProbability, safeFuel, hs, ↓reduceIte, expectation_const]

/-- While held, the designated man contributes no counted proposal at the next genuine step. -/
theorem reward_zero_of_held {n : ℕ} (S : Caps n) (C : Protocol n)
    (h : List (Entry n)) (w : Fin n) (hw : (recordState h).held w = some S.man) :
    S.reward C h = 0 := by
  by_cases hm : selected C h = some S.man
  · exact False.elim ((selected_some_spec C h S.man hm).2 w hw)
  · simp only [reward, ite_eq_right hm]

/-- Every positive next-entry branch before a cap is a genuine selected proposal. -/
theorem entry_some_of_support {n : ℕ} (S : Caps n) (a b : Fin n → ℝ≥0) (C : Protocol n)
    (h : List (Entry n)) (hs : S.stopped C h = false) (entry : Entry n)
    (he : ProfileHistories.nextLaw (market a b) C h entry ≠ 0) :
    ∃ u w accepted, selected C h = some u ∧ entry = some ((w, u), accepted) := by
  obtain ⟨p, _, hp⟩ := (PMF.mem_support_map_iff (ProfileHistories.nextObservation C h)
    (ProfileHistories.lawAt (market a b) C h) entry).mp he
  obtain ⟨u, w, accepted, hu, hn⟩ := S.nextObservation_some C h p hs
  exact ⟨u, w, accepted, hu, hp.symm.trans hn⟩

/-- The protected safe probability obeys the exact one-step conditional profile law tower. -/
theorem safeProbability_succ {n : ℕ} (S : Caps n) (a b : Fin n → ℝ≥0) (C : Protocol n)
    (w : Fin n) (k : ℕ) (h : List (Entry n))
    (hh : eventMass (market a b) (historyEvent C h) ≠ 0) (hs : S.stopped C h = false) :
    S.safeProbability a b C w (k + 1) h =
      ∑ entry, (ProfileHistories.nextLaw (market a b) C h entry).toReal *
        match entry with
        | none => 1
        | some (q, _) => if q.1 = w then 0 else S.safeProbability a b C w k (entry :: h) := by
  let F (entry : Entry n) (p : Profile n) : ℝ := match entry with
    | none => 1
    | some (q, _) => if q.1 = w then 0 else if S.safeFuel C w k (entry :: h) p then 1 else 0
  have ht := expectation_next_branch (market a b) C h hh F
  have hleft : S.safeProbability a b C w (k + 1) h =
      VisitBounds.expectation (ProfileHistories.lawAt (market a b) C h)
        (fun p ↦ F (ProfileHistories.nextObservation C h p) p) := by
    unfold safeProbability
    congr 1
    funext p
    simp only [safeFuel, hs, Bool.false_eq_true, ↓reduceIte]
    cases he : ProfileHistories.nextObservation C h p with
    | none => rfl
    | some e =>
      rcases e with ⟨q, accepted⟩
      by_cases hw : q.1 = w <;> simp only [F, hw, Bool.false_eq_true, ↓reduceIte]
  rw [hleft, ht]
  apply Finset.sum_congr rfl
  intro entry he
  cases entry with
  | none => simp only [F, expectation_const]
  | some e =>
    rcases e with ⟨q, accepted⟩
    by_cases hw : q.1 = w <;> simp only [F, hw, ↓reduceIte, expectation_const]
    rfl

/-- The held-phase auxiliary step uses actual profile conditioning, current zero reward,
and a protected-destination safe event. It does not condition on eventual survival. -/
theorem held_moment_step {n : ℕ} (S : Caps n) (a b : Fin n → ℝ≥0) (C : Protocol n)
    (θ : ℝ) (k : ℕ) (h : List (Entry n)) (w : Fin n)
    (hh : eventMass (market a b) (historyEvent C h) ≠ 0)
    (hs : S.stopped C h = false) (hw : (recordState h).held w = some S.man)
    (hgeneral : ∀ entry, ProfileHistories.nextLaw (market a b) C h entry ≠ 0 →
      S.moment a b C θ k (entry :: h) ≤ 2)
    (hprotected : ∀ u v accepted,
      ProfileHistories.nextLaw (market a b) C h (some ((v, u), accepted)) ≠ 0 → v ≠ w →
      S.moment a b C θ k (some ((v, u), accepted) :: h) ≤
        2 - S.safeProbability a b C w k (some ((v, u), accepted) :: h)) :
    S.moment a b C θ (k + 1) h ≤ 2 - S.safeProbability a b C w (k + 1) h := by
  rw [S.moment_succ a b C θ k h hh hs, S.reward_zero_of_held C h w hw,
    Nat.cast_zero, mul_zero, Real.exp_zero, one_mul, S.safeProbability_succ a b C w k h hh hs]
  have hsum : (∑ entry : Entry n,
      (ProfileHistories.nextLaw (market a b) C h entry).toReal * 2) = 2 := by
    rw [← Finset.sum_mul, sum_mass_real, one_mul]
  rw [← hsum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro entry hentry
  by_cases hz : ProfileHistories.nextLaw (market a b) C h entry = 0
  · simp only [hz, ENNReal.toReal_zero, zero_mul, sub_zero, le_refl]
  obtain ⟨u, v, accepted, _, rfl⟩ := S.entry_some_of_support a b C h hs entry hz
  by_cases hv : v = w
  · subst v
    simp only [↓reduceIte, mul_zero, sub_zero]
    exact mul_le_mul_of_nonneg_left (hgeneral _ hz) ENNReal.toReal_nonneg
  · simp only [hv, ↓reduceIte]
    have hb := mul_le_mul_of_nonneg_left (hprotected u v accepted hz hv)
      (ENNReal.toReal_nonneg (a := ProfileHistories.nextLaw (market a b) C h
        (some ((v, u), accepted))))
    linarith


/-- The actual free-phase attempt step has potential at most two. Acceptance mass is the
visible next-observation mass, to which the exact actual hazard theorem applies. -/
theorem free_selected_moment_step {n : ℕ} (S : Caps n) (a b : Fin n → ℝ≥0)
    (C : Protocol n) {r q : ℝ} (hr : r ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    (k : ℕ) (h : List (Entry n))
    (hh : eventMass (market a b) (historyEvent C h) ≠ 0)
    (hs : S.stopped C h = false) (hf : Free h S.man)
    (hm : selected C h = some S.man) (ha : r ≤ acceptedMass a b C h)
    (hchild : ∀ entry, ProfileHistories.nextLaw (market a b) C h entry ≠ 0 →
      S.moment a b C (StoppedHazards.theta r q) k (entry :: h) ≤
        if Free (entry :: h) S.man then 2 else 2 - q) :
    S.moment a b C (StoppedHazards.theta r q) (k + 1) h ≤ 2 := by
  classical
  rw [S.moment_succ a b C _ k h hh hs]
  simp only [reward, hm, ↓reduceIte, Nat.cast_one, mul_one]
  have hterm (entry : Entry n) (he : ProfileHistories.nextLaw (market a b) C h entry ≠ 0) :
      S.moment a b C (StoppedHazards.theta r q) k (entry :: h) ≤
        if acceptedFlag entry then 2 - q else 2 := by
    obtain ⟨u, w, accepted, hu, rfl⟩ := S.entry_some_of_support a b C h hs entry he
    have hum : u = S.man := Option.some.inj (hu.symm.trans hm)
    subst u
    have hb := hchild _ he
    cases accepted with
    | false =>
      have hfree : Free (some ((w, S.man), false) :: h) S.man := hf
      simpa only [ite_eq_left hfree, acceptedFlag, Bool.false_eq_true, ↓reduceIte] using hb
    | true =>
      have hnfree : ¬ Free (some ((w, S.man), true) :: h) S.man := by
        intro hfree
        exact hfree w (by simp [recordState, recordStep])
      simpa only [ite_eq_right hnfree, acceptedFlag, ↓reduceIte] using hb
  have hsum : (∑ entry, (ProfileHistories.nextLaw (market a b) C h entry).toReal *
      S.moment a b C (StoppedHazards.theta r q) k (entry :: h)) ≤
      2 - acceptedMass a b C h * q := by
    calc
      _ ≤ ∑ entry, (ProfileHistories.nextLaw (market a b) C h entry).toReal *
          (if acceptedFlag entry then 2 - q else 2) := by
        apply Finset.sum_le_sum
        intro entry he
        by_cases hz : ProfileHistories.nextLaw (market a b) C h entry = 0
        · simp only [hz, ENNReal.toReal_zero, zero_mul, le_refl]
        · exact mul_le_mul_of_nonneg_left (hterm entry hz) ENNReal.toReal_nonneg
      _ = _ := by rw [weighted_if]; unfold acceptedMass; ring
  exact (mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le).trans
    (StoppedHazards.free_bellman_le hr hq hq0 ha)

/-- When another man proposes, a currently free designated man remains free and accrues
no reward. This gives the other free-phase branch of the actual moment induction. -/
theorem free_other_moment_step {n : ℕ} (S : Caps n) (a b : Fin n → ℝ≥0) (C : Protocol n)
    (θ q : ℝ) (k : ℕ) (h : List (Entry n))
    (hh : eventMass (market a b) (historyEvent C h) ≠ 0)
    (hs : S.stopped C h = false) (hf : Free h S.man)
    (hm : selected C h ≠ some S.man)
    (hchild : ∀ entry, ProfileHistories.nextLaw (market a b) C h entry ≠ 0 →
      S.moment a b C θ k (entry :: h) ≤ if Free (entry :: h) S.man then 2 else 2 - q) :
    S.moment a b C θ (k + 1) h ≤ 2 := by
  classical
  rw [S.moment_succ a b C θ k h hh hs]
  simp only [reward, ite_eq_right hm, Nat.cast_zero, mul_zero, Real.exp_zero, one_mul]
  calc
    _ ≤ ∑ entry : Entry n, (ProfileHistories.nextLaw (market a b) C h entry).toReal * 2 := by
      apply Finset.sum_le_sum
      intro entry he
      by_cases hz : ProfileHistories.nextLaw (market a b) C h entry = 0
      · simp only [hz, ENNReal.toReal_zero, zero_mul, le_refl]
      obtain ⟨u, w, accepted, hu, rfl⟩ := S.entry_some_of_support a b C h hs entry hz
      have hne : u ≠ S.man := by intro heq; subst u; exact hm hu
      have hfree := free_record_of_ne h (w, u) accepted S.man hf hne
      have hb := hchild _ hz
      rw [ite_eq_left hfree] at hb
      exact mul_le_mul_of_nonneg_left hb ENNReal.toReal_nonneg
    _ = 2 := by rw [← Finset.sum_mul, sum_mass_real, one_mul]


/-- The actual capped safe event is exactly the event in the independently proved ordinal
competing-hazard theorem. -/
theorem safeFuel_eq_actual {n : ℕ} (S : Caps n) (C : Protocol n) (w : Fin n)
    (k : ℕ) (h : List (Entry n)) (p : Profile n) :
    S.safeFuel C w k h p = ActualCompeting.safeFuel (S.stopped C) C w k h p := by
  induction k generalizing h with
  | zero => rfl
  | succ k ih =>
    simp only [safeFuel, ActualCompeting.safeFuel, ih]
    rfl

/-- Exact actual conditional safe probability, with the original PR profile law. -/
theorem safeProbability_eq_actual {n : ℕ} (S : Caps n) (a b : Fin n → ℝ≥0)
    (C : Protocol n) (w : Fin n) (k : ℕ) (h : List (Entry n)) :
    S.safeProbability a b C w k h =
      ActualCompeting.safeProbability (VisitBounds.profileLaw a b) (S.stopped C) C w k h := by
  simp only [safeProbability, ActualCompeting.safeProbability, safeFuel_eq_actual,
    lawAt, historyEvent, ProfileHistories.lawAt, ProfileHistories.event, market,
    VisitBounds.profileLaw]


/-- Finite capped recursion uses at most its available genuine global horizon. -/
theorem stepsFuel_le {n : ℕ} (S : Caps n) (C : Protocol n) (p : Profile n)
    (k : ℕ) (h : List (Entry n)) : S.stepsFuel C k h p ≤ k := by
  induction k generalizing h with
  | zero => exact le_rfl
  | succ k ih =>
    by_cases hs : S.stopped C h = true
    · simp only [stepsFuel, hs, ↓reduceIte, Nat.zero_le]
    · simp only [stepsFuel, hs, Bool.false_eq_true, ↓reduceIte]
      have hi := ih (ProfileHistories.nextObservation C h p :: h)
      omega

/-- The stopped future is an actual prefix of the very same original profile's protocol
execution, at the exact number of genuine pre-cap steps. -/
theorem endHistory_eq_transcript {n : ℕ} (S : Caps n) (C : Protocol n) (p : Profile n)
    (k : ℕ) (h : List (Entry n)) (hp : profileTranscript C p h.length = h) :
    S.endHistory C k h p = profileTranscript C p (h.length + S.stepsFuel C k h p) := by
  induction k generalizing h with
  | zero => simpa only [endHistory, stepsFuel, Nat.add_zero] using hp.symm
  | succ k ih =>
    by_cases hs : S.stopped C h = true
    · simpa only [endHistory, stepsFuel, hs, ↓reduceIte, Nat.add_zero] using hp.symm
    let entry := ProfileHistories.nextObservation C h p
    have hchild : profileTranscript C p (entry :: h).length = entry :: h := by
      exact (profileTranscript_cons_iff C p h entry).mpr ⟨hp, rfl⟩
    have hi := ih (entry :: h) hchild
    simpa only [endHistory, stepsFuel, hs, Bool.false_eq_true, ↓reduceIte,
      List.length_cons, Nat.add_assoc, Nat.add_left_comm] using hi

/-- Every actual capped end history contains its visible starting history as a suffix. -/
theorem endHistory_suffix {n : ℕ} (S : Caps n) (C : Protocol n) (p : Profile n)
    (k : ℕ) (h : List (Entry n)) : h.IsSuffix (S.endHistory C k h p) := by
  induction k generalizing h with
  | zero => exact ⟨[], rfl⟩
  | succ k ih =>
    by_cases hs : S.stopped C h = true
    · simpa only [endHistory, hs, ↓reduceIte] using (show h.IsSuffix h from ⟨[], rfl⟩)
    · simp only [endHistory, hs, Bool.false_eq_true, ↓reduceIte]
      exact (List.suffix_cons _ _).trans (ih _)

end Caps



/-- A later recorded proposal can remove empty women but can never create them. -/
theorem emptyWomen_cons_subset {n : ℕ} (entry : Entry n) (h : List (Entry n)) :
    VisitBounds.emptyWomen (entry :: h) ⊆ VisitBounds.emptyWomen h := by
  cases entry with
  | none => exact Finset.Subset.refl _
  | some e =>
    rcases e with ⟨⟨w, m⟩, accepted⟩
    cases accepted with
    | false => exact Finset.Subset.refl _
    | true => rw [VisitBounds.emptyWomen_cons_true]; exact Finset.erase_subset _ _

/-- The source's two-empty setup property holds at every later visible history. -/
theorem emptyWomen_suffix_subset {n : ℕ} (h0 h : List (Entry n)) (hs : h0.IsSuffix h) :
    VisitBounds.emptyWomen h ⊆ VisitBounds.emptyWomen h0 := by
  obtain ⟨L, rfl⟩ := hs
  induction L with
  | nil => exact Finset.Subset.refl _
  | cons entry L ih => exact (emptyWomen_cons_subset entry (L ++ h0)).trans ih

/-- Every actually revealed partial-protocol counter is bounded by its unchanged PR terminal
counter. This follows from the proved schedule-independent rejection closure. -/
theorem profile_counter_le_pr {n : ℕ} (C : Protocol n) (p : Profile n)
    (h : List (Entry n)) (hp : profileTranscript C p h.length = h) (m : Fin n) :
    (recordState h).next m ≤ (deferredAcceptance p).next m := by
  have hr : Schedules.Reachable p Finset.univ (recordState h) := by
    rw [← hp]
    exact profileTranscript_reachable C p Finset.univ h.length (uses_univ _ _)
  by_contra hn
  have hlt : (deferredAcceptance p).next m < (recordState h).next m := by omega
  have hb := (Schedules.reachable_valid p Finset.univ hr).next_le m
  have hterm : (deferredAcceptance p).next m < n := by omega
  let w := (p.manRank m).symm ⟨(deferredAcceptance p).next m, hterm⟩
  have hproposal : HasProposed p (recordState h) m w := by
    simpa only [HasProposed, w, Equiv.apply_symm_apply] using hlt
  have hpr := Schedules.reachable_proposals_subset_larger_terminal p (Finset.Subset.refl _)
    hr (Schedules.pr_terminal p).1 (Schedules.pr_terminal p).2 m w hproposal
  simp only [HasProposed, w, Equiv.apply_symm_apply, lt_self_iff_false] at hpr

/-- All hypotheses of the bounded-state source continuation, on the actual visible setup.
No stochastic acceptance or regeneration bound is supplied. -/
structure Setting (n : ℕ) where
  a : Fin n → ℝ≥0
  b : Fin n → ℝ≥0
  setupProtocol : Protocol n
  setup : List (Entry n)
  man : Fin n
  A : ℝ
  B : ℝ
  C : ℝ
  K : ℝ
  L : ℝ
  n_ge : 8 ≤ n
  A_ge : 1 ≤ A
  B_ge : 1 ≤ B
  C_nonneg : 0 ≤ C
  K_nonneg : 0 ≤ K
  L_ge : 1 ≤ L
  a_ge : ∀ w, 1 ≤ (a w : ℝ)
  a_le : ∀ w, (a w : ℝ) ≤ A
  b_ge : ∀ m, 1 ≤ (b m : ℝ)
  b_le : ∀ m, (b m : ℝ) ≤ B
  setup_nonnull : eventMass (market a b) (historyEvent setupProtocol setup) ≠ 0
  setup_total : (potential (recordState setup) : ℝ) ≤ C * n * L
  setup_quarter : ((recordState setup).next man : ℝ) < (n : ℝ) / 4
  setup_empty : (VisitBounds.emptyWomen setup).card ≤ 2

namespace Setting

variable {n : ℕ} (S : Setting n)

/-- The concrete exact PR continuation switches to the ordinary first-free rule after setup. -/
def protocol : Protocol n := ordinaryAfter S.setupProtocol S.setup

/-- The actual global ceiling cap and designated quarter-prefix cap. -/
noncomputable def caps : Caps n :=
  ⟨S.setup, S.man, Nat.ceil (S.K * n * S.L), n / 4⟩

/-- A uniform explicit acceptance lower bound before either genuine proposal cap. -/
noncomputable def acceptanceRate : ℝ :=
  1 / (4 * S.A * (1 + S.B * (S.C + S.K + 1)) * S.L)

/-- A conservative two-empty protected-destination survival probability. -/
noncomputable def survivalRate : ℝ := CompetingHazards.potential S.A 2

/-- Setup conditioning is preserved exactly by switching to the ordinary continuation. -/
theorem setup_nonnull_protocol :
    eventMass (market S.a S.b) (historyEvent S.protocol S.setup) ≠ 0 := by
  rw [protocol, ordinaryAfter_historyEvent]
  exact S.setup_nonnull

/-- The explicit continuation acceptance parameter is strictly positive. -/
theorem acceptanceRate_pos : 0 < S.acceptanceRate := by
  have hA : 0 < S.A := by linarith [S.A_ge]
  have hL : 0 < S.L := by linarith [S.L_ge]
  have hB : 0 ≤ S.B := by linarith [S.B_ge]
  have hD : 0 ≤ S.C + S.K + 1 := by linarith [S.C_nonneg, S.K_nonneg]
  exact one_div_pos.mpr (mul_pos (mul_pos (mul_pos (by norm_num) hA)
    (by nlinarith [mul_nonneg hB hD])) hL)

/-- The explicit continuation acceptance parameter is a genuine probability lower bound. -/
theorem acceptanceRate_le_one : S.acceptanceRate ≤ 1 := by
  have hBD : 0 ≤ S.B * (S.C + S.K + 1) :=
    mul_nonneg (by linarith [S.B_ge]) (by linarith [S.C_nonneg, S.K_nonneg])
  have hd : 1 ≤ 4 * S.A * (1 + S.B * (S.C + S.K + 1)) * S.L := by
    have h1 := mul_le_mul S.A_ge (show 1 ≤ 1 + S.B * (S.C + S.K + 1) by linarith)
      (by norm_num) (by linarith [S.A_ge] : 0 ≤ S.A)
    have h2 := mul_le_mul h1 S.L_ge (by norm_num) (by positivity : 0 ≤ S.A *
      (1 + S.B * (S.C + S.K + 1)))
    nlinarith
  exact (one_div_le_one_div_of_le zero_lt_one hd).trans_eq (by norm_num)

/-- The exact two-empty regeneration parameter is positive and at most one. -/
theorem survivalRate_bounds : 0 < S.survivalRate ∧ S.survivalRate ≤ 1 :=
  ⟨CompetingHazards.potential_pos (by linarith [S.A_ge]) _,
    CompetingHazards.potential_le_one (by linarith [S.A_ge]) _⟩

/-- Every nonnull pre-cap history at which the designated man is selected has the required
actual acceptance hazard. The total and fresh-count hypotheses are proved from the caps. -/
theorem selected_acceptance_lower (h : List (Entry n))
    (hh : eventMass (market S.a S.b) (historyEvent S.protocol h) ≠ 0)
    (hstop : S.caps.stopped S.protocol h = false)
    (hselected : selected S.protocol h = some S.man) :
    ENNReal.ofReal S.acceptanceRate ≤
      eventMass (lawAt S.a S.b S.protocol h) (acceptanceEvent S.protocol h S.man) := by
  have hn : 0 < n := by have := S.n_ge; omega
  have hd0 : 4 * (recordState S.setup).next S.man < n := by
    have hr : (4 : ℝ) * (recordState S.setup).next S.man < n := by linarith [S.setup_quarter]
    exact_mod_cast hr
  have hcap : (recordState h).next S.man - (recordState S.setup).next S.man < n / 4 :=
    S.caps.individual_lt_cap S.protocol h hstop
  have hroom : n ≤ 2 * (untried h S.man).card := by
    rw [card_untried S.a S.b S.protocol h hh]
    omega
  have htotal : (potential (recordState h) : ℝ) ≤ (S.C + S.K + 1) * n * S.L :=
    capped_total_bound (by omega) S.K_nonneg S.L_ge _ _ S.setup_total
      (S.caps.total_le_cap S.protocol h hstop)
  exact actual_acceptance_lower hn S.a S.b S.A_ge S.B_ge
    (by linarith [S.C_nonneg, S.K_nonneg]) S.L_ge S.a_ge S.a_le S.b_ge S.b_le
    S.protocol h hh S.man hselected hroom htotal

/-- The concrete ordinary continuation cannot pause while a still-empty woman remains. -/
theorem workConserving : EmptySurvival.WorkConserving (market S.a S.b) S.protocol S.setup := by
  intro h hbase hh hempty hnone
  obtain ⟨p, hp⟩ := exists_profile_of_nonnull S.a S.b S.protocol h hh
  have hr : Schedules.Reachable p Finset.univ (recordState h) := by
    rw [← hp]
    exact profileTranscript_reachable S.protocol p Finset.univ h.length (uses_univ _ _)
  have hsched : Ordinal.scheduledMan (recordState h) = none :=
    (selected_ordinaryAfter S.setupProtocol S.setup h hbase).symm.trans hnone
  have ht : Schedules.Terminal Finset.univ (recordState h) := by
    intro m hm
    have hn := List.find?_eq_none.mp hsched m (by simp)
    exact hn (by simpa using hm.2)
  have heq := Schedules.terminal_state_eq_pr p hr ht
  obtain ⟨w, hw⟩ := hempty
  obtain ⟨m, hm⟩ := terminal_has_holder p w
  rw [heq] at hw
  simp only [hw, reduceCtorEq] at hm

/-- The actual ordinary global continuation exceeds its ceiling budget with the stated
coupon-scale error, derived without independent draws or a future conditioning event. -/
theorem global_cap_error :
    (eventMass (lawAt S.a S.b S.protocol S.setup)
      {p | ∃ w, (recordState (profileTranscript S.protocol p
        (S.setup.length + S.caps.global))).held w = none}).toReal ≤
      2 * Real.exp (-(S.caps.global : ℝ) / (S.A * n)) := by
  exact EmptySurvival.incomplete_probability_le_exp (by have := S.n_ge; omega)
    S.a S.b S.A_ge S.a_ge S.a_le
    (fun m ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (S.b_ge m))
    S.protocol S.setup S.workConserving S.setup_nonnull_protocol S.caps.global 2 S.setup_empty

/-- The actual next-observation acceptance mass has the derived pre-cap lower bound. -/
theorem selected_acceptedMass_lower (h : List (Entry n))
    (hh : eventMass (market S.a S.b) (historyEvent S.protocol h) ≠ 0)
    (hstop : S.caps.stopped S.protocol h = false)
    (hselected : selected S.protocol h = some S.man) :
    S.acceptanceRate ≤ acceptedMass S.a S.b S.protocol h := by
  have hr := ENNReal.toReal_mono (eventMass_ne_top _ _)
    (S.selected_acceptance_lower h hh hstop hselected)
  rw [ENNReal.toReal_ofReal S.acceptanceRate_pos.le] at hr
  exact hr.trans (acceptance_event_le_acceptedMass S.a S.b S.protocol h S.man)

/-- The setup's empty count bounds every continuation prefix deterministically. -/
theorem empty_card_le_two (h : List (Entry n)) (hs : S.setup.IsSuffix h) :
    (VisitBounds.emptyWomen h).card ≤ 2 :=
  (Finset.card_le_card (emptyWomen_suffix_subset S.setup h hs)).trans S.setup_empty

/-- The exact actual finite-profile moment induction, isolated from the independent safe-
event estimate. The eventual specialization supplies that estimate as a proved theorem. -/
private theorem moment_bounds_of_safe
    (hsafe : ∀ (h : List (Entry n)) (w : Fin n) (k : ℕ), S.setup.IsSuffix h →
      eventMass (market S.a S.b) (historyEvent S.protocol h) ≠ 0 →
      (recordState h).held w = some S.man →
      S.survivalRate ≤ S.caps.safeProbability S.a S.b S.protocol w k h) (k : ℕ) :
    (∀ h : List (Entry n), S.setup.IsSuffix h →
      eventMass (market S.a S.b) (historyEvent S.protocol h) ≠ 0 →
      S.caps.moment S.a S.b S.protocol (StoppedHazards.theta S.acceptanceRate S.survivalRate) k h ≤
        if Free h S.man then 2 else 2 - S.survivalRate) ∧
    (∀ (h : List (Entry n)) (w : Fin n), S.setup.IsSuffix h →
      eventMass (market S.a S.b) (historyEvent S.protocol h) ≠ 0 →
      (recordState h).held w = some S.man →
      S.caps.moment S.a S.b S.protocol (StoppedHazards.theta S.acceptanceRate S.survivalRate) k h ≤
        2 - S.caps.safeProbability S.a S.b S.protocol w k h) := by
  classical
  induction k with
  | zero =>
    constructor
    · intro h _ _
      rw [Caps.moment_zero]
      split_ifs <;> linarith [S.survivalRate_bounds.2]
    · intro h w _ _ _
      rw [Caps.moment_zero, Caps.safeProbability_zero]
      norm_num
  | succ k ih =>
    have haux : ∀ (h : List (Entry n)) (w : Fin n), S.setup.IsSuffix h →
        eventMass (market S.a S.b) (historyEvent S.protocol h) ≠ 0 →
        (recordState h).held w = some S.man →
        S.caps.moment S.a S.b S.protocol
          (StoppedHazards.theta S.acceptanceRate S.survivalRate) (k + 1) h ≤
          2 - S.caps.safeProbability S.a S.b S.protocol w (k + 1) h := by
      intro h w hbase hh hw
      by_cases hstop : S.caps.stopped S.protocol h = true
      · rw [Caps.moment_stopped _ _ _ _ _ _ _ hstop,
          Caps.safeProbability_stopped _ _ _ _ _ _ _ hstop]
        norm_num
      have hstop' := Bool.eq_false_iff.mpr hstop
      apply S.caps.held_moment_step S.a S.b S.protocol _ k h w hh hstop' hw
      · intro entry he
        have hb := ih.1 (entry :: h) (hbase.trans (List.suffix_cons _ _))
          (ProfileHistories.child_nonnull _ _ _ _ hh he)
        split_ifs at hb <;> linarith [S.survivalRate_bounds.1]
      · intro u v accepted he hne
        apply ih.2 _ w (hbase.trans (List.suffix_cons _ _))
          (ProfileHistories.child_nonnull _ _ _ _ hh he)
        rw [held_record_of_ne h (v, u) accepted w hne]
        exact hw
    refine ⟨?_, haux⟩
    intro h hbase hh
    by_cases hf : Free h S.man
    · rw [ite_eq_left hf]
      by_cases hstop : S.caps.stopped S.protocol h = true
      · rw [Caps.moment_stopped _ _ _ _ _ _ _ hstop]
        norm_num
      have hstop' := Bool.eq_false_iff.mpr hstop
      have hchild : ∀ entry, ProfileHistories.nextLaw (market S.a S.b) S.protocol h entry ≠ 0 →
          S.caps.moment S.a S.b S.protocol
            (StoppedHazards.theta S.acceptanceRate S.survivalRate) k (entry :: h) ≤
            if Free (entry :: h) S.caps.man then 2 else 2 - S.survivalRate := by
        intro entry he
        exact ih.1 _ (hbase.trans (List.suffix_cons _ _))
          (ProfileHistories.child_nonnull _ _ _ _ hh he)
      by_cases hm : selected S.protocol h = some S.man
      · exact S.caps.free_selected_moment_step S.a S.b S.protocol S.acceptanceRate_le_one
          S.survivalRate_bounds.1.le S.survivalRate_bounds.2 k h hh hstop' hf hm
          (S.selected_acceptedMass_lower h hh hstop' hm) hchild
      · exact S.caps.free_other_moment_step S.a S.b S.protocol _ _ k h hh hstop' hf hm hchild
    · rw [ite_eq_right hf]
      have hw : ∃ w, (recordState h).held w = some S.man := by simpa only [Free, not_forall,
        not_not] using hf
      obtain ⟨w, hw⟩ := hw
      exact (haux h w hbase hh hw).trans (by linarith [hsafe h w (k + 1) hbase hh hw])

/-- The protected-destination regeneration probability is derived under the actual past-
conditioned PR law. No acceptance, regeneration, or survival estimate is an assumption. -/
theorem survival_lower (h : List (Entry n)) (w : Fin n) (k : ℕ)
    (hbase : S.setup.IsSuffix h)
    (hh : eventMass (market S.a S.b) (historyEvent S.protocol h) ≠ 0)
    (hw : (recordState h).held w = some S.man) :
    S.survivalRate ≤ S.caps.safeProbability S.a S.b S.protocol w k h := by
  rw [Caps.safeProbability_eq_actual]
  exact ActualCompeting.two_empty_le_safeProbability S.a S.b S.A_ge S.a_ge S.a_le
    (fun m ↦ by exact_mod_cast lt_of_lt_of_le zero_lt_one (S.b_ge m))
    (S.caps.stopped S.protocol) S.protocol w k h hh ⟨S.man, hw⟩ (S.empty_card_le_two h hbase)

/-- The capped actual conditional profile exponential moment is bounded by the exact free/
held potential, with all source local hazard estimates discharged. -/
theorem moment_le_potential (k : ℕ) (h : List (Entry n)) (hbase : S.setup.IsSuffix h)
    (hh : eventMass (market S.a S.b) (historyEvent S.protocol h) ≠ 0) :
    S.caps.moment S.a S.b S.protocol (StoppedHazards.theta S.acceptanceRate S.survivalRate) k h ≤
      if Free h S.man then 2 else 2 - S.survivalRate :=
  (S.moment_bounds_of_safe S.survival_lower k).1 h hbase hh

/-- The source's actual additional capped ordinary-proposal count. -/
noncomputable def cappedCount (p : Profile n) : ℕ :=
  S.caps.countFuel S.protocol S.caps.global S.setup p

/-- The actual capped count has exponential moment at most two, uniformly in the nonnull
setup history and its public scores. -/
theorem capped_exponential_moment :
    VisitBounds.expectation (lawAt S.a S.b S.protocol S.setup)
      (fun p ↦ Real.exp (StoppedHazards.theta S.acceptanceRate S.survivalRate *
        (S.cappedCount p : ℝ))) ≤ 2 := by
  change S.caps.moment S.a S.b S.protocol
    (StoppedHazards.theta S.acceptanceRate S.survivalRate) S.caps.global S.setup ≤ 2
  have hb := S.moment_le_potential S.caps.global S.setup ⟨[], rfl⟩ S.setup_nonnull_protocol
  split_ifs at hb <;> linarith [S.survivalRate_bounds.1]

/-- The concrete source tilt is strictly positive. -/
theorem tilt_pos : 0 < StoppedHazards.theta S.acceptanceRate S.survivalRate :=
  StoppedHazards.theta_pos S.acceptanceRate_pos S.acceptanceRate_le_one
    S.survivalRate_bounds.1 S.survivalRate_bounds.2

/-- The actual capped ordinary count has geometric-scale conditional mean. -/
theorem capped_mean_le :
    VisitBounds.expectation (lawAt S.a S.b S.protocol S.setup)
      (fun p ↦ (S.cappedCount p : ℝ)) ≤ 2 / (S.acceptanceRate * S.survivalRate) := by
  apply (mean_le_inv_of_exponential_moment _ S.cappedCount S.tilt_pos
    S.capped_exponential_moment).trans
  have ht := StoppedHazards.theta_ge_half_mul S.acceptanceRate_le_one
    S.survivalRate_bounds.2 S.survivalRate_bounds.1.le
  have hrq : 0 < S.acceptanceRate * S.survivalRate :=
    mul_pos S.acceptanceRate_pos S.survivalRate_bounds.1
  apply (le_div_iff₀ hrq).mpr
  have hm := mul_le_mul_of_nonneg_right ht (inv_pos.mpr S.tilt_pos).le
  rw [mul_inv_cancel₀ S.tilt_pos.ne'] at hm
  nlinarith

/-- The actual capped count has the source's exponential tail, with all local hazards derived. -/
theorem capped_tail_le (threshold : ℝ) :
    (eventMass (lawAt S.a S.b S.protocol S.setup)
      {p | threshold ≤ (S.cappedCount p : ℝ)}).toReal ≤
      2 * Real.exp (-StoppedHazards.theta S.acceptanceRate S.survivalRate * threshold) :=
  tail_le_of_exponential_moment _ S.cappedCount S.tilt_pos S.capped_exponential_moment threshold

/-- At nonnegative thresholds the simpler product-hazard form follows. -/
theorem capped_tail_le_half_mul (threshold : ℝ) (ht : 0 ≤ threshold) :
    (eventMass (lawAt S.a S.b S.protocol S.setup)
      {p | threshold ≤ (S.cappedCount p : ℝ)}).toReal ≤
      2 * Real.exp (-(S.acceptanceRate * S.survivalRate / 2) * threshold) := by
  apply (S.capped_tail_le threshold).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  have hb := mul_le_mul_of_nonneg_right
    (StoppedHazards.theta_ge_half_mul S.acceptanceRate_le_one
      S.survivalRate_bounds.2 S.survivalRate_bounds.1.le) ht
  linarith

/-- Once the continued protocol is visibly paused, it is terminal under the exact PR rule. -/
theorem terminal_of_selected_none (h : List (Entry n)) (hbase : S.setup.IsSuffix h)
    (hnone : selected S.protocol h = none) : Schedules.Terminal Finset.univ (recordState h) := by
  have hsched : Ordinal.scheduledMan (recordState h) = none :=
    (selected_ordinaryAfter S.setupProtocol S.setup h hbase).symm.trans hnone
  intro m hm
  have hn := List.find?_eq_none.mp hsched m (by simp)
  exact hn (by simpa using hm.2)

/-- An actually realized ordinary continuation that has filled all women or paused has the
exact original PR terminal state. -/
theorem state_eq_pr_of_complete (h : List (Entry n)) (p : Profile n)
    (hp : profileTranscript S.protocol p h.length = h) (hbase : S.setup.IsSuffix h)
    (hc : (VisitBounds.emptyWomen h).card = 0 ∨ selected S.protocol h = none) :
    recordState h = deferredAcceptance p := by
  have hnone : selected S.protocol h = none := by
    rcases hc with hc | hn
    · cases hs : selected S.protocol h with
      | none => rfl
      | some u =>
        obtain ⟨w, hw⟩ := VisitBounds.exists_empty_of_selected S.protocol p h hp u hs
        have hmem : w ∈ VisitBounds.emptyWomen h := by simp only [VisitBounds.emptyWomen,
          Finset.mem_filter, Finset.mem_univ, true_and, hw]
        exact False.elim ((Finset.card_pos.mpr ⟨w, hmem⟩).ne' hc)
    · exact hn
  have hr : Schedules.Reachable p Finset.univ (recordState h) := by
    rw [← hp]
    exact profileTranscript_reachable S.protocol p Finset.univ h.length (uses_univ _ _)
  exact Schedules.terminal_state_eq_pr p hr (S.terminal_of_selected_none h hbase hnone)

/-- The actual additional ordinary proposal count is the unchanged PR terminal counter minus
the visible setup counter. -/
noncomputable def ordinaryCount (p : Profile n) : ℕ :=
  (deferredAcceptance p).next S.man - (recordState S.setup).next S.man

/-- The exact ordinary designated count is bounded by the complete list length. -/
theorem ordinaryCount_le (p : Profile n) : S.ordinaryCount p ≤ n :=
  (Nat.sub_le _ _).trans (terminal_next_le p S.man)

/-- Outside the two explicit cap-error events, the actual ordinary count equals its capped
count. The cap-reaching proposal is included in both counters. -/
theorem ordinaryCount_eq_capped (p : Profile n)
    (hp : profileTranscript S.protocol p S.setup.length = S.setup)
    (hindividual : S.cappedCount p < S.caps.individual)
    (hcomplete : ¬ ∃ w, (recordState (profileTranscript S.protocol p
      (S.setup.length + S.caps.global))).held w = none) :
    S.ordinaryCount p = S.cappedCount p := by
  let E := S.caps.endHistory S.protocol S.caps.global S.setup p
  let t := S.caps.stepsFuel S.protocol S.caps.global S.setup p
  have he : E = profileTranscript S.protocol p (S.setup.length + t) :=
    S.caps.endHistory_eq_transcript S.protocol p S.caps.global S.setup hp
  have hlen : E.length = S.setup.length + t := by
    rw [he]
    exact transcript_length _ _ _ _
  have hpe : profileTranscript S.protocol p E.length = E := by rw [hlen, ← he]
  have hbase : S.setup.IsSuffix E := S.caps.endHistory_suffix _ _ _ _
  have ht : t ≤ S.caps.global := S.caps.stepsFuel_le _ _ _ _
  have hpot : potential (recordState E) = potential (recordState S.setup) + t :=
    S.caps.potential_endHistory _ _ _ _
  have hnext : (recordState E).next S.man = (recordState S.setup).next S.man + S.cappedCount p :=
    S.caps.next_endHistory _ _ _ _
  have hglobal : potential (recordState E) - potential (recordState S.setup) = t := by omega
  have hind : (recordState E).next S.man - (recordState S.setup).next S.man = S.cappedCount p :=
    by omega
  have hdone : (VisitBounds.emptyWomen E).card = 0 ∨ selected S.protocol E = none := by
    by_cases hlast : t = S.caps.global
    · left
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have hheld : (recordState E).held w = none := (Finset.mem_filter.mp hw).2
      apply hcomplete
      exact ⟨w, by simpa only [he, hlast] using hheld⟩
    · have hs := S.caps.endHistory_stopped S.protocol p
      have hh : S.caps.global ≤ t ∨ S.caps.individual ≤ S.cappedCount p ∨
          (VisitBounds.emptyWomen E).card = 0 ∨ selected S.protocol E = none := by
        simp only [Caps.stopped, decide_eq_true_eq] at hs
        change S.caps.global ≤ potential (recordState E) - potential (recordState S.setup) ∨
          S.caps.individual ≤ (recordState E).next S.man - (recordState S.setup).next S.man ∨
          (VisitBounds.emptyWomen E).card = 0 ∨ selected S.protocol E = none at hs
        simpa only [hglobal, hind] using hs
      rcases hh with hh | hh
      · omega
      rcases hh with hh | hh
      · omega
      exact hh
  have hpr := S.state_eq_pr_of_complete E p hpe hbase hdone
  change (deferredAcceptance p).next S.man - (recordState S.setup).next S.man = _
  rw [← hpr, hnext]
  omega

/-- The ordinary global-cap error is an actual visible missing-woman event at H genuine steps. -/
def globalError : Set (Profile n) := {p | ∃ w, (recordState (profileTranscript S.protocol p
  (S.setup.length + S.caps.global))).held w = none}

/-- Pathwise uncapping agreement on the supported setup-conditioned original profile law. -/
theorem uncapping_agreement (p : Profile n)
    (hp : lawAt S.a S.b S.protocol S.setup p ≠ 0) (hg : p ∉ S.globalError)
    (hz : S.cappedCount p < S.caps.individual) : S.ordinaryCount p = S.cappedCount p := by
  have hs : p ∈ (condition (market S.a S.b) (historyEvent S.protocol S.setup)).support := hp
  rw [support_condition _ _ S.setup_nonnull_protocol] at hs
  exact S.ordinaryCount_eq_capped p hs.1 hz hg

/-- Removing both genuine caps gives the actual ordinary-count mean with explicit errors. -/
theorem ordinary_mean_le :
    VisitBounds.expectation (lawAt S.a S.b S.protocol S.setup)
      (fun p ↦ (S.ordinaryCount p : ℝ)) ≤ 2 / (S.acceptanceRate * S.survivalRate) + n *
        (2 * Real.exp (-(S.caps.global : ℝ) / (S.A * n)) +
          2 * Real.exp (-(S.acceptanceRate * S.survivalRate / 2) * S.caps.individual)) := by
  have hb := mean_cap_transfer (lawAt S.a S.b S.protocol S.setup) S.ordinaryCount S.cappedCount
    n S.caps.individual S.globalError (fun p _ ↦ S.ordinaryCount_le p) S.uncapping_agreement
  have hglobal := S.global_cap_error
  have hind := S.capped_tail_le_half_mul (S.caps.individual : ℝ) (Nat.cast_nonneg _)
  have hind' : (eventMass (lawAt S.a S.b S.protocol S.setup)
      {p | S.caps.individual ≤ S.cappedCount p}).toReal ≤
      2 * Real.exp (-(S.acceptanceRate * S.survivalRate / 2) * S.caps.individual) := by
    simpa only [Nat.cast_le] using hind
  dsimp only [globalError] at hb
  have hm := S.capped_mean_le
  have herrors := add_le_add hglobal hind'
  have hscale := mul_le_mul_of_nonneg_left herrors (Nat.cast_nonneg (α := ℝ) n)
  linarith

/-- Below the designated prefix cap, the actual ordinary tail pays only the global-cap error. -/
theorem ordinary_tail_le (k : ℕ) (hk : k < S.caps.individual) :
    (eventMass (lawAt S.a S.b S.protocol S.setup) {p | k ≤ S.ordinaryCount p}).toReal ≤
      2 * Real.exp (-(S.acceptanceRate * S.survivalRate / 2) * k) +
        2 * Real.exp (-(S.caps.global : ℝ) / (S.A * n)) := by
  have hb := tail_cap_transfer (lawAt S.a S.b S.protocol S.setup) S.ordinaryCount S.cappedCount
    S.caps.individual k hk S.globalError S.uncapping_agreement
  have ht := S.capped_tail_le_half_mul (k : ℝ) (Nat.cast_nonneg _)
  have ht' : (eventMass (lawAt S.a S.b S.protocol S.setup) {p | k ≤ S.cappedCount p}).toReal ≤
      2 * Real.exp (-(S.acceptanceRate * S.survivalRate / 2) * k) := by
    simpa only [Nat.cast_le] using ht
  exact hb.trans (add_le_add ht' S.global_cap_error)

/-- The continuation bounds condition on exactly the user's original staged setup event. -/
theorem setup_law_eq : lawAt S.a S.b S.protocol S.setup =
    lawAt S.a S.b S.setupProtocol S.setup := by
  unfold lawAt protocol
  rw [ordinaryAfter_historyEvent]

/-- The ordinary additional count exactly completes the compatible visible setup counter. -/
theorem setup_add_ordinaryCount (p : Profile n)
    (hp : profileTranscript S.protocol p S.setup.length = S.setup) :
    (recordState S.setup).next S.man + S.ordinaryCount p = (deferredAcceptance p).next S.man := by
  exact Nat.add_sub_of_le (profile_counter_le_pr S.protocol p S.setup hp S.man)

/-- The actual capped count never exceeds the additional ordinary PR count on a compatible
setup profile. This is a deterministic semantic relation, independent of the cap errors. -/
theorem cappedCount_le_ordinaryCount (p : Profile n)
    (hp : profileTranscript S.protocol p S.setup.length = S.setup) :
    S.cappedCount p ≤ S.ordinaryCount p := by
  let E := S.caps.endHistory S.protocol S.caps.global S.setup p
  have he : E = profileTranscript S.protocol p
      (S.setup.length + S.caps.stepsFuel S.protocol S.caps.global S.setup p) :=
    S.caps.endHistory_eq_transcript S.protocol p S.caps.global S.setup hp
  have hlen : E.length = S.setup.length + S.caps.stepsFuel S.protocol S.caps.global S.setup p := by
    rw [he]
    exact transcript_length _ _ _ _
  have hpe : profileTranscript S.protocol p E.length = E := by rw [hlen, ← he]
  have hb := profile_counter_le_pr S.protocol p E hpe S.man
  have hx : (recordState E).next S.man = (recordState S.setup).next S.man + S.cappedCount p :=
    S.caps.next_endHistory _ _ _ _
  have heq := S.setup_add_ordinaryCount p hp
  omega

end Setting









end TieredMatching.Continuation
